# Thin entry points over dune. Crane is built in place from the submodule, so
# nothing here installs over your opam switch.

DUNE ?= dune
ROCQCHK ?= rocqchk
BUILD := _build/default
GENERATED := native/generated
MODULES := Cube.Sticker Cube.TurnTables Cube.BasicRubik Cube.Geometry Cube.CubieDefs Cube.CubieTables Cube.Cubie Cube.Group Cube.Parity Cube.ParityTables Cube.Subgroup Cube.Invariant Bounds.Chain Bounds.ChainTables Bounds.Domino Bounds.DominoTables Bounds.Solvable Search.Prune Search.Admissible Search.Tables Search.Phase1 Search.Phase2 Search.Solve Viewer Audit

.DEFAULT_GOAL := all
.PHONY: all extract check check-generated check-chain check-solver tests html install clean web

# Build and audit the proofs. Needs no C++ toolchain and no Crane.
all:
	$(DUNE) build theories

# Extract the viewer to C++ and publish it where CMake expects to find it.
# The C++ files are a side effect of compiling Extract.v rather than declared
# targets, so that compilation has to run instead of being restored from cache.
extract:
	rm -f $(BUILD)/native/Extract.vo
	$(DUNE) build --cache=disabled native/Extract.vo
	@mkdir -p $(GENERATED)
	cp $(BUILD)/native/rubik.h $(BUILD)/native/rubik.cpp $(GENERATED)/

# The three fast generators: each rebuilds its file from scratch and compares.
check-generated:
	python3 scripts/generate_moves.py --check
	python3 scripts/generate_cubies.py --check
	python3 scripts/generate_parity.py --check

# The fourth one, kept out of "check" because it solves several hundred cubes
# and takes about ten minutes. Needs the batch solver:
#   cmake --build build/native --target solve_tool
check-chain:
	python3 scripts/generate_chain.py --check

# Exercise the built solver on scrambles it has never seen and multiply every
# answer back out. This is the one check that covers extraction, the C++
# toolchain and the bindings, none of which the kernel can see. Needs the
# batch solver, as above.
check-solver:
	python3 scripts/check_solver.py

# Recheck the compiled proofs with the kernel, independently of the build.
check: all check-generated
	$(ROCQCHK) -silent -R $(BUILD)/theories Rubik \
	  $(addprefix Rubik.,$(MODULES))

tests: check

html:
	$(DUNE) build @theories/doc
	@echo "Browse $(BUILD)/theories/Rubik.html/index.html"

install:
	$(DUNE) build -p rocq-rubik @install
	$(DUNE) install rocq-rubik

# Build the WebAssembly bundle into docs/, which GitHub Pages serves. The page
# itself, docs/index.html, is hand-written and not touched here; this only
# produces the rubik.js, rubik.wasm and rubik.data it loads. raylib has no
# emscripten port, so it is compiled from the source the native CMake build
# already fetched; configure that first if this errors.
EMXX ?= em++
RAYLIB_SRC ?= build/native/_deps/raylib-src/src
WEB_OBJ := _build/web
WEB_INC := -I$(GENERATED) -Inative -Inative/Bindings -Icrane/theories/cpp -I$(RAYLIB_SRC)
WEB_FLAGS := -std=c++23 -fbracket-depth=1024 -Os -sUSE_GLFW=3
WEB_LINK := -sUSE_GLFW=3 -sALLOW_MEMORY_GROWTH=1 -sEXIT_RUNTIME=0 \
  -sSTACK_SIZE=4MB -sINITIAL_MEMORY=256MB \
  --preload-file assets/fonts@assets/fonts
RAYLIB_UNITS := rcore rshapes rtextures rtext rmodels utils raudio

web: extract
	@test -d $(RAYLIB_SRC) || \
	  (echo "error: raylib sources not at $(RAYLIB_SRC)"; \
	   echo "Run: cmake -S . -B build/native -DCMAKE_BUILD_TYPE=Release"; \
	   exit 1)
	@mkdir -p $(WEB_OBJ)/raylib docs
	@for unit in $(RAYLIB_UNITS); do \
	  $(EMXX) -c -std=gnu11 -x c -Os -DPLATFORM_WEB -DGRAPHICS_API_OPENGL_ES2 \
	    -I$(RAYLIB_SRC) -I$(RAYLIB_SRC)/external/glfw/include \
	    $(RAYLIB_SRC)/$$unit.c -o $(WEB_OBJ)/raylib/$$unit.o || exit 1; \
	done
	emar rcs $(WEB_OBJ)/libraylib.a $(WEB_OBJ)/raylib/*.o
	$(EMXX) $(WEB_FLAGS) $(WEB_INC) -Dmain=rubik_generated_main \
	  -c $(GENERATED)/rubik.cpp -o $(WEB_OBJ)/rubik.o
	$(EMXX) $(WEB_FLAGS) $(WEB_INC) -c web/web_main.cpp -o $(WEB_OBJ)/web_main.o
	$(EMXX) $(WEB_OBJ)/rubik.o $(WEB_OBJ)/web_main.o $(WEB_OBJ)/libraylib.a \
	  $(WEB_LINK) -Os -o docs/rubik.js

# dune's tree holds the WebAssembly objects too. The CMake tree under build/
# is yours to remove.
clean:
	$(DUNE) clean
	rm -rf $(GENERATED)
