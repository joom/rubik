# Thin entry points over dune. Crane is built in place from the submodule, so
# nothing here installs over your opam switch.

DUNE ?= dune
ROCQCHK ?= rocqchk
BUILD := _build/default
GENERATED := native/generated
MODULES := Sticker TurnTables BasicRubik Geometry CubieDefs CubieTables Cubie Subgroup Invariant Prune Admissible Tables Phase1 Phase2 Solve Viewer Example

.DEFAULT_GOAL := all
.PHONY: all extract check check-generated tests html install clean web

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

check-generated:
	python3 scripts/generate_moves.py --check
	python3 scripts/generate_cubies.py --check

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
WEB_INC := -I$(GENERATED) -Inative -Icrane/theories/cpp -I$(RAYLIB_SRC)
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

clean:
	$(DUNE) clean
	rm -rf $(GENERATED)
