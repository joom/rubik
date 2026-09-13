# Thin entry points over dune. Crane is built in place from the submodule, so
# nothing here installs over your opam switch.

DUNE ?= dune
ROCQCHK ?= rocqchk
BUILD := _build/default
GENERATED := native/generated
MODULES := Sticker TurnTables BasicRubik Geometry CubieDefs CubieTables Cubie Subgroup Invariant Prune Admissible Tables Phase1 Phase2 Solve Viewer Example

.DEFAULT_GOAL := all
.PHONY: all extract check check-generated tests html install clean

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

clean:
	$(DUNE) clean
	rm -rf $(GENERATED)
