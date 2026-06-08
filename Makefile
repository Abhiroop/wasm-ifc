# ===============================
# Configuration (overrideable)
# ===============================

N        := 10
REPS     := 1000

EXE      := /home/abhiroop/Haskell/wasm-ifc/dist-newstyle/build/x86_64-linux/ghc-9.12.2/wasm-ifc-0.1.0.0/x/wasm-ifc/build/wasm-ifc/wasm-ifc
ITER     := $(shell echo $$(($(N) * $(REPS))))

# ===============================
# Targets
# ===============================

.PHONY: build run bench throughput clean

build:
	cabal build

run: build
	cabal run $(EXE) -- $(N) $(REPS)

bench: build
	hyperfine --warmup 3 '$(EXE) -- $(N) $(REPS)'

throughput:
	@echo "Total iterations: $(ITER)"
	@echo "If time = T seconds, throughput = $(ITER) / T iterations/sec"

clean:
	cabal clean
