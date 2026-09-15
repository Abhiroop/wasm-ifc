#!/usr/bin/env bash
# Build the driver for the Hackage wasm package's interpreter (TODO.md §I, comparator C3) and
# print its path, for `bench/run.py --binary haskell-wasm=PATH`.
#
# wasm-1.1.1 predates GHC 9.12, so its source is fetched into this directory, patched with
# ghc-9.12.patch, and built with the relaxed bounds in cabal.project. None of it is committed
# except the patch, and none of it touches wasm-ifc's own build.
#
#   ./bench/drivers/haskell-wasm/build.sh
set -euo pipefail
cd "$(dirname "$0")"
if [ ! -d wasm-1.1.1 ]; then
    cabal get wasm-1.1.1 >/dev/null
    if [ -s ghc-9.12.patch ]; then patch -s -p1 -d wasm-1.1.1 < ghc-9.12.patch; fi
fi
cabal build exe:haskell-wasm-driver >&2
cabal list-bin exe:haskell-wasm-driver
