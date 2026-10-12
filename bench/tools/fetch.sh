#!/usr/bin/env bash
# Install what the benchmarks need but the repository must not contain — toolchains, other
# WebAssembly runtimes, third-party benchmark sources — into ~/.local/wasm-bench-tools, without
# root. Idempotent, and a verified download cache means a re-install needs no network.
#
#   ./bench/tools/fetch.sh                  # everything
#   ./bench/tools/fetch.sh wasm3 coremark   # just these
#   WASM_BENCH_TOOLS=/elsewhere ./bench/tools/fetch.sh
#
# Every version and checksum is pinned: a benchmark result names the toolchain and runtimes that
# produced it, so none of them may drift underneath. Release digests are the ones GitHub
# publishes on the asset (API field `digest`). GitHub publishes none for commit archives, so the
# source digests were pinned on first download (2026-09-13; WAMR's on 2026-10-12); a mismatch means the archive was
# regenerated or tampered with — look before re-pinning either way.
set -euo pipefail

TOOLS=${WASM_BENCH_TOOLS:-$HOME/.local/wasm-bench-tools}
CACHE=$TOOLS/downloads
SCRATCH=$(mktemp -d)
trap 'rm -rf "$SCRATCH"' EXIT
mkdir -p "$TOOLS/bin" "$TOOLS/src" "$CACHE"

WASI_SDK_VERSION=34.0
WASI_SDK_SHA256=b761e3a0721dbae9c09a0059e5fdb2bf917d1b4a8a7b430fb3b5aafb0984b2c4
# (wasm3 replaced the binaries of this release on 2026-09-14, four days after publishing it and
# a day after the first pin, 05bf303d…; this is the digest GitHub publishes for the asset now.)
WASM3_VERSION=0.9.1-beta.1
WASM3_SHA256=3d6d56112f38e87ce41fcd17d88b15646ebf0672fe44ff2ffdc2ab10df9edbb8
WAMR_VERSION=2.4.5
WAMR_SHA256=61e9d4c77e8f7b06d5cea657b2c319b9be5d51ec51ad8f6f576af84cecd391a3
WAMR_SOURCE_SHA256=1ab09d51099f276ca4a1d6629f6b589aab2bd0caa01445e05031a4bed22c199b
WASMTIME_VERSION=48.0.1
WASMTIME_SHA256=4c2e31b68ad99e0a519f225a261fda099eb15f056d4a24fdb3c2a46517bde1df
WASMI_VERSION=2.0.0
WASMI_SHA256=fccca87717806246cadab3aec0e3b136742198d1562d6e0af4362f38b6bcc334
COREMARK_COMMIT=1f483d5b8316753a742cbf5590caf5bd0a4e4777
COREMARK_SHA256=4067e7f260218df13f2875d8f821a8ff32a84153c6e0759d7c89f96c0a8bf987
POLYBENCH_COMMIT=3e872547cef7e5c9909422ef1e6af03cf4e56072
POLYBENCH_SHA256=79add9ee16277733d5811a0a3dfc4e968249f45acaf150f9cbbbc5a36157c766

# fetch FILE URL SHA256: make sure the cache holds FILE with that digest, downloading if needed.
fetch () {
    local file=$1 url=$2 sha=$3
    if [ ! -s "$CACHE/$file" ]; then
        echo "downloading $url"
        curl -fsSL --retry 3 -o "$CACHE/$file.part" "$url"
        mv "$CACHE/$file.part" "$CACHE/$file"
    fi
    echo "$sha  $CACHE/$file" | sha256sum -c --quiet - || { echo "checksum mismatch: $CACHE/$file" >&2; exit 1; }
}

# clang + wasm-ld + a WASI Preview 1 libc: builds the real-program tier.
install_wasi_sdk () {
    local name="wasi-sdk-${WASI_SDK_VERSION}-x86_64-linux"
    if [ ! -x "$TOOLS/$name/bin/clang" ]; then
        fetch "$name.tar.gz" "https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-${WASI_SDK_VERSION%%.*}/$name.tar.gz" "$WASI_SDK_SHA256"
        tar -xzf "$CACHE/$name.tar.gz" -C "$TOOLS"
    fi
    ln -sfn "$name" "$TOOLS/wasi-sdk"
    echo "wasi-sdk $WASI_SDK_VERSION  $TOOLS/wasi-sdk/bin/clang"
}

# The classic fast C interpreter (a single static binary).
install_wasm3 () {
    local file="wasm3-${WASM3_VERSION}-linux-x64.elf"
    fetch "$file" "https://github.com/wasm3/wasm3/releases/download/v${WASM3_VERSION}/wasm3-linux-x64.elf" "$WASM3_SHA256"
    install -m 755 "$CACHE/$file" "$TOOLS/bin/wasm3"
    echo "wasm3 $WASM3_VERSION  $TOOLS/bin/wasm3"
}

# WAMR's iwasm, the Bytecode Alliance's embedded runtime. The release binary is built on Ubuntu
# 22.04 and needs a newer libstdc++ than some systems have (Enterprise Linux 9, for one); where
# it does not run, iwasm is built from the source of the same release instead (needs cmake and a
# C compiler), with its interpreter only: no JIT, no ahead-of-time loader, and no vector
# instructions, which the fast interpreter would fetch another library for.
install_wamr () {
    local file="iwasm-${WAMR_VERSION}-x86_64-ubuntu-22.04.tar.gz"
    fetch "$file" "https://github.com/bytecodealliance/wasm-micro-runtime/releases/download/WAMR-${WAMR_VERSION}/$file" "$WAMR_SHA256"
    tar -xzf "$CACHE/$file" -C "$SCRATCH" iwasm
    install -m 755 "$SCRATCH/iwasm" "$TOOLS/bin/iwasm"
    if "$TOOLS/bin/iwasm" --version >/dev/null 2>&1; then
        echo "WAMR $WAMR_VERSION  $TOOLS/bin/iwasm"
        return
    fi
    echo "the release binary of iwasm does not run here: building WAMR $WAMR_VERSION from source"
    local source="wamr-src-${WAMR_VERSION}.tar.gz"
    fetch "$source" "https://codeload.github.com/bytecodealliance/wasm-micro-runtime/tar.gz/refs/tags/WAMR-${WAMR_VERSION}" "$WAMR_SOURCE_SHA256"
    tar -xzf "$CACHE/$source" -C "$SCRATCH"
    local linux="$SCRATCH/wasm-micro-runtime-WAMR-${WAMR_VERSION}/product-mini/platforms/linux"
    cmake -S "$linux" -B "$SCRATCH/wamr-build" -DCMAKE_BUILD_TYPE=Release -DWAMR_BUILD_AOT=0 -DWAMR_BUILD_SIMD=0 >"$SCRATCH/wamr-cmake.log" 2>&1 \
        || { tail -20 "$SCRATCH/wamr-cmake.log" >&2; exit 1; }
    nice -n 19 cmake --build "$SCRATCH/wamr-build" -j4 >"$SCRATCH/wamr-make.log" 2>&1 || { tail -20 "$SCRATCH/wamr-make.log" >&2; exit 1; }
    install -m 755 "$SCRATCH/wamr-build/iwasm" "$TOOLS/bin/iwasm"
    echo "WAMR $WAMR_VERSION (built from source)  $TOOLS/bin/iwasm"
}

# Wasmtime, whose three tiers the benchmarks run: Cranelift, Winch and the Pulley interpreter.
install_wasmtime () {
    local name="wasmtime-v${WASMTIME_VERSION}-x86_64-linux"
    fetch "$name.tar.xz" "https://github.com/bytecodealliance/wasmtime/releases/download/v${WASMTIME_VERSION}/$name.tar.xz" "$WASMTIME_SHA256"
    tar -xJf "$CACHE/$name.tar.xz" -C "$SCRATCH" "$name/wasmtime"
    install -m 755 "$SCRATCH/$name/wasmtime" "$TOOLS/bin/wasmtime"
    echo "wasmtime $WASMTIME_VERSION  $TOOLS/bin/wasmtime"
}

# wasmi, the Rust interpreter.
install_wasmi () {
    local name="wasmi-v${WASMI_VERSION}-x86_64-linux-full"
    fetch "$name.tar.xz" "https://github.com/wasmi-labs/wasmi/releases/download/v${WASMI_VERSION}/$name.tar.xz" "$WASMI_SHA256"
    tar -xJf "$CACHE/$name.tar.xz" -C "$SCRATCH" "$name/wasmi"
    install -m 755 "$SCRATCH/$name/wasmi" "$TOOLS/bin/wasmi"
    echo "wasmi $WASMI_VERSION  $TOOLS/bin/wasmi"
}

# install_source NAME FILE URL SHA256 DIR: a source tree in src/, reachable as src/NAME.
install_source () {
    local name=$1 file=$2 url=$3 sha=$4 dir=$5
    fetch "$file" "$url" "$sha"
    [ -d "$TOOLS/src/$dir" ] || tar -xzf "$CACHE/$file" -C "$TOOLS/src"
    ln -sfn "$dir" "$TOOLS/src/$name"
    echo "$name  $TOOLS/src/$name"
}

install_coremark () {
    install_source coremark "coremark-${COREMARK_COMMIT:0:8}.tar.gz" \
        "https://codeload.github.com/eembc/coremark/tar.gz/$COREMARK_COMMIT" "$COREMARK_SHA256" "coremark-$COREMARK_COMMIT"
}

install_polybench () {
    install_source polybench "polybench-c-4.2.1-${POLYBENCH_COMMIT:0:8}.tar.gz" \
        "https://codeload.github.com/MatthiasJReisinger/PolyBenchC-4.2.1/tar.gz/$POLYBENCH_COMMIT" "$POLYBENCH_SHA256" "PolyBenchC-4.2.1-$POLYBENCH_COMMIT"
}

targets=("$@")
[ ${#targets[@]} -gt 0 ] || targets=(wasi-sdk wasm3 wamr wasmtime wasmi coremark polybench)
for target in "${targets[@]}"; do
    case "$target" in
        wasi-sdk) install_wasi_sdk ;;
        wasm3) install_wasm3 ;;
        wamr) install_wamr ;;
        wasmtime) install_wasmtime ;;
        wasmi) install_wasmi ;;
        coremark) install_coremark ;;
        polybench) install_polybench ;;
        *) echo "unknown target: $target" >&2; exit 2 ;;
    esac
done
