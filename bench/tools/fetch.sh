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
# source digests were pinned on first download (2026-09-13); a mismatch means the archive was
# regenerated or tampered with — look before re-pinning either way.
set -euo pipefail

TOOLS=${WASM_BENCH_TOOLS:-$HOME/.local/wasm-bench-tools}
CACHE=$TOOLS/downloads
SCRATCH=$(mktemp -d)
trap 'rm -rf "$SCRATCH"' EXIT
mkdir -p "$TOOLS/bin" "$TOOLS/src" "$CACHE"

WASI_SDK_VERSION=34.0
WASI_SDK_SHA256=b761e3a0721dbae9c09a0059e5fdb2bf917d1b4a8a7b430fb3b5aafb0984b2c4
WASM3_VERSION=0.9.1-beta.1
WASM3_SHA256=05bf303d35feb05e6c5885a31f607ff20daca391d0dd5fa342cc29fbbf8c93d2
WAMR_VERSION=2.4.5
WAMR_SHA256=61e9d4c77e8f7b06d5cea657b2c319b9be5d51ec51ad8f6f576af84cecd391a3
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

# WAMR's iwasm, the Bytecode Alliance's embedded runtime.
install_wamr () {
    local file="iwasm-${WAMR_VERSION}-x86_64-ubuntu-22.04.tar.gz"
    fetch "$file" "https://github.com/bytecodealliance/wasm-micro-runtime/releases/download/WAMR-${WAMR_VERSION}/$file" "$WAMR_SHA256"
    tar -xzf "$CACHE/$file" -C "$SCRATCH" iwasm
    install -m 755 "$SCRATCH/iwasm" "$TOOLS/bin/iwasm"
    echo "WAMR $WAMR_VERSION  $TOOLS/bin/iwasm"
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
[ ${#targets[@]} -gt 0 ] || targets=(wasi-sdk wasm3 wamr wasmi coremark polybench)
for target in "${targets[@]}"; do
    case "$target" in
        wasi-sdk) install_wasi_sdk ;;
        wasm3) install_wasm3 ;;
        wamr) install_wamr ;;
        wasmi) install_wasmi ;;
        coremark) install_coremark ;;
        polybench) install_polybench ;;
        *) echo "unknown target: $target" >&2; exit 2 ;;
    esac
done
