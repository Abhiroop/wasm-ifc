#!/usr/bin/env bash
# Install the external toolchains the benchmarks need into ~/.local/wasm-bench-tools — never
# into the repository, and without root. Idempotent: a tool already in place is left alone.
#
#   ./bench/tools/fetch.sh
#   WASM_BENCH_TOOLS=/elsewhere ./bench/tools/fetch.sh
#
# Versions and checksums are pinned. A benchmark result names the toolchain that built its
# binaries, so the toolchain must not drift under it. To upgrade, change a version and its
# digest together; the digest is on the release asset in the GitHub API
# (https://api.github.com/repos/WebAssembly/wasi-sdk/releases/latest, field `digest`).
set -euo pipefail

TOOLS=${WASM_BENCH_TOOLS:-$HOME/.local/wasm-bench-tools}
SCRATCH=$(mktemp -d)
trap 'rm -rf "$SCRATCH"' EXIT

# wasi-sdk: clang + wasm-ld + a WASI Preview 1 libc, for the real-program tier (C → wasm32-wasip1).
WASI_SDK_VERSION=34.0
WASI_SDK_SHA256=b761e3a0721dbae9c09a0059e5fdb2bf917d1b4a8a7b430fb3b5aafb0984b2c4

fetch_wasi_sdk () {
    local name="wasi-sdk-${WASI_SDK_VERSION}-x86_64-linux"
    local dest="$TOOLS/$name"
    if [ -x "$dest/bin/clang" ]; then
        echo "wasi-sdk $WASI_SDK_VERSION: already installed at $dest"
    else
        local url="https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-${WASI_SDK_VERSION%%.*}/$name.tar.gz"
        echo "wasi-sdk $WASI_SDK_VERSION: downloading $url"
        curl -fsSL --retry 3 -o "$SCRATCH/$name.tar.gz" "$url"
        echo "$WASI_SDK_SHA256  $SCRATCH/$name.tar.gz" | sha256sum -c --quiet -
        echo "wasi-sdk $WASI_SDK_VERSION: checksum ok"
        mkdir -p "$TOOLS"
        tar -xzf "$SCRATCH/$name.tar.gz" -C "$TOOLS"
        [ -x "$dest/bin/clang" ] || { echo "wasi-sdk: the archive did not unpack to $dest" >&2; exit 1; }
        echo "wasi-sdk $WASI_SDK_VERSION: installed at $dest"
    fi
    # A stable name for scripts to use, whichever version is current.
    ln -sfn "$name" "$TOOLS/wasi-sdk"
}

fetch_wasi_sdk
echo "clang: $TOOLS/wasi-sdk/bin/clang"
