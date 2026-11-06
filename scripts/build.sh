#!/usr/bin/env bash
# Build nanoda (versions.env), patched (patches/nanoda.patch), for WebAssembly into javascript/: lean.wasm and
# lean.sha256. Needs the Rust toolchain in rust-toolchain.toml.
set -euo pipefail
cd "$(dirname "$0")/.."
# shellcheck source=../versions.env
. ./versions.env

SRC=build/nanoda
if [ "$(git -C "$SRC" rev-parse HEAD 2>/dev/null)" != "$NANODA_REV" ]; then
  rm -rf "$SRC"
  git init -q "$SRC"
  git -C "$SRC" fetch -q --depth 1 "$NANODA_REPO" "$NANODA_REV"
  git -C "$SRC" checkout -q FETCH_HEAD
  git -C "$SRC" apply ../../patches/nanoda.patch
fi

cargo build --release --locked --target wasm32-unknown-unknown
cp target/wasm32-unknown-unknown/release/lean_wasm.wasm javascript/lean.wasm
(cd javascript && sha256sum lean.wasm >lean.sha256)
ls -l javascript/lean.wasm
