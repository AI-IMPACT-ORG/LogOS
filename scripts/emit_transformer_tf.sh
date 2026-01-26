#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

MODE="default"
OUT=""
if [[ "${1:-}" == "--example" ]]; then
  MODE="example"
  shift
fi

BUILD_ROOT="${LIB_ROOT}/_build/emit_transformer_tf"
BIN="${BUILD_ROOT}/emit_transformer_tf"
HS_SRC="${BUILD_ROOT}/MAlonzo/Code/LogOS/Packs/Agents/Experimental/Emit/Backends/TensorFlow/Emit.hs"
HS_DRIVER="${BUILD_ROOT}/EmitDriver.hs"

mkdir -p "${BUILD_ROOT}"

OUT="${1:-${BUILD_ROOT}/transformer_tf.py}"

cd "${LIB_ROOT}"

require_bin() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "emit-transformer-tf: missing $1 in PATH" >&2
    exit 1
  fi
}

find_symbol() {
  local pattern="$1"
  if command -v rg >/dev/null 2>&1; then
    rg -o -m 1 "${pattern}" "${HS_SRC}" || true
  else
    grep -Eo -m 1 "${pattern}" "${HS_SRC}" || true
  fi
}

require_bin agda
require_bin ghc

agda --compile --no-main --ghc-dont-call-ghc \
  --compile-dir="${BUILD_ROOT}" \
  -i . \
  LogOS/Packs/Agents/Experimental/Emit/Backends/TensorFlow/Emit.agda

if [[ ! -f "${HS_SRC}" ]]; then
  echo "emit-transformer-tf: missing ${HS_SRC}" >&2
  exit 1
fi

if [[ "${MODE}" == "example" ]]; then
  EMIT_SYM="$(find_symbol 'd_emitPythonExample_[0-9]+')"
  if [[ -z "${EMIT_SYM}" ]]; then
    echo "emit-transformer-tf: failed to locate example emitter symbol in ${HS_SRC}" >&2
    exit 1
  fi
  EMIT_EXPR="Emit.${EMIT_SYM}"
else
  EMIT_SYM="$(find_symbol 'd_emitPython_[0-9]+')"
  SPEC_SYM="$(find_symbol 'd_defaultSpec_[0-9]+')"
  if [[ -z "${EMIT_SYM}" || -z "${SPEC_SYM}" ]]; then
    echo "emit-transformer-tf: failed to locate emitter symbols in ${HS_SRC}" >&2
    exit 1
  fi
  EMIT_EXPR="Emit.${EMIT_SYM} Emit.${SPEC_SYM}"
fi

cat > "${HS_DRIVER}" <<EOF
-- LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
-- Copyright (C) 2026 AI.IMPACT GmbH
-- SPDX-License-Identifier: GPL-3.0-only

module Main where

import qualified Data.Text as Text
import qualified MAlonzo.Code.LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Emit as Emit
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  let out = case args of
        (p : _) -> p
        [] -> "transformer_tf.py"
  let code = ${EMIT_EXPR}
  writeFile out (Text.unpack code)
  putStrLn ("emit-transformer-tf: wrote " ++ out)
EOF

ghc -i"${BUILD_ROOT}" \
  -outputdir "${BUILD_ROOT}/ghc-out" \
  -o "${BIN}" \
  "${HS_DRIVER}"

"${BIN}" "${OUT}"
