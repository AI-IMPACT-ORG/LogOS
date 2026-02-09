#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "dangerous-pragmas-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

# This check relies on ripgrep’s stable regex + glob semantics.
command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# shellcheck source=lib/docs_agda_blocks.sh
source "${SCRIPT_DIR}/lib/docs_agda_blocks.sh"

scan_agda_sources() {
  local pattern="$1"

  local out status
  set +e
  out="$(rg -n \
    --glob '*.agda' \
    --glob '!_build/**' \
    -- "${pattern}" . 2>&1)"
  status="$?"
  set -e
  if [[ "$status" -eq 2 ]]; then
    die $'rg error:\n'"${out}"
  fi
  if [[ "$status" -eq 1 ]]; then
    out=""
  fi
  printf "%s" "${out}"
}

# We already enforce `{-# OPTIONS --safe #-}` everywhere. This check is a belt-and-
# suspenders scan for pragma patterns that can compromise soundness or confuse the
# "safe surface" story (even if Agda rejects them under `--safe`).

BAD_OPTIONS_PATTERN='^[[:space:]]*\{-# OPTIONS[^}]*--(no-termination-check|no-positivity-check|type-in-type|rewriting)'
BAD_TERMINATION_PRAGMAS_PATTERN='^[[:space:]]*\{-# (NO_TERMINATION_CHECK|NO_POSITIVITY_CHECK|TERMINATING|NON_TERMINATING)[[:space:]]*#-\}'
BAD_REWRITE_PRAGMAS_PATTERN='^[[:space:]]*\{-# (REWRITE|BUILTIN[[:space:]]+REWRITE)([[:space:]]|$)'
BAD_FFI_PRAGMAS_PATTERN='^[[:space:]]*\{-# (FOREIGN|COMPILE)([[:space:]]|$)'
BAD_PRIMITIVE_PATTERN='^[[:space:]]*primitive([[:space:]]|$)'

bad_opts="$(scan_agda_sources "${BAD_OPTIONS_PATTERN}")"
if [[ -n "${bad_opts}" ]]; then
  die $'found dangerous Agda OPTIONS flags:\n'"${bad_opts}"
fi

bad_term="$(scan_agda_sources "${BAD_TERMINATION_PRAGMAS_PATTERN}")"
if [[ -n "${bad_term}" ]]; then
  die $'found dangerous termination pragmas:\n'"${bad_term}"
fi

bad_rewrite="$(scan_agda_sources "${BAD_REWRITE_PRAGMAS_PATTERN}")"
if [[ -n "${bad_rewrite}" ]]; then
  die $'found rewriting-related pragmas:\n'"${bad_rewrite}"
fi

bad_ffi="$(scan_agda_sources "${BAD_FFI_PRAGMAS_PATTERN}")"
if [[ -n "${bad_ffi}" ]]; then
  die $'found FFI/COMPILE pragmas:\n'"${bad_ffi}"
fi

bad_prim="$(scan_agda_sources "${BAD_PRIMITIVE_PATTERN}")"
if [[ -n "${bad_prim}" ]]; then
  die $'found primitive declarations:\n'"${bad_prim}"
fi

docs_code="$(docs_scan_agda_blocks)"

docs_bad_opts="$(printf "%s" "${docs_code}" | grep -E '^[^:]+:[0-9]+:.*\{-# OPTIONS[^}]*--(no-termination-check|no-positivity-check|type-in-type|rewriting)' || true)"
if [[ -n "${docs_bad_opts}" ]]; then
  die $'found dangerous Agda OPTIONS flags in docs (Agda code blocks):\n'"${docs_bad_opts}"
fi

docs_bad_term="$(printf "%s" "${docs_code}" | grep -E '^[^:]+:[0-9]+:[[:space:]]*\{-#( )*(NO_TERMINATION_CHECK|NO_POSITIVITY_CHECK|TERMINATING|NON_TERMINATING)([[:space:]]|$)' || true)"
if [[ -n "${docs_bad_term}" ]]; then
  die $'found dangerous termination pragmas in docs (Agda code blocks):\n'"${docs_bad_term}"
fi

docs_bad_rewrite="$(printf "%s" "${docs_code}" | grep -E '^[^:]+:[0-9]+:[[:space:]]*\{-#( )*(REWRITE|BUILTIN[[:space:]]+REWRITE)([[:space:]]|$)' || true)"
if [[ -n "${docs_bad_rewrite}" ]]; then
  die $'found rewriting-related pragmas in docs (Agda code blocks):\n'"${docs_bad_rewrite}"
fi

docs_bad_ffi="$(printf "%s" "${docs_code}" | grep -E '^[^:]+:[0-9]+:[[:space:]]*\{-#( )*(FOREIGN|COMPILE)([[:space:]]|$)' || true)"
if [[ -n "${docs_bad_ffi}" ]]; then
  die $'found FFI/COMPILE pragmas in docs (Agda code blocks):\n'"${docs_bad_ffi}"
fi

docs_bad_prim="$(printf "%s" "${docs_code}" | grep -E '^[^:]+:[0-9]+:[[:space:]]*primitive([[:space:]]|$)' || true)"
if [[ -n "${docs_bad_prim}" ]]; then
  die $'found primitive declarations in docs (Agda code blocks):\n'"${docs_bad_prim}"
fi

echo "dangerous-pragmas-check: OK"
