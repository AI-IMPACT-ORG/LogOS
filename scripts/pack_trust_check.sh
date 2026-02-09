#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "pack-trust-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

rg_capture() {
  local out status
  set +e
  out="$(rg "$@" 2>&1)"
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

rg_quiet() {
  local out status
  set +e
  out="$(rg -q "$@" 2>&1)"
  status="$?"
  set -e
  if [[ "$status" -eq 2 ]]; then
    die $'rg error:\n'"${out}"
  fi
  return "$status"
}

# Docs claim that pack entrypoints export `packTrust : PackTrust`. Enforce that
# this is present in the core pack entrypoints (All/Core), experimental
# entrypoints (Experimental All/Core), and any pack-level kernel wiring modules.

shopt -s nullglob

FILES=(
  LogOS/Packs/*/All.agda
  LogOS/Packs/*/Core.agda
  LogOS/Packs/*/Kernel.agda
  LogOS/Packs/*/Experimental/All.agda
  LogOS/Packs/*/Experimental/Core.agda
  LogOS/Packs/*/Experimental/Kernel.agda
)

if ((${#FILES[@]} == 0)); then
  die "no pack entrypoints found"
fi

missing_type=""
missing_def=""
inconsistent_levels=""

PACKTRUST_RECORD_RE='^[[:space:]]*packTrust[[:space:]]*=[[:space:]]*record[[:space:]]*\{[[:space:]]*level[[:space:]]*=[[:space:]]*(stable|experimental|scaffold|deprecated)[[:space:]]*\}'
PACKTRUST_ALIAS_RE='^[[:space:]]*packTrust[[:space:]]*=[[:space:]]*PackCore\.packTrust[[:space:]]*$'

extract_level() {
  local file="$1"
  local hits
  hits="$(rg_capture -n -- "${PACKTRUST_RECORD_RE}" "${file}")"
  if [[ -z "${hits}" ]]; then
    return 1
  fi
  if [[ "$(printf "%s\n" "${hits}" | wc -l | tr -d ' ')" != "1" ]]; then
    die "${file}: expected exactly one packTrust definition line, found:\n${hits}"
  fi
  printf "%s\n" "${hits}" | sed -nE 's/^.*level[[:space:]]*=[[:space:]]*(stable|experimental|scaffold|deprecated)[[:space:]]*\\}.*$/\\1/p'
}

for f in "${FILES[@]}"; do
  [[ -f "$f" ]] || continue

  if ! rg_quiet '^[[:space:]]*packTrust[[:space:]]*:[[:space:]]*PackTrust' "$f"; then
    missing_type+="$f"$'\n'
  fi

  if [[ "$f" == */Core.agda ]]; then
    if ! rg_quiet "${PACKTRUST_RECORD_RE}" "$f"; then
      missing_def+="$f"$'\n'
    fi
  else
    if ! rg_quiet "${PACKTRUST_RECORD_RE}" "$f" && ! rg_quiet "${PACKTRUST_ALIAS_RE}" "$f"; then
      missing_def+="$f"$'\n'
    fi
  fi
done

if [[ -n "${missing_type}" ]]; then
  die $'missing `packTrust : PackTrust` in pack entrypoints:\n'"${missing_type}"
fi

if [[ -n "${missing_def}" ]]; then
  die $'missing `packTrust` definition in pack entrypoints:\n'"${missing_def}"
fi

# Consistency: pack-level surfaces should agree on the `packTrust.level`.
#
# We intentionally enforce this only for (All/Core) pairs, because these are the
# public “pack surfaces”. Kernel wiring modules may intentionally carry a
# different label (e.g. scaffold wiring around a stable pack surface).
shopt -s nullglob
for pack_dir in LogOS/Packs/*; do
  [[ -d "${pack_dir}" ]] || continue

  all="${pack_dir}/All.agda"
  core="${pack_dir}/Core.agda"
  if [[ -f "${all}" && -f "${core}" ]]; then
    level_core="$(extract_level "${core}")"
    if rg_quiet "${PACKTRUST_RECORD_RE}" "${all}"; then
      level_all="$(extract_level "${all}")"
    elif rg_quiet "${PACKTRUST_ALIAS_RE}" "${all}"; then
      level_all="${level_core}"
    else
      die "${all}: expected packTrust record literal or alias to PackCore.packTrust"
    fi

    if [[ -n "${level_all}" && -n "${level_core}" && "${level_all}" != "${level_core}" ]]; then
      inconsistent_levels+="${all}: ${level_all}"$'\n'
      inconsistent_levels+="${core}: ${level_core}"$'\n'
      inconsistent_levels+=$'\n'
    fi
  fi

  exp_dir="${pack_dir}/Experimental"
  if [[ -d "${exp_dir}" ]]; then
    exp_all="${exp_dir}/All.agda"
    exp_core="${exp_dir}/Core.agda"
    if [[ -f "${exp_all}" && -f "${exp_core}" ]]; then
      level_core="$(extract_level "${exp_core}")"
      if rg_quiet "${PACKTRUST_RECORD_RE}" "${exp_all}"; then
        level_all="$(extract_level "${exp_all}")"
      elif rg_quiet "${PACKTRUST_ALIAS_RE}" "${exp_all}"; then
        level_all="${level_core}"
      else
        die "${exp_all}: expected packTrust record literal or alias to PackCore.packTrust"
      fi

      if [[ -n "${level_all}" && -n "${level_core}" && "${level_all}" != "${level_core}" ]]; then
        inconsistent_levels+="${exp_all}: ${level_all}"$'\n'
        inconsistent_levels+="${exp_core}: ${level_core}"$'\n'
        inconsistent_levels+=$'\n'
      fi
    fi
  fi
done
shopt -u nullglob

if [[ -n "${inconsistent_levels}" ]]; then
  die $'packTrust levels drifted between pack surfaces (All/Core must match):\n'"${inconsistent_levels}"
fi

echo "pack-trust-check: OK"
