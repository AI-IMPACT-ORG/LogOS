#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "readme-pack-trust-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

README="README.md"
[[ -f "${README}" ]] || die "missing ${README}"

bad=""

# Expect README pack bullets to use the form:
#   - Name (stable|experimental|scaffold|deprecated): `LogOS/Packs/.../(All|Core|Kernel).agda`
#
# We validate the *first* backticked path on each labeled line against the
# file's declared `packTrust` level.

hits=""
status=0
set +e
hits="$(rg -n --with-filename -- '^[[:space:]]*-[[:space:]].*\((stable|experimental|scaffold|deprecated)\):' "$README" 2>&1)"
status="$?"
set -e
if [[ "$status" -eq 2 ]]; then
  die $'rg error:\n'"${hits}"
fi
if [[ "$status" -eq 1 ]]; then
  die "no README pack bullet lines found (expected: - Name (stable|experimental|scaffold|deprecated): LogOS/Packs/.../(All|Core|Kernel).agda)"
fi

while IFS= read -r hit; do
  [[ -z "${hit}" ]] && continue

  file="${hit%%:*}"
  rest="${hit#*:}"
  lineno="${rest%%:*}"
  line="${rest#*:}"

  if [[ ! "$line" =~ \(stable\)|\(experimental\)|\(scaffold\)|\(deprecated\) ]]; then
    die "${file}:${lineno}: internal error: unexpected rg match format"
  fi

  level="$(printf '%s' "$line" | sed -nE 's/^.*\((stable|experimental|scaffold|deprecated)\):.*$/\1/p')"
  [[ -n "$level" ]] || die "${file}:${lineno}: cannot parse trust label level"

  # shellcheck disable=SC2016
  path="$(printf '%s' "$line" | sed -nE 's/^.*\):[[:space:]]*`([^`]+)`.*$/\1/p')"
  if [[ -z "$path" ]]; then
    bad+="${file}:${lineno}: missing backticked pack entrypoint path after trust label"$'\n'
    continue
  fi

  case "$path" in
    LogOS/Packs/*/All.agda|LogOS/Packs/*/Core.agda|LogOS/Packs/*/Kernel.agda) ;;
    *)
      bad+="${file}:${lineno}: unexpected pack entrypoint path (expected All/Core/Kernel): \`${path}\`"$'\n'
      continue
      ;;
  esac

  if [[ ! -f "$path" ]]; then
    bad+="${file}:${lineno}: missing \`${path}\`"$'\n'
    continue
  fi

  # Prefer a direct `packTrust = record { level = ... }` literal, but allow
  # `All.agda` entrypoints to alias their `packTrust` to the pack core module
  # (standardised as `packTrust = PackCore.packTrust`).
  if rg -q "^[[:space:]]*packTrust[[:space:]]*=[[:space:]]*record[[:space:]]*\\{[[:space:]]*level[[:space:]]*=[[:space:]]*${level}[[:space:]]*\\}" "$path"; then
    continue
  fi

  if rg -q '^[[:space:]]*packTrust[[:space:]]*=[[:space:]]*PackCore\.packTrust[[:space:]]*$' "$path"; then
    core_path="${path%/All.agda}/Core.agda"
    if [[ ! -f "${core_path}" ]]; then
      bad+="${file}:${lineno}: \`${path}\` aliases packTrust, but core entrypoint is missing: \`${core_path}\`"$'\n'
      continue
    fi
    if ! rg -q "^[[:space:]]*packTrust[[:space:]]*=[[:space:]]*record[[:space:]]*\\{[[:space:]]*level[[:space:]]*=[[:space:]]*${level}[[:space:]]*\\}" "${core_path}"; then
      bad+="${file}:${lineno}: \`${path}\` labeled (${level}), but \`${core_path}\` packTrust level does not match"$'\n'
    fi
    continue
  fi

  bad+="${file}:${lineno}: \`${path}\` labeled (${level}), but packTrust is neither a record literal nor an allowed alias"$'\n'
done <<< "${hits}"

if [[ -n "$bad" ]]; then
  die $'README pack trust labels drifted:\n'"${bad}"
fi

echo "readme-pack-trust-check: OK"
