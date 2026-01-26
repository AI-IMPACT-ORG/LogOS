#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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

README="README.md"
[[ -f "${README}" ]] || die "missing ${README}"

bad=""

# Expect README pack bullets to use the form:
#   - Name (stable|experimental|scaffold|deprecated): `LogOS/Packs/.../(All|Core|Kernel).agda`
#
# We validate the *first* backticked path on each labeled line against the
# file's declared `packTrust` level.

while IFS= read -r line; do
  if [[ ! "$line" =~ \(stable\)|\(experimental\)|\(scaffold\)|\(deprecated\) ]]; then
    continue
  fi

  level="$(printf '%s' "$line" | sed -nE 's/^.*\\((stable|experimental|scaffold|deprecated)\\):.*$/\\1/p')"
  [[ -n "$level" ]] || continue

  path="$(printf '%s' "$line" | sed -nE 's/^.*\\):[[:space:]]*`([^`]+)`.*$/\\1/p')"
  [[ -n "$path" ]] || continue

  case "$path" in
    LogOS/Packs/*/*.agda|LogOS/Packs/*/*/*.agda) ;;
    *) continue ;;
  esac

  if [[ ! -f "$path" ]]; then
    bad+="${README}: missing \`${path}\`"$'\n'
    continue
  fi

  if command -v rg >/dev/null 2>&1; then
    if ! rg -q "^[[:space:]]*packTrust[[:space:]]*=[[:space:]]*record[[:space:]]*\\{[[:space:]]*level[[:space:]]*=[[:space:]]*${level}[[:space:]]*\\}" "$path"; then
      bad+="${README}: \`${path}\` labeled (${level}), but packTrust level does not match"$'\n'
    fi
  else
    if ! grep -qE "^[[:space:]]*packTrust[[:space:]]*=[[:space:]]*record[[:space:]]*\\{[[:space:]]*level[[:space:]]*=[[:space:]]*${level}[[:space:]]*\\}" "$path"; then
      bad+="${README}: \`${path}\` labeled (${level}), but packTrust level does not match"$'\n'
    fi
  fi
done < <(grep -E '^[[:space:]]*-[[:space:]].*\\((stable|experimental|scaffold|deprecated)\\):' "$README" || true)

if [[ -n "$bad" ]]; then
  die $'README pack trust labels drifted:\n'"${bad}"
fi

echo "readme-pack-trust-check: OK"

