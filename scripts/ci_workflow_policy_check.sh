#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "ci-workflow-policy-check: $*" >&2
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

shopt -s nullglob
WORKFLOWS=(.github/workflows/*.yml .github/workflows/*.yaml)
shopt -u nullglob

if ((${#WORKFLOWS[@]} == 0)); then
  die "no workflow files found in .github/workflows/"
fi

[[ -f ".github/cabal-index-state.txt" ]] || die "missing .github/cabal-index-state.txt"

bad_actions=""
bad_runners=""
missing_index_state_usage=""
unpinned_cabal_cmds=""
missing_cabal_update_false=""

for wf in "${WORKFLOWS[@]}"; do
  # 1) Pin all third-party actions by full commit SHA.
  uses_hits="$(rg_capture -n -- '^[[:space:]]*uses:[[:space:]]*[^#]+' "${wf}")"
  if [[ -n "${uses_hits}" ]]; then
    while IFS= read -r hit; do
      [[ -n "${hit}" ]] || continue

      lineno="${hit%%:*}"
      line="${hit#*:}"
      value="${line#*uses:}"
      value="${value%%#*}"
      value="$(printf "%s" "${value}" | sed -E 's/^[[:space:]]*//; s/[[:space:]]*$//')"
      value="${value#\"}"
      value="${value%\"}"
      value="${value#\'}"
      value="${value%\'}"

      if [[ -z "${value}" ]]; then
        bad_actions+="${wf}:${lineno}: empty uses target"$'\n'
        continue
      fi

      case "${value}" in
        ./* | ../* | docker://*)
          continue
          ;;
      esac

      if [[ "${value}" != *"@"* ]]; then
        bad_actions+="${wf}:${lineno}: ${value} (missing @ref)"$'\n'
        continue
      fi

      ref="${value##*@}"
      if [[ ! "${ref}" =~ ^[0-9a-fA-F]{40}$ ]]; then
        bad_actions+="${wf}:${lineno}: ${value} (ref is not a 40-hex SHA)"$'\n'
      fi
    done <<<"${uses_hits}"
  fi

  # 2) Avoid runner drift: ban *-latest labels.
  latest_hits="$(rg_capture -n -- '(ubuntu|macos|windows)-latest' "${wf}")"
  if [[ -n "${latest_hits}" ]]; then
    bad_runners+="${wf}:"$'\n'"${latest_hits}"$'\n'
  fi

  # 3) Cabal must be used with a pinned index-state.
  if ! rg_quiet 'cabal-index-state\.txt' "${wf}"; then
    missing_index_state_usage+="${wf}: missing cabal-index-state.txt reference"$'\n'
  fi

  cabal_update_hits="$(rg_capture -n -- '\\bcabal([[:space:]]+v2)?[[:space:]]+update\\b' "${wf}")"
  if [[ -n "${cabal_update_hits}" ]]; then
    while IFS= read -r hit; do
      [[ -n "${hit}" ]] || continue
      lineno="${hit%%:*}"
      line="${hit#*:}"
      if [[ "${line}" != *"--index-state"* ]]; then
        unpinned_cabal_cmds+="${wf}:${lineno}: cabal update without --index-state"$'\n'
      fi
    done <<<"${cabal_update_hits}"
  fi

  cabal_install_hits="$(rg_capture -n -- '\\bcabal([[:space:]]+v2)?[[:space:]]+install\\b' "${wf}")"
  if [[ -n "${cabal_install_hits}" ]]; then
    while IFS= read -r hit; do
      [[ -n "${hit}" ]] || continue
      lineno="${hit%%:*}"
      line="${hit#*:}"
      if [[ "${line}" != *"--index-state"* ]]; then
        unpinned_cabal_cmds+="${wf}:${lineno}: cabal install without --index-state"$'\n'
      fi
    done <<<"${cabal_install_hits}"
  fi

  if rg_quiet 'haskell-actions/setup@' "${wf}"; then
    if ! rg_quiet '^[[:space:]]*cabal-update:[[:space:]]*false([[:space:]]*#.*)?$' "${wf}"; then
      missing_cabal_update_false+="${wf}: haskell-actions/setup used without cabal-update: false"$'\n'
    fi
  fi
done

if [[ -f ".github/workflows/ci.yml" ]]; then
  if ! rg_quiet '^[[:space:]]*make[[:space:]]+check-all([[:space:]]|$)' ".github/workflows/ci.yml"; then
    die ".github/workflows/ci.yml must run make check-all to enforce the cold full gate"
  fi
fi

errors=""

if [[ -n "${bad_actions}" ]]; then
  errors+=$'Unpinned actions (use full 40-hex SHA in uses: ...@<sha>):\n'"${bad_actions}"$'\n'
fi

if [[ -n "${bad_runners}" ]]; then
  errors+=$'Runner drift (ban *-latest; pin e.g. ubuntu-24.04):\n'"${bad_runners}"$'\n'
fi

if [[ -n "${missing_index_state_usage}" ]]; then
  errors+=$'Cabal index-state must be referenced (use .github/cabal-index-state.txt):\n'"${missing_index_state_usage}"$'\n'
fi

if [[ -n "${unpinned_cabal_cmds}" ]]; then
  errors+=$'Cabal commands must use --index-state:\n'"${unpinned_cabal_cmds}"$'\n'
fi

if [[ -n "${missing_cabal_update_false}" ]]; then
  errors+=$'Disable implicit cabal update in haskell-actions/setup (set cabal-update: false):\n'"${missing_cabal_update_false}"$'\n'
fi

if [[ -n "${errors}" ]]; then
  die $'\n'"${errors}"
fi

echo "ci-workflow-policy-check: OK"
