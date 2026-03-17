#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - CI must be reproducible: pin third-party actions by full commit SHA and avoid `*-latest` runners.
# - CI must be strict: the default CI lane must enforce the core gate, and at least one
#   workflow must enforce the cold full gate (`make check-all`).
# - CI must be hardened: minimal permissions, no credential persistence, strict bash defaults, and
#   cancel in-progress runs on the same ref.

set -euo pipefail

CHECK_NAME="ci-workflow-policy-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

LIB_ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"

cd "${LIB_ROOT}"

check_require_cmd "${CHECK_NAME}" rg

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

warn_profile_is_strict() {
  local value="$1"
  local -a warn_tokens=()
  local name
  local i
  local has_all=0
  local has_error=0

  read -r -a warn_tokens <<< "${value}"
  if (( ${#warn_tokens[@]} != 4 )); then
    return 1
  fi

  for ((i = 0; i < ${#warn_tokens[@]}; i += 2)); do
    if [[ "${warn_tokens[i]}" != "-W" ]]; then
      return 1
    fi
    name="${warn_tokens[i+1]}"
    case "${name}" in
      all)
        has_all=1
        ;;
      error)
        has_error=1
        ;;
      *)
        return 1
        ;;
    esac
  done

  if (( has_all == 0 || has_error == 0 )); then
    return 1
  fi
  return 0
}

normalize_warn_value() {
  local value="$1"
  value="$(printf "%s" "${value}" | sed -E 's/^[[:space:]]*//; s/[[:space:]]*(#.*)?$//')"
  case "${value}" in
    \'*\') value="${value#\'}"; value="${value%\'}" ;;
    \"*\") value="${value#\"}"; value="${value%\"}" ;;
  esac
  value="${value//--W /-W }"
  printf "%s" "${value}"
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
strictness_downgrades=""
agda_warn_profile_violations=""
missing_gate_enforcement=""
workflow_hardening_violations=""
has_any_full_gate=0

for wf in "${WORKFLOWS[@]}"; do
  workflow_has_full_gate=0

  if rg_quiet -- '^[[:space:]]*make[[:space:]]+check-all([[:space:]]|$)' "${wf}" || \
     rg_quiet -- '^[[:space:]]*- check-all([[:space:]]|$)' "${wf}"; then
    workflow_has_full_gate=1
    has_any_full_gate=1
  fi

  # 0) Hardening baseline: minimal permissions + concurrency + strict bash defaults.
  if ! rg_quiet --multiline -- '^permissions:[[:space:]]*$' "${wf}"; then
    workflow_hardening_violations+="${wf}: missing top-level permissions block (require minimal permissions, e.g. contents: read)"$'\n'
  else
    # Require a minimal read-only token: only `contents: read`, nothing else.
    if ! rg_quiet --multiline -- '^permissions:[[:space:]]*\n[[:space:]]+contents:[[:space:]]+read([[:space:]]*#.*)?\n(?:\n|concurrency:|on:|jobs:)' "${wf}"; then
      workflow_hardening_violations+="${wf}: permissions must be minimal (exactly 'contents: read')"$'\n'
    fi
  fi

  if ! rg_quiet -- '^concurrency:[[:space:]]*$' "${wf}"; then
    workflow_hardening_violations+="${wf}: missing concurrency block (avoid duplicate runs; set cancel-in-progress: true)"$'\n'
  else
    if ! rg_quiet --fixed-strings "group: \${{ github.workflow }}-\${{ github.ref }}" "${wf}"; then
      workflow_hardening_violations+="${wf}: concurrency must set group to \${{ github.workflow }}-\${{ github.ref }}"$'\n'
    fi
    if ! rg_quiet -- '^[[:space:]]+cancel-in-progress:[[:space:]]+true([[:space:]]*#.*)?$' "${wf}"; then
      workflow_hardening_violations+="${wf}: concurrency must set cancel-in-progress: true"$'\n'
    fi
  fi

  # Require strict bash as the default shell for all `run:` steps.
  if ! rg_quiet --multiline -- '^defaults:[[:space:]]*$' "${wf}"; then
    workflow_hardening_violations+="${wf}: missing defaults block (require strict bash run shell)"$'\n'
  else
    if ! rg_quiet --fixed-strings '  run:' "${wf}" || \
       ! rg_quiet --fixed-strings '    shell: bash --noprofile --norc -euo pipefail {0}' "${wf}"; then
      workflow_hardening_violations+="${wf}: defaults.run.shell must be strict: bash --noprofile --norc -euo pipefail {0}"$'\n'
    fi
  fi

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

  # 1b) Avoid credential persistence by checkout.
  if rg_quiet -- '^[[:space:]]*uses:[[:space:]]*actions/checkout@' "${wf}"; then
    if ! rg_quiet -- '^[[:space:]]*persist-credentials:[[:space:]]*false([[:space:]]*#.*)?$' "${wf}"; then
      workflow_hardening_violations+="${wf}: actions/checkout must set persist-credentials: false"$'\n'
    fi
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

  # 4) Ban obvious strictness downgrades in workflow commands.
  #
  # We keep CI on the strict profile and forbid skip flags / fast profile flags.
  downgrade_hits="$(rg_capture -n -- 'PIPELINE_SKIP[[:space:]]*=[[:space:]]*1|AGDA_FLAGS_FAST|--no-exact-split|--allow-unsolved-metas|--allow-incomplete-matches|--no-termination-check|--no-positivity-check|AGDA_WARN_FLAGS[^[:cntrl:]]*(-W[[:space:]]*noError|-W[[:space:]]*noWarning)' "${wf}")"
  if [[ -n "${downgrade_hits}" ]]; then
    strictness_downgrades+="${wf}:"$'\n'"${downgrade_hits}"$'\n'
  fi

  # 4b) Ensure any explicit AGDA_WARN_FLAGS assignment is strict:
  #     it must be exactly `-W all -W error`.
  warn_assign_hits="$(rg_capture -n -- 'AGDA_WARN_FLAGS[[:space:]]*=' "${wf}")"
  if [[ -n "${warn_assign_hits}" ]]; then
    while IFS= read -r hit; do
      [[ -n "${hit}" ]] || continue
      lineno="${hit%%:*}"
      line="${hit#*:}"
      warn_value="${line#*=}"
      warn_value="$(normalize_warn_value "${warn_value}")"
      if ! warn_profile_is_strict "${warn_value}"; then
        agda_warn_profile_violations+="${wf}:${lineno}: AGDA_WARN_FLAGS is not exact strict profile (\`${warn_value}\`)"$'\n'
      fi
    done <<<"${warn_assign_hits}"
  fi

  warn_env_hits="$(rg_capture -n -- '^[[:space:]]*AGDA_WARN_FLAGS[[:space:]]*:' "${wf}")"
  if [[ -n "${warn_env_hits}" ]]; then
    while IFS= read -r hit; do
      [[ -n "${hit}" ]] || continue
      lineno="${hit%%:*}"
      line="${hit#*:}"
      warn_value="${line#*:}"
      warn_value="$(normalize_warn_value "${warn_value}")"
      if ! warn_profile_is_strict "${warn_value}"; then
        agda_warn_profile_violations+="${wf}:${lineno}: AGDA_WARN_FLAGS is not exact strict profile (\`${warn_value}\`)"$'\n'
      fi
    done <<<"${warn_env_hits}"
  fi

  # 5) Require gate coverage on all workflows that run Agda/build tooling.
  if rg_quiet '(\bcabal([[:space:]]+(v2)?[[:space:]]+)?(install|update)\b.*[Aa]gda|\.agda\b|\.lagda\.md\b|AGDA_WARN_FLAGS|\\bmake[[:space:]]+check-all|\\bmake[[:space:]]+html|\\bmake[[:space:]]+check-[a-z-]*|\\bmake[[:space:]]+check-all-docs|\\bmake[[:space:]]+check-all-agda)' "${wf}"; then
    has_core_gate=0

    if rg_quiet -- '^[[:space:]]*make[[:space:]]+check-core-warm([[:space:]]|$)' "${wf}" || \
       rg_quiet -- '^[[:space:]]*- check-core([[:space:]]|$)' "${wf}"; then
      has_core_gate=1
    fi

    if (( has_core_gate == 0 && workflow_has_full_gate == 0 )); then
      missing_gate_enforcement+="${wf}: must enforce either the core gate (make check-core-warm) or the cold full gate (make check-all)"$'\n'
    fi
  fi
done

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

if [[ -n "${strictness_downgrades}" ]]; then
  errors+=$'Workflow strictness downgrades detected (forbidden):\n'"${strictness_downgrades}"$'\n'
fi

if [[ -n "${agda_warn_profile_violations}" ]]; then
  errors+=$'AGDA warning profile is not explicitly strict in workflow policy:\n'"${agda_warn_profile_violations}"$'\n'
fi

if [[ -n "${missing_gate_enforcement}" ]]; then
  errors+=$'Workflows that run Agda/build steps must enforce a checked gate:\n'"${missing_gate_enforcement}"$'\n'
fi

if (( has_any_full_gate == 0 )); then
  errors+=$'At least one workflow must enforce the cold full gate (make check-all).\n\n'
fi

if [[ -n "${workflow_hardening_violations}" ]]; then
  errors+=$'Workflow hardening violations:\n'"${workflow_hardening_violations}"$'\n'
fi

if [[ -n "${errors}" ]]; then
  die $'\n'"${errors}"
fi

echo "ci-workflow-policy-check: OK"
