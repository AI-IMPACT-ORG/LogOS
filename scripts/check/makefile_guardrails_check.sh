#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The repository build must stay host-minimal and strict: `--no-libraries --safe` and warnings-as-errors.
# - CI gate shape is stable: `check-all` cleans then runs the telemetry-backed full warm gate; `ci` runs the core warm gate.

set -euo pipefail

CHECK_NAME="makefile-guardrails-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

LIB_ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${LIB_ROOT}"

check_require_cmd "${CHECK_NAME}" rg
check_require_cmd "${CHECK_NAME}" make

[[ -f "Makefile" ]] || die "missing Makefile"
[[ -s "Makefile" ]] || die "empty Makefile"

target_prereqs() {
  local target="$1"
  local line
  line="$(make -np --no-print-directory "${target}" 2>/dev/null | awk -v t="${target}" '$1 == (t ":") {sub(/^[^:]+:[[:space:]]*/, "", $0); print $0; exit}')"
  [[ -n "${line}" ]] || die "Makefile: missing/invalid target '${target}'"
  printf '%s' "${line}"
}

need() {
  local label="$1"
  local pattern="$2"
  rg -q -- "${pattern}" Makefile || die "Makefile: missing/invalid ${label} (pattern: ${pattern})"
}

# Philosophy-critical defaults:
# - stdlib independence (`--no-libraries`)
# - safe surface (`--safe` + per-module safe pragmas checked elsewhere)
# - no K axiom (`--without-K`)
# - strict warnings-as-errors

need "AGDA_FLAGS_BASE includes --no-libraries" '^AGDA_FLAGS_BASE[[:space:]]*\?=[[:space:]].*--no-libraries'
need "AGDA_FLAGS_BASE includes --safe" '^AGDA_FLAGS_BASE[[:space:]]*\?=[[:space:]].*--safe'
need "AGDA_FLAGS_BASE includes -i ." '^AGDA_FLAGS_BASE[[:space:]]*\?=[[:space:]].*-i[[:space:]]*[.]'
need "AGDA_FLAGS_BASE includes --without-K" '^AGDA_FLAGS_BASE[[:space:]]*\?=[[:space:]].*--without-K'
need "AGDA_WARN_FLAGS includes -W all" '^AGDA_WARN_FLAGS[[:space:]]*\?=[[:space:]].*-W[[:space:]]+all'
need "AGDA_WARN_FLAGS includes -W error" '^AGDA_WARN_FLAGS[[:space:]]*\?=[[:space:]].*-W[[:space:]]+error'
need "AGDA_WARN_FLAGS is pristine" '^AGDA_WARN_FLAGS[[:space:]]*\?=[[:space:]]*-W[[:space:]]+all[[:space:]]+-W[[:space:]]+error[[:space:]]*$'

# CI gate shape: cold gate must clean first; warm gate must exist.
read -r -a check_all_prereqs <<< "$(target_prereqs check-all)"
if (( ${#check_all_prereqs[@]} != 2 )); then
  die "check-all must have exactly two prerequisites in Makefile"
fi
if [[ "${check_all_prereqs[0]}" != "clean" || "${check_all_prereqs[1]}" != "check-all-warm" ]]; then
  die "check-all must be 'clean check-all-warm' in Makefile"
fi

read -r -a check_all_warm_prereqs <<< "$(target_prereqs check-all-warm)"
if (( ${#check_all_warm_prereqs[@]} != 4 )); then
  die "check-all-warm must have exactly four prerequisites in Makefile"
fi
if [[ "${check_all_warm_prereqs[0]}" != "check-policy" || "${check_all_warm_prereqs[1]}" != "check-all-agda-telemetry" || "${check_all_warm_prereqs[2]}" != "check-all-docs-telemetry" || "${check_all_warm_prereqs[3]}" != "check-lib" ]]; then
  die "check-all-warm must be 'check-policy check-all-agda-telemetry check-all-docs-telemetry check-lib' in Makefile"
fi

if rg -q '^check-all-with-telemetry:' Makefile; then
  die "check-all-with-telemetry must not exist in Makefile; telemetry is now the default for check-all"
fi

need "make help documents check-all as cold telemetry-backed gate" 'make check-all[[:space:]]+- cold full gate with Agda compile telemetry'
need "make help documents check-all-warm as warm telemetry-backed gate" 'make check-all-warm - warm full gate with Agda compile telemetry'
if rg -q 'check-all-with-telemetry' Makefile; then
  die "Makefile help must not mention check-all-with-telemetry"
fi

read -r -a check_core_prereqs <<< "$(target_prereqs check-core-warm)"
if (( ${#check_core_prereqs[@]} == 0 )); then
  die "check-core-warm must exist in Makefile"
fi

read -r -a ci_prereqs <<< "$(target_prereqs ci)"
if (( ${#ci_prereqs[@]} != 1 )); then
  die "ci must have exactly one prerequisite in Makefile"
fi
if [[ "${ci_prereqs[0]}" != "check-core-warm" ]]; then
  die "ci must be 'check-core-warm' in Makefile"
fi

echo "${CHECK_NAME}: OK"
