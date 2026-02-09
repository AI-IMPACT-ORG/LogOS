#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "dev.sh: $*" >&2
  exit 1
}

usage() {
  cat <<'EOF'
Usage: scripts/dev.sh [mode]

Modes:
  quick (default)  make ci-policy + tests + docs-curated
  fast             make ci-policy + fast            (legacy splitting)
  tests            make ci-policy + tests
  docs             make ci-policy + docs-curated
  packs            make ci-policy + packs
  ci               make ci
  check-all        make check-all                  (full publication gate)

Examples:
  scripts/dev.sh
  scripts/dev.sh fast
  scripts/dev.sh packs
EOF
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

mode="${1:-quick}"

run() {
  echo "+ $*"
  "$@"
}

case "${mode}" in
  -h|--help|help)
    usage
    exit 0
    ;;
  quick)
    run make ci-policy
    run make tests
    run make docs-curated
    ;;
  fast)
    run make ci-policy
    run make fast
    ;;
  tests)
    run make ci-policy
    run make tests
    ;;
  docs)
    run make ci-policy
    run make docs-curated
    ;;
  packs)
    run make ci-policy
    run make packs
    ;;
  ci)
    run make ci
    ;;
  check-all)
    run make check-all
    ;;
  *)
    die "unknown mode: ${mode} (try: scripts/dev.sh --help)"
    ;;
esac
