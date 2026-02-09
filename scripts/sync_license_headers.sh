#!/usr/bin/env bash
set -euo pipefail

# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# shellcheck source=scripts/lib/header_policy.sh
source "${SCRIPT_DIR}/lib/header_policy.sh"

cd "${LIB_ROOT}"

updated=0
while IFS= read -r f; do
  [[ -f "$f" ]] || continue
  [[ "$f" == "scripts/lib/header_policy.sh" ]] && continue
  for legacy in "${HEADER_LEGACY_TITLE_LINES[@]}"; do
    if grep -Fq "$legacy" "$f"; then
      perl -0pi -e "s/\\Q${legacy}\\E/${HEADER_TITLE_LINE}/g" "$f"
      updated=$((updated + 1))
      break
    fi
  done
done < <(header_list_allowlisted_files)

echo "sync-license-headers: updated ${updated} file(s)"
