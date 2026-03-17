#!/usr/bin/env bash
set -euo pipefail

CHECK_NAME="license-headers-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Every allowlisted text file must contain the standard per-file license header (title + copyright + SPDX).
# - Tracked binary assets must be handled explicitly (they cannot carry per-file text headers).

die() { check_die "${CHECK_NAME}" "$*"; }

LIB_ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"

# shellcheck source=scripts/lib/header_policy.sh
source "${SCRIPT_DIR}/lib/header_policy.sh"

cd "${LIB_ROOT}"

bad=""
while IFS= read -r f; do
  # Dedicated license file is checked separately in `scripts/check_gplv3_notice.sh`.
  [[ "$f" == "LICENSE" ]] && continue

  # Skip missing files in a dirty working tree (CI always has a clean checkout).
  [[ -f "$f" ]] || continue

  # Require that any tracked binary assets are explicitly dealt with.
  if ! grep -Iq . "$f"; then
    bad+="${f}: binary file (cannot contain per-file license header)"$'\n'
    continue
  fi

  head="$(sed -n '1,40p' "$f")"
  has_title=0
  if grep -Fq "$HEADER_TITLE_LINE" <<<"$head"; then
    has_title=1
  else
    for legacy_title in "${HEADER_LEGACY_TITLE_LINES[@]}"; do
      if grep -Fq "$legacy_title" <<<"$head"; then
        has_title=1
        break
      fi
    done
  fi
  [[ "$has_title" -eq 1 ]] || bad+="${f}: missing title header"$'\n'
  grep -Fq "$HEADER_COPY_LINE" <<<"$head" || bad+="${f}: missing copyright header"$'\n'
  grep -Fq "$HEADER_SPDX_LINE" <<<"$head" || bad+="${f}: missing SPDX identifier"$'\n'
done < <(header_list_allowlisted_files)

if [[ -n "$bad" ]]; then
  die $'missing required per-file license header:\n'"${bad}"
fi

echo "license-headers-check: OK"
