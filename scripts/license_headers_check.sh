#!/usr/bin/env bash
set -euo pipefail

# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

die() {
  echo "license-headers-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

TITLE_LINE="LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning"
COPY_LINE="Copyright (C) 2026 AI.IMPACT GmbH"
SPDX_LINE="SPDX-License-Identifier: GPL-3.0-only"

scan_files() {
  if command -v git >/dev/null 2>&1 && git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    # Scan both tracked files and untracked-but-not-ignored files so new sources
    # cannot silently bypass the header policy.
    git ls-files -z --cached --others --exclude-standard
    return 0
  fi

  find . \
    -type f \
    -not -path './_build/*' \
    -not -path './.git/*' \
    -not -path './.agda/*' \
    -print0
}

bad=""
while IFS= read -r -d '' f; do
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
  grep -Fq "$TITLE_LINE" <<<"$head" || bad+="${f}: missing title header"$'\n'
  grep -Fq "$COPY_LINE" <<<"$head" || bad+="${f}: missing copyright header"$'\n'
  grep -Fq "$SPDX_LINE" <<<"$head" || bad+="${f}: missing SPDX identifier"$'\n'
done < <(scan_files)

if [[ -n "$bad" ]]; then
  die $'missing required per-file license header:\n'"${bad}"
fi

echo "license-headers-check: OK"
