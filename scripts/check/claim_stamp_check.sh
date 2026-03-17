#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - High-risk docs must carry explicit claim stamps (`<!-- CLAIM-STAMP: ... -->`).
# - Every claim stamp must have a valid anchor into an existing file+symbol/label/heading.

set -euo pipefail

CHECK_NAME="claim-stamp-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg
check_require_cmd "${CHECK_NAME}" python3

FORMAT_DOC="docs/Core/Meta/Claim_Stamps.md"
REQUIRED_FILES=(
  "docs/Core/Project/Design_Goals.md"
  "docs/Core/Orientation/LogOS_Overview.lagda.md"
  "docs/Core/Spec/LogOS_Specification.lagda.md"
  "docs/Core/Spec/LogicalTransformers.lagda.md"
  "docs/Core/Meta/Assumptions_Ledger.md"
)

[[ -f "${FORMAT_DOC}" ]] || die "missing claim-stamp format doc: ${FORMAT_DOC}"
rg -q --fixed-strings "Claim stamp format (CNL-lite)" "${FORMAT_DOC}" \
  || die "missing format marker in ${FORMAT_DOC}"

for kind in DEFINITION DERIVED ASSUMPTION ANALOGY PLANNED; do
  rg -q --fixed-strings "CLAIM-STAMP: ${kind} | anchor=" "${FORMAT_DOC}" \
    || die "missing ${kind} format example in ${FORMAT_DOC}"
done

stamps="$(rg -n \
  --glob '*.md' \
  --glob '*.lagda.md' \
  --glob '!**/_build/**' \
  -- '^[[:space:]]*<!--[[:space:]]*CLAIM-STAMP:' docs || true)"

[[ -n "${stamps}" ]] || die "no claim stamps found under docs/"

STAMP_RE='^[[:space:]]*<!--[[:space:]]CLAIM-STAMP:[[:space:]](DEFINITION|DERIVED|ASSUMPTION|ANALOGY|PLANNED)[[:space:]]\\|[[:space:]]anchor=[^|>#]+#[^|>]+[[:space:]]-->[[:space:]]*$'

invalid=""
bad_anchor=""
bad_anchor_path=""
bad_anchor_symbol=""
bad_anchor_md_anchor=""

markdown_anchor_exists() {
  local path="$1"
  local sym="$2"
  python3 - "$path" "$sym" <<'PY'
import pathlib
import re
import sys


def md_slug(text: str) -> str:
    text = text.strip().lower()
    text = re.sub(r"[^a-z0-9\s-]", "", text)
    text = re.sub(r"\s+", "-", text)
    text = re.sub(r"-+", "-", text)
    return text.strip("-")


path = pathlib.Path(sys.argv[1])
sym = sys.argv[2].strip().lower()

for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
    m = re.match(r"^(#{1,6})\s+(.*)$", line)
    if not m:
        continue

    rest = m.group(2).strip()
    explicit = re.search(r"\{#([A-Za-z0-9_-]+)\}\s*$", rest)

    heading = rest
    if explicit:
        anchor_id = explicit.group(1).lower()
        if sym == anchor_id:
            raise SystemExit(0)
        heading = rest[: explicit.start()].rstrip()

    if md_slug(heading) == sym:
        raise SystemExit(0)

    if sym == heading.lower():
        raise SystemExit(0)

raise SystemExit(1)
PY
}

while IFS= read -r line; do
  [[ -n "${line}" ]] || continue

  file="${line%%:*}"
  rest="${line#*:}"
  lno="${rest%%:*}"
  text="${rest#*:}"

  if [[ ! "${text}" =~ ${STAMP_RE} ]]; then
    invalid+="${file}:${lno}:${text}"$'\n'
    continue
  fi

  anchor="$(printf '%s' "${text}" | sed -E 's/^.*anchor=([^[:space:]]+).*$/\1/')"
  path="${anchor%%#*}"
  sym="${anchor#*#}"

  if [[ "${path}" == "${anchor}" || -z "${sym}" ]]; then
    bad_anchor+="${file}:${lno}: missing #symbol in anchor: ${anchor}"$'\n'
    continue
  fi

  path="${path#./}"
  path="${path#/}"

  if [[ ! -f "${path}" ]]; then
    bad_anchor_path+="${file}:${lno}: anchor path does not exist: ${path}"$'\n'
  elif [[ "${path}" == *.agda || "${path}" == *.lagda.md ]]; then
    if ! rg -q --fixed-strings "${sym}" "${path}"; then
      bad_anchor_symbol+="${file}:${lno}: symbol '${sym}' not found in ${path}"$'\n'
    fi
  elif [[ "${path}" == *.tex ]]; then
    if ! rg -q --fixed-strings "\\label{${sym}}" "${path}"; then
      bad_anchor_symbol+="${file}:${lno}: TeX label '${sym}' not found in ${path}"$'\n'
    fi
  elif [[ "${path}" == *.md || "${path}" == *.markdown ]]; then
    if ! markdown_anchor_exists "${path}" "${sym}"; then
      bad_anchor_md_anchor+="${file}:${lno}: markdown anchor '${sym}' not found in ${path}"$'\n'
    fi
  fi
done <<<"${stamps}"

errors=""
if [[ -n "${invalid}" ]]; then
  errors+=$'malformed claim stamps (expected: <!-- CLAIM-STAMP: KIND | anchor=path#symbol -->):\n'"${invalid}"$'\n'
fi
if [[ -n "${bad_anchor}" ]]; then
  errors+=$'invalid claim-stamp anchors:\n'"${bad_anchor}"$'\n'
fi
if [[ -n "${bad_anchor_path}" ]]; then
  errors+=$'claim-stamp anchors reference missing files:\n'"${bad_anchor_path}"$'\n'
fi
if [[ -n "${bad_anchor_symbol}" ]]; then
  errors+=$'claim-stamp anchors reference missing symbols:\n'"${bad_anchor_symbol}"$'\n'
fi
if [[ -n "${bad_anchor_md_anchor}" ]]; then
  errors+=$'claim-stamp anchors reference missing markdown anchors:\n'"${bad_anchor_md_anchor}"$'\n'
fi
if [[ -n "${errors}" ]]; then
  die $'\n'"${errors}"
fi

missing=""
for file in "${REQUIRED_FILES[@]}"; do
  if [[ ! -f "${file}" ]]; then
    missing+="${file} (missing file)"$'\n'
    continue
  fi
  if ! rg -q -- 'CLAIM-STAMP:' "${file}"; then
    missing+="${file}"$'\n'
  fi
done

if [[ -n "${missing}" ]]; then
  die $'missing required claim stamps in high-risk docs:\n'"${missing}"
fi

echo "${CHECK_NAME}: OK"
