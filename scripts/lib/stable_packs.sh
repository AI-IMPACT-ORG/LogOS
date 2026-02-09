#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

# Small helper for policy scripts:
# discover stable pack roots by reading `packTrust` from `LogOS/Packs/**/All.agda`.

stable_pack_roots() {
  command -v rg >/dev/null 2>&1 || { echo "stable_pack_roots: rg is required" >&2; return 2; }

  local stable_re out status
  stable_re='^[[:space:]]*packTrust[[:space:]]*=[[:space:]]*record[[:space:]]*\{[[:space:]]*level[[:space:]]*=[[:space:]]*stable[[:space:]]*\}'

  out=""
  status=0
  if out="$(rg -l \
    --glob 'LogOS/Packs/**/All.agda' \
    --glob '!_build/**' \
    -- "${stable_re}" . 2>&1)"; then
    status=0
  else
    status="$?"
  fi

  if [[ "$status" -eq 2 ]]; then
    echo "stable_pack_roots: rg error:" >&2
    printf "%s\n" "${out}" >&2
    return 2
  fi

  if [[ "$status" -eq 1 ]]; then
    return 1
  fi

  out="$(
    printf "%s\n" "${out}" \
      | sed 's#^[.]/##' \
      | sed 's#/All[.]agda$##' \
      | sort -u
  )"
  [[ -n "${out}" ]] || return 1
  printf "%s\n" "${out}"
}
