#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

check_die() {
  local prefix="$1"
  shift
  echo "${prefix}: $*" >&2
  exit 1
}

check_repo_root() {
  local script_path="$1"
  local script_dir
  script_dir="$(cd "$(dirname "${script_path}")" && pwd)"
  (cd "${script_dir}/.." && pwd)
}

check_require_cmd() {
  local prefix="$1"
  local cmd="$2"
  command -v "${cmd}" >/dev/null 2>&1 || check_die "${prefix}" "${cmd} is required for this check"
}

check_rg_capture() {
  local prefix="$1"
  shift
  local out status
  set +e
  out="$(rg "$@" 2>&1)"
  status="$?"
  set -e
  if [[ "${status}" -eq 2 ]]; then
    check_die "${prefix}" $'rg error:\n'"${out}"
  fi
  if [[ "${status}" -eq 1 ]]; then
    out=""
  fi
  printf "%s" "${out}"
}
