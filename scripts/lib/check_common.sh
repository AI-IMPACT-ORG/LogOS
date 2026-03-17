#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
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

  # Repo policy: scripts live under `<repo>/scripts/**`.
  # Support nested script locations (e.g. `scripts/check/**`, `scripts/metamath/**`)
  # by walking up until we reach the `scripts` directory, then return its parent.
  local dir="${script_dir}"
  while true; do
    if [[ "$(basename "${dir}")" == "scripts" ]]; then
      (cd "${dir}/.." && pwd)
      return 0
    fi
    if [[ "${dir}" == "/" ]]; then
      break
    fi
    dir="$(cd "${dir}/.." && pwd)"
  done

  # Fallback (previous behaviour): parent of the script directory.
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

require_no_with_k() {
  local prefix="$1"
  local flags="$2"

  if printf "%s" "${flags}" | rg -q -- "--with-K"; then
    check_die "${prefix}" "AGDA_FLAGS must not contain --with-K"
  fi
}
