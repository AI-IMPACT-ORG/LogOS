#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail
set +m

usage() {
  cat >&2 <<'EOF'
Usage:
  scripts/lib/run_agda_with_telemetry.sh <modules.tsv> -- <agda> <args...>

Telemetry:
  - prefixes Agda output with elapsed time
  - writes a TSV of (ModuleName, Milliseconds, FilePath) for each module Agda reports as "Checking …"
  - prints a heartbeat every N seconds while Agda is silent

Environment variables:
  AGDA_TELEMETRY_HEARTBEAT_SECS   (default: 10; set to 0 to disable)
  AGDA_TELEMETRY_TOP_N            (default: 20)
  AGDA_TIMEOUT_SECS               (default: 0; kill the Agda run after N seconds)
EOF
}

if [[ $# -lt 3 ]]; then
  usage
  exit 2
fi

MODULES_TSV="$1"
shift

if [[ "${1:-}" != "--" ]]; then
  usage
  exit 2
fi
shift

if [[ $# -lt 1 ]]; then
  usage
  exit 2
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "run_agda_with_telemetry.sh: python3 is required" >&2
  exit 2
fi

mkdir -p "$(dirname "${MODULES_TSV}")"
: > "${MODULES_TSV}"

start_epoch="$(date +%s)"
current_file="$(mktemp -t agda_current.XXXXXX)"

heartbeat_secs="${AGDA_TELEMETRY_HEARTBEAT_SECS:-10}"
top_n="${AGDA_TELEMETRY_TOP_N:-20}"

hb_pid=""
watchdog_pid=""
pipeline_pid=""
pipeline_isolated="0"
timed_out_file="$(mktemp -t agda_timeout.XXXXXX)"
: > "${timed_out_file}"
telemetry_stream="${BASH_SOURCE%/*}/run_agda_with_telemetry_stream.py"
telemetry_setsid_cmd=$'set -o pipefail\n"$@" 2>&1 | python3 -u "$TELEMETRY_STREAM" \\\n  --out-tsv "$TELEMETRY_TSV" \\\n  --current-file "$TELEMETRY_CURRENT_FILE"\n'

stop_background_pid() {
  local pid="${1:-}"
  if [[ -z "${pid}" ]]; then
    return 0
  fi
  kill "${pid}" >/dev/null 2>&1 || true
  wait "${pid}" >/dev/null 2>&1 || true
}

terminate_pipeline() {
  local pid="$1"
  local job_pids
  job_pids="$(jobs -pr 2>/dev/null || true)"

  if [[ "${pipeline_isolated}" == "1" ]]; then
    kill -TERM -"${pid}" 2>/dev/null || true
  fi
  kill -TERM "${pid}" 2>/dev/null || true
  if command -v pkill >/dev/null 2>&1; then
    pkill -TERM -P "${pid}" 2>/dev/null || true
  fi
  if [[ -n "${job_pids}" ]]; then
    while IFS= read -r job_pid; do
      [[ -z "${job_pid}" || "${job_pid}" == "${pid}" ]] && continue
      kill -TERM "${job_pid}" 2>/dev/null || true
    done <<< "${job_pids}"
  fi
  sleep 2
  if [[ "${pipeline_isolated}" == "1" ]]; then
    kill -KILL -"${pid}" 2>/dev/null || true
  fi
  kill -KILL "${pid}" 2>/dev/null || true
  if command -v pkill >/dev/null 2>&1; then
    pkill -KILL -P "${pid}" 2>/dev/null || true
  fi
  if [[ -n "${job_pids}" ]]; then
    while IFS= read -r job_pid; do
      [[ -z "${job_pid}" || "${job_pid}" == "${pid}" ]] && continue
      kill -KILL "${job_pid}" 2>/dev/null || true
    done <<< "${job_pids}"
  fi
}

# shellcheck disable=SC2329
cleanup() {
  if [[ -n "${pipeline_pid}" ]]; then
    terminate_pipeline "${pipeline_pid}"
    wait "${pipeline_pid}" >/dev/null 2>&1 || true
    pipeline_pid=""
  fi
  if [[ -n "${watchdog_pid}" ]]; then
    stop_background_pid "${watchdog_pid}"
    watchdog_pid=""
  fi
  if [[ -n "${hb_pid}" ]]; then
    stop_background_pid "${hb_pid}"
    hb_pid=""
  fi
  rm -f "${current_file}" || true
  rm -f "${timed_out_file}" || true
}
trap cleanup EXIT
trap 'cleanup; exit 129' HUP
trap 'cleanup; exit 130' INT
trap 'cleanup; exit 143' TERM

human_duration() {
  local total="$1"
  local h=$(( total / 3600 ))
  local m=$(( (total % 3600) / 60 ))
  local s=$(( total % 60 ))
  if [[ "${h}" -gt 0 ]]; then
    printf '%02d:%02d:%02d' "${h}" "${m}" "${s}"
  else
    printf '%02d:%02d' "${m}" "${s}"
  fi
}

heartbeat() {
  if [[ "${heartbeat_secs}" -le 0 ]]; then
    return 0
  fi

  while true; do
    sleep "${heartbeat_secs}"
    local now elapsed current
    now="$(date +%s)"
    elapsed="$(( now - start_epoch ))"
    current="(no module yet)"
    if [[ -s "${current_file}" ]]; then
      current="$(cat "${current_file}" 2>/dev/null || true)"
    fi

    local checked last
    checked="0"
    last=""
    if [[ -f "${MODULES_TSV}" ]]; then
      checked="$(wc -l < "${MODULES_TSV}" 2>/dev/null || echo 0)"
      checked="${checked//[[:space:]]/}"
      if [[ "${checked}" -gt 0 ]]; then
        last="$(tail -n 1 "${MODULES_TSV}" 2>/dev/null || true)"
      fi
    fi

    if [[ -n "${last}" ]]; then
      printf '[+%s] still running: %s  (checked %s; last: %s)\n' \
        "$(human_duration "${elapsed}")" "${current}" "${checked}" "${last}" >&2
    else
      printf '[+%s] still running: %s  (checked %s)\n' \
        "$(human_duration "${elapsed}")" "${current}" "${checked}" >&2
    fi
  done
}

heartbeat &
hb_pid="$!"

timeout_secs="${AGDA_TIMEOUT_SECS:-0}"

timeout_watchdog() {
  if [[ "${timeout_secs}" -le 0 ]]; then
    return 0
  fi

  sleep "${timeout_secs}"

  if [[ -n "${pipeline_pid}" ]]; then
    printf 'timeout\n' > "${timed_out_file}"
    printf 'agda-telemetry: timeout after %ss; terminating current run\n' "${timeout_secs}" >&2
    terminate_pipeline "${pipeline_pid}"
  fi
}

run_telemetry_pipeline() {
  set -o pipefail
  "$@" 2>&1 | python3 -u "${telemetry_stream}" \
    --out-tsv "${MODULES_TSV}" \
    --current-file "${current_file}"
}

set +e
if command -v setsid >/dev/null 2>&1; then
  setsid env \
    TELEMETRY_STREAM="${telemetry_stream}" \
    TELEMETRY_TSV="${MODULES_TSV}" \
    TELEMETRY_CURRENT_FILE="${current_file}" \
    bash -lc "${telemetry_setsid_cmd}" bash "$@" &
  pipeline_isolated="1"
else
  run_telemetry_pipeline "$@" &
fi
pipeline_pid="$!"

timeout_watchdog &
watchdog_pid="$!"

wait "${pipeline_pid}"
status="$?"
pipeline_pid=""
set -e

stop_background_pid "${hb_pid}"
hb_pid=""

stop_background_pid "${watchdog_pid}"
watchdog_pid=""

if [[ -s "${timed_out_file}" ]]; then
  status=124
fi

echo "agda-telemetry: wrote ${MODULES_TSV}" >&2

if [[ -s "${MODULES_TSV}" ]]; then
  echo "agda-telemetry: slowest modules (approx; wall time between 'Checking …' lines):" >&2
  sorted_tsv="$(mktemp -t agda_sorted.XXXXXX)"
  sort -t $'\t' -k2,2nr "${MODULES_TSV}" > "${sorted_tsv}"
  head -n "${top_n}" "${sorted_tsv}" \
    | awk -F $'\t' '{ printf "  %8.3fs  %s  (%s)\n", ($2 / 1000.0), $1, $3 }' >&2
  rm -f "${sorted_tsv}"
fi

exit "${status}"
