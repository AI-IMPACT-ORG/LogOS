#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "check-all-agda: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

AGDA="${AGDA:-agda}"
AGDA_FLAGS="${AGDA_FLAGS:---no-libraries -i . --safe}"
AGDA_WARN_FLAGS="${AGDA_WARN_FLAGS:--W all -W noCoverageNoExactSplit -W error}"
PIPELINE_SEED_PREFIXES="${PIPELINE_SEED_PREFIXES:-LogOS.Packs.Agents.Experimental.Arguments.Transformer,LogOS.Packs.Agents.Experimental.Arguments.ControlledFeedback}"
PIPELINE_SEED_MODULE="${PIPELINE_SEED_MODULE:-}"
PIPELINE_PROFILE="${PIPELINE_PROFILE:-0}"
PIPELINE_SKIP="${PIPELINE_SKIP:-0}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"
command -v python3 >/dev/null 2>&1 || die "python3 is required for this check"

BUILD_DIR="_build/CheckAll"
MODULE_LIST="${BUILD_DIR}/AllAgda.modules"
MAIN_MODULE_FILE="${BUILD_DIR}/AllAgdaMain.agda"
MAIN_MODULE_LIST="${BUILD_DIR}/AllAgdaMain.modules"
PIPELINE_MODULE_FILE="${BUILD_DIR}/AllAgdaPipeline.agda"
PIPELINE_MODULE_LIST="${BUILD_DIR}/AllAgdaPipeline.modules"

mkdir -p "${BUILD_DIR}"
: > "${MODULE_LIST}"

while IFS= read -r -d '' f; do
  f="${f#./}"
  mod="${f%.agda}"
  mod="${mod//\//.}"
  printf '%s\n' "${mod}" >> "${MODULE_LIST}"
done < <(
  rg --files -0 --hidden \
    --glob '*.agda' \
    --glob '!_build/**' \
    --glob '!.git/**' \
    --glob '!.agda/**'
)

if [[ ! -s "${MODULE_LIST}" ]]; then
  die "no .agda files found"
fi

sort -u "${MODULE_LIST}" -o "${MODULE_LIST}"

python3 - "${PIPELINE_SEED_PREFIXES}" "${PIPELINE_SEED_MODULE}" "${MODULE_LIST}" "${MAIN_MODULE_LIST}" "${PIPELINE_MODULE_LIST}" <<'PY'
from __future__ import annotations

import pathlib
import re
import sys
from collections import defaultdict, deque

seed_prefixes = [part.strip() for part in sys.argv[1].split(",") if part.strip()]
legacy_seed = sys.argv[2].strip()
module_list_path = pathlib.Path(sys.argv[3])
main_out_path = pathlib.Path(sys.argv[4])
pipeline_out_path = pathlib.Path(sys.argv[5])

modules = [line.strip() for line in module_list_path.read_text(encoding="utf-8").splitlines() if line.strip()]
module_set = set(modules)
import_re = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)")

edges: dict[str, set[str]] = {mod: set() for mod in modules}
for mod in modules:
  path = pathlib.Path(*mod.split(".")).with_suffix(".agda")
  for line in path.read_text(encoding="utf-8").splitlines():
    match = import_re.match(line)
    if not match:
      continue
    dep = match.group(1)
    if dep in module_set:
      edges[mod].add(dep)

reverse: dict[str, set[str]] = defaultdict(set)
for mod, deps in edges.items():
  for dep in deps:
    reverse[dep].add(mod)

def is_seed_module(mod: str) -> bool:
  for prefix in seed_prefixes:
    if mod.startswith(prefix):
      return True
  if legacy_seed:
    seed_prefix = f"{legacy_seed}."
    if mod == legacy_seed or mod.startswith(seed_prefix):
      return True
  return False

pipeline_seed_modules = {mod for mod in modules if is_seed_module(mod)}
blocked: set[str] = set(pipeline_seed_modules)
queue: deque[str] = deque(sorted(pipeline_seed_modules))

while queue:
  current = queue.popleft()
  for parent in reverse.get(current, ()):
    if parent in blocked:
      continue
    blocked.add(parent)
    queue.append(parent)

main_modules = [mod for mod in modules if mod not in blocked]

def pipeline_order_key(mod: str) -> tuple[int, str]:
  if mod.startswith("LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge."):
    return (0, mod)
  if mod == "LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge":
    return (1, mod)
  if mod.startswith("LogOS.Packs.Agents.Experimental.Arguments.TransformerFormalization"):
    return (2, mod)
  if mod.startswith("LogOS.Packs.Agents.Experimental.Arguments.ControlledFeedback"):
    return (3, mod)
  if mod == "LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Core":
    return (4, mod)
  if mod == "LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.ResourcePrinciple":
    return (5, mod)
  if mod == "LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.PowerLaw":
    return (6, mod)
  if mod == "LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Experimental":
    return (7, mod)
  if mod == "LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Calibration":
    return (8, mod)
  if mod == "LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.ExperimentalCompute":
    return (9, mod)
  if mod == "LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Examples":
    return (10, mod)
  if mod == "LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Full":
    return (11, mod)
  if mod.startswith("LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline."):
    return (12, mod)
  if mod == "LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline":
    return (13, mod)
  if mod.startswith("LogOS.Packs.Agents.Experimental.Arguments.TransformerKolmogorovScaling"):
    return (14, mod)
  if mod.startswith("LogOS.Packs.Agents.Experimental.Arguments.TransformerScaling"):
    return (15, mod)
  if mod == "LogOS.Packs.Agents.Experimental.Arguments.Transformer":
    return (16, mod)
  if mod.startswith("LogOS.Packs.Agents.Experimental.Arguments."):
    return (17, mod)
  if mod.startswith("LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow."):
    return (18, mod)
  if mod.startswith("LogOS.Packs.Agents.Experimental."):
    return (19, mod)
  if mod.startswith("Tests."):
    return (20, mod)
  if any(mod.startswith(prefix) for prefix in seed_prefixes):
    return (21, mod)
  if legacy_seed and (mod == legacy_seed or mod.startswith(f"{legacy_seed}.")):
    return (22, mod)
  return (23, mod)

pipeline_modules = sorted((mod for mod in modules if mod in blocked), key=pipeline_order_key)

main_out_path.write_text("".join(f"{mod}\n" for mod in main_modules), encoding="utf-8")
pipeline_out_path.write_text("".join(f"{mod}\n" for mod in pipeline_modules), encoding="utf-8")

if not pipeline_seed_modules:
  if legacy_seed:
    print(f"check-all-agda: warning: no modules matched seed prefixes={seed_prefixes} or legacy seed={legacy_seed}", file=sys.stderr)
  else:
    print(f"check-all-agda: warning: no modules matched seed prefixes={seed_prefixes}", file=sys.stderr)
PY

main_count=$(wc -l < "${MAIN_MODULE_LIST}" | tr -d '[:space:]')
pipeline_count=$(wc -l < "${PIPELINE_MODULE_LIST}" | tr -d '[:space:]')

echo "check-all-agda: split module sets main=${main_count} pipeline=${pipeline_count} prefixes=${PIPELINE_SEED_PREFIXES} legacy-seed=${PIPELINE_SEED_MODULE:-<none>} profile=${PIPELINE_PROFILE} skip=${PIPELINE_SKIP}"

write_synthetic_module() {
  local module_name="$1"
  local module_file="$2"
  local module_list_file="$3"

  cat > "${module_file}" <<EOF
-- Auto-generated by scripts/check_all_agda.sh. Do not edit.
module ${module_name} where
EOF

  while IFS= read -r mod; do
    printf 'import %s\n' "${mod}" >> "${module_file}"
  done < "${module_list_file}"
}

read -r -a agda_flags <<< "${AGDA_FLAGS}"
read -r -a agda_warn_flags <<< "${AGDA_WARN_FLAGS}"

is_true() {
  case "${1:-}" in
    1|true|TRUE|yes|YES|on|ON) return 0 ;;
    *) return 1 ;;
  esac
}

if [[ -s "${MAIN_MODULE_LIST}" ]]; then
  write_synthetic_module "CheckAll.AllAgdaMain" "${MAIN_MODULE_FILE}" "${MAIN_MODULE_LIST}"
  main_start=${SECONDS}
  "${AGDA}" "${agda_flags[@]}" -i _build "${agda_warn_flags[@]}" "${MAIN_MODULE_FILE}"
  main_elapsed=$((SECONDS - main_start))
  echo "check-all-agda: main pass completed in ${main_elapsed}s"
fi

if [[ -s "${PIPELINE_MODULE_LIST}" ]]; then
  if is_true "${PIPELINE_SKIP}"; then
    echo "check-all-agda: pipeline pass skipped (PIPELINE_SKIP=${PIPELINE_SKIP}); modules=${pipeline_count}"
  else
    pipeline_start=${SECONDS}
    if is_true "${PIPELINE_PROFILE}"; then
      while IFS= read -r mod; do
        module_path="$(printf '%s' "${mod}" | tr '.' '/').agda"
        module_start=${SECONDS}
        "${AGDA}" "${agda_flags[@]}" -i _build "${agda_warn_flags[@]}" "${module_path}"
        module_elapsed=$((SECONDS - module_start))
        echo "check-all-agda: pipeline module ${mod} completed in ${module_elapsed}s"
      done < "${PIPELINE_MODULE_LIST}"
    else
      write_synthetic_module "CheckAll.AllAgdaPipeline" "${PIPELINE_MODULE_FILE}" "${PIPELINE_MODULE_LIST}"
      "${AGDA}" "${agda_flags[@]}" -i _build "${agda_warn_flags[@]}" "${PIPELINE_MODULE_FILE}"
    fi
    pipeline_elapsed=$((SECONDS - pipeline_start))
    echo "check-all-agda: pipeline pass completed in ${pipeline_elapsed}s"
  fi
fi
