#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Generated docs committed in-tree must match their generators.
# - After changes, run `make views-all`, `make design-all`, `make layer-order-legend`,
#   `make module-index`, `make policy-index`, `make docs-index`,
#   `make claim-stamp-index`, `make published-surface-index`,
#   `make zfc-upgrade-index`, `make equality-surface-map`,
#   `make strictification-inventory`, `make architecture-clarity-report`,
#   and `make lt-ports-import-graph`.

set -euo pipefail

CHECK_NAME="generated-docs-fresh-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" cmp

tmpdir="$(mktemp -d)"
trap 'rm -rf "${tmpdir}"' EXIT

mismatch=""

check_generated_doc() {
  local target="$1"
  local generator="$2"
  local tmp_out="$3"

  [[ -f "${target}" ]] || die "missing generated doc: ${target}"
  [[ -x "${generator}" || -f "${generator}" ]] || die "missing generator script: ${generator}"

  bash "${generator}" "${tmp_out}" >/dev/null

  if ! cmp -s "${target}" "${tmp_out}"; then
    mismatch+="${target} (run: bash ${generator})"$'\n'
  fi
}

check_generated_doc \
  "docs/Interpretations/Views/All.lagda.md" \
  "scripts/gen/write_views_all.sh" \
  "${tmpdir}/Views_All.lagda.md"

check_generated_doc \
  "docs/Patterns/All.lagda.md" \
  "scripts/gen/write_design_all.sh" \
  "${tmpdir}/Design_All.lagda.md"

check_generated_doc \
  "docs/Generated/Architecture_Layer_Order.md" \
  "scripts/gen/write_layer_order_legend.sh" \
  "${tmpdir}/Architecture_Layer_Order.md"

check_generated_doc \
  "docs/Generated/Module_Index.md" \
  "scripts/gen/write_module_index.sh" \
  "${tmpdir}/Module_Index.md"

check_generated_doc \
  "docs/Generated/Policy_Index.md" \
  "scripts/gen/write_policy_index.sh" \
  "${tmpdir}/Policy_Index.md"

check_generated_doc \
  "docs/Generated/Docs_Index.md" \
  "scripts/gen/write_docs_index.sh" \
  "${tmpdir}/Docs_Index.md"

check_generated_doc \
  "docs/Generated/Claim_Stamp_Index.md" \
  "scripts/gen/write_claim_stamp_index.sh" \
  "${tmpdir}/Claim_Stamp_Index.md"

check_generated_doc \
  "docs/Generated/Published_Surface_Index.md" \
  "scripts/gen/write_published_surface_index.sh" \
  "${tmpdir}/Published_Surface_Index.md"

python3 -B scripts/generate_zfc_upgrade_index.py "${tmpdir}/ZFC_Upgrade_Index.md" >/dev/null
if ! cmp -s "docs/Generated/ZFC_Upgrade_Index.md" "${tmpdir}/ZFC_Upgrade_Index.md"; then
  mismatch+="docs/Generated/ZFC_Upgrade_Index.md (run: python3 -B scripts/generate_zfc_upgrade_index.py docs/Generated/ZFC_Upgrade_Index.md)"$'\n'
fi

python3 -B scripts/generate_equality_surface_map.py "${tmpdir}/Equality_Surface_Map.md" >/dev/null
if ! cmp -s "docs/Generated/Equality_Surface_Map.md" "${tmpdir}/Equality_Surface_Map.md"; then
  mismatch+="docs/Generated/Equality_Surface_Map.md (run: python3 -B scripts/generate_equality_surface_map.py docs/Generated/Equality_Surface_Map.md)"$'\n'
fi

python3 -B scripts/generate_strictification_inventory.py "${tmpdir}/Strictification_Inventory.md" >/dev/null
if ! cmp -s "docs/Generated/Strictification_Inventory.md" "${tmpdir}/Strictification_Inventory.md"; then
  mismatch+="docs/Generated/Strictification_Inventory.md (run: python3 -B scripts/generate_strictification_inventory.py docs/Generated/Strictification_Inventory.md)"$'\n'
fi

check_generated_doc \
  "docs/Generated/Architecture_Clarity_Index.md" \
  "scripts/gen/write_architecture_clarity_index.sh" \
  "${tmpdir}/Architecture_Clarity_Index.md"

check_generated_doc \
  "docs/Generated/LT_Ports_Import_Graph.md" \
  "scripts/gen/write_lt_ports_import_graph.sh" \
  "${tmpdir}/LT_Ports_Import_Graph.md"

if [[ -n "${mismatch}" ]]; then
  die $'generated docs are stale:\n'"${mismatch}"$'\n\nRun:\n  make views-all\n  make design-all\n  make layer-order-legend\n  make module-index\n  make policy-index\n  make docs-index\n  make claim-stamp-index\n  make published-surface-index\n  make zfc-upgrade-index\n  make equality-surface-map\n  make strictification-inventory\n  make architecture-clarity-report\n  make lt-ports-import-graph'
fi

echo "${CHECK_NAME}: OK"
