#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The canonical abstract Deutsch-category construction must be documented at a stable anchor.
# - v1.1 defines abstract Deutsch via locality + causality + local reversibility (weaker than unitarity).

set -euo pipefail

CHECK_NAME="abstract-deutsch-doc-contract-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"
# shellcheck source=scripts/lib/abstract_deutsch_doc_contract_check_impl.sh
source "${SCRIPT_DIR}/lib/abstract_deutsch_doc_contract_check_impl.sh"

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

abstract_deutsch_doc_contract_check_impl "${CHECK_NAME}"
