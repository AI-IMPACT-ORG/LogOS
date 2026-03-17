#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

CHECK_NAME="against-cubical-lib-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

AGDA="${AGDA:-agda}"
AGDA_FLAGS_BASE="${AGDA_FLAGS_BASE:---no-libraries -i . --safe --without-K}"
AGDA_FLAGS="${AGDA_FLAGS:-${AGDA_FLAGS_BASE}}"
AGDA_WARN_FLAGS="${AGDA_WARN_FLAGS:--W all -W error}"

# NOTE: Agda uses `-W ...` (single dash). Keep the default valid for direct
# script invocation (CI/Makefile override this explicitly).
AGDA_WARN_FLAGS="${AGDA_WARN_FLAGS//--W /-W }"
check_require_cmd "${CHECK_NAME}" rg
check_require_cmd "${CHECK_NAME}" "${AGDA}"
require_no_with_k "${CHECK_NAME}" "${AGDA_FLAGS}"

CUBICAL_ROOT="${AGDA_CUBICAL_LIB:-}"
if [[ -z "${CUBICAL_ROOT}" ]]; then
  die "missing AGDA_CUBICAL_LIB (set to the Cubical library root; expected: <AGDA_CUBICAL_LIB>/Cubical/Foundations/Prelude.agda)"
fi

CUBICAL_ROOT="${CUBICAL_ROOT%/}"
[[ -d "${CUBICAL_ROOT}" ]] || die "AGDA_CUBICAL_LIB not found: ${CUBICAL_ROOT}"
[[ -f "${CUBICAL_ROOT}/Cubical/Foundations/Prelude.agda" ]] || die "cubical-library sanity check failed (missing Cubical/Foundations/Prelude.agda under): ${CUBICAL_ROOT}"

read -r -a agda_flags <<< "${AGDA_FLAGS}"
read -r -a agda_warn_flags <<< "${AGDA_WARN_FLAGS}"

BUILD_DIR="_build/AgainstCubicalLib"
MODULE_FILE="${BUILD_DIR}/All.agda"

mkdir -p "${BUILD_DIR}"

cat > "${MODULE_FILE}" <<'EOF'
{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module AgainstCubicalLib.All where

-- Downstream consistency harness:
-- typecheck LogOS alongside the Cubical library (Agda invoked with `--cubical`)
-- without importing Cubical from LogOS.

open import LogOS.Prelude hiding ()

open import Cubical.Foundations.Prelude using (Type)

idType : ∀ {ℓ} → Type ℓ → Type ℓ
idType X = X

logos⊤-is-Type : ∀ {ℓ} → Type ℓ
logos⊤-is-Type {ℓ} = ⊤ {ℓ}
EOF

"${AGDA}" --cubical "${agda_flags[@]}" -i _build -i "${CUBICAL_ROOT}" "${agda_warn_flags[@]}" "${MODULE_FILE}"
