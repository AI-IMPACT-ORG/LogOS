#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

CHECK_NAME="against-std-lib-check"
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

STDLIB_ROOT="${AGDA_STDLIB:-}"
if [[ -z "${STDLIB_ROOT}" ]]; then
  die "missing AGDA_STDLIB (set to the agda-stdlib root; expected: <AGDA_STDLIB>/src/Relation/Binary/Bundles.agda)"
fi

STDLIB_SRC="${STDLIB_ROOT%/}/src"
[[ -d "${STDLIB_SRC}" ]] || die "AGDA_STDLIB/src not found: ${STDLIB_SRC}"
[[ -f "${STDLIB_SRC}/Relation/Binary/Bundles.agda" ]] || die "stdlib sanity check failed (missing Relation/Binary/Bundles.agda under): ${STDLIB_SRC}"

read -r -a agda_flags <<< "${AGDA_FLAGS}"
read -r -a agda_warn_flags <<< "${AGDA_WARN_FLAGS}"

BUILD_DIR="_build/AgainstStdLib"
MODULE_FILE="${BUILD_DIR}/All.agda"

mkdir -p "${BUILD_DIR}"

cat > "${MODULE_FILE}" <<'EOF'
{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module AgainstStdLib.All where

-- Downstream consistency harness:
-- typecheck LogOS alongside agda-stdlib without importing stdlib from LogOS.

open import LogOS.Prelude hiding ()

open import Data.Unit.Polymorphic using (⊤; tt) renaming (⊤ to ⊤ₛ; tt to ttₛ)

toStd⊤ : ∀ {ℓ} → ⊤ {ℓ} → ⊤ₛ {ℓ}
toStd⊤ _ = ttₛ

fromStd⊤ : ∀ {ℓ} → ⊤ₛ {ℓ} → ⊤ {ℓ}
fromStd⊤ _ = tt

to-from⊤ : ∀ {ℓ} (x : ⊤ₛ {ℓ}) → toStd⊤ (fromStd⊤ x) ≡ x
to-from⊤ ttₛ = refl

from-to⊤ : ∀ {ℓ} (x : ⊤ {ℓ}) → fromStd⊤ (toStd⊤ x) ≡ x
from-to⊤ tt = refl
EOF

"${AGDA}" "${agda_flags[@]}" -i _build -i "${STDLIB_SRC}" "${agda_warn_flags[@]}" "${MODULE_FILE}"
