{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Conventions.ObservedCodePreorder where

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel; CodePreorder; ObservedCodePreorder)

observed-code-preorder-is-code-preorderDef
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → ObservedCodePreorder K ≡ CodePreorder K
observed-code-preorder-is-code-preorderDef = refl
