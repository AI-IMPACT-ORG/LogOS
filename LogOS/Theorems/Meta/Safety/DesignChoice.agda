{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Safety.DesignChoice where

-- Design choice: the meta-theory assumes only the kernel interface.
-- Any additional internal paradox-enabling structure (truth over code,
-- provability, diagonalization, comprehension, etc.) must be provided explicitly
-- as separate assumption packs.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

record DesignChoice {ℓ : Level}
                    (Sig : LogOSSignature ℓ)
                    (Q   : QAdapter ℓ)
                    : Set (lsuc (lsuc ℓ)) where
  field
    K : Kernel Sig Q
