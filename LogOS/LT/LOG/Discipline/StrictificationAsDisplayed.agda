{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.Discipline.StrictificationAsDisplayed where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Discipline gate: explicit strictification law ports must also remain
-- displayed + Σ-decorated.

open import LogOS.Prelude using (Level; Setω; lzero; ⊤; tt; _≡_; refl)
open import LogOS.LT.DisplayedThin2Cat using
    ( DecoratedThin2Cat
    ; forgetDecorated
    )

import LogOS.LT.LOG.ClassicalLimit2Cat as ClassicalLimit
import LogOS.LT.LOG.StrictDecode2Cat as StrictDecode

classicalLimitLayer-isDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → ClassicalLimit.WithPort {ℓ} {ℓRel} {ℓCode}
    ≡
    DecoratedThin2Cat (ClassicalLimit.ClassicalLimitDisplayed {ℓ} {ℓRel} {ℓCode})
classicalLimitLayer-isDecorated = refl

forgetClassicalLimit-isForgetDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → ClassicalLimit.forget {ℓ} {ℓRel} {ℓCode}
    ≡
    forgetDecorated (ClassicalLimit.ClassicalLimitDisplayed {ℓ} {ℓRel} {ℓCode})
forgetClassicalLimit-isForgetDecorated = refl

strictDecodeLayer-isDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → StrictDecode.WithPort {ℓ} {ℓRel} {ℓCode}
    ≡
    DecoratedThin2Cat (StrictDecode.Displayed {ℓ} {ℓRel} {ℓCode})
strictDecodeLayer-isDecorated = refl

forgetStrictDecode-isForgetDecorated
  : ∀ {ℓ ℓRel ℓCode : Level}
  → StrictDecode.forget {ℓ} {ℓRel} {ℓCode}
    ≡
    forgetDecorated (StrictDecode.Displayed {ℓ} {ℓRel} {ℓCode})
forgetStrictDecode-isForgetDecorated = refl

record SupportedStrictificationLayers (ℓ ℓRel ℓCode : Level) : Setω where
  field
    classicalLimit
      : ClassicalLimit.WithPort {ℓ} {ℓRel} {ℓCode}
        ≡
        DecoratedThin2Cat (ClassicalLimit.ClassicalLimitDisplayed {ℓ} {ℓRel} {ℓCode})

    strictDecode
      : StrictDecode.WithPort {ℓ} {ℓRel} {ℓCode}
        ≡
        DecoratedThin2Cat (StrictDecode.Displayed {ℓ} {ℓRel} {ℓCode})

supportedStrictificationLayers
  : ∀ {ℓ ℓRel ℓCode : Level}
  → SupportedStrictificationLayers ℓ ℓRel ℓCode
supportedStrictificationLayers =
  record
    { classicalLimit = classicalLimitLayer-isDecorated
    ; strictDecode = strictDecodeLayer-isDecorated
    }

ok : ⊤ {ℓ = lzero}
ok = tt
