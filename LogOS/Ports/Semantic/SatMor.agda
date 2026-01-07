{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.SatMor where

-- Satisfaction morphisms (generic):
-- a map on contexts and constraints that preserves+reflects satisfaction.
--
-- This is the missing “glue” to make ports/adapters compose across *changing*
-- logics, not just between presentations of the same satisfaction relation.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

record SatMor
  {ℓCtx₁ ℓCon₁ ℓSat₁ ℓCtx₂ ℓCon₂ ℓSat₂ : Level}
  (Ctx₁ : Set ℓCtx₁)
  (Con₁ : Set ℓCon₁)
  (Sat₁ : Ctx₁ → Con₁ → Set ℓSat₁)
  (Ctx₂ : Set ℓCtx₂)
  (Con₂ : Set ℓCon₂)
  (Sat₂ : Ctx₂ → Con₂ → Set ℓSat₂)
  : Set (lsuc (ℓCtx₁ ⊔ ℓCon₁ ⊔ ℓSat₁ ⊔ ℓCtx₂ ⊔ ℓCon₂ ⊔ ℓSat₂)) where
  field
    mapCtx : Ctx₁ → Ctx₂
    mapCon : Con₁ → Con₂
    sat-↔  : ∀ p c → Sat₁ p c ↔ Sat₂ (mapCtx p) (mapCon c)

  -- Projections (make the two directions explicit).
  --
  -- Many “translation” interfaces are one-way (soundness only). In LogOS,
  -- `SatMor` is *conservative*: it preserves and reflects satisfaction.
  sat→ : ∀ p c → Sat₁ p c → Sat₂ (mapCtx p) (mapCon c)
  sat→ p c = Prop.to (sat-↔ p c)

  sat← : ∀ p c → Sat₂ (mapCtx p) (mapCon c) → Sat₁ p c
  sat← p c = Prop.from (sat-↔ p c)

  -- Target satisfaction pulled back along `mapCtx`.
  Sat₂↑ : Ctx₁ → Con₂ → Set ℓSat₂
  Sat₂↑ p c = Sat₂ (mapCtx p) c

  -- `mapCon` respects the observational equality induced by satisfaction,
  -- relative to the pulled-back target observers.
  mapCon-respects-ObsEq
    : ∀ {c d}
    → Prop.ObsEqOn Sat₁ c d
    → Prop.ObsEqOn Sat₂↑ (mapCon c) (mapCon d)
  mapCon-respects-ObsEq {c} {d} eq p =
    Prop.↔-trans
      (Prop.↔-sym (sat-↔ p c))
      (Prop.↔-trans (eq p) (sat-↔ p d))

idSatMor
  : ∀ {ℓCtx ℓCon ℓSat : Level}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    (Sat : Ctx → Con → Set ℓSat)
  → SatMor Ctx Con Sat Ctx Con Sat
idSatMor Sat =
  record
    { mapCtx = λ x → x
    ; mapCon = λ x → x
    ; sat-↔  = λ _ _ → Prop.↔-refl
    }

composeSatMor
  : ∀ {ℓCtx₁ ℓCon₁ ℓSat₁ ℓCtx₂ ℓCon₂ ℓSat₂ ℓCtx₃ ℓCon₃ ℓSat₃ : Level}
    {Ctx₁ : Set ℓCtx₁} {Con₁ : Set ℓCon₁} {Sat₁ : Ctx₁ → Con₁ → Set ℓSat₁}
    {Ctx₂ : Set ℓCtx₂} {Con₂ : Set ℓCon₂} {Sat₂ : Ctx₂ → Con₂ → Set ℓSat₂}
    {Ctx₃ : Set ℓCtx₃} {Con₃ : Set ℓCon₃} {Sat₃ : Ctx₃ → Con₃ → Set ℓSat₃}
  → SatMor Ctx₁ Con₁ Sat₁ Ctx₂ Con₂ Sat₂
  → SatMor Ctx₂ Con₂ Sat₂ Ctx₃ Con₃ Sat₃
  → SatMor Ctx₁ Con₁ Sat₁ Ctx₃ Con₃ Sat₃
composeSatMor m₁ m₂ =
  record
    { mapCtx = λ p → SatMor.mapCtx m₂ (SatMor.mapCtx m₁ p)
    ; mapCon = λ c → SatMor.mapCon m₂ (SatMor.mapCon m₁ c)
    ; sat-↔  = λ p c →
        Prop.↔-trans
          (SatMor.sat-↔ m₁ p c)
          (SatMor.sat-↔ m₂ (SatMor.mapCtx m₁ p) (SatMor.mapCon m₁ c))
    }
