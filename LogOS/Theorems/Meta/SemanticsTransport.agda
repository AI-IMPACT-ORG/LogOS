{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.SemanticsTransport where

-- Pseudo-functorial semantics transport.
--
-- This module packages the “canonical translation determined by satisfaction”
-- into easy-to-use identity and composition laws (up to observational equality).
--
-- The underlying constructions live in:
-- `LogOS.Ports.Semantic.HeteroInterlinguaCore`.

open import LogOS.Prelude

open import LogOS.Ports.Semantic.PresentationCore using (SatSystem; PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor; composeSatMor)
import LogOS.Ports.Semantic.HeteroInterlinguaCore as Hetero

-- ---------------------------------------------------------------------------
-- Homogeneous case: fixed satisfaction system.
-- ---------------------------------------------------------------------------

translate-id
  : ∀ {ℓCtx ℓCon ℓForm ℓSat : Level}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    (P : PresentationC {ℓForm = ℓForm} S)
  → Hetero.ForPresentations._≈⇒_ P P
      (Hetero.ForPresentations.translate P P)
      (λ x → x)
translate-id = Hetero.translate-id-core

translate-comp-presentations
  : ∀ {ℓCtx ℓCon ℓForm₁ ℓForm₂ ℓForm₃ ℓSat : Level}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    (P₁ : PresentationC {ℓForm = ℓForm₁} S)
    (P₂ : PresentationC {ℓForm = ℓForm₂} S)
    (P₃ : PresentationC {ℓForm = ℓForm₃} S)
  → Hetero.ForPresentations._≈⇒_ P₁ P₃
      (Hetero.ForPresentations.translate P₁ P₃)
      (λ φ →
        Hetero.ForPresentations.translate P₂ P₃
          (Hetero.ForPresentations.translate P₁ P₂ φ))
translate-comp-presentations = Hetero.translate-comp-core

-- ---------------------------------------------------------------------------
-- Heterogeneous case: changing satisfaction relations along `SatMor`.
-- ---------------------------------------------------------------------------

translate-comp
  : ∀ {ℓCtx₁ ℓCon₁ ℓForm₁ ℓSat₁ : Level}
    {S₁ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₁} {ℓSat = ℓSat₁}}
    {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
    {S₂ : SatSystem {ℓCtx = ℓCtx₂} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂}}
    {ℓCtx₃ ℓCon₃ ℓForm₃ ℓSat₃ : Level}
    {S₃ : SatSystem {ℓCtx = ℓCtx₃} {ℓCon = ℓCon₃} {ℓSat = ℓSat₃}}
  → (m₁ : SatMor S₁ S₂)
  → (m₂ : SatMor S₂ S₃)
  → (P₁ : PresentationC {ℓForm = ℓForm₁} S₁)
  → (P₂ : PresentationC {ℓForm = ℓForm₂} S₂)
  → (P₃ : PresentationC {ℓForm = ℓForm₃} S₃)
  → Hetero.For._≈⇒_ (composeSatMor m₁ m₂) P₁ P₃
      (Hetero.For.translate (composeSatMor m₁ m₂) P₁ P₃)
      (λ φ → Hetero.For.translate m₂ P₂ P₃ (Hetero.For.translate m₁ P₁ P₂ φ))
translate-comp m₁ m₂ P₁ P₂ P₃ =
  let module C = Hetero.Compose m₁ m₂ P₁ P₂ P₃ in
  C.translate-comp

