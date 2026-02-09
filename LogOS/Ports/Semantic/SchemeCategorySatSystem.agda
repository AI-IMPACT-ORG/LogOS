{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.SchemeCategorySatSystem where

-- SatSystem view (bridge): “budgeted computation as satisfaction”.
--
-- This intentionally lives in Ports (not Computation) so the computation layer
-- stays independent of the ports/adapters spine.

open import LogOS.Prelude

open import LogOS.Minimal.Adapter using (QAdapter)
import LogOS.Minimal.Truth as Truth

import LogOS.Computation.Scheme as Sch
open import LogOS.Computation.SchemeCategory using
  ( Process
  ; Interface
  ; schemeFromInterface
  ; ProcessHomCost
  ; mapInterface
  ; ComputesWithin-map
  )

open import LogOS.Ports.Semantic.Core using (SatSystem; satSystem)
open import LogOS.Ports.Semantic.SatMor using (SatHom)

computesWithinSatSystem
  : ∀ {ℓI ℓO ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
  → Interface Input P
  → SatSystem {ℓCtx = ℓI ⊔ ℓQ} {ℓCon = ℓO} {ℓSat = ℓC ⊔ ℓO ⊔ ℓQ}
computesWithinSatSystem {Input = Input} {Output = Output} P I =
  let
    S = schemeFromInterface P I
    Ctx = Input × QAdapter.Scale (Process.Q P)
    Con = Output
    Sat : Ctx → Con → Set _
    Sat (x , b) y = Sch.Scheme.ComputesWithin S x b y
  in
  satSystem Ctx Con Sat

computesWithinSatSystem-map
  : ∀ {ℓI ℓO ℓC₁ ℓC₂ ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCost P₁ P₂)
    (I  : Interface Input P₁)
  → SatHom
      (computesWithinSatSystem P₁ I)
      (computesWithinSatSystem P₂ (mapInterface (ProcessHomCost.hom hc) I))
computesWithinSatSystem-map {P₁ = P₁} {P₂ = P₂} hc I =
  let
    φ = ProcessHomCost.grade hc
    open Truth.GuardedCore.GradeHom φ renaming (map to mapg)
  in
  record
    { mapCtx = λ (x , b) → x , mapg b
    ; mapCon = λ y → y
    ; sat-→  = λ (x , b) y → ComputesWithin-map hc I x b y
    }

