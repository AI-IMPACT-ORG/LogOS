{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.SetTheory.FormulaFromDefinable where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.API.Kernel

open import LogOS.ZFC.SetTheory.DefinablePack using (ZFAxiomsᵈ; ZFCAxiomsᵈ)
open import LogOS.ZFC.SetTheory.FormulaPack using (ZFAxiomsᶠ; ZFCAxiomsᶠ)

-- Bridge: coded/definable schemata ⇒ Metamath-style formula-pack schemata.
--
-- In the definable pack, a “predicate code” is interpreted as a set `⟦ φ ⟧` and
-- satisfied by membership; a “relation code” is interpreted as a graph `Graph φ`.
--
-- This makes the FormulaPack interface operational without changing any model.

toZFAxiomsᶠ
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → ZFAxiomsᵈ K
  → ZFAxiomsᶠ K
toZFAxiomsᶠ A =
  let open ZFAxiomsᵈ A in
  record
    { SetU   = SetU
    ; _∈_    = _∈_
    ; ⟦_⟧     = ⟦_⟧
    ; by-decode≈ = by-decode≈
    ; mem-congL = mem-congL
    ; empty = empty
    ; pairing = pairing
    ; union = union
    ; powerset = powerset
    ; zeroS = zeroS
    ; zeroS-empty = zeroS-empty
    ; succ  = succ
    ; mem-succ↔ = mem-succ↔
    ; infinity = infinity
    ; Pred = λ φ z → z ∈ ⟦ φ ⟧
    ; Rel  = λ ψ u z → Graph ψ u z
    ; separationᶠ = separationᵈ
    ; replacementᶠ = replacementᵈ
    ; foundation  = foundation
    }

toZFCAxiomsᶠ
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → ZFCAxiomsᵈ K
  → ZFCAxiomsᶠ K
toZFCAxiomsᶠ A =
  record
    { zf = toZFAxiomsᶠ (ZFCAxiomsᵈ.zf A)
    ; AC = ZFCAxiomsᵈ.AC A
    }
