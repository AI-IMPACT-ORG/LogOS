{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Logic.ZFC.Theory where

open import LogOS.Prelude

open import Data.List using (List; []; _∷_)
open import LogOS.Domain.SetTheory.FormulaPack using (ZFAxiomsᶠ; ZFCAxiomsᶠ)
open import LogOS.Logic.FOL.All as FOL
open import LogOS.Logic.FOL.ND using (Deriv; hyp; ⊥E; ⇒I; ⇒E; ∧I; ∧E₁; ∧E₂; ∀I; ∀E)
open import LogOS.Logic.FOL.Soundness as FOLSoundness
import LogOS.Logic.ZFC.Axioms as ZFCAxioms

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

-- A small “theory façade”:
-- - packages the ZF axiom sentences into a FOL context
-- - gives the interpretation statement: derivations from those axioms are
--   semantically valid in any `ZFAxiomsᶠ` model.
--
-- Note: the proof system used here is intuitionistic natural deduction
-- (`LogOS.Logic.FOL.ND`). Classical reasoning is an explicit extra assumption
-- on top of the axiom contexts.

module FromZFAxiomsᶠ-Theory {ℓ : Level}
                            {Sig : LogOSSignature ℓ}
                            {Q   : QAdapter ℓ}
                            (K   : Kernel Sig Q)
                            (zf  : ZFAxiomsᶠ K)
                            where

  module Ax = ZFCAxioms.FromZFAxiomsᶠ K zf
  open Ax
  open Ax.Sem
  open ZFAxiomsᶠ zf using (SetU; Pred)

  -- --------------------------------------------------------------------------
  -- Axiom contexts
  -- --------------------------------------------------------------------------

  BaseCtx : FOL.Ctx ΣZ 0
  BaseCtx =
      EqReflᶠ
    ∷ EqSymᶠ
    ∷ EqTransᶠ
    ∷ MemCongRᶠ
    ∷ MemCongLᶠ
    ∷ Extensionalityᶠ
    ∷ Emptyᶠ
    ∷ Pairingᶠ
    ∷ Unionᶠ
    ∷ Powersetᶠ
    ∷ Infinityᶠ
    ∷ Foundationᶠ
    ∷ []

  addSeparation : List (Kernel.Code K) → FOL.Ctx ΣZ 0 → FOL.Ctx ΣZ 0
  addSeparation []       Γ = Γ
  addSeparation (φ ∷ Φ)  Γ = Separationᶠ φ ∷ addSeparation Φ Γ

  addReplacement : List (Kernel.Code K) → FOL.Ctx ΣZ 0 → FOL.Ctx ΣZ 0
  addReplacement []       Γ = Γ
  addReplacement (ψ ∷ Ψ)  Γ = Replacementᶠ ψ ∷ addReplacement Ψ Γ

  -- A ZF context parameterised by finite “instances” of the two schemata.
  ZFctx : List (Kernel.Code K) → List (Kernel.Code K) → FOL.Ctx ΣZ 0
  ZFctx seps reps = addReplacement reps (addSeparation seps BaseCtx)

  -- --------------------------------------------------------------------------
  -- Satisfaction of the axiom contexts
  -- --------------------------------------------------------------------------

  satCtx-Base : ∀ env → SatCtx env BaseCtx
  satCtx-Base env =
    valid-EqReflᶠ env
    , (valid-EqSymᶠ env
    , (valid-EqTransᶠ env
    , (valid-MemCongRᶠ env
    , (valid-MemCongLᶠ env
    , (valid-Extensionalityᶠ env
    , (valid-Emptyᶠ env
    , (valid-Pairingᶠ env
    , (valid-Unionᶠ env
    , (valid-Powersetᶠ env
    , (valid-Infinityᶠ env
    , (valid-Foundationᶠ env
    , tt)))))))))))

  satCtx-addSeparation
    : ∀ (Φ : List (Kernel.Code K)) Γ env
    → SatCtx env Γ
    → SatCtx env (addSeparation Φ Γ)
  satCtx-addSeparation []        Γ env satΓ = satΓ
  satCtx-addSeparation (φ ∷ Φ)  Γ env satΓ =
    valid-Separationᶠ φ env , satCtx-addSeparation Φ Γ env satΓ

  satCtx-addReplacement
    : ∀ (Ψ : List (Kernel.Code K)) Γ env
    → SatCtx env Γ
    → SatCtx env (addReplacement Ψ Γ)
  satCtx-addReplacement []        Γ env satΓ = satΓ
  satCtx-addReplacement (ψ ∷ Ψ)  Γ env satΓ =
    valid-Replacementᶠ ψ env , satCtx-addReplacement Ψ Γ env satΓ

  satCtx-ZFctx
    : ∀ (Φ : List (Kernel.Code K)) (Ψ : List (Kernel.Code K)) env
    → SatCtx env (ZFctx Φ Ψ)
  satCtx-ZFctx Φ Ψ env =
    satCtx-addReplacement Ψ (addSeparation Φ BaseCtx) env
      (satCtx-addSeparation Φ BaseCtx env (satCtx-Base env))

  -- --------------------------------------------------------------------------
  -- Interpretation statement (soundness specialised to the ZF context)
  -- --------------------------------------------------------------------------

  zf-sound
    : ∀ {Γ : FOL.Ctx ΣZ 0} {φ : FOL.Fml ΣZ 0}
    → Deriv Γ φ
    → ∀ env
    → SatCtx env Γ
    → Sat env φ
  zf-sound = FOLSoundness.sound SetU Pred RelI

  sound-BaseCtx
    : ∀ {φ : FOL.Fml ΣZ 0}
    → Deriv BaseCtx φ
    → ∀ env
    → Sat env φ
  sound-BaseCtx d env = zf-sound d env (satCtx-Base env)

  sound-ZFctx
    : ∀ (Φ : List (Kernel.Code K)) (Ψ : List (Kernel.Code K)) {φ : FOL.Fml ΣZ 0}
    → Deriv (ZFctx Φ Ψ) φ
    → ∀ env
    → Sat env φ
  sound-ZFctx Φ Ψ d env = zf-sound d env (satCtx-ZFctx Φ Ψ env)

  -- --------------------------------------------------------------------------
  -- Tiny ND proof-of-concept
  -- --------------------------------------------------------------------------

  -- Any two empty sets are `≈`-equal (uses Extensionality only).
  EmptyUniqueᶠ : FOL.Fml ΣZ 0
  EmptyUniqueᶠ =
    FOL.All (FOL.All
      (((IsEmpty v1) FOL.∧ (IsEmpty v0)) FOL.⇒ (v1 ≈ᶠ v0)))

  extIdx : wkFml (wkFml Extensionalityᶠ) FOL.∈ᶜ (wkCtx (wkCtx BaseCtx))
  extIdx =
    FOL.there (FOL.there (FOL.there (FOL.there (FOL.there FOL.here))))

  -- In the 2-variable context: derive `x≈y` from emptiness of both.
  emptyUnique-body
    : Deriv (wkCtx (wkCtx BaseCtx)) (
        ((IsEmpty v1) FOL.∧ (IsEmpty v0)) FOL.⇒ (v1 ≈ᶠ v0))
  emptyUnique-body =
    ⇒I
      (let
         Γ₂ = wkCtx (wkCtx BaseCtx)
         Γ₁ = ((IsEmpty v1) FOL.∧ (IsEmpty v0)) ∷ Γ₂

         memEq : Deriv Γ₁ (FOL.All (FOL.Iff (v0 ∈ᶠ v2) (v0 ∈ᶠ v1)))
         memEq =
           ∀I
             (let
                Γ₃ = wkCtx Γ₁

                z∈x⇒z∈y : Deriv Γ₃ ((v0 ∈ᶠ v2) FOL.⇒ (v0 ∈ᶠ v1))
                z∈x⇒z∈y =
                  ⇒I
                    (let
                       Γ₄ = (v0 ∈ᶠ v2) ∷ Γ₃
                       emptyX'' : Deriv Γ₄ (wkFml (IsEmpty v1))
                       emptyX'' = ∧E₁ (hyp (FOL.there FOL.here))
                       notZ∈x'' : Deriv Γ₄ (FOL.Not (v0 ∈ᶠ v2))
                       notZ∈x'' = ∀E emptyX'' v0
                     in
                     ⊥E (⇒E notZ∈x'' (hyp FOL.here)))

                z∈y⇒z∈x : Deriv Γ₃ ((v0 ∈ᶠ v1) FOL.⇒ (v0 ∈ᶠ v2))
                z∈y⇒z∈x =
                  ⇒I
                    (let
                       Γ₅ = (v0 ∈ᶠ v1) ∷ Γ₃
                       emptyY'' : Deriv Γ₅ (wkFml (IsEmpty v0))
                       emptyY'' = ∧E₂ (hyp (FOL.there FOL.here))
                       notZ∈y'' : Deriv Γ₅ (FOL.Not (v0 ∈ᶠ v1))
                       notZ∈y'' = ∀E emptyY'' v0
                     in
                     ⊥E (⇒E notZ∈y'' (hyp FOL.here)))

              in
              ∧I z∈x⇒z∈y z∈y⇒z∈x)

         ext : Deriv Γ₁ (wkFml (wkFml Extensionalityᶠ))
         ext = hyp (FOL.there extIdx)

         ext-x = ∀E ext v1
         ext-x-y = ∀E ext-x v0

      in
      ⇒E ext-x-y memEq)

  emptyUnique : Deriv BaseCtx EmptyUniqueᶠ
  emptyUnique =
    ∀I (∀I emptyUnique-body)

  valid-EmptyUniqueᶠ : ∀ env → Sat env EmptyUniqueᶠ
  valid-EmptyUniqueᶠ env = sound-BaseCtx emptyUnique env

-- ZFC extension: package the ZF theory façade together with
-- - the explicit AC witness (`ZFCAxiomsᶠ.AC`), and
-- - a first-order Choice sentence (`Choiceᶠ`) plus its validity proof.

module FromZFCAxiomsᶠ-Theory {ℓ : Level}
                             {Sig : LogOSSignature ℓ}
                             {Q   : QAdapter ℓ}
                             (K   : Kernel Sig Q)
                             (zfc : ZFCAxiomsᶠ K)
                             where
  module AxZFC = ZFCAxioms.FromZFCAxiomsᶠ K zfc

  open ZFCAxiomsᶠ zfc public using (AC)

  module AxZF = ZFCAxioms.FromZFAxiomsᶠ K (ZFCAxiomsᶠ.zf zfc)
  open AxZF using (ΣZ)
  open AxZF.Sem

  module ZFTheory = FromZFAxiomsᶠ-Theory K (ZFCAxiomsᶠ.zf zfc)
  open ZFTheory public

  -- A ZFC base context: ZF base axioms plus the Choice sentence.
  BaseCtxZFC : FOL.Ctx ΣZ 0
  BaseCtxZFC = AxZFC.Choiceᶠ ∷ BaseCtx

  -- A ZFC context: ZF (base + selected schema instances) plus Choice.
  ZFCtx : List (Kernel.Code K) → List (Kernel.Code K) → FOL.Ctx ΣZ 0
  ZFCtx seps reps = AxZFC.Choiceᶠ ∷ ZFctx seps reps

  satCtx-BaseZFC : ∀ env → SatCtx env BaseCtxZFC
  satCtx-BaseZFC env = AxZFC.valid-Choiceᶠ env , satCtx-Base env

  satCtx-ZFCtx
    : ∀ (Φ : List (Kernel.Code K)) (Ψ : List (Kernel.Code K)) env
    → SatCtx env (ZFCtx Φ Ψ)
  satCtx-ZFCtx Φ Ψ env = AxZFC.valid-Choiceᶠ env , satCtx-ZFctx Φ Ψ env

  sound-BaseCtxZFC
    : ∀ {φ : FOL.Fml ΣZ 0}
    → Deriv BaseCtxZFC φ
    → ∀ env
    → Sat env φ
  sound-BaseCtxZFC d env = zf-sound d env (satCtx-BaseZFC env)

  sound-ZFCtx
    : ∀ (Φ : List (Kernel.Code K)) (Ψ : List (Kernel.Code K)) {φ : FOL.Fml ΣZ 0}
    → Deriv (ZFCtx Φ Ψ) φ
    → ∀ env
    → Sat env φ
  sound-ZFCtx Φ Ψ d env = zf-sound d env (satCtx-ZFCtx Φ Ψ env)
