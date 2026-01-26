{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ObjectLogic.ZFC.Theory where

open import LogOS.Prelude
import LogOS.Syntax.Prop as Prop

open import LogOS.Prelude.Fin using (fzero; fsuc)
open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.Domain.ZFC.SetTheory.FormulaPack using (ZFAxiomsᶠ; ZFCAxiomsᶠ)
open import LogOS.ObjectLogic.FOL.All as FOL
open import LogOS.ObjectLogic.FOL.ND using (Deriv; hyp; ⊥E; ⇒I; ⇒E; ∧I; ∧E₁; ∧E₂; ∀I; ∀E)
import LogOS.ObjectLogic.FOL.NDTheory as NDTheory
open import LogOS.ObjectLogic.FOL.Soundness as FOLSoundness
import LogOS.ObjectLogic.ZFC.Axioms as ZFCAxioms

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

-- A small “theory façade”:
-- - packages the ZF axiom sentences into a FOL context
-- - gives the interpretation statement: derivations from those axioms are
--   semantically valid in any `ZFAxiomsᶠ` model.
--
-- Note: the proof system used here is intuitionistic natural deduction
-- (`LogOS.ObjectLogic.FOL.ND`). Classical reasoning is an explicit extra assumption
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
  open ZFAxiomsᶠ zf public using (SetU; Pred)

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

  addSeparation : List ZPredCode → FOL.Ctx ΣZ 0 → FOL.Ctx ΣZ 0
  addSeparation []       Γ = Γ
  addSeparation (φ ∷ Φ)  Γ = Separationᶠ φ ∷ addSeparation Φ Γ

  addReplacement : List ZRelCode → FOL.Ctx ΣZ 0 → FOL.Ctx ΣZ 0
  addReplacement []       Γ = Γ
  addReplacement (ψ ∷ Ψ)  Γ = Replacementᶠ ψ ∷ addReplacement Ψ Γ

  -- A ZF context parameterised by finite “instances” of the two schemata.
  ZFctx : List ZPredCode → List ZRelCode → FOL.Ctx ΣZ 0
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
    : ∀ (Φ : List ZPredCode) Γ env
    → SatCtx env Γ
    → SatCtx env (addSeparation Φ Γ)
  satCtx-addSeparation []        Γ env satΓ = satΓ
  satCtx-addSeparation (φ ∷ Φ)  Γ env satΓ =
    valid-Separationᶠ φ env , satCtx-addSeparation Φ Γ env satΓ

  satCtx-addReplacement
    : ∀ (Ψ : List ZRelCode) Γ env
    → SatCtx env Γ
    → SatCtx env (addReplacement Ψ Γ)
  satCtx-addReplacement []        Γ env satΓ = satΓ
  satCtx-addReplacement (ψ ∷ Ψ)  Γ env satΓ =
    valid-Replacementᶠ ψ env , satCtx-addReplacement Ψ Γ env satΓ

  satCtx-ZFctx
    : ∀ (Φ : List ZPredCode) (Ψ : List ZRelCode) env
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
  zf-sound = FOLSoundness.sound SetU PredI RelI

  sound-BaseCtx
    : ∀ {φ : FOL.Fml ΣZ 0}
    → Deriv BaseCtx φ
    → ∀ env
    → Sat env φ
  sound-BaseCtx d env = zf-sound d env (satCtx-Base env)

  sound-ZFctx
    : ∀ (Φ : List ZPredCode) (Ψ : List ZRelCode) {φ : FOL.Fml ΣZ 0}
    → Deriv (ZFctx Φ Ψ) φ
    → ∀ env
    → Sat env φ
  sound-ZFctx Φ Ψ d env = zf-sound d env (satCtx-ZFctx Φ Ψ env)

  -- --------------------------------------------------------------------------
  -- Schema-native axioms (no finite instance lists)
  -- --------------------------------------------------------------------------

  -- Axioms are provided as an explicit predicate, closed under weakening. This
  -- lets the theory range over *all* schema instances `Separationᶠ φ` and
  -- `Replacementᶠ ψ` without enumerating them.

  data ZFAx : ∀ {n} → FOL.Fml ΣZ n → Set ℓ where
    EqRefl-ax : ZFAx EqReflᶠ
    EqSym-ax  : ZFAx EqSymᶠ
    EqTrans-ax : ZFAx EqTransᶠ
    MemCongR-ax : ZFAx MemCongRᶠ
    MemCongL-ax : ZFAx MemCongLᶠ
    Extensionality-ax : ZFAx Extensionalityᶠ
    Empty-ax : ZFAx Emptyᶠ
    Pairing-ax : ZFAx Pairingᶠ
    Union-ax : ZFAx Unionᶠ
    Powerset-ax : ZFAx Powersetᶠ
    Infinity-ax : ZFAx Infinityᶠ
    Foundation-ax : ZFAx Foundationᶠ
    Separation-ax : (φ : ZPredCode) → ZFAx (Separationᶠ φ)
    Replacement-ax : (ψ : ZRelCode) → ZFAx (Replacementᶠ ψ)

    wk-ax : ∀ {n} {φ : FOL.Fml ΣZ n} → ZFAx φ → ZFAx (wkFml φ)

  axValid-ZFAx : ∀ {n} {φ : FOL.Fml ΣZ n} → ZFAx φ → ∀ env → Sat env φ
  axValid-ZFAx EqRefl-ax env = valid-EqReflᶠ env
  axValid-ZFAx EqSym-ax env = valid-EqSymᶠ env
  axValid-ZFAx EqTrans-ax env = valid-EqTransᶠ env
  axValid-ZFAx MemCongR-ax env = valid-MemCongRᶠ env
  axValid-ZFAx MemCongL-ax env = valid-MemCongLᶠ env
  axValid-ZFAx Extensionality-ax env = valid-Extensionalityᶠ env
  axValid-ZFAx Empty-ax env = valid-Emptyᶠ env
  axValid-ZFAx Pairing-ax env = valid-Pairingᶠ env
  axValid-ZFAx Union-ax env = valid-Unionᶠ env
  axValid-ZFAx Powerset-ax env = valid-Powersetᶠ env
  axValid-ZFAx Infinity-ax env = valid-Infinityᶠ env
  axValid-ZFAx Foundation-ax env = valid-Foundationᶠ env
  axValid-ZFAx (Separation-ax φ) env = valid-Separationᶠ φ env
  axValid-ZFAx (Replacement-ax ψ) env = valid-Replacementᶠ ψ env
  axValid-ZFAx (wk-ax {φ = φ} h) env =
    let
      env₀ = renEnv wkRen env
      d   = env fzero

      eq : EnvEq env (extend d env₀)
      eq = λ where
        fzero    → refl
        (fsuc i) → refl

      satWk : Sat (extend d env₀) (wkFml φ)
      satWk = Prop.from (sat-wk env₀ d φ) (axValid-ZFAx h env₀)
    in
    Prop.from (sat-envEq eq (wkFml φ)) satWk

  DerivZF : FOL.Fml ΣZ 0 → Set ℓ
  DerivZF φ = NDTheory.DerivAx ZFAx [] φ

  sound-ZF
    : ∀ {φ : FOL.Fml ΣZ 0}
    → DerivZF φ
    → ∀ env → Sat env φ
  sound-ZF d env =
    let module S = NDTheory.Soundness SetU PredI RelI in
    S.soundAx ZFAx axValid-ZFAx d env tt

  -- ZF with extra axioms: soundness is parametric in any additional axiom pack.
  --
  -- This is the clean “ZFC + additional axioms” surface: add axioms by extending
  -- the axiom predicate, and discharge them by supplying their validity.

  ZFAx+ : ∀ {ℓExtra} (Extra : ∀ {n} → FOL.Fml ΣZ n → Set ℓExtra) → ∀ {n} → FOL.Fml ΣZ n → Set (ℓ ⊔ ℓExtra)
  ZFAx+ Extra φ = ZFAx φ ⊎ Extra φ

  DerivZF+ : ∀ {ℓExtra} (Extra : ∀ {n} → FOL.Fml ΣZ n → Set ℓExtra) → FOL.Fml ΣZ 0 → Set (ℓ ⊔ ℓExtra)
  DerivZF+ Extra φ = NDTheory.DerivAx (ZFAx+ Extra) [] φ

  sound-ZF+
    : ∀ {ℓExtra} (Extra : ∀ {n} → FOL.Fml ΣZ n → Set ℓExtra)
    → (extraValid : ∀ {n} {φ : FOL.Fml ΣZ n} → Extra φ → ∀ env → Sat env φ)
    → ∀ {φ : FOL.Fml ΣZ 0}
    → DerivZF+ Extra φ
    → ∀ env → Sat env φ
  sound-ZF+ Extra extraValid d env =
    let module S = NDTheory.Soundness SetU PredI RelI in
    S.soundAx (ZFAx+ Extra) axValid d env tt
    where
      axValid : ∀ {n} {φ : FOL.Fml ΣZ n} → ZFAx+ Extra φ → ∀ env → Sat env φ
      axValid (inj₁ h) env = axValid-ZFAx h env
      axValid (inj₂ h) env = extraValid h env

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
  open AxZF using (ΣZ; ZPredCode; ZRelCode)
  open AxZF.Sem

  module ZFTheory = FromZFAxiomsᶠ-Theory K (ZFCAxiomsᶠ.zf zfc)
  open ZFTheory public

  -- A ZFC base context: ZF base axioms plus the Choice sentence.
  BaseCtxZFC : FOL.Ctx ΣZ 0
  BaseCtxZFC = AxZFC.Choiceᶠ ∷ BaseCtx

  -- A ZFC context: ZF (base + selected schema instances) plus Choice.
  ZFCtx : List ZPredCode → List ZRelCode → FOL.Ctx ΣZ 0
  ZFCtx seps reps = AxZFC.Choiceᶠ ∷ ZFctx seps reps

  satCtx-BaseZFC : ∀ env → SatCtx env BaseCtxZFC
  satCtx-BaseZFC env = AxZFC.valid-Choiceᶠ env , satCtx-Base env

  satCtx-ZFCtx
    : ∀ (Φ : List ZPredCode) (Ψ : List ZRelCode) env
    → SatCtx env (ZFCtx Φ Ψ)
  satCtx-ZFCtx Φ Ψ env = AxZFC.valid-Choiceᶠ env , satCtx-ZFctx Φ Ψ env

  sound-BaseCtxZFC
    : ∀ {φ : FOL.Fml ΣZ 0}
    → Deriv BaseCtxZFC φ
    → ∀ env
    → Sat env φ
  sound-BaseCtxZFC d env = zf-sound d env (satCtx-BaseZFC env)

  -- --------------------------------------------------------------------------
  -- Schema-native ZFC (axioms as a predicate)
  -- --------------------------------------------------------------------------

  data ZFCAx : ∀ {n} → FOL.Fml ΣZ n → Set ℓ where
    ZF-ax     : ∀ {n} {φ : FOL.Fml ΣZ n} → ZFAx φ → ZFCAx φ
    Choice-ax : ZFCAx AxZFC.Choiceᶠ
    wk-ax     : ∀ {n} {φ : FOL.Fml ΣZ n} → ZFCAx φ → ZFCAx (wkFml φ)

  axValid-ZFCAx : ∀ {n} {φ : FOL.Fml ΣZ n} → ZFCAx φ → ∀ env → Sat env φ
  axValid-ZFCAx (ZF-ax h) env = axValid-ZFAx h env
  axValid-ZFCAx Choice-ax env = AxZFC.valid-Choiceᶠ env
  axValid-ZFCAx (wk-ax {φ = φ} h) env =
    let
      env₀ = renEnv wkRen env
      d   = env fzero

      eq : EnvEq env (extend d env₀)
      eq = λ where
        fzero    → refl
        (fsuc i) → refl

      satWk : Sat (extend d env₀) (wkFml φ)
      satWk = Prop.from (sat-wk env₀ d φ) (axValid-ZFCAx h env₀)
    in
    Prop.from (sat-envEq eq (wkFml φ)) satWk

  DerivZFC : FOL.Fml ΣZ 0 → Set ℓ
  DerivZFC φ = NDTheory.DerivAx ZFCAx [] φ

  sound-ZFC
    : ∀ {φ : FOL.Fml ΣZ 0}
    → DerivZFC φ
    → ∀ env → Sat env φ
  sound-ZFC d env =
    let module S = NDTheory.Soundness SetU AxZF.PredI AxZF.RelI in
    S.soundAx ZFCAx axValid-ZFCAx d env tt

  ZFCAx+ : ∀ {ℓExtra} (Extra : ∀ {n} → FOL.Fml ΣZ n → Set ℓExtra) → ∀ {n} → FOL.Fml ΣZ n → Set (ℓ ⊔ ℓExtra)
  ZFCAx+ Extra φ = ZFCAx φ ⊎ Extra φ

  DerivZFC+ : ∀ {ℓExtra} (Extra : ∀ {n} → FOL.Fml ΣZ n → Set ℓExtra) → FOL.Fml ΣZ 0 → Set (ℓ ⊔ ℓExtra)
  DerivZFC+ Extra φ = NDTheory.DerivAx (ZFCAx+ Extra) [] φ

  sound-ZFC+
    : ∀ {ℓExtra} (Extra : ∀ {n} → FOL.Fml ΣZ n → Set ℓExtra)
    → (extraValid : ∀ {n} {φ : FOL.Fml ΣZ n} → Extra φ → ∀ env → Sat env φ)
    → ∀ {φ : FOL.Fml ΣZ 0}
    → DerivZFC+ Extra φ
    → ∀ env → Sat env φ
  sound-ZFC+ Extra extraValid d env =
    let module S = NDTheory.Soundness SetU AxZF.PredI AxZF.RelI in
    S.soundAx (ZFCAx+ Extra) axValid d env tt
    where
      axValid : ∀ {n} {φ : FOL.Fml ΣZ n} → ZFCAx+ Extra φ → ∀ env → Sat env φ
      axValid (inj₁ h) env = axValid-ZFCAx h env
      axValid (inj₂ h) env = extraValid h env

  sound-ZFCtx
    : ∀ (Φ : List ZPredCode) (Ψ : List ZRelCode) {φ : FOL.Fml ΣZ 0}
    → Deriv (ZFCtx Φ Ψ) φ
    → ∀ env
    → Sat env φ
  sound-ZFCtx Φ Ψ d env = zf-sound d env (satCtx-ZFCtx Φ Ψ env)
