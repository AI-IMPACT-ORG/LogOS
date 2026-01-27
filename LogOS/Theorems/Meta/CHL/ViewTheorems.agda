{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.ViewTheorems where

-- Quoteable theorem surfaces for the documentation views, packaged under CHL.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Base.Signature.Hom using (SigHom)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary; ≡→≈CP)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel hiding (Box; decode-Box; box-mono)

import LogOS.Algebra.Quantale as Quantale
import LogOS.Algebra.ConAlg as ConAlg
import LogOS.Free.ConstraintsOverSig as ConOverSig
import LogOS.Kernel.Boundary as KBoundary
import LogOS.Kernel.Core as KCore
import LogOS.Kernel.LogicKernel as LK
import LogOS.Theorems.Meta.CHL.Core as Core
import LogOS.Theorems.Meta.CHL.Category as Category
import LogOS.Theorems.Meta.CHL.Completeness as Complete
import LogOS.Theorems.Meta.CHL.Definition as Definition
import LogOS.Theorems.Meta.CHL.Capstone as Capstone
import LogOS.Theorems.Meta.CHL.2Cat as Cat2
import LogOS.Theorems.Meta.CHL.Indexed as Indexed
import LogOS.Theorems.Meta.CHL.Guarded as Guarded
import LogOS.Theorems.CategoryTheory.KernelCat as KernelCat
import LogOS.Boundary.Budget as Budget
import LogOS.Boundary.Telemetry as Telemetry
import LogOS.Theorems.Meta.Views as MetaViews
import LogOS.Theorems.Meta.ObserverCore as ObsCore
import LogOS.Theorems.Meta.CommunicableTruth as Comm
import LogOS.Theorems.CategoryTheory.Port2Cat as Port2Catₜ

-- Signature change surface (multi-institution direction).
module Reindex
  {ℓ : Level}
  {Sig₁ Sig₂ : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (σ : SigHom Sig₁ Sig₂)
  (K : Kernel Sig₂ Q)
  where
  open Indexed.For σ K public

module ReindexWithFml
  {ℓ : Level}
  {Sig₁ Sig₂ : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (σ : SigHom Sig₁ Sig₂)
  (K : Kernel Sig₂ Q)
  {Fml₁ : Set ℓ}
  (mapFml : Fml₁ → Kernel.Fml K)
  where
  open Indexed.WithFml σ K mapFml public

module ReindexingSatisfaction
  {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (σ : SigHom Sig₁ Sig₂)
  (K₂ : Kernel Sig₂ Q)
  where
  open MetaViews.ReindexingSatisfaction σ K₂ public

module ReindexingSatisfactionWithFml
  {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (σ : SigHom Sig₁ Sig₂)
  (K₂ : Kernel Sig₂ Q)
  {Fml₁ : Set ℓ}
  (mapFml : Fml₁ → Kernel.Fml K₂)
  where
  open MetaViews.ReindexingSatisfactionWithFml σ K₂ mapFml public

module ReindexingSatisfactionWithFmlLogic
  {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (σ : SigHom Sig₁ Sig₂)
  (K₂ : LK.LogicKernel Sig₂ Q)
  {Fml₁ : Set ℓ}
  (mapFml : Fml₁ → LK.LogicKernel.Fml K₂)
  where
  open MetaViews.ReindexingSatisfactionWithFmlLogic σ K₂ mapFml public

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  module C  = Core.For K
  module Cat = Category.For K
  module Co = Complete.For K
  module Def = Definition.For K
  module Cap = Capstone.For K
  module K2  = Cat2.For {Sig = Sig} {Q = Q}

  -- CHL capstone view (kernel-native proof/model/category/observer bundle).
  module CHL where
    open C public using
      ( Ty; Refines; Equiv; Box; truth
      ; proofs-as-refinement; truth-fixed; truth≤Box; box≤truth
      )

    capstone : Cap.Capstone
    capstone = Cap.capstone

    capstone-complete : ∀ (A : Cap.Adequacy) → Cap.CapstoneComplete A
    capstone-complete = Cap.capstone-complete

    capstone-complete-budget
      : ∀ {B} (A : Co.BudgetedAdequacy B)
      → Cap.CapstoneCompleteBudget B A
    capstone-complete-budget = Cap.capstone-complete-budget

    completeF
      : Co.BoundaryAdequacy
      → ∀ {φ ψ} → (Def._⊢F_ φ ψ) ↔ Def.S.EntailsS φ ψ
    completeF = Def.completeF

    completeF-budget
      : ∀ {B} → Co.BudgetedAdequacy B
      → ∀ {φ ψ} → (Def._⊢F_ φ ψ) ↔ Def.S.EntailsS-budget B φ ψ
    completeF-budget = Def.completeF-budget

    formula-program = Def.formula-program

  -- Multi-institution view: S↔H coherence and boundary coherence.
  module MultiInstitution where
    module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)
    open Truth.StrictTruth Sig

    coh-SH
      : ∀ (w : LogOSSignature.Cosp Sig) (φ : Kernel.Fml K)
      → Prop._↔_
          (StrictLayer.Sat_S (Kernel.Strict K) w φ)
          (HT.HLayer.Sat_H (Kernel.HTruth K) w (Kernel.TransH K φ))
    coh-SH = Kernel.coh-LH K

    coh-H∂
      : ∀ (w : LogOSSignature.Cosp Sig)
        (c : ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K)))
      → Prop._↔_
          (HT.HLayer.Sat_H (Kernel.HTruth K) w c)
          (Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c)
    coh-H∂ = Kernel.sat-coh K

    -- Sentence/program layer: covariant renaming along signature morphisms.
    module SentenceLayer where
      open ConOverSig public
        using
          ( Con∂; Conb
          ; rename∂; renameb
          ; rename∂-id; renameb-id
          ; rename∂-compose; renameb-compose
          ; rename∂-mono; renameb-mono
          ; interp∂-rename; interpb-rename
          )

  -- 3-level HoTT-style view: tier coherences + guarded reflection.
  module HoTT3Level where
    module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)
    open Truth.StrictTruth Sig

    coh-SH = Kernel.coh-LH K
    coh-H∂ = Kernel.sat-coh K
    decode-Box = C.decode-Box
    guarded-fixed = C.truth-fixed
    module G = Guarded.For K
    open G public using (Stable; stable-truth)

  -- Commuting square: strict semantics ↔ boundary semantics of encoded formulas.
  module Commuting where
    module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)
    open Truth.StrictTruth Sig

    formula-sat-boundary
      : ∀ (w : LogOSSignature.Cosp Sig) (φ : Kernel.Fml K)
      → Prop._↔_
          (StrictLayer.Sat_S (Kernel.Strict K) w φ)
          (Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w)
            (C.denote (Def.FormulaType φ)))
    formula-sat-boundary w φ =
      let
        coh₁ = Kernel.coh-LH K w φ
        coh₂ = Kernel.sat-coh K w (Kernel.TransH K φ)
        eq   = Def.FormulaType-decode φ
        eq≈  = ≡→≈CP {CP = BulkBoundary.bnd (Kernel.BB K)} eq
        rew  : Prop._↔_
                 (Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (Kernel.TransH K φ))
                 (Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w)
                   (C.denote (Def.FormulaType φ)))
        rew =
          Prop.intro
            (λ sat → KCore.Sat_H_bnd-mono (Kernel.shape K) (snd eq≈) sat)
            (λ sat → KCore.Sat_H_bnd-mono (Kernel.shape K) (fst eq≈) sat)
      in
      Prop.↔-trans coh₁ (Prop.↔-trans coh₂ rew)

  -- Categorical logic view: ops-only preorder-category + endofunctor + kernel 2-category interface
  -- (thin/lawful only under an explicit proof-irrelevance assumption).
  module CategoricalLogic where
    CodeThinCat = Cat.CodeThinCat
    BoxFunctor = Cat.BoxFunctor
    Kernel2Cat = K2.KernelRef2Cat

    -- Optional strengthening: if refinement proofs are thin/proof-irrelevant,
    -- the usual category/functor laws become available (and are explicit).
    ThinHom = Category.ThinHom
    ThinCatLaws = Category.ThinCatLaws
    EndoFunctorLaws = Category.EndoFunctorLaws

    ThinRefines = Cat.ThinRefines
    codeCat-laws = Cat.codeCat-laws
    boxFunctor-laws = Cat.boxFunctor-laws

    Port2Cat
      : ∀ {ℓForm}
      → Port2Catₜ.Port2Cat {ℓ = ℓ} {ℓForm = ℓForm} (KBoundary.boundaryIO K)
    Port2Cat {ℓForm} =
      let module P = Port2Catₜ.For {ℓForm = ℓForm} (KBoundary.boundaryIO K) in
      P.Port2Cat-instance

    KernelCategory : KernelCat.KernelCat Sig Q
    KernelCategory = KernelCat.KernelCat-instance Sig Q

    quantale : Quantale.Quantale {ℓ}
    quantale = Quantale.quantaleFromQAdapter Q

    conAlg : ConAlg.ConAlg {ℓ}
    conAlg =
      record
        { BB    = Kernel.BB K
        ; MBulk = Kernel.MBulk K
        ; MBnd  = Kernel.MBnd K
        ; Holo  = Kernel.Holo K
        }

  -- Observer semantics view: boundary entailment and budgeted variants.
  module ObserverSemantics where
    boundaryIO = KBoundary.boundaryIO K

    open Co public
      using
        ( Entails∂
        ; Entails∂-budget
        ; Budget
        ; BudgetedAdequacy
        ; ObsAdequacy
        ; sound-complete∂-budget
        )

    module TelemetryBudget
      (T : Telemetry.TelemetryTrace ℓ)
      (P : Telemetry.ProgramTelemetryPort Sig Q (Kernel.HWorld K)
              (Kernel.BB K) (Kernel.HTruth K) (KBoundary.boundaryIO K) T)
      where
      module B =
        Budget.For Sig Q (Kernel.HWorld K) (Kernel.BB K)
          (Kernel.HTruth K) (KBoundary.boundaryIO K) T P
      open B public using (Budget∂; BudgetCosp; budget-from-trace)

    module SafeReflection where
      -- Cross-link: meta-theory overview in `LogOS/Theorems/Meta/README.md`
      -- (“Safe reflection (literature-aligned)” section).
      -- Semantically polymorphic safety (generic observer core).
      open ObsCore public
        using (SafeAdmissible; SafeAdmissible≈)
        renaming
          ( Safe⋆            to Safe⋆≡-generic
          ; safe⋆-sound      to safe⋆≡-sound-generic
          ; safe⋆-ext        to safe⋆≡-ext-generic
          ; safe⋆-stable     to safe⋆≡-stable-generic
          ; safe⋆-admissible to safe⋆≡-admissible-generic
          ; safe⋆-largest    to safe⋆≡-largest-generic

          ; Safe⋆≈           to Safe⋆-generic
          ; safe⋆≈-sound     to safe⋆-sound-generic
          ; safe⋆≈-ext       to safe⋆-ext-generic
          ; safe⋆≈-stable    to safe⋆-stable-generic
          ; safe⋆≈-admissible to safe⋆-admissible-generic
          ; safe⋆≈-largest   to safe⋆-largest-generic
          )

      -- Kernel-specific safe reflection (closure-stable communicable truth).
      open Comm public
        using (SafeReflection)
        renaming
          ( Safe⋆          to Safe⋆-kernel
          ; safe⋆-core     to safe⋆-core-kernel
          ; safe⋆-intro    to safe⋆-intro-kernel
          ; safe⋆-sound    to safe⋆-sound-kernel
          ; safe⋆-stable   to safe⋆-stable-kernel
          ; safe⋆-ext      to safe⋆-ext-kernel
          ; safe⋆-admissible to safe⋆-admissible-kernel
          ; safe⋆-mono-Truth to safe⋆-mono-Truth-kernel
          )

  -- Projection certificates: each view is a direct projection of kernel fields.
  module Projections where
    record Projection : Set (lsuc ℓ) where
      field
        coh-SH-proj : MultiInstitution.coh-SH ≡ Kernel.coh-LH K
        coh-H∂-proj : MultiInstitution.coh-H∂ ≡ Kernel.sat-coh K
        decode-Box-proj : HoTT3Level.decode-Box ≡ C.decode-Box
        guarded-fixed-proj : HoTT3Level.guarded-fixed ≡ C.truth-fixed
        conAlg-BB : ConAlg.ConAlg.BB CategoricalLogic.conAlg ≡ Kernel.BB K
        conAlg-MBulk : ConAlg.ConAlg.MBulk CategoricalLogic.conAlg ≡ Kernel.MBulk K
        conAlg-MBnd : ConAlg.ConAlg.MBnd CategoricalLogic.conAlg ≡ Kernel.MBnd K
        conAlg-Holo : ConAlg.ConAlg.Holo CategoricalLogic.conAlg ≡ Kernel.Holo K
        boundaryIO-proj : ObserverSemantics.boundaryIO ≡ KBoundary.boundaryIO K

    projection : Projection
    projection =
      record
        { coh-SH-proj = refl
        ; coh-H∂-proj = refl
        ; decode-Box-proj = refl
        ; guarded-fixed-proj = refl
        ; conAlg-BB = refl
        ; conAlg-MBulk = refl
        ; conAlg-MBnd = refl
        ; conAlg-Holo = refl
        ; boundaryIO-proj = refl
        }
