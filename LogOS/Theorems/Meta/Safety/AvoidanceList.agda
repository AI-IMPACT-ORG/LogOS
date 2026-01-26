{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Safety.AvoidanceList where

-- Paradox avoidance inventory: each paradox is gated by explicit assumptions.
-- The kernel alone does not supply these gates; they must be added deliberately.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_; ¬_; ⊥; ⊥-elim)
open import LogOS.Prelude.Product using (Σ; _,_; proj₁; proj₂)
open import LogOS.Prelude.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Theorems.Meta.Base using (DeciderC; NonTrivialC)
open import LogOS.Theorems.Meta.Assumptions.Core as Core
open import LogOS.Theorems.Meta.Assumptions.Diagonal as Diag
import LogOS.Theorems.Meta.Lob as Lob
import LogOS.Theorems.Meta.Godel as Godel
import LogOS.Theorems.Meta.Tarski as Tarski

-- ---------------------------------------------------------------------------
-- Set-theoretic paradox gates (Russell / Burali-Forti).
-- ---------------------------------------------------------------------------

record MembershipTheory {ℓ : Level} : Set (lsuc ℓ) where
  infix 4 _∈_
  field
    Obj : Set ℓ
    _∈_ : Obj → Obj → Set ℓ

record Comprehension {ℓ : Level} (T : MembershipTheory {ℓ}) : Set (lsuc ℓ) where
  open MembershipTheory T
  field
    setOf : (Obj → Set ℓ) → Obj
    mem   : ∀ {P x} → x ∈ setOf P ↔ P x

record RussellRequires {ℓ : Level} : Set (lsuc ℓ) where
  field
    Theory : MembershipTheory {ℓ}
    Comp   : Comprehension Theory

BuraliFortiRequires : ∀ {ℓ : Level} → Set (lsuc ℓ)
BuraliFortiRequires = RussellRequires

-- ---------------------------------------------------------------------------
-- Truth- and diagonalization-based paradoxes (Liar / Tarski / Yablo).
-- ---------------------------------------------------------------------------

record TruthDiagonalRequires {ℓ : Level}
                             {Sig : LogOSSignature ℓ}
                             {Q   : QAdapter ℓ}
                             (K  : Kernel Sig Q)
                             : Set (lsuc ℓ) where
  field
    TruthK : Kernel.Code K → Set ℓ
    TD     : Diag.TruthDiagonal K TruthK

module Liar
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q) (R : TruthDiagonalRequires K)
  where
  open TruthDiagonalRequires R

  no-decider : ¬ (DeciderC {K = K} TruthK)
  no-decider = Tarski.undef-classical K TruthK TD

  nontrivial : NonTrivialC {K = K} TruthK
  nontrivial =
    let
      decFalse : ∀ γ → (⊥ {ℓ = ℓ}) ⊎ ¬ (⊥ {ℓ = ℓ})
      decFalse _ = inj₂ (λ x → ⊥-elim x)

      pairTrue = Diag.TruthDiagonal.liarForDecider TD (λ _ → ⊥) decFalse
      γtrue = proj₁ pairTrue
      eqtrue = proj₂ pairTrue
      truthγ : TruthK γtrue
      truthγ = Prop.from eqtrue (λ x → ⊥-elim x)

      decTrue : ∀ γ → ⊤ ⊎ ¬ ⊤
      decTrue _ = inj₁ tt

      pairFalse = Diag.TruthDiagonal.liarForDecider TD (λ _ → ⊤) decTrue
      γfalse = proj₁ pairFalse
      eqfalse = proj₂ pairFalse
      notTruthγ : ¬ TruthK γfalse
      notTruthγ t = Prop.to eqfalse t tt
    in
    (γtrue , truthγ) , (γfalse , notTruthγ)

-- Tarski and Yablo share the same gate as Liar: an internal truth predicate
-- plus diagonalization.

-- ---------------------------------------------------------------------------
-- Gödel/Löb-style paradoxes (provability + implication + diagonalization).
-- ---------------------------------------------------------------------------

record GodelRequires {ℓ : Level}
                     {Sig : LogOSSignature ℓ}
                     {Q   : QAdapter ℓ}
                     (K  : Kernel Sig Q)
                     : Set (lsuc ℓ) where
  field
    Pr   : Core.Provability K
    Op   : Core.ProvabilityOps K
    LobA : Lob.LoebAxiom K Pr Op

module Godel2
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (R : GodelRequires K)
  (Bot Con : Kernel.Code K)
  (ConDef  : Con ≡ Core.ProvabilityOps.Imp (GodelRequires.Op R) (Core.ProvabilityOps.Box (GodelRequires.Op R) Bot) Bot)
  (Consistent : ¬ (Core.Provability.Prov (GodelRequires.Pr R) Bot))
  where
  open GodelRequires R

  incompleteness : ¬ (Core.Provability.Prov Pr Con)
  incompleteness = Godel.incompleteness K Pr Op LobA Bot Con ConDef Consistent

record CurryRequires {ℓ : Level}
                     {Sig : LogOSSignature ℓ}
                     {Q   : QAdapter ℓ}
                     (K  : Kernel Sig Q)
                     : Set (lsuc ℓ) where
  field
    Pr : Core.Provability K
    Op : Core.ProvabilityOps K
    Ir : Core.ImpRules K Pr Op
    Dl : Diag.Diagonalization K Pr Op

module Curry
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (R : CurryRequires K)
  (Bot : Kernel.Code K)
  where
  open CurryRequires R
  open Core.Provability Pr renaming (Prov to ⊢)
  open Core.ProvabilityOps Op

  record FixedPoint : Set (lsuc ℓ) where
    field
      γ : Kernel.Code K
      γ→γ→⊥ : ⊢ (Imp γ (Imp γ Bot))
      γ→⊥→γ : ⊢ (Imp (Imp γ Bot) γ)

  curry-fixedpoint : FixedPoint
  curry-fixedpoint =
    let
      f : Kernel.Code K → Kernel.Code K
      f x = Imp x Bot

      γ = Diag.Diagonalization.diag Dl f
      γ→fγ = Diag.Diagonalization.diag→ Dl f
      fγ→γ = Diag.Diagonalization.→diag Dl f
    in
    record { γ = γ ; γ→γ→⊥ = γ→fγ ; γ→⊥→γ = fγ→γ }

-- ---------------------------------------------------------------------------
-- Definability / Berry-style gates.
-- ---------------------------------------------------------------------------

record Definability {ℓ : Level} (Code : Set ℓ) : Set (lsuc ℓ) where
  field
    Def : Code → Set ℓ

record BerryRequires {ℓ : Level}
                     {Sig : LogOSSignature ℓ}
                     {Q   : QAdapter ℓ}
                     (K  : Kernel Sig Q)
                     : Set (lsuc ℓ) where
  field
    DefK : Definability (Kernel.Code K)

-- ---------------------------------------------------------------------------
-- Reflection and fixpoint gates.
-- ---------------------------------------------------------------------------

record UnsafeReflection {ℓ : Level}
                        {Sig : LogOSSignature ℓ}
                        {Q   : QAdapter ℓ}
                        (K  : Kernel Sig Q)
                        : Set (lsuc ℓ) where
  field
    QS : Diag.QuoteSubst K

record UnrestrictedFixpoint {ℓ : Level}
                            {Sig : LogOSSignature ℓ}
                            {Q   : QAdapter ℓ}
                            (K  : Kernel Sig Q)
                            : Set (lsuc ℓ) where
  field
    Fix : Core.BoundaryFix K

-- ---------------------------------------------------------------------------
-- Explosion gate (ex-falso).
-- ---------------------------------------------------------------------------

record Explosion {ℓ : Level}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K  : Kernel Sig Q)
                 : Set (lsuc ℓ) where
  field
    Pr  : Core.Provability K
    Bot : Kernel.Code K
    ex-falso : ∀ {φ} → Core.Provability.Prov Pr Bot → Core.Provability.Prov Pr φ

module ExplosionConsequences
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  (E : Explosion K)
  where
  open Explosion E
  open Core.Provability Pr renaming (Prov to ⊢)

  provable-all
    : ⊢ Bot → ∀ {φ} → ⊢ φ
  provable-all pBot {φ} = ex-falso {φ} pBot

  no-bot-if-nontrivial
    : NonTrivialC {K = K} ⊢
    → ¬ ⊢ Bot
  no-bot-if-nontrivial nt pBot =
    let
      _ , (γ , notγ) = nt
    in
    notγ (provable-all pBot {φ = γ})
