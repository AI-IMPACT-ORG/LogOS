{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Assumptions.Diagonal where

open import LogOS.Prelude
open import LogOS.Prelude using (Σ; proj₁; proj₂; fst; snd)
open import LogOS.Prelude using (_⊎_; inj₁; inj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Endo
open import LogOS.Minimal.Con
open import LogOS.Theorems.Meta.ConditionalPacks using
  (Provability; ProvabilityOps; ProvabilityOpsC; toOpsC)
open import LogOS.Theorems.Code.Core as Code
open import LogOS.Kernel.Eq using (module ForKernel)

-- Diagonalisation and self-reference packs.
--
-- These assumptions are intentionally separated from `Assumptions.Core` so that
-- imports make the trust boundary explicit.

record DiagonalizationC {ℓCode ℓPr : Level}
                        {Code : Set ℓCode}
                        (⊢    : Code → Set ℓPr)
                        (Op   : ProvabilityOpsC Code)
                        : Set (lsuc (ℓCode ⊔ ℓPr)) where
  open ProvabilityOpsC Op
  field
    diag : (Code → Code) → Code
    -- Internal fixed-point: ⊢ diag f ↔ f (diag f)
    diag→ : ∀ f → ⊢ (Imp (diag f) (f (diag f)))
    →diag : ∀ f → ⊢ (Imp (f (diag f)) (diag f))

record Diagonalization {ℓ}
                       {Sig : LogOSSignature ℓ}
                       {Q   : QAdapter ℓ}
                       (K  : Kernel Sig Q)
                       (Pr : Provability K)
                       (Op : ProvabilityOps K)
                       : Set (lsuc ℓ) where
  open Kernel K
  open Provability Pr renaming (Prov to ⊢)
  open ProvabilityOps Op
  field
    diag : (Code → Code) → Code
    -- Internal fixed-point: ⊢ diag f ↔ f (diag f)
    diag→ : ∀ f → ⊢ (Imp (diag f) (f (diag f)))
    →diag : ∀ f → ⊢ (Imp (f (diag f)) (diag f))

Diagonalization→C
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K  : Kernel Sig Q}
    {Pr : Provability K}
    {Op : ProvabilityOps K}
  → Diagonalization K Pr Op
  → DiagonalizationC (Provability.Prov Pr) (toOpsC Op)
Diagonalization→C Dl = record
  { diag  = Diagonalization.diag Dl
  ; diag→ = Diagonalization.diag→ Dl
  ; →diag = Diagonalization.→diag Dl
  }

DiagonalizationC→Diagonalization
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K  : Kernel Sig Q}
    {Pr : Provability K}
    {Op : ProvabilityOps K}
  → DiagonalizationC (Provability.Prov Pr) (toOpsC Op)
  → Diagonalization K Pr Op
DiagonalizationC→Diagonalization Dl = record
  { diag  = DiagonalizationC.diag Dl
  ; diag→ = DiagonalizationC.diag→ Dl
  ; →diag = DiagonalizationC.→diag Dl
  }

-- A purely syntactic self-reference/representation pack for codes, kept outside the core.
-- It states that definable functions f : Code → Code are represented by single-hole
-- templates, and that each template admits a self-instantiation.
--
-- Two variants are provided:
-- - `QuoteSubst⊑`: aligned with the boundary preorder (mutual refinement).
-- - `QuoteSubst` : convenience variant derived from `QuoteSubst⊑` once the
--                  boundary preorder is a partial order (antisymmetry).

record QuoteSubst⊑ {ℓ}
                   {Sig : LogOSSignature ℓ}
                   {Q   : QAdapter ℓ}
                   (K   : Kernel Sig Q)
                   : Set (lsuc ℓ) where
  open Kernel K
  private
    _⊑_ = ConPreorder._⊑_ (BulkBoundary.bnd BB)
  field
    Code₁         : Set ℓ
    inst          : Code₁ → Code → Code
    representable : (f : Code → Code) → Σ Code₁ (λ u → ∀ γ →
                      (decode (inst u γ) ⊑ decode (f γ))
                    × (decode (f γ) ⊑ decode (inst u γ)))
    self          : (u : Code₁) → Σ Code (λ s →
                      (decode s ⊑ decode (inst u s))
                    × (decode (inst u s) ⊑ decode s))

record QuoteSubst {ℓ}
                  {Sig : LogOSSignature ℓ}
                  {Q   : QAdapter ℓ}
                  (K   : Kernel Sig Q)
                  : Set (lsuc ℓ) where
  open Kernel K
  open ForKernel K
  private
    _⊑_ = ConPreorder._⊑_ (BulkBoundary.bnd BB)
  field
    po   : BulkBoundaryPO BB
    core : QuoteSubst⊑ K

  open QuoteSubst⊑ core public using (Code₁; inst)

  representable⊑ : (f : Code → Code) → Σ Code₁ (λ u → ∀ γ →
                    (decode (inst u γ) ⊑ decode (f γ))
                  × (decode (f γ) ⊑ decode (inst u γ)))
  representable⊑ = QuoteSubst⊑.representable core

  self⊑ : (u : Code₁) → Σ Code (λ s →
            (decode s ⊑ decode (inst u s))
          × (decode (inst u s) ⊑ decode s))
  self⊑ = QuoteSubst⊑.self core
  open BulkBoundaryPO po using (po-bnd)
  open PartialOrder po-bnd using (antisym)

  representable : (f : Code → Code) → Σ Code₁ (λ u → ∀ γ → inst u γ ≃K f γ)
  representable f =
    let
      rep  = representable⊑ f
      u    = proj₁ rep
      repr = proj₂ rep
    in
    u , (λ γ → antisym (fst (repr γ)) (snd (repr γ)))

  self : (u : Code₁) → Σ Code (λ s → s ≃K inst u s)
  self u =
    let
      se    = self⊑ u
      s     = proj₁ se
      pair  = proj₂ se
    in
    s , antisym (fst pair) (snd pair)

-- ----------------------------------------------------------------------------
-- Lawvere fixed point (boundary-preorder form).
--
-- In the presence of `QuoteSubst⊑ K` (a “code-as-internal-hom” witness), we can
-- produce a decoded fixed point of any endomap `f : Code → Code` without
-- assuming antisymmetry of the boundary preorder.

InternalHomWitness
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Set (lsuc ℓ)
InternalHomWitness = QuoteSubst⊑

lawvereFix
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → InternalHomWitness K
  → (f : Kernel.Code K → Kernel.Code K)
  → Σ (Kernel.Code K) (λ s →
      ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Kernel.decode K s) (Kernel.decode K (f s))
      ×
      ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Kernel.decode K (f s)) (Kernel.decode K s))
lawvereFix {K = K} QS f =
  let
    open Kernel K
    open QuoteSubst⊑ QS

    rep  = representable f
    u    = proj₁ rep
    repr = proj₂ rep
    se   = self u
    s    = proj₁ se

    selfL = fst (proj₂ se)
    selfR = snd (proj₂ se)
    reprL = fst (repr s)
    reprR = snd (repr s)

    left  = ConPreorder.trans (BulkBoundary.bnd BB) selfL reprL
    right = ConPreorder.trans (BulkBoundary.bnd BB) reprR selfR
  in
  s , (left , right)

-- Optional strengthening: if the boundary preorder is antisymmetric (a partial
-- order), the mutual refinement from `lawvereFix` upgrades to an equality.

lawvereFix≡
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → BulkBoundaryPO (Kernel.BB K)
  → InternalHomWitness K
  → (f : Kernel.Code K → Kernel.Code K)
  → Σ (Kernel.Code K) (λ s → ForKernel._≃K_ K s (f s))
lawvereFix≡ {K = K} po QS f =
  let
    open Kernel K
    open ForKernel K
    open BulkBoundaryPO po using (po-bnd)
    open PartialOrder po-bnd using (antisym)
    s , (le₁ , le₂) = lawvereFix {K = K} QS f
  in
  s , antisym le₁ le₂

-- A convenient fixed-point chooser (used by derived diagonalisation constructors).

lawvereDiag
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → InternalHomWitness K
  → (Kernel.Code K → Kernel.Code K)
  → Kernel.Code K
lawvereDiag QS f = proj₁ (lawvereFix QS f)

lawvereDiag≡
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → BulkBoundaryPO (Kernel.BB K)
  → (QS : InternalHomWitness K)
  → (f  : Kernel.Code K → Kernel.Code K)
  → ForKernel._≃K_ K (lawvereDiag QS f) (f (lawvereDiag QS f))
lawvereDiag≡ po QS f = proj₂ (lawvereFix≡ po QS f)

lawvereDiag-⊑
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → (QS : InternalHomWitness K)
  → (f  : Kernel.Code K → Kernel.Code K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Kernel.decode K (lawvereDiag QS f))
      (Kernel.decode K (f (lawvereDiag QS f)))
lawvereDiag-⊑ QS f = fst (proj₂ (lawvereFix QS f))

⊑-lawvereDiag
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → (QS : InternalHomWitness K)
  → (f  : Kernel.Code K → Kernel.Code K)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Kernel.decode K (f (lawvereDiag QS f)))
      (Kernel.decode K (lawvereDiag QS f))
⊑-lawvereDiag QS f = snd (proj₂ (lawvereFix QS f))

-- A minimal reflection principle: decoded “sameness” implies provability of an implication
-- built with the object-level Imp constructor. This stays model-local.
--
-- Two variants are provided:
-- - `DecodeImp⊑`: from boundary entailment/refinement.
-- - `DecodeImp` : from strict decode equality (`≡`).

record DecodeImp⊑ {ℓ}
                  {Sig : LogOSSignature ℓ}
                  {Q   : QAdapter ℓ}
                  (K  : Kernel Sig Q)
                  (Pr : Provability K)
                  (Op : ProvabilityOps K)
                  : Set (lsuc ℓ) where
  open Kernel K
  open Provability Pr renaming (Prov to ⊢)
  open ProvabilityOps Op
  private
    _⊑_ = ConPreorder._⊑_ (BulkBoundary.bnd BB)
  field
    from-decode⊑→imp : ∀ {φ ψ} → decode φ ⊑ decode ψ → ⊢ (Imp φ ψ)

record DecodeImp {ℓ}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K  : Kernel Sig Q)
                 (Pr : Provability K)
                 (Op : ProvabilityOps K)
                 : Set (lsuc ℓ) where
  open Kernel K
  open ForKernel K
  open Provability Pr renaming (Prov to ⊢)
  open ProvabilityOps Op
  field
    from-decode≃→imp : ∀ {φ ψ} → φ ≃K ψ → ⊢ (Imp φ ψ)

-- Provability-level diagonalization as a theorem:
-- internal-hom witness + local decode⊑→imp bridge ⇒ the classical diagonal schema.

Diagonalization-from-InternalHom
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (Pr : Provability K)
    (Op : ProvabilityOps K)
    (IH : InternalHomWitness K)
    (DI : DecodeImp⊑ K Pr Op)
  → Diagonalization K Pr Op
Diagonalization-from-InternalHom K Pr Op IH DI = record
  { diag  = λ f → lawvereDiag IH f
  ; diag→ = λ f → DecodeImp⊑.from-decode⊑→imp DI (lawvereDiag-⊑ IH f)
  ; →diag = λ f → DecodeImp⊑.from-decode⊑→imp DI (⊑-lawvereDiag IH f)
  }

Diagonalization-from-QuoteSubst
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (Pr : Provability K)
    (Op : ProvabilityOps K)
    (QS : QuoteSubst K)
    (DI : DecodeImp K Pr Op)
  → Diagonalization K Pr Op
Diagonalization-from-QuoteSubst K Pr Op QS DI = record
  { diag  = diag
  ; diag→ = diag→
  ; →diag = →diag
  }
  where
    open Kernel K
    open ForKernel K
    open Provability Pr renaming (Prov to ⊢)
    open ProvabilityOps Op
    open QuoteSubst QS
    open DecodeImp DI

    diag : (Code → Code) → Code
    diag f = s where
      rep : Σ Code₁ (λ u₁ → ∀ γ → inst u₁ γ ≃K f γ)
      rep = representable f
      u : Code₁
      u = proj₁ rep
      repr : ∀ γ → inst u γ ≃K f γ
      repr = proj₂ rep
      se : Σ Code (λ s₁ → s₁ ≃K inst u s₁)
      se = self u
      s : Code
      s = proj₁ se
      _ = proj₂ se -- s ≃K inst u s

    diag-eq : ∀ f → diag f ≃K f (diag f)
    diag-eq f =
      let
        rep : Σ Code₁ (λ u₁ → ∀ γ → inst u₁ γ ≃K f γ)
        rep = representable f
        u : Code₁
        u = proj₁ rep
        repr : ∀ γ → inst u γ ≃K f γ
        repr = proj₂ rep
        se : Σ Code (λ s₁ → s₁ ≃K inst u s₁)
        se = self u
        s : Code
        s = proj₁ se
        selfeq : s ≃K inst u s
        selfeq = proj₂ se
      in
      trans selfeq (repr s)

    diag→ : ∀ f → ⊢ (Imp (diag f) (f (diag f)))
    diag→ f = from-decode≃→imp (diag-eq f)

    →diag : ∀ f → ⊢ (Imp (f (diag f)) (diag f))
    →diag f = from-decode≃→imp (sym (diag-eq f))

-- ----------------------------------------------------------------------------
-- Code-level diagonalization (Body/Flow form).
--
-- This packs the classic diagonal witness over code functions as a separate
-- assumption, useful for boundary/flow transport without committing to any
-- proof-theoretic diagonalization schema.

record Diagonal {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                (K : Kernel Sig Q)
                : Set (lsuc ℓ) where
  field
    diagonal
      : (F : Kernel.Code K → Kernel.Code K)
      → Σ (Kernel.Code K) (λ γ → Kernel.Body K (F γ) ≡ Kernel.Body K γ)

Diagonal-Body∂-eq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (D   : Diagonal K)
    (F   : Kernel.Code K → Kernel.Code K)
  → Σ (Kernel.Code K) (λ γ →
       Kernel.Body∂ K (Kernel.decode K (F γ)) ≡
       Kernel.Body∂ K (Kernel.decode K γ))
Diagonal-Body∂-eq K D F with Diagonal.diagonal D F
... | γ , eq =
  let step₁ = Kernel.body-decode K (F γ)
      step₂ = Kernel.body-decode K γ
      bodyEq = trans (sym step₁) (trans (cong (Kernel.decode K) eq) step₂)
  in γ , bodyEq

Diagonal-FlowStep-eq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (D   : Diagonal K)
    (F   : Kernel.Code K → Kernel.Code K)
  → Σ (Kernel.Code K) (λ γ →
       GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
         (Kernel.Body∂ K (Kernel.decode K (F γ)))
       ≡ GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
         (Kernel.Body∂ K (Kernel.decode K γ)))
Diagonal-FlowStep-eq K D F with Diagonal.diagonal D F
... | γ , eq =
  let guardEq = cong (Kernel.Guard K) eq
      decEq = cong (Kernel.decode K) guardEq
      lhs   = Code.decode-FlowCode-eq K (F γ)
      rhs   = Code.decode-FlowCode-eq K γ
      flowEq = trans (sym lhs) (trans decEq rhs)
  in γ , flowEq

open import LogOS.Computation.Core as CompCore
open import LogOS.Syntax.Prop using (_↔_; ¬_; to; from; ⊥)

record HaltingModel {ℓ}
                    {Sig : LogOSSignature ℓ}
                    {Q   : QAdapter ℓ}
                    (K  : Kernel Sig Q)
                    : Set (lsuc ℓ) where
  open Kernel K
  field
    Comp : CompCore.Computation Code

record DiagonalAgainstDecidable {ℓCode ℓTruth : Level}
                                (Code   : Set ℓCode)
                                (TruthK : Code → Set ℓTruth)
                                : Set (lsuc (ℓCode ⊔ ℓTruth)) where
  field
    liarForDecider
      : (P : Code → Set ℓTruth)
      → (decP : ∀ γ → P γ ⊎ ¬ P γ)
      → Σ Code (λ γ → (TruthK γ) ↔ (¬ (P γ)))

record HaltingDiagonal {ℓ}
                       {Sig : LogOSSignature ℓ}
                       {Q   : QAdapter ℓ}
                       (K  : Kernel Sig Q)
                       (HM : HaltingModel K)
                       : Set (lsuc ℓ) where
  open Kernel K
  open HaltingModel HM
  open CompCore.Computation Comp renaming (Halts to HaltsC)
  field
    diagonal : DiagonalAgainstDecidable Code HaltsC
  open DiagonalAgainstDecidable diagonal public

record TruthDiagonal {ℓ}
                     {Sig : LogOSSignature ℓ}
                     {Q   : QAdapter ℓ}
                     (K  : Kernel Sig Q)
                     (TruthK : Kernel.Code K → Set ℓ)
                     : Set (lsuc ℓ) where
  open Kernel K
  field
    diagonal : DiagonalAgainstDecidable Code TruthK
  open DiagonalAgainstDecidable diagonal public

-- Code-generic form:
-- this decouples diagonalisation from any particular kernel structure, so it
-- can be instantiated equally for `Kernel` and `GradedKernel` code languages.

record TruthDiagonalC {ℓCode ℓTruth : Level}
                      (Code   : Set ℓCode)
                      (TruthK : Code → Set ℓTruth)
                      : Set (lsuc (ℓCode ⊔ ℓTruth)) where
  field
    diagonal : DiagonalAgainstDecidable Code TruthK
  open DiagonalAgainstDecidable diagonal public

TruthDiagonal→TruthDiagonalC
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ}
    {Q   : QAdapter ℓ}
    {K   : Kernel Sig Q}
    (TruthK : Kernel.Code K → Set ℓ)
  → TruthDiagonal K TruthK
  → TruthDiagonalC (Kernel.Code K) TruthK
TruthDiagonal→TruthDiagonalC TruthK TD =
  record { diagonal = TruthDiagonal.diagonal TD }

-- Diagonal witness: for any truth predicate with a diagonal-against-decidable
-- principle, there exists an explicit code where the predicate fails.

liar-witnessC
  : ∀ {ℓCode ℓTruth : Level}
    {Code   : Set ℓCode}
    {TruthK : Code → Set ℓTruth}
  → TruthDiagonalC Code TruthK
  → Σ Code (λ γ → ¬ TruthK γ)
liar-witnessC TD =
  let
    liar = TruthDiagonalC.liarForDecider TD (λ _ → ⊤) (λ _ → inj₁ tt)
    γ    = proj₁ liar
    eqv  = proj₂ liar
  in
  (γ , λ t → to eqv t tt)

no-totalC
  : ∀ {ℓCode ℓTruth : Level}
    {Code   : Set ℓCode}
    {TruthK : Code → Set ℓTruth}
  → TruthDiagonalC Code TruthK
  → ¬ (∀ γ → TruthK γ)
no-totalC TD all =
  let w = liar-witnessC TD
  in (proj₂ w) (all (proj₁ w))

liar-witness
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ}
    {Q   : QAdapter ℓ}
    {K   : Kernel Sig Q}
    {TruthK : Kernel.Code K → Set ℓ}
  → TruthDiagonal K TruthK
  → Σ (Kernel.Code K) (λ γ → ¬ TruthK γ)
liar-witness {TruthK = TruthK} TD =
  liar-witnessC (TruthDiagonal→TruthDiagonalC TruthK TD)

no-total
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ}
    {Q   : QAdapter ℓ}
    {K   : Kernel Sig Q}
    {TruthK : Kernel.Code K → Set ℓ}
  → TruthDiagonal K TruthK
  → ¬ (∀ γ → TruthK γ)
no-total TD all =
  let w = liar-witness TD
  in (proj₂ w) (all (proj₁ w))

noOmniscientDeciderC
  : ∀ {ℓCode ℓT : Level}
    (Code   : Set ℓCode)
    (TruthK : Code → Set ℓT)
  → TruthDiagonalC Code TruthK
  → ¬ (∀ γ → TruthK γ ⊎ ¬ TruthK γ)
noOmniscientDeciderC Code TruthK TD dec =
  go (dec γ)
  where
    open _↔_
    open TruthDiagonalC TD

    liar = liarForDecider TruthK dec
    γ    = proj₁ liar
    eqv  = proj₂ liar

    go : TruthK γ ⊎ ¬ TruthK γ → ⊥
    go (inj₁ t)  = to eqv t t
    go (inj₂ nt) = nt (from eqv nt)
