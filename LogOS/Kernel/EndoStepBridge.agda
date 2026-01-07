{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.EndoStepBridge where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel.LogicKernel
import LogOS.Kernel.LogicKernel.Endo as LKEndo

-- Generic bridge: reuse the canonical `LogicKernel.Endo.ClosureStep` API and its
-- proofs, then wrap it back into the target kernel-like endomap DSL.
--
-- Intended use: ungraded and graded kernels instantiate this module with
-- `asLogicKernel` and `toLKEndo/fromLKEndo` conversions.

module With
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (Obj : Set (lsuc (lsuc ℓ)))
  (asLogicKernel : Obj → LogicKernel Sig Q)
  (Endo : Obj → Set (lsuc ℓ))
  (_≤₂_ : (K : Obj) → Endo K → Endo K → Set ℓ)
  (idEndo : (K : Obj) → Endo K)
  (Flow-Endo : (K : Obj) → Endo K)
  (toLKEndo : ∀ {K : Obj} → Endo K → LKEndo.Endo (asLogicKernel K))
  (fromLKEndo : ∀ {K : Obj} → LKEndo.Endo (asLogicKernel K) → Endo K)
  (toLK≤₂ : ∀ {K : Obj} {f g : Endo K}
         → _≤₂_ K f g
         → LKEndo._≤₂_ (asLogicKernel K) (toLKEndo f) (toLKEndo g))
  (fromLK≤₂ : ∀ {K : Obj} {f g : Endo K}
           → LKEndo._≤₂_ (asLogicKernel K) (toLKEndo f) (toLKEndo g)
           → _≤₂_ K f g)
  (idFn : ∀ {K : Obj}
        → (c : ConPoset.Con (BulkBoundary.bnd (LogicKernel.BB (asLogicKernel K))))
        → LKEndo.Endo.fn (toLKEndo (idEndo K)) c ≡ LKEndo.Endo.fn (LKEndo.idEndo (asLogicKernel K)) c)
  (flowFn : ∀ {K : Obj}
          → (c : ConPoset.Con (BulkBoundary.bnd (LogicKernel.BB (asLogicKernel K))))
          → LKEndo.Endo.fn (toLKEndo (Flow-Endo K)) c ≡ LKEndo.Endo.fn (LKEndo.Flow-Endo (asLogicKernel K)) c)
  (toLK∘fromLK-fn : ∀ {K : Obj}
                 → (e : LKEndo.Endo (asLogicKernel K))
                 → (c : ConPoset.Con (BulkBoundary.bnd (LogicKernel.BB (asLogicKernel K))))
                 → LKEndo.Endo.fn (toLKEndo (fromLKEndo e)) c ≡ LKEndo.Endo.fn e c)
  where

  record ClosureStep (K : Obj) : Set (lsuc ℓ) where
    field
      endo   : Endo K
      infl   : _≤₂_ K (idEndo K) endo
      leFlow : _≤₂_ K endo (Flow-Endo K)

  mkClosureStep
    : ∀ {K : Obj}
    → (f : Endo K)
    → _≤₂_ K (idEndo K) f
    → _≤₂_ K f (Flow-Endo K)
    → ClosureStep K
  mkClosureStep f infl leFlow = record { endo = f ; infl = infl ; leFlow = leFlow }

  toLKStep : ∀ {K : Obj} → ClosureStep K → LKEndo.ClosureStep (asLogicKernel K)
  toLKStep {K = K} s =
    let open LogicKernel (asLogicKernel K)
        CP = BulkBoundary.bnd BB
        infl₀ = toLK≤₂ (ClosureStep.infl s)
        leFlow₀ = toLK≤₂ (ClosureStep.leFlow s)
        infl' : LKEndo._≤₂_ (asLogicKernel K) (LKEndo.idEndo (asLogicKernel K)) (toLKEndo (ClosureStep.endo s))
        infl' c =
          subst
            (λ x → ConPoset._⊑_ CP x (LKEndo.Endo.fn (toLKEndo (ClosureStep.endo s)) c))
            (idFn c)
            (infl₀ c)
        leFlow' : LKEndo._≤₂_ (asLogicKernel K) (toLKEndo (ClosureStep.endo s)) (LKEndo.Flow-Endo (asLogicKernel K))
        leFlow' c =
          subst
            (λ y → ConPoset._⊑_ CP (LKEndo.Endo.fn (toLKEndo (ClosureStep.endo s)) c) y)
            (flowFn c)
            (leFlow₀ c)
    in LKEndo.mkClosureStep (toLKEndo (ClosureStep.endo s)) infl' leFlow'

  fromLKStep : ∀ {K : Obj} → LKEndo.ClosureStep (asLogicKernel K) → ClosureStep K
  fromLKStep {K = K} sk =
    let open LogicKernel (asLogicKernel K)
        CP = BulkBoundary.bnd BB
        endoLK = LKEndo.ClosureStep.endo sk
        endoK = fromLKEndo endoLK
        endoFnEq : ∀ c → LKEndo.Endo.fn (toLKEndo endoK) c ≡ LKEndo.Endo.fn endoLK c
        endoFnEq c = toLK∘fromLK-fn endoLK c
        inflLK = LKEndo.ClosureStep.infl sk
        leFlowLK = LKEndo.ClosureStep.leFlow sk
        infl' : LKEndo._≤₂_ (asLogicKernel K) (toLKEndo (idEndo K)) (toLKEndo endoK)
        infl' c =
          let infl₁ : ConPoset._⊑_ CP
                        (LKEndo.Endo.fn (LKEndo.idEndo (asLogicKernel K)) c)
                        (LKEndo.Endo.fn (toLKEndo endoK) c)
              infl₁ =
                subst
                  (λ y → ConPoset._⊑_ CP (LKEndo.Endo.fn (LKEndo.idEndo (asLogicKernel K)) c) y)
                  (sym (endoFnEq c))
                  (inflLK c)
          in
          subst
            (λ x → ConPoset._⊑_ CP x (LKEndo.Endo.fn (toLKEndo endoK) c))
            (sym (idFn c))
            infl₁
        leFlow' : LKEndo._≤₂_ (asLogicKernel K) (toLKEndo endoK) (toLKEndo (Flow-Endo K))
        leFlow' c =
          let leFlow₁ : ConPoset._⊑_ CP
                         (LKEndo.Endo.fn (toLKEndo endoK) c)
                         (LKEndo.Endo.fn (LKEndo.Flow-Endo (asLogicKernel K)) c)
              leFlow₁ =
                subst
                  (λ x → ConPoset._⊑_ CP x (LKEndo.Endo.fn (LKEndo.Flow-Endo (asLogicKernel K)) c))
                  (sym (endoFnEq c))
                  (leFlowLK c)
          in
          subst
            (λ y → ConPoset._⊑_ CP (LKEndo.Endo.fn (toLKEndo endoK) c) y)
            (sym (flowFn c))
            leFlow₁
    in mkClosureStep endoK (fromLK≤₂ infl') (fromLK≤₂ leFlow')

  Flow-closeStep : (K : Obj) → ClosureStep K → ClosureStep K
  Flow-closeStep K s =
    fromLKStep (LKEndo.Flow-closeStep (asLogicKernel K) (toLKStep s))

  _∘Step_ : ∀ {K : Obj} → ClosureStep K → ClosureStep K → ClosureStep K
  _∘Step_ {K = K} s₂ s₁ =
    fromLKStep (LKEndo._∘Step_ {K = asLogicKernel K} (toLKStep s₂) (toLKStep s₁))

  -- Left-to-right composition (operand order matches execution order).
  _thenStep_ : ∀ {K : Obj} → ClosureStep K → ClosureStep K → ClosureStep K
  _thenStep_ s₁ s₂ = s₂ ∘Step s₁

  infixr 9 _∘Step_
  infixl 9 _thenStep_
