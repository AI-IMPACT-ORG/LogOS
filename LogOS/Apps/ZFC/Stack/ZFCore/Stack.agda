{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ZFCore.Stack where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Kernel using (Kernel)

open import LogOS.Apps.ZFC.Stack.ZFCore.Context using (SetContext)
import LogOS.Apps.ZFC.Stack.ZFCore.Signature as Signature
open Signature using (ZFSignature)
open import LogOS.Apps.ZFC.Stack.ZFCore.Laws using (ZFLaws; succ-spec-from-core)
open import LogOS.Apps.ZFC.Stack.ZFCore.Pointwise using
  ( ZFMembershipLawsAt
  ; ZFLawsPointwise
  ; toPointwiseLaws
  )
import LogOS.Apps.ZFC.Stack.ZFCore.PrimitiveStack as PrimitiveStack

record ZFStack {ℓ : Level} : Set (lsuc ℓ) where
  field
    ctx  : SetContext {ℓ}
    sig  : ZFSignature ctx
    laws : ZFLaws ctx sig

  open SetContext ctx public
  open ZFSignature sig public
  open ZFLaws laws public

  -- Pointwise view of the constructor laws (per membership probe `z`).
  pointwiseLaws : ZFLawsPointwise ctx sig
  pointwiseLaws = toPointwiseLaws laws

  membershipLawsAt : (z : SetU) → ZFMembershipLawsAt ctx sig z
  membershipLawsAt = ZFLawsPointwise.membershipLawsAt pointwiseLaws

  -- ------------------------------------------------------------------------
  -- Derived constructions (compose Views; no new axioms).

  module SigD = Signature.Derived sig

  ZeroV : View (⊤ {ℓ}) SetBnd
  ZeroV = SigD.ZeroV

  singletonV : View SetU SetBnd
  singletonV = SigD.singletonV

  union₂V : View (SetU × SetU) SetBnd
  union₂V = SigD.union₂V

  SuccV : View SetU SetBnd
  SuccV = SigD.SuccV

  -- Spec of the derived 0 constructor.
  zero-spec : ∀ z → ¬ (z ∈ μ ZeroV tt)
  zero-spec = empty-spec

  -- Spec of the derived successor constructor.
  succ-spec
    : ∀ x z
    → (z ∈ μ SuccV x) ↔ ((z ∈ x) ⊎ (z ≈ x))
  succ-spec x z = succ-spec-from-core (ZFSignature.coreSig sig) (ZFLaws.coreLaws laws) x z

  -- ------------------------------------------------------------------------
  -- Kernel packaging: treat the primitive ZF constructors as a `LogOS.LT.Stack`
  -- (a family of Views into the shared set boundary).

  module Prim =
    PrimitiveStack.Primitive ctx (ZFSignature.coreSig sig) (ZFSignature.powSig sig) (ZFSignature.omegaSig sig)

  open Prim public using
    ( PrimOp
    ; PrimCode
    ; primView
    ; primStack
    ; PrimK
    ; PrimProgramK
    ; EmptyK
    ; PairK
    ; UnionK
    ; PowersetK
    ; ZeroK
    ; SuccK
    ; OmegaK
    )

  -- The boundary kernel (identity view).
  SetK : Kernel ℓ ℓ ℓ
  SetK = record { bnd = SetBnd ; Code = SetU ; decode = λ x → x }
