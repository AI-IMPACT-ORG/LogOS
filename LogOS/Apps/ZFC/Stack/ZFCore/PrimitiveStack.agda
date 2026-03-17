{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ZFCore.PrimitiveStack where

-- Canonical ZF primitive constructor stack (stack-first; no laws).
--
-- Policy note:
-- this module depends only on the signature fragments needed to present the
-- primitive constructors as Views into the set boundary preorder.

open import LogOS.Prelude
open import LogOS.LT.View using (View)
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Stack using (Stack; stackKernel; programKernel; opKernel)

open import LogOS.Apps.ZFC.Stack.ZFCore.Context using (SetContext)
import LogOS.Apps.ZFC.Stack.ZFCore.Signature as Signature
open Signature using (ZFSignatureCore; ZFSignaturePowerset; ZFSignatureOmega)

module Primitive {ℓ : Level}
  (C : SetContext {ℓ})
  (CoreSig : ZFSignatureCore C)
  (PowSig : ZFSignaturePowerset C)
  (OmegaSig : ZFSignatureOmega C)
  where

  open SetContext C
  open ZFSignatureCore CoreSig
  open ZFSignaturePowerset PowSig
  open ZFSignatureOmega OmegaSig

  module D = Signature.DerivedCore CoreSig
  open D using (ZeroV; SuccV) public

  data PrimOp : Set ℓ where
    emptyOp powersetOp unionOp pairOp zeroOp succOp omegaOp : PrimOp

  PrimCode : PrimOp → Set ℓ
  PrimCode emptyOp = ⊤ {ℓ}
  PrimCode powersetOp = SetU
  PrimCode unionOp = SetU
  PrimCode pairOp = SetU × SetU
  PrimCode zeroOp = ⊤ {ℓ}
  PrimCode succOp = SetU
  PrimCode omegaOp = ⊤ {ℓ}

  primView : (o : PrimOp) → View (PrimCode o) SetBnd
  primView emptyOp = EmptyV
  primView powersetOp = PowersetV
  primView unionOp = UnionV
  primView pairOp = PairV
  primView zeroOp = ZeroV
  primView succOp = SuccV
  primView omegaOp = OmegaV

  primStack : Stack {ℓ} {ℓ} {ℓ} {ℓ}
  primStack =
    record
      { bnd = SetBnd
      ; Op = PrimOp
      ; Code = PrimCode
      ; op = primView
      }

  PrimK : Kernel ℓ ℓ (ℓ ⊔ ℓ)
  PrimK = stackKernel primStack

  PrimProgramK : Kernel ℓ ℓ (ℓ ⊔ ℓ ⊔ ℓ)
  PrimProgramK = programKernel primStack

  EmptyK    : Kernel ℓ ℓ ℓ; EmptyK    = opKernel primStack emptyOp
  PairK     : Kernel ℓ ℓ ℓ; PairK     = opKernel primStack pairOp
  UnionK    : Kernel ℓ ℓ ℓ; UnionK    = opKernel primStack unionOp
  PowersetK : Kernel ℓ ℓ ℓ; PowersetK = opKernel primStack powersetOp
  ZeroK     : Kernel ℓ ℓ ℓ; ZeroK     = opKernel primStack zeroOp
  SuccK     : Kernel ℓ ℓ ℓ; SuccK     = opKernel primStack succOp
  OmegaK    : Kernel ℓ ℓ ℓ; OmegaK    = opKernel primStack omegaOp
