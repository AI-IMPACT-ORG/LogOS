{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Stack.Laws where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Refinement-facing stack laws.
--
-- Definitional/bookkeeping equalities live in `LogOS.LT.Stack.Definitional`.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (_≈_; ≈-refl)
open import LogOS.LT.Coherence using (CohMode; CohRel)
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Core using (KernelHomLike)
import LogOS.LT.Hom.Core as Hom
open import LogOS.LT.Stack.Core using
  ( Stack
  ; StackCode
  ; StackMapLike
  ; SameBoundaryStackMap
  ; SameBoundaryStackMapLike
  ; Code
  ; Op
  ; bnd
  ; code
  ; decode-mapCode
  ; fromKernelHomLike
  ; injOp
  ; mapCode
  ; opIdx
  ; opKernel
  ; stackKernel
  ; toKernelHomLike
  )
open import LogOS.LT.Stack.Program using (Program; decodeProgram; SameBoundaryProgramMap)

injOp-decode≈
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
    (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
    (o : Op S)
    (γ : Code S o)
  → _≈_ (bnd S)
      (Kernel.decode (stackKernel S) (Hom.mapCode (injOp S o) γ))
      (Kernel.decode (opKernel S o) γ)
injOp-decode≈ S o γ = ≈-refl (bnd S) (Kernel.decode (opKernel S o) γ)

mapStackCode-preserves
  : ∀ {m : CohMode}
    {ℓB ℓRel ℓSrcOp ℓSrcCode ℓTgtOp ℓTgtCode : Level}
    {B : LogOS.LT.ConPreorder.ConPreorder ℓB ℓRel}
    (M : SameBoundaryStackMapLike m
           {ℓSrcOp = ℓSrcOp}
           {ℓSrcCode = ℓSrcCode}
           {ℓTgtOp = ℓTgtOp}
           {ℓTgtCode = ℓTgtCode}
           B)
    (oc : StackCode (SameBoundaryStackMapLike.Source M))
  → CohRel m B
      (Kernel.decode
        (opKernel
          (SameBoundaryStackMapLike.Target M)
          (SameBoundaryStackMapLike.mapOp M (opIdx oc)))
        (SameBoundaryStackMapLike.mapCodeAt M (opIdx oc) (code oc)))
      (Kernel.decode
        (opKernel (SameBoundaryStackMapLike.Source M) (opIdx oc))
        (code oc))
mapStackCode-preserves M oc =
  SameBoundaryStackMapLike.mapCodeAt-preserves M (opIdx oc) (code oc)

toKernelHomLike-fromKernelHomLike≈
  : ∀ {m : CohMode} {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    {K' : Kernel ℓB ℓRel ℓCode'}
    (h : KernelHomLike m (stackKernel S) K')
    (o : Op S)
    (γ : Code S o)
  → CohRel m (Kernel.bnd K')
      (Kernel.decode K' (mapCode (fromKernelHomLike h) o γ))
      (Hom.map∂ h (Kernel.decode (opKernel S o) γ))
toKernelHomLike-fromKernelHomLike≈ h o γ =
  decode-mapCode (fromKernelHomLike h) o γ

fromKernelHomLike-toKernelHomLike≈
  : ∀ {m : CohMode} {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    {K' : Kernel ℓB ℓRel ℓCode'}
    (h : StackMapLike {m = m} S K')
    (oc : StackCode S)
  → CohRel m (Kernel.bnd K')
      (Kernel.decode K' (Hom.mapCode (toKernelHomLike h) oc))
      (Hom.map∂ (toKernelHomLike h) (Kernel.decode (stackKernel S) oc))
fromKernelHomLike-toKernelHomLike≈ h oc =
  Hom.decode-mapCode (toKernelHomLike h) oc

evalBoundaryExpr-respects-≈
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
    {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    (F : LogOS.LT.Stack.Program.BoundaryEndo S)
    {x y : LogOS.LT.ConPreorder.Con (bnd S)}
  → _≈_ (bnd S) x y
  → _≈_ (bnd S)
      (LogOS.LT.Stack.Program.evalBoundaryExpr (LogOS.LT.Stack.Program.expr F) x)
      (LogOS.LT.Stack.Program.evalBoundaryExpr (LogOS.LT.Stack.Program.expr F) y)
evalBoundaryExpr-respects-≈ F = LogOS.LT.Stack.Program.preserves-≈ F

primProgram-decode≈
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
    (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
    (oc : StackCode S)
  → _≈_ (bnd S)
      (decodeProgram (LogOS.LT.Stack.Program.primProgram S oc))
      (Kernel.decode (stackKernel S) oc)
primProgram-decode≈ S oc = ≈-refl (bnd S) (Kernel.decode (stackKernel S) oc)

decode-mapProgram≈
  : ∀ {ℓB ℓRel ℓSrcOp ℓSrcCode ℓTgtOp ℓTgtCode : Level}
    {B : LogOS.LT.ConPreorder.ConPreorder ℓB ℓRel}
    {M₀ : SameBoundaryStackMap
            {ℓSrcOp = ℓSrcOp}
            {ℓSrcCode = ℓSrcCode}
            {ℓTgtOp = ℓTgtOp}
            {ℓTgtCode = ℓTgtCode}
            B}
    (M : SameBoundaryProgramMap M₀)
    (p : Program (SameBoundaryStackMapLike.Source M₀))
  → _≈_ B
      (decodeProgram (SameBoundaryProgramMap.mapProgram M p))
      (decodeProgram p)
decode-mapProgram≈ M = SameBoundaryProgramMap.decode-mapProgram M
