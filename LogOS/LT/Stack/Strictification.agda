{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Stack.Strictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Explicit strictification surface for stacks.
--
-- The canonical stack core is refinement-first. This module isolates the
-- opt-in strict decode-coherence view of stack morphisms and same-boundary
-- stack maps.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; MonoMap; idMonoMap; ≡→≈)
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Strictification using (KernelHom≡)
import LogOS.LT.Hom.Strictification as Hom
import LogOS.LT.Stack.Core as Core

record StackMap≡
  {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
  (S : Core.Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  (K' : Kernel ℓB ℓRel ℓCode')
  : Set (lsuc ℓB ⊔ lsuc ℓRel ⊔ ℓOp ⊔ ℓCode ⊔ ℓCode' ⊔ ℓB) where
  field
    map∂ : Con (Core.bnd S) → Con (Kernel.bnd K')
    map∂-mono : MonoMap (Core.bnd S) (Kernel.bnd K') map∂

    mapCode : ∀ o → Core.Code S o → Kernel.Code K'

    decode-mapCode
      : ∀ o γ
      → Kernel.decode K' (mapCode o γ) ≡ map∂ (μ (Core.op S o) γ)

open StackMap≡ public

toKernelHom≡
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Core.Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}} {K' : Kernel ℓB ℓRel ℓCode'}
  → StackMap≡ S K'
  → KernelHom≡ (Core.stackKernel S) K'
toKernelHom≡ {S = S} {K' = K'} h =
  Hom.mkKernelHom≡Parts
    (record
      { map∂ = map∂ h
      ; map∂-mono = map∂-mono h
      })
    (record
      { mapCode = λ oc → mapCode h (Core.opIdx oc) (Core.code oc)
      ; decode-mapCode = λ oc → decode-mapCode h (Core.opIdx oc) (Core.code oc)
      })

fromKernelHom≡
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Core.Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}} {K' : Kernel ℓB ℓRel ℓCode'}
  → KernelHom≡ (Core.stackKernel S) K'
  → StackMap≡ S K'
fromKernelHom≡ {S = S} {K' = K'} h =
  record
    { map∂ = Hom.map∂ h
    ; map∂-mono = Hom.map∂-mono h
    ; mapCode = λ o γ → Hom.mapCode h (Core.mkStackCode o γ)
    ; decode-mapCode = λ o γ → Hom.decode-mapCode≡ h (Core.mkStackCode o γ)
    }

record SameBoundaryStackMap≡
  {ℓB ℓRel ℓSrcOp ℓSrcCode ℓTgtOp ℓTgtCode : Level}
  (B : ConPreorder ℓB ℓRel)
  : Set (lsuc (ℓB ⊔ ℓRel ⊔ ℓSrcOp ⊔ ℓSrcCode ⊔ ℓTgtOp ⊔ ℓTgtCode) ⊔ ℓB) where
  field
    SourceOp : Set ℓSrcOp
    TargetOp : Set ℓTgtOp

    SourceCode : SourceOp → Set ℓSrcCode
    TargetCode : TargetOp → Set ℓTgtCode

    sourceView : (o : SourceOp) → View (SourceCode o) B
    targetView : (o : TargetOp) → View (TargetCode o) B

    mapOp : SourceOp → TargetOp
    mapCodeAt : (o : SourceOp) → SourceCode o → TargetCode (mapOp o)

    mapCodeAt-preserves
      : ∀ o γ
      → μ (targetView (mapOp o)) (mapCodeAt o γ) ≡ μ (sourceView o) γ

  Source : Core.Stack {ℓB} {ℓRel} {ℓSrcOp} {ℓSrcCode}
  Source =
    record
      { bnd = B
      ; Op = SourceOp
      ; Code = SourceCode
      ; op = sourceView
      }

  Target : Core.Stack {ℓB} {ℓRel} {ℓTgtOp} {ℓTgtCode}
  Target =
    record
      { bnd = B
      ; Op = TargetOp
      ; Code = TargetCode
      ; op = targetView
      }

  mapStackCode : Core.StackCode Source → Core.StackCode Target
  mapStackCode oc = Core.mkStackCode (mapOp (Core.opIdx oc)) (mapCodeAt (Core.opIdx oc) (Core.code oc))

  opKernelHom≡
    : (o : SourceOp)
    → KernelHom≡ (Core.opKernel Source o) (Core.opKernel Target (mapOp o))
  opKernelHom≡ o =
    Hom.mkKernelHom≡Parts
      (record
        { map∂ = λ c → c
        ; map∂-mono = idMonoMap {CP = B}
        })
      (record
        { mapCode = mapCodeAt o
        ; decode-mapCode = λ γ → mapCodeAt-preserves o γ
        })

  stackKernelHom≡ : KernelHom≡ (Core.stackKernel Source) (Core.stackKernel Target)
  stackKernelHom≡ =
    Hom.mkKernelHom≡Parts
      (record
        { map∂ = λ c → c
        ; map∂-mono = idMonoMap {CP = B}
        })
      (record
        { mapCode = mapStackCode
        ; decode-mapCode = λ oc → mapCodeAt-preserves (Core.opIdx oc) (Core.code oc)
        })

homFromMap
  : ∀ {ℓB ℓRel ℓSrcOp ℓSrcCode ℓTgtOp ℓTgtCode : Level} {B : ConPreorder ℓB ℓRel}
  → SameBoundaryStackMap≡
      {ℓSrcOp = ℓSrcOp}
      {ℓSrcCode = ℓSrcCode}
      {ℓTgtOp = ℓTgtOp}
      {ℓTgtCode = ℓTgtCode}
      B
  → Core.SameBoundaryStackMap
      {ℓSrcOp = ℓSrcOp}
      {ℓSrcCode = ℓSrcCode}
      {ℓTgtOp = ℓTgtOp}
      {ℓTgtCode = ℓTgtCode}
      B
homFromMap {B = B} M =
  let open SameBoundaryStackMap≡ M in
  record
    { SourceOp = SourceOp
    ; TargetOp = TargetOp
    ; SourceCode = SourceCode
    ; TargetCode = TargetCode
    ; sourceView = sourceView
    ; targetView = targetView
    ; mapOp = mapOp
    ; mapCodeAt = mapCodeAt
    ; mapCodeAt-preserves = λ o γ → ≡→≈ {CP = B} (mapCodeAt-preserves o γ)
    }
