{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Stack.Core where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Stacks of transformers (Views) over a shared boundary.
--
-- A stack is an indexed family of Views into one boundary preorder.
-- Crucially, the stack itself can be packaged as a single kernel by tagging
-- codes with their operation index.
--
-- This makes “a stack of transformers is a transformer” precise, without adding
-- any axioms: it is bookkeeping on top of `View` and `Kernel`.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; Con
  ; _≈_
  ; MonoMap
  ; idMonoMap
  ; ≈-refl
  ; ≡→≈
  )
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.View.Family using (IndexedViewFamily; FamilyCode; bundleView; bundleKernel)
open import LogOS.LT.Kernel using (Kernel; kernelFromView)
open import LogOS.LT.Coherence using (CohMode; approx; under; CohRel; CohLevel)
open import LogOS.LT.Hom.Core using (KernelHom; KernelHomLike)
import LogOS.LT.View.Family as Family
import LogOS.LT.Hom.Core as Hom

record Stack {ℓB ℓRel ℓOp ℓCode : Level} : Set (lsuc (ℓB ⊔ ℓRel ⊔ ℓOp ⊔ ℓCode)) where
  field
    bnd  : ConPreorder ℓB ℓRel
    Op   : Set ℓOp
    Code : Op → Set ℓCode
    op   : (o : Op) → View (Code o) bnd

open Stack public
-- A stack is an indexed family of Views; bundling is the canonical tagged-code
-- construction for the whole stack.
stackAsFamily
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
  → (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  → IndexedViewFamily {ℓB = ℓB} {ℓRel = ℓRel} {ℓI = ℓOp} {ℓCode = ℓCode} (bnd S)
stackAsFamily S =
  record
    { Ix = Op S
    ; Code = Code S
    ; view = op S
    }

-- The tagged code space of the whole stack: choose an operation + its code.
StackCode : ∀ {ℓB ℓRel ℓOp ℓCode : Level} → Stack {ℓB} {ℓRel} {ℓOp} {ℓCode} → Set (ℓOp ⊔ ℓCode)
StackCode S = FamilyCode (stackAsFamily S)

mkStackCode
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level} {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
  → (o : Op S)
  → Code S o
  → StackCode S
mkStackCode o γ = Family.mkFamilyCodeR o γ

opIdx
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level} {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
  → StackCode S
  → Op S
opIdx = Family.ix

code
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level} {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
  → (oc : StackCode S)
  → Code S (opIdx oc)
code = Family.code

stackView
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
  → (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  → View (StackCode S) (bnd S)
stackView S =
  record
    { μ = λ oc → μ (op S (opIdx oc)) (code oc) }

-- Each operation is a kernel (with the shared boundary).
opKernel
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
  → (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  → Op S
  → Kernel ℓB ℓRel ℓCode
opKernel S o = kernelFromView (op S o)

-- The whole stack is a kernel (tagging codes by their operation index).
stackKernel : ∀ {ℓB ℓRel ℓOp ℓCode : Level} → Stack {ℓB} {ℓRel} {ℓOp} {ℓCode} → Kernel ℓB ℓRel (ℓOp ⊔ ℓCode)
stackKernel S = kernelFromView (stackView S)

-- Canonical injections: each operation embeds into the whole stack kernel.
injOp
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
  → (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  → (o : Op S)
  → KernelHom (opKernel S o) (stackKernel S)
injOp S o =
  Hom.mkKernelHomParts
    (record
      { map∂ = λ c → c
      ; map∂-mono = idMonoMap {CP = bnd S}
      })
    (record
      { mapCode = λ γ → mkStackCode o γ
      ; decode-mapCode = λ γ → ≈-refl (bnd S) (μ (op S o) γ)
      })

-- A morphism out of a stack kernel is exactly:
-- - one boundary translation, and
-- - a code translation per operation,
-- with a single ≈-coherence per operation.
record StackMapLike
  {m : CohMode}
  {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
  (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  (K' : Kernel ℓB ℓRel ℓCode')
  : Set (lsuc ℓB ⊔ lsuc ℓRel ⊔ ℓOp ⊔ ℓCode ⊔ ℓCode' ⊔ CohLevel m ℓB ℓRel) where
  field
    map∂      : Con (bnd S) → Con (Kernel.bnd K')
    map∂-mono : MonoMap (bnd S) (Kernel.bnd K') map∂

    mapCode : ∀ o → Code S o → Kernel.Code K'

    decode-mapCode
      : ∀ o γ
      → CohRel m (Kernel.bnd K') (Kernel.decode K' (mapCode o γ)) (map∂ (μ (op S o) γ))

StackMap
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
  → Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}
  → Kernel ℓB ℓRel ℓCode'
  → Set _
StackMap = StackMapLike {m = approx}

StackMap⊑
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
  → Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}
  → Kernel ℓB ℓRel ℓCode'
  → Set _
StackMap⊑ = StackMapLike {m = under}

open StackMapLike public

toKernelHomLike
  : ∀ {m : CohMode} {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}} {K' : Kernel ℓB ℓRel ℓCode'}
  → StackMapLike {m = m} S K'
  → KernelHomLike m (stackKernel S) K'
toKernelHomLike {S = S} {K' = K'} h =
  Hom.mkKernelHomParts
    (record
      { map∂ = map∂ h
      ; map∂-mono = map∂-mono h
      })
    (record
      { mapCode = λ oc → mapCode h (opIdx oc) (code oc)
      ; decode-mapCode = λ oc → decode-mapCode h (opIdx oc) (code oc)
      })

toKernelHom
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}} {K' : Kernel ℓB ℓRel ℓCode'}
  → StackMap S K'
  → KernelHom (stackKernel S) K'
toKernelHom = toKernelHomLike {m = approx}

fromKernelHomLike
  : ∀ {m : CohMode} {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}} {K' : Kernel ℓB ℓRel ℓCode'}
  → KernelHomLike m (stackKernel S) K'
  → StackMapLike {m = m} S K'
fromKernelHomLike {S = S} {K' = K'} h =
  record
    { map∂ = Hom.map∂ h
    ; map∂-mono = Hom.map∂-mono h
    ; mapCode = λ o γ → Hom.mapCode h (mkStackCode o γ)
    ; decode-mapCode =
        λ o γ → Hom.decode-mapCode h (mkStackCode o γ)
    }

fromKernelHom
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}} {K' : Kernel ℓB ℓRel ℓCode'}
  → KernelHom (stackKernel S) K'
  → StackMap S K'
fromKernelHom = fromKernelHomLike {m = approx}

-- Same-boundary stack transport: operation-level translations over one shared
-- boundary.
--
-- The default public surface is refinement-first (`SameBoundaryStackMap`). The
-- explicit equality-bearing same-boundary map lives in
-- `LogOS.LT.Stack.Strictification`.
record SameBoundaryStackMapLike (m : CohMode)
  {ℓB ℓRel ℓSrcOp ℓSrcCode ℓTgtOp ℓTgtCode : Level}
  (B : ConPreorder ℓB ℓRel)
  : Set (lsuc (ℓB ⊔ ℓRel ⊔ ℓSrcOp ⊔ ℓSrcCode ⊔ ℓTgtOp ⊔ ℓTgtCode) ⊔ CohLevel m ℓB ℓRel) where
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
      → CohRel m B
          (μ (targetView (mapOp o)) (mapCodeAt o γ))
          (μ (sourceView o) γ)

  Source : Stack {ℓB} {ℓRel} {ℓSrcOp} {ℓSrcCode}
  Source =
    record
      { bnd = B
      ; Op = SourceOp
      ; Code = SourceCode
      ; op = sourceView
      }

  Target : Stack {ℓB} {ℓRel} {ℓTgtOp} {ℓTgtCode}
  Target =
    record
      { bnd = B
      ; Op = TargetOp
      ; Code = TargetCode
      ; op = targetView
      }

  mapStackCode : StackCode Source → StackCode Target
  mapStackCode oc = mkStackCode (mapOp (opIdx oc)) (mapCodeAt (opIdx oc) (code oc))

  opKernelHomLike
    : (o : SourceOp)
    → KernelHomLike m (opKernel Source o) (opKernel Target (mapOp o))
  opKernelHomLike o =
    Hom.mkKernelHomParts
      (record
        { map∂ = λ c → c
        ; map∂-mono = idMonoMap {CP = B}
        })
      (record
        { mapCode = mapCodeAt o
        ; decode-mapCode = λ γ → mapCodeAt-preserves o γ
        })

  stackKernelHomLike : KernelHomLike m (stackKernel Source) (stackKernel Target)
  stackKernelHomLike =
    Hom.mkKernelHomParts
      (record
        { map∂ = λ c → c
        ; map∂-mono = idMonoMap {CP = B}
        })
      (record
        { mapCode = mapStackCode
        ; decode-mapCode = λ oc → mapCodeAt-preserves (opIdx oc) (code oc)
        })

SameBoundaryStackMap
  : ∀ {ℓB ℓRel ℓSrcOp ℓSrcCode ℓTgtOp ℓTgtCode : Level}
  → ConPreorder ℓB ℓRel
  → Set (lsuc (ℓB ⊔ ℓRel ⊔ ℓSrcOp ⊔ ℓSrcCode ⊔ ℓTgtOp ⊔ ℓTgtCode) ⊔ CohLevel approx ℓB ℓRel)
SameBoundaryStackMap {ℓSrcOp = ℓSrcOp} {ℓSrcCode = ℓSrcCode} {ℓTgtOp = ℓTgtOp} {ℓTgtCode = ℓTgtCode} B =
  SameBoundaryStackMapLike approx
    {ℓSrcOp = ℓSrcOp}
    {ℓSrcCode = ℓSrcCode}
    {ℓTgtOp = ℓTgtOp}
    {ℓTgtCode = ℓTgtCode}
    B
