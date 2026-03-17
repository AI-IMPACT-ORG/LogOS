{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Stack.Program where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Free view language over a stack (macros/programs).
--
-- This is the “PL-style” layer: a small DSL for building new views from a
-- fixed stack by wiring (`pullback`) and postcomposition (`post`).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; idMonoMap; _≈_; ≈-refl)
open import LogOS.LT.View using (View; μ; idView; pullbackView)
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Core using (KernelHom; mkKernelHomParts)
import LogOS.LT.Stack.Core as Stack
open import LogOS.LT.Stack.Core using
  ( Stack
  ; Op
  ; Code
  ; bnd
  ; op
  ; StackCode
  ; opIdx
  ; code
  ; SameBoundaryStackMap
  )

-- A small universe of domain shapes built from:
-- - the code sorts of the stack operations,
-- - the boundary carrier itself,
-- - finite sums and products.
--
-- This avoids quantifying over arbitrary `Set ℓ` while still supporting the
-- “construct a language for your problem” style.

data Shape {ℓB ℓRel ℓOp ℓCode : Level} (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}) : Set (ℓOp ⊔ ℓCode) where
  opS   : Op S → Shape S
  bndS  : Shape S
  unitS : Shape S
  _×S_  : Shape S → Shape S → Shape S
  _⊎S_  : Shape S → Shape S → Shape S

infixr 5 _×S_
infixr 4 _⊎S_

⟦_⟧Shape : ∀ {ℓB ℓRel ℓOp ℓCode : Level} {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}} → Shape S → Set (ℓB ⊔ ℓCode)
⟦_⟧Shape {ℓB = ℓB} {ℓCode = ℓCode} {S = S} (opS o) = Lift ℓB (Code S o)
⟦_⟧Shape {ℓB = ℓB} {ℓCode = ℓCode} {S = S} bndS = Lift ℓCode (Con (bnd S))
⟦_⟧Shape unitS = ⊤
⟦_⟧Shape (σ ×S τ) = ⟦ σ ⟧Shape × ⟦ τ ⟧Shape
⟦_⟧Shape (σ ⊎S τ) = ⟦ σ ⟧Shape ⊎ ⟦ τ ⟧Shape

-- A syntactic view built from:
-- - primitive stack views,
-- - pullback/reindexing along a map,
-- - postcomposition by a boundary-level transformer.
--
-- Postcomposition is restricted to boundary endomaps that preserve
-- observational equivalence (`≈`) on the shared boundary. Without that witness,
-- refinement-safe transport of programs is false in general.

mutual
  data ViewExpr {ℓB ℓRel ℓOp ℓCode : Level} (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}) : Shape S → Set (ℓB ⊔ ℓRel ⊔ ℓOp ⊔ ℓCode) where
    prim    : (o : Op S) → ViewExpr S (opS o)
    idBnd   : ViewExpr S bndS

    pullback
      : ∀ {σ τ}
      → (f : ⟦ τ ⟧Shape → ⟦ σ ⟧Shape)
      → ViewExpr S σ
      → ViewExpr S τ

    post
      : ∀ {σ}
      → BoundaryEndo S
      → ViewExpr S σ
      → ViewExpr S σ

  record BoundaryEndo {ℓB ℓRel ℓOp ℓCode : Level} (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
    : Set (ℓB ⊔ ℓRel ⊔ ℓOp ⊔ ℓCode) where
    inductive
    constructor mkBoundaryEndo
    field
      expr : ViewExpr S bndS
      preserves-≈
        : ∀ {x y}
        → _≈_ (bnd S) x y
        → _≈_ (bnd S) (evalBoundaryExpr expr x) (evalBoundaryExpr expr y)

  evalBoundaryExpr
    : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
      {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}}
    → ViewExpr S bndS
    → Con (bnd S)
    → Con (bnd S)
  evalBoundaryExpr F c = μ (evalViewExpr F) (lift c)

  evalViewExpr
    : ∀ {ℓB ℓRel ℓOp ℓCode : Level} {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}} {σ : Shape S}
    → ViewExpr S σ
    → View (⟦ σ ⟧Shape) (bnd S)
  evalViewExpr {S = S} (prim o) =
    record { μ = λ x → μ (op S o) (lower x) }
  evalViewExpr {S = S} idBnd =
    record { μ = λ x → lower x }
  evalViewExpr (pullback f V) = pullbackView f (evalViewExpr V)
  evalViewExpr (post F V) =
    record
      { μ = λ x → evalBoundaryExpr (BoundaryEndo.expr F) (μ (evalViewExpr V) x) }

open BoundaryEndo public

-- A closed program is a view expression together with concrete input data.
record Program {ℓB ℓRel ℓOp ℓCode : Level} (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}) : Set (ℓB ⊔ ℓRel ⊔ ℓOp ⊔ ℓCode) where
  constructor mkProgram
  field
    shape : Shape S
    expr  : ViewExpr S shape
    input : ⟦ shape ⟧Shape

open Program public

decodeProgram : ∀ {ℓB ℓRel ℓOp ℓCode : Level} {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}} → Program S → Con (bnd S)
decodeProgram P =
  μ (evalViewExpr (expr P)) (input P)

-- The stack-as-a-transformer, upgraded: programs/macros as code.
programKernel
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
  → Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}
  → Kernel ℓB ℓRel (ℓB ⊔ ℓRel ⊔ ℓOp ⊔ ℓCode)
programKernel S =
  record
    { bnd = bnd S
    ; Code = Program S
    ; decode = decodeProgram
    }

-- Primitive codes embed as programs.
primProgram
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
  → (S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
  → StackCode S
  → Program S
primProgram S oc = mkProgram (opS (opIdx oc)) (prim (opIdx oc)) (lift (code oc))

-- Structural transport of shape-indexed values along a same-boundary stack map
-- plus a code-level retraction. The boundary coherence lives in the map; the
-- code-level retraction isolates the recursive bookkeeping needed by pullback.
record ShapeEmbedding
  {ℓB ℓRel ℓSrcOp ℓSrcCode ℓTgtOp ℓTgtCode : Level}
  {B : ConPreorder ℓB ℓRel}
  (M : SameBoundaryStackMap
         {ℓSrcOp = ℓSrcOp}
         {ℓSrcCode = ℓSrcCode}
         {ℓTgtOp = ℓTgtOp}
         {ℓTgtCode = ℓTgtCode}
         B)
  (unmapCode : (o : Stack.SameBoundaryStackMapLike.SourceOp M) → Stack.SameBoundaryStackMapLike.TargetCode M (Stack.SameBoundaryStackMapLike.mapOp M o) → Stack.SameBoundaryStackMapLike.SourceCode M o)
  (unmapCode-mapCode : ∀ o γ → unmapCode o (Stack.SameBoundaryStackMapLike.mapCodeAt M o γ) ≡ γ)
  : Set (lsuc (ℓB ⊔ ℓRel ⊔ ℓSrcOp ⊔ ℓSrcCode ⊔ ℓTgtOp ⊔ ℓTgtCode)) where
  open Stack.SameBoundaryStackMapLike M

  field
    mapShape : Shape Source → Shape Target
    mapVal : (σ : Shape Source) → ⟦ σ ⟧Shape → ⟦ mapShape σ ⟧Shape
    unmapVal : (σ : Shape Source) → ⟦ mapShape σ ⟧Shape → ⟦ σ ⟧Shape
    unmapVal-mapVal
      : ∀ (σ : Shape Source) (x : ⟦ σ ⟧Shape)
      → unmapVal σ (mapVal σ x) ≡ x

shapeEmbedding
  : ∀ {ℓB ℓRel ℓSrcOp ℓSrcCode ℓTgtOp ℓTgtCode : Level}
      {B : ConPreorder ℓB ℓRel}
      (M : SameBoundaryStackMap
             {ℓSrcOp = ℓSrcOp}
             {ℓSrcCode = ℓSrcCode}
             {ℓTgtOp = ℓTgtOp}
             {ℓTgtCode = ℓTgtCode}
             B)
      (unmapCode : (o : Stack.SameBoundaryStackMapLike.SourceOp M) → Stack.SameBoundaryStackMapLike.TargetCode M (Stack.SameBoundaryStackMapLike.mapOp M o) → Stack.SameBoundaryStackMapLike.SourceCode M o)
      (unmapCode-mapCode : ∀ o γ → unmapCode o (Stack.SameBoundaryStackMapLike.mapCodeAt M o γ) ≡ γ)
  → ShapeEmbedding M unmapCode unmapCode-mapCode
shapeEmbedding {ℓB = ℓB} {ℓSrcCode = ℓSrcCode} {ℓTgtCode = ℓTgtCode} M unmapCode unmapCode-mapCode =
  let open Stack.SameBoundaryStackMapLike M in
  record
    { mapShape = mapShape
    ; mapVal = mapVal
    ; unmapVal = unmapVal
    ; unmapVal-mapVal = unmapVal-mapVal
    }
  where
    open Stack.SameBoundaryStackMapLike M

    mapShape : Shape Source → Shape Target
    mapShape (opS o) = opS (mapOp o)
    mapShape bndS = bndS
    mapShape unitS = unitS
    mapShape (σ ×S τ) = mapShape σ ×S mapShape τ
    mapShape (σ ⊎S τ) = mapShape σ ⊎S mapShape τ

    mapVal : (σ : Shape Source) → ⟦ σ ⟧Shape → ⟦ mapShape σ ⟧Shape
    mapVal (opS o) x = lift (mapCodeAt o (lower x))
    mapVal bndS x = lift (lower x)
    mapVal unitS _ = tt {ℓ = ℓB ⊔ ℓTgtCode}
    mapVal (σ ×S τ) (x , y) = mapVal σ x , mapVal τ y
    mapVal (σ ⊎S τ) (inj₁ x) = inj₁ (mapVal σ x)
    mapVal (σ ⊎S τ) (inj₂ y) = inj₂ (mapVal τ y)

    unmapVal : (σ : Shape Source) → ⟦ mapShape σ ⟧Shape → ⟦ σ ⟧Shape
    unmapVal (opS o) x = lift (unmapCode o (lower x))
    unmapVal bndS x = lift (lower x)
    unmapVal unitS _ = tt {ℓ = ℓB ⊔ ℓSrcCode}
    unmapVal (σ ×S τ) (x , y) = unmapVal σ x , unmapVal τ y
    unmapVal (σ ⊎S τ) (inj₁ x) = inj₁ (unmapVal σ x)
    unmapVal (σ ⊎S τ) (inj₂ y) = inj₂ (unmapVal τ y)

    unmapVal-mapVal
      : ∀ (σ : Shape Source) (x : ⟦ σ ⟧Shape)
      → unmapVal σ (mapVal σ x) ≡ x
    unmapVal-mapVal (opS o) x = cong lift (unmapCode-mapCode o (lower x))
    unmapVal-mapVal bndS (lift _) = refl
    unmapVal-mapVal unitS ttℓ = refl
    unmapVal-mapVal (σ ×S τ) (x , y) =
      cong₂ (λ a b → a , b) (unmapVal-mapVal σ x) (unmapVal-mapVal τ y)
    unmapVal-mapVal (σ ⊎S τ) (inj₁ x) = cong inj₁ (unmapVal-mapVal σ x)
    unmapVal-mapVal (σ ⊎S τ) (inj₂ y) = cong inj₂ (unmapVal-mapVal τ y)

-- Program-level functoriality over a shared boundary. To transport arbitrary
-- `pullback` programs we need a retraction on mapped code sorts.
record SameBoundaryProgramMap
  {ℓB ℓRel ℓSrcOp ℓSrcCode ℓTgtOp ℓTgtCode : Level}
  {B : ConPreorder ℓB ℓRel}
  (M : SameBoundaryStackMap
         {ℓSrcOp = ℓSrcOp}
         {ℓSrcCode = ℓSrcCode}
         {ℓTgtOp = ℓTgtOp}
         {ℓTgtCode = ℓTgtCode}
         B)
  : Set (lsuc (ℓB ⊔ ℓRel ⊔ ℓSrcOp ⊔ ℓSrcCode ⊔ ℓTgtOp ⊔ ℓTgtCode)) where
  open Stack.SameBoundaryStackMapLike M

  field
    unmapCode
      : (o : SourceOp)
      → TargetCode (mapOp o)
      → SourceCode o

    unmapCode-mapCode
      : ∀ o γ
      → unmapCode o (mapCodeAt o γ) ≡ γ

  private
    shapeEmbeddingCore : ShapeEmbedding M unmapCode unmapCode-mapCode
    shapeEmbeddingCore = shapeEmbedding M unmapCode unmapCode-mapCode

  open ShapeEmbedding shapeEmbeddingCore public
    using (mapShape; mapVal; unmapVal; unmapVal-mapVal)

  mutual
    mapBoundaryEndo
      : BoundaryEndo Source
      → BoundaryEndo Target
    mapBoundaryEndo F =
      let
        mappedExpr = mapViewExpr (expr F)
        module R = LogOS.Prelude.RefinementKit.Reasoning B
        open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
      in
      mkBoundaryEndo
        mappedExpr
        (λ {x} {y} x≈y →
          let
            Fx = eval-mapViewExpr (expr F) (lift x)
            Fy = eval-mapViewExpr (expr F) (lift y)
            Fxy = preserves-≈ F x≈y
          in
          ( (begin⊑
              evalBoundaryExpr mappedExpr x
                ⊑⟨ fst Fx ⟩
              evalBoundaryExpr (expr F) x
                ⊑⟨ fst Fxy ⟩
              evalBoundaryExpr (expr F) y
                ⊑⟨ snd Fy ⟩
              evalBoundaryExpr mappedExpr y
            ∎⊑)
          , (begin⊑
              evalBoundaryExpr mappedExpr y
                ⊑⟨ fst Fy ⟩
              evalBoundaryExpr (expr F) y
                ⊑⟨ snd Fxy ⟩
              evalBoundaryExpr (expr F) x
                ⊑⟨ snd Fx ⟩
              evalBoundaryExpr mappedExpr x
            ∎⊑)
          ))

    mapViewExpr
      : ∀ {σ : Shape Source}
      → ViewExpr Source σ
      → ViewExpr Target (mapShape σ)
    mapViewExpr (prim o) = prim (mapOp o)
    mapViewExpr idBnd = idBnd
    mapViewExpr (pullback {σ = σ} {τ = τ} f V) =
      pullback (λ x → mapVal σ (f (unmapVal τ x))) (mapViewExpr V)
    mapViewExpr (post F V) = post (mapBoundaryEndo F) (mapViewExpr V)

    eval-mapViewExpr
      : ∀ {σ : Shape Source}
      → (V : ViewExpr Source σ)
      → (x : ⟦ σ ⟧Shape)
      → _≈_ B (μ (evalViewExpr (mapViewExpr V)) (mapVal σ x)) (μ (evalViewExpr V) x)
    eval-mapViewExpr (prim o) x = mapCodeAt-preserves o (lower x)
    eval-mapViewExpr idBnd x = ≈-refl B (lower x)
    eval-mapViewExpr (pullback {σ = σ} {τ = τ} f V) x
      rewrite unmapVal-mapVal τ x
      = eval-mapViewExpr V (f x)
    eval-mapViewExpr {σ = σ} (post F V) x =
      let
        mapped = μ (evalViewExpr (mapViewExpr V)) (mapVal σ x)
        source = μ (evalViewExpr V) x
        Fmapped = eval-mapViewExpr (expr F) (lift mapped)
        Fsource = preserves-≈ F (eval-mapViewExpr V x)
        mappedEndo = mapBoundaryEndo F
        module R = LogOS.Prelude.RefinementKit.Reasoning B
        open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
      in
      ( (begin⊑
          evalBoundaryExpr (expr mappedEndo) mapped
            ⊑⟨ fst Fmapped ⟩
          evalBoundaryExpr (expr F) mapped
            ⊑⟨ fst Fsource ⟩
          evalBoundaryExpr (expr F) source
        ∎⊑)
      , (begin⊑
          evalBoundaryExpr (expr F) source
            ⊑⟨ snd Fsource ⟩
          evalBoundaryExpr (expr F) mapped
            ⊑⟨ snd Fmapped ⟩
          evalBoundaryExpr (expr mappedEndo) mapped
        ∎⊑)
      )

  mapProgram : Program Source → Program Target
  mapProgram (mkProgram σ V x) = mkProgram (mapShape σ) (mapViewExpr V) (mapVal σ x)

  decode-mapProgram : ∀ p → _≈_ B (decodeProgram (mapProgram p)) (decodeProgram p)
  decode-mapProgram (mkProgram _ V x) = eval-mapViewExpr V x

  programKernelHom : KernelHom (programKernel Source) (programKernel Target)
  programKernelHom =
    mkKernelHomParts
      (record
        { map∂ = λ c → c
        ; map∂-mono = idMonoMap {CP = B}
        })
      (record
        { mapCode = mapProgram
        ; decode-mapCode = λ p → decode-mapProgram p
        })
