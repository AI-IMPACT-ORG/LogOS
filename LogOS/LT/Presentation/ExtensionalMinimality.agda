{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Presentation.ExtensionalMinimality where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Extensional minimality (design-target spec).
--
-- See spec v5.8 “Extensional minimality: decoding forces refinement”.
--
-- Once `decode` is taken as the observable semantics boundary:
-- - the code order is forced as the pullback preorder along `decode`
-- - monotonicity of code transport is derived (no extra axioms)
-- - morphism refinement is forced as pointwise refinement after boundary transport
--   (canonically `_⇒∂_`; the implementation-first `_⇒_` is a derived view)
-- - refinement is preserved under composition (whiskering monotone)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _⊑_; MonoMap)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode; CodePreorder)
open import LogOS.LT.Hom.Core using
    ( KernelHom
    ; map∂
    ; mapCode
    ; map∂-mono
    ; decode-mapCode≈
    ; _⇒∂_
    ; _∘_
    ; whiskerL∂
    ; whiskerR∂
    )

-- --------------------------------------------------------------------------
-- (II) Monotonicity of code transport is derived from boundary monotonicity
--      plus decode coherence.

mapCode-mono
  : ∀ {ℓ ℓRel ℓCode ℓCode'} {K : Kernel ℓ ℓRel ℓCode} {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHom K K')
  → MonoMap (CodePreorder K) (CodePreorder K') (mapCode h)
mapCode-mono {K = K} {K' = K'} h {x = γ} {y = δ} le =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning (bnd K')
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
  in
  begin⊑
    decode K' (mapCode h γ)
      ⊑⟨ fst (decode-mapCode≈ h γ) ⟩
    map∂ h (decode K γ)
      ⊑⟨ map∂-mono h le ⟩
    map∂ h (decode K δ)
      ⊑⟨ snd (decode-mapCode≈ h δ) ⟩
    decode K' (mapCode h δ) ∎⊑

-- --------------------------------------------------------------------------
-- (III) Compositionality: whiskering preserves refinement.
