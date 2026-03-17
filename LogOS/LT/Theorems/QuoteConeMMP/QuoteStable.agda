{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.QuoteConeMMP.QuoteStable where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Cone theorem: code-level quotation yields a canonical cone into stable points.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( Con
  ; _≈_
  ; ≈-sym
  )
open import LogOS.LT.Flow using (GuardedClosure; Stable; elem)
open import LogOS.LT.Reflection using (quot; evalm)
open import LogOS.LT.Kernel using (Kernel; bnd; decode; EncodePort; encode)
open import LogOS.LT.LOG.ArchitectureQuote2Cat using
  ( QuotePort
  ; GC
  ; decode-encode≈Flow
  ; decodedStable
  )
private
  module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

-- The “cone legs” are the stable points produced by decoding encoded constraints.
quoteStable
  : ∀ {ℓ ℓRel ℓCode : Level} {K : Kernel ℓ ℓRel ℓCode}
  → (QP : QuotePort K)
  → Con (bnd K)
  → Stable {CP = bnd K} (GuardedClosure.Flow (GC QP))
quoteStable = decodedStable

-- The stable-point meaning of code-level quotation is equivalent to the canonical
-- boundary quotation `quot` induced by the guarded closure.
quoteStable≈quot
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → (QP : QuotePort K)
  → (c : Con (bnd K))
  → _≈_ (bnd K)
      (elem (quoteStable QP c))
      (evalm {GC = GC QP} (quot (GC QP) c))
quoteStable≈quot {K = K} QP c =
  -- elem (quoteStable QP c) = decode (encode c)  ≈  Flow c = evalm (quot c)
  decode-encode≈Flow QP c

-- Pointwise equivalence (up to mutual refinement) of quotation realisations.
--
-- This is the key “no semantic fork” consequence: any two QuotePorts induce the
-- same boundary-level quotation (up to observation).
quoteNoFork
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → (GC₀ : GuardedClosure (bnd K))
  → (EK EK' : EncodePort K)
  → (law : ∀ c → _≈_ (bnd K) (decode K (encode EK c)) (GuardedClosure.Flow GC₀ c))
  → (law' : ∀ c → _≈_ (bnd K) (decode K (encode EK' c)) (GuardedClosure.Flow GC₀ c))
  → (c : Con (bnd K))
  → _≈_ (bnd K)
      (decode K (encode EK c))
      (decode K (encode EK' c))
quoteNoFork {K = K} GC₀ EK EK' law law' c =
  let
    module R = ≤-Reasoning (bnd K)
    open R using (begin≈_; _≈⟨_⟩_; _∎≈)
  in
  begin≈
    decode K (encode EK c) ≈⟨ law c ⟩
    GuardedClosure.Flow GC₀ c ≈⟨ ≈-sym {CP = bnd K} (law' c) ⟩
    decode K (encode EK' c) ∎≈
