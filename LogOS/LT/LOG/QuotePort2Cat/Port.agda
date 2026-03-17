{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.QuotePort2Cat.Port where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Guarded self-reference as a port (encode + flow + a linking law).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; ≈-refl)
private
  module CPReasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.Kernel using (Kernel; EncodePort; bnd; decode; encode)
open import LogOS.LT.Flow using (GuardedClosure; Stable; mkStable; Flow)

record QuotePort {ℓ ℓRel ℓCode : Level} (K : Kernel ℓ ℓRel ℓCode)
  : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode)) where
  field
    GC : GuardedClosure (bnd K)
    EK : EncodePort K

    -- Code-level quotation soundness (G-tier):
    -- decoding an encoded boundary constraint is equivalent to normalisation.
    decode-encode≈Flow
      : ∀ c
      → _≈_ (bnd K) (decode K (encode EK c)) (Flow GC c)

open QuotePort public

-- --------------------------------------------------------------------------
-- Canonical quotation from a guarded closure (no extra structure).
--
-- Any guarded closure already determines a "quotation kernel":
-- code is the space of stable points, decode is `elem`, and encode is the
-- canonical `mkStable (Flow c) (idemp-lax c)`. This yields a QuotePort by construction.

quoteKernel
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → Kernel ℓCon ℓRel (lsuc (ℓCon ⊔ ℓRel))
quoteKernel {CP = CP} GC =
  record
    { bnd = CP
    ; Code = Stable {CP = CP} (Flow GC)
    ; decode = Stable.elem
    }

quoteEncodePort
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → EncodePort (quoteKernel GC)
quoteEncodePort {CP = CP} GC =
  record
    { encode =
        λ c → mkStable (Flow GC c) (GuardedClosure.idemp-lax GC c)
    }

quotePort
  : ∀ {ℓCon ℓRel : Level} {CP : ConPreorder ℓCon ℓRel}
  → (GC : GuardedClosure CP)
  → QuotePort (quoteKernel GC)
quotePort {CP = CP} GC =
  record
    { GC = GC
    ; EK = quoteEncodePort GC
    ; decode-encode≈Flow =
        λ c → ≈-refl CP (Flow GC c)
    }

-- Derived: encoding is “sound up to Flow” in the refinement direction.
--
-- Because `Flow` is inflationary and `decode ∘ encode ≈ Flow`, any encoded
-- constraint refines the original constraint.
encode-sound
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → (QP : QuotePort K)
  → (c : Con (bnd K))
  → _⊑_ (bnd K) c (decode K (encode (EK QP) c))
encode-sound {K = K} QP c =
  let
    module R = CPReasoning (bnd K)
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
    GC = QuotePort.GC QP
    ek = QuotePort.EK QP
    c≤Flowc : _⊑_ (bnd K) c (Flow GC c)
    c≤Flowc = GuardedClosure.infl GC c

    Flowc≤dec : _⊑_ (bnd K) (Flow GC c) (decode K (encode ek c))
    Flowc≤dec = snd (decode-encode≈Flow QP c)
  in
  begin⊑
    c ⊑⟨ c≤Flowc ⟩
    Flow GC c ⊑⟨ Flowc≤dec ⟩
    decode K (encode ek c) ∎⊑

-- Derived: decoded quotations are stable points of the guarded closure.
decodedStable
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → (QP : QuotePort K)
  → (c : Con (bnd K))
  → Stable {CP = bnd K} (Flow (GC QP))
decodedStable {K = K} QP c =
  let
    module R = CPReasoning (bnd K)
    open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
    open GuardedClosure (GC QP) using (mono; idemp-lax)

    dec : Con (bnd K)
    dec = decode K (encode (EK QP) c)

    dec≤Flowc : _⊑_ (bnd K) dec (Flow (GC QP) c)
    dec≤Flowc = fst (decode-encode≈Flow QP c)

    Flowc≤dec : _⊑_ (bnd K) (Flow (GC QP) c) dec
    Flowc≤dec = snd (decode-encode≈Flow QP c)

    Flowdec≤FlowFlowc : _⊑_ (bnd K) (Flow (GC QP) dec) (Flow (GC QP) (Flow (GC QP) c))
    Flowdec≤FlowFlowc = mono dec≤Flowc

    FlowFlowc≤Flowc : _⊑_ (bnd K) (Flow (GC QP) (Flow (GC QP) c)) (Flow (GC QP) c)
    FlowFlowc≤Flowc = idemp-lax c

    Flowdec≤Flowc : _⊑_ (bnd K) (Flow (GC QP) dec) (Flow (GC QP) c)
    Flowdec≤Flowc =
      begin⊑
        Flow (GC QP) dec ⊑⟨ Flowdec≤FlowFlowc ⟩
        Flow (GC QP) (Flow (GC QP) c) ⊑⟨ FlowFlowc≤Flowc ⟩
        Flow (GC QP) c ∎⊑

    Flowdec≤dec : _⊑_ (bnd K) (Flow (GC QP) dec) dec
    Flowdec≤dec =
      begin⊑
        Flow (GC QP) dec ⊑⟨ Flowdec≤Flowc ⟩
        Flow (GC QP) c ⊑⟨ Flowc≤dec ⟩
        dec ∎⊑
  in
  mkStable dec Flowdec≤dec
