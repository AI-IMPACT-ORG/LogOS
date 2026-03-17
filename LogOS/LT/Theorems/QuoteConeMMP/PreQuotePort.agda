{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.QuoteConeMMP.PreQuotePort where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Precones: a one-sided (lax) quotation law.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (_⊑_)
open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.Kernel using (Kernel; bnd; decode; EncodePort; encode)
open import LogOS.LT.LOG.ArchitectureQuote2Cat using
  ( QuotePort
  ; GC
  ; EK
  ; decode-encode≈Flow
  )

record PreQuotePort {ℓ ℓRel ℓCode : Level} (K : Kernel ℓ ℓRel ℓCode)
  : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode)) where
  field
    GC : GuardedClosure (bnd K)
    EK : EncodePort K

    -- “Lax cone” direction: decoding an encoding is below the normalised meaning.
    --
    -- (The opposite direction gives a different precone; a full QuotePort is both.)
    decode-encode≤Flow
      : ∀ c
      → _⊑_ (bnd K) (decode K (encode EK c)) (GuardedClosure.Flow GC c)

open PreQuotePort public

-- QuotePort is the “cone” completion of a PreQuotePort (it contains both legs).
precone-from-quote
  : ∀ {ℓ ℓRel ℓCode : Level} {K : Kernel ℓ ℓRel ℓCode}
  → QuotePort K
  → PreQuotePort K
precone-from-quote {K = K} QP =
  record
    { GC = GC QP
    ; EK = EK QP
    ; decode-encode≤Flow = λ c → fst (decode-encode≈Flow QP c)
    }
