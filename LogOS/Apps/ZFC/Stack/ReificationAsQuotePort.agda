{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ReificationAsQuotePort where

-- Predicate reification, expressed as a kernel-level quote/encode port.
--
-- This module makes the “direct path” precise:
--
--   membership observation  :  View SetU PredBnd
--   sets-as-code kernel     :  kernelFromView membershipView
--   reification doctrine    :  an EncodePort + guarded-closure law
--
-- Concretely, `Stack.AsymptoticReification.TotalPredicateReification` is
-- equivalent to providing a `QuotePort` for the membership kernel:
--
--   decode (encode P)  ≈  Flow P
--
-- The restricted-by-default `PredicateReification` can be obtained from a
-- `QuotePort` by declaring all predicates admissible (`Reifiable = ⊤`), but the
-- converse direction requires an explicit “totality” witness.
--
-- This is the same quine-shaped interface used by the generic quotation and
-- reification layers (`LogOS.LT.LOG.ArchitectureQuote2Cat` /
-- `LogOS.Ports.Reification`), but specialised
-- to the membership-local predicate boundary.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _≈_)
open import LogOS.LT.Flow using (Flow)
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Kernel using (Kernel; kernelFromView; EncodePort; decode)
open import LogOS.LT.LOG.ArchitectureQuote2Cat using (QuotePort)

open import LogOS.Apps.ZFC.Stack.Boundary using (PredicateBoundary; membershipView)
import LogOS.Apps.ZFC.Stack.ZFCore as ZF
import LogOS.Apps.ZFC.Stack.AsymptoticReification as AR

module ForContext {ℓ : Level} (C : ZF.SetContext {ℓ}) where
  open ZF.SetContext C using (SetU; _∈_)

  PredBnd : ConPreorder (lsuc ℓ) ℓ
  PredBnd = PredicateBoundary SetU

  memV : View SetU PredBnd
  memV = membershipView SetU _∈_

  -- The membership kernel: code is sets, decode is their membership predicate.
  MemK : Kernel (lsuc ℓ) ℓ ℓ
  MemK = kernelFromView memV

  -- Convert a kernel-level quote port into the ZFC pack’s reification ledger.
  --
  -- Intuition: `reify` is `encode`, and `mem-reify↔` is the pointwise
  -- form of `decode-encode≈Flow`.
  totalPredicateReificationFromQuotePort
    : QuotePort MemK
    → AR.TotalPredicateReification C
  totalPredicateReificationFromQuotePort QP =
    record
      { GC = QuotePort.GC QP
      ; reify = EncodePort.encode (QuotePort.EK QP)
      ; mem-reify↔ =
          λ P z →
            let eq = QuotePort.decode-encode≈Flow QP P in
            intro
              (QuotePort2to eq z)
              (QuotePort2from eq z)
      }
    where
      -- Helper: turn boundary equivalence of predicates into pointwise ↔.
      --
      -- For `PredBnd`, `F ≈ G` is mutual pointwise implication, i.e. a pointwise ↔.
      QuotePort2to
        : ∀ {F G : Con PredBnd}
        → _≈_ PredBnd F G
        → (z : SetU) → F z → G z
      QuotePort2to (FG , GF) z fz = GF z fz

      QuotePort2from
        : ∀ {F G : Con PredBnd}
        → _≈_ PredBnd F G
        → (z : SetU) → G z → F z
      QuotePort2from (FG , GF) z gz = FG z gz

  -- Convenience: obtain the restricted-by-default reification ledger by
  -- declaring all predicates admissible (`Reifiable = ⊤`).
  predicateReificationFromQuotePort
    : QuotePort MemK
    → AR.PredicateReification C
  predicateReificationFromQuotePort QP =
    AR.total→restricted (totalPredicateReificationFromQuotePort QP)

  -- Convert a *total/unrestricted* predicate reification ledger into a
  -- kernel-level quote port.
  --
  -- This is useful if you want to reuse generic quote-port theorems (e.g.
  -- `decodedStable`) in ZFC developments.
  quotePortFromTotalPredicateReification
    : AR.TotalPredicateReification C
    → QuotePort MemK
  quotePortFromTotalPredicateReification R =
    record
      { GC = AR.TotalPredicateReification.GC R
      ; EK = record { encode = AR.TotalPredicateReification.reify R }
      ; decode-encode≈Flow =
          λ P →
            ( (λ z → _↔_.from (AR.TotalPredicateReification.mem-reify↔ R P z))
            , (λ z → _↔_.to   (AR.TotalPredicateReification.mem-reify↔ R P z))
            )
      }

  -- Convert a restricted predicate reification ledger into a quote port, given
  -- a proof that all predicates are admissible.
  quotePortFromPredicateReification
    : (R : AR.PredicateReification C)
    → (total : ∀ P → AR.PredicateReification.Reifiable R P)
    → QuotePort MemK
  quotePortFromPredicateReification R total =
    quotePortFromTotalPredicateReification (AR.restricted→total R total)
