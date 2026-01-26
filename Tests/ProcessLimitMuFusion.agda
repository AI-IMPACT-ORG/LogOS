{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.ProcessLimitMuFusion where

-- Smoke test: the process-level μ/limit semantics layer is usable and the
-- μ-fusion transport theorem typechecks with explicit assumptions.

open import LogOS.Prelude

open import LogOS.Minimal.Con using (ConPreorder)
open import LogOS.Minimal.Adapter using (trivialQAdapter)
import LogOS.Minimal.Truth as Truth

open import LogOS.Computation.SchemeCategory using (Process; ProcessHomLax)
import LogOS.Computation.ProcessLimit as PL

private
  module GC = Truth.GuardedCore {ℓ = lzero}

  Con₀ : Set lzero
  Con₀ = ⊤ {ℓ = lzero}

  CP : ConPreorder lzero
  CP = record
    { Con  = Con₀
    ; _⊑_  = λ _ _ → ⊤
    ; refl = tt
    ; trans = λ _ _ → tt
    }

  ωCPO : GC.OmegaCPO CP
  ωCPO = record
    { ⊥     = tt
    ; isBot = λ _ → tt
    ; supω  = λ _ → tt
    ; ub    = λ _ _ → tt
    ; least = λ _ _ _ → tt
    }

  Step : Con₀ → Con₀
  Step _ = tt

  P : Process {lzero} {lzero} {lzero} Con₀
  P = record
    { CP       = CP
    ; Step     = Step
    ; Close     = record
        { cl        = λ x → x
        ; mono      = λ _ → tt
        ; infl      = λ _ → tt
        ; idemp-lax = λ _ → tt
        }
    ; decode   = λ _ → tt
    ; Q        = trivialQAdapter
    ; stepCost = λ _ → tt
    }

  D : PL.For.LimitData P
  D = record
    { ωCPO     = ωCPO
    ; stepInfl = λ _ → tt
    ; stepMono = λ _ → tt
    ; stepSC   = record { cont-ω = λ _ _ → tt }
    }

  h : ProcessHomLax P P
  h = record
    { map         = λ x → x
    ; mono        = λ _ → tt
    ; step-comm≤  = λ _ → tt
    ; norm-comm≤  = λ _ → tt
    ; decode-comm = λ _ → refl
    }

  cont-map : PL.TransportLax.cont-map D D h
  cont-map _ _ = tt

-- Statement-only check: the μ-transport lemma produces a proof.

_ : ∀ c → Process._⊑_ P
          (ProcessHomLax.map h (PL.For.run∞ P D c))
          (PL.For.run∞ P D (ProcessHomLax.map h c))
_ = PL.TransportLax.run∞-map≤ D D h cont-map
