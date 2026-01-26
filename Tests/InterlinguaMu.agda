{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.InterlinguaMu where

-- Smoke test: instantiate the μ-level port transport lemma via the
-- interoperability spine, in a trivial model.
--
-- Goal: ensure `LogOS.Ports.Semantic.Interoperability.Limit.translate-μ≤`
-- typechecks and its assumptions are consistent with the ωCPO/μ-fusion
-- infrastructure.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Minimal.Con using (ConPreorder)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Ports.Semantic.PresentationCore using (PresentationC)
open import LogOS.Ports.Semantic.SatMor using (idSatMor)
import LogOS.Ports.Semantic.Interoperability as Interop

import LogOS.Theorems.Boundary.OmegaCPOMapKit as OmegaKit

Ctx : Set lzero
Ctx = ⊤ {ℓ = lzero}

Con : Set lzero
Con = ⊤ {ℓ = lzero}

-- Trivial preorder on ⊤.
CP⊤ : ConPreorder lzero
CP⊤ =
  record
    { Con = Con
    ; _⊑_ = λ _ _ → ⊤ {ℓ = lzero}
    ; refl = tt
    ; trans = λ _ _ → tt
    }

ω⊤ : Truth.GuardedCore.OmegaCPO CP⊤
ω⊤ =
  record
    { ⊥ = tt
    ; isBot = λ _ → tt
    ; supω = λ _ → tt
    ; ub = λ _ _ → tt
    ; least = λ _ _ _ → tt
    }

Sat : Ctx → Con → Set lzero
Sat _ _ = ⊤ {ℓ = lzero}

P : PresentationC {ℓCtx = lzero} {ℓCon = lzero} {ℓForm = lzero} {ℓSat = lzero} Ctx Con Sat
P =
  record
    { Form = Con
    ; SatF = Sat
    ; Export = λ c → c
    ; SatC≈F = λ _ _ → Prop.↔-refl
    ; Import = λ φ → φ
    ; SatF≈C = λ _ _ → Prop.↔-refl
    }

module L = Interop.Limit CP⊤ CP⊤ (idSatMor Sat) P P

F : Con → Con
F x = x

inflF : ∀ c → ConPreorder._⊑_ CP⊤ c (F c)
inflF _ = tt

commF : ∀ c → ConPreorder._⊑_ CP⊤ ((λ x → x) (F c)) (F ((λ x → x) c))
commF _ = tt

transportData : L.MuTransportData ω⊤ ω⊤ F F
transportData =
  record
    { Mω = OmegaKit.idOmegaCPOMap CP⊤ {ω = ω⊤}
    ; monoF₂ = λ {c} {d} _ → tt
    ; inflF₁ = inflF
    ; comm = commF
    ; monoSat₂ = λ {p} {c} {d} _ _ → tt
    }

-- The lemma itself: in this trivial setting, it reduces to an identity.
transport-ok : ∀ p → ⊤ {ℓ = lzero} → ⊤ {ℓ = lzero}
transport-ok p = L.translate-μ≤ transportData p
