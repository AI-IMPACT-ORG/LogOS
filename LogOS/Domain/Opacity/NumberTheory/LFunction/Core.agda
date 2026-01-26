{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.NumberTheory.LFunction.Core where

open import LogOS.Prelude

open import LogOS.Algebra.Ring

-- L-function core: abstract over a ring R whose Carrier is the domain/codomain

record LFunction {ℓ : Level} (R : Ring {ℓ}) : Set (lsuc ℓ) where
  field
    In    : Ring.Carrier R → Set ℓ
    L     : Ring.Carrier R → Ring.Carrier R
    Gamma : Ring.Carrier R → Ring.Carrier R
    Q     : Ring.Carrier R         -- conductor-like constant
    eps   : Ring.Carrier R         -- epsilon-like constant (unused here, but standard)

  mirror : Ring.Carrier R → Ring.Carrier R
  mirror u = Ring.inv R (Ring._*_ R Q u)

  Lambda : Ring.Carrier R → Ring.Carrier R
  Lambda u = Ring._*_ R (Gamma u) (L u)

-- Layer 1: Z-level (uncompleted) functional equation

record LZ-FE {ℓ} {R : Ring {ℓ}} (LF : LFunction R) : Set (lsuc ℓ) where
  open LFunction LF
  field
    z-fe : ∀ {u} → In u → L u ≡ L (mirror u)

-- Layer 2: Gamma-factor symmetry (completion factor is symmetric under mirror)

record GammaSym {ℓ} {R : Ring {ℓ}} (LF : LFunction R) : Set (lsuc ℓ) where
  open LFunction LF
  field
    gamma-sym    : ∀ {u} → In u → Gamma u ≡ Gamma (mirror u)
    domain-closed : ∀ {u} → In u → In (mirror u)

-- Layer 3: Completed functional equation (textbook-aligned primary interface)
--
-- For classical analytic L-functions (including Riemann ζ), the functional equation
-- is naturally stated for the completed object Λ (often also written ξ/Ξ after
-- folding additional symmetric factors into Gamma).

record LambdaFE {ℓ} {R : Ring {ℓ}} (LF : LFunction R) : Set (lsuc ℓ) where
  open LFunction LF
  field
    lambda-fe    : ∀ {u} → In u → Lambda u ≡ Lambda (mirror u)
    domain-closed : ∀ {u} → In u → In (mirror u)

-- Layer 3: Completed FE for Λ from Z-FE + GammaSym

LambdaFE-from-LZ+Gamma
  : ∀ {ℓ} {R : Ring {ℓ}}
    (LF : LFunction R)
    (ZFE : LZ-FE LF)
    (GS  : GammaSym LF)
    {u}
  → LFunction.In LF u
  → LFunction.Lambda LF u ≡ LFunction.Lambda LF (LFunction.mirror LF u)
LambdaFE-from-LZ+Gamma {R = R} LF ZFE GS {u} inu =
  let open LFunction LF
      open LZ-FE ZFE
      open GammaSym GS
      module RR = Ring R
      s1 = cong (λ z → RR._*_ (Gamma u) z) (z-fe inu)
      s2 = cong (λ g → RR._*_ g (L (mirror u))) (gamma-sym inu)
  in trans s1 s2

-- Bundle the derived equality into the `LambdaFE` record.

LambdaFE-pack-from-LZ+Gamma
  : ∀ {ℓ} {R : Ring {ℓ}}
    (LF  : LFunction R)
    (ZFE : LZ-FE LF)
    (GS  : GammaSym LF)
  → LambdaFE LF
LambdaFE-pack-from-LZ+Gamma LF ZFE GS = record
  { lambda-fe    = LambdaFE-from-LZ+Gamma LF ZFE GS
  ; domain-closed = GammaSym.domain-closed GS
  }
