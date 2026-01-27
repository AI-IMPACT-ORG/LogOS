{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.ContinuityCore where

-- Shared continuity/approximant wrappers for any guarded closure.

open import LogOS.Prelude
open import LogOS.Prelude.Product using (_×_; _,_)
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth

module For {ℓ : Level}
  (CP : ConPreorder ℓ)
  (GC : Truth.GuardedCore.GuardedClosure CP)
  where

  open ConPreorder CP
  open Truth.GuardedCore

  Flow-continuity
    : (ωCPO : OmegaCPO CP)
      (FF   : FiniteFirst CP GC ωCPO)
      (f    : ℕ → Con)
    → (mono-chain : ∀ n → _⊑_ (f n) (f (suc n)))
    → _⊑_
        (GuardedClosure.Flow GC (OmegaCPO.supω ωCPO f))
        (OmegaCPO.supω ωCPO (λ n → GuardedClosure.Flow GC (f n)))
  Flow-continuity ωCPO FF f mono =
    FiniteFirst.cont-ω FF f mono

  Th*-as-sup
    : (ωCPO : OmegaCPO CP)
      (FF   : FiniteFirst CP GC ωCPO)
    → (_⊑_ (GuardedClosure.Th* GC) (OmegaCPO.supω ωCPO (FiniteFirst.approxS FF)))
      ×
      (_⊑_ (OmegaCPO.supω ωCPO (FiniteFirst.approxS FF)) (GuardedClosure.Th* GC))
  Th*-as-sup ωCPO FF =
    FiniteFirst.Th⋆-as-sup FF

  -- -------------------------------------------------------------------------
  -- Th* as a Kleene μ fixed point (under FiniteFirst).
  -- -------------------------------------------------------------------------
  --
  -- `FiniteFirst` provides a concrete approximant chain `approxS : ℕ → Con` with
  -- `approxS 0 = ⊥` and `approxS (suc n) = Flow (approxS n)`.
  --
  -- The generic Kleene μ construction is `μ Flow = supω (iter Flow)` where
  -- `iter` is defined by the same equations. In general this μ is a least
  -- *pre*-fixed point (Park induction); it becomes a (preorder) fixed point only
  -- under additional continuity assumptions. We expose the equivalence (up to
  -- the preorder) so downstream theorems can talk about “stabilised truth = μ
  -- Flow” under explicit ωCPO assumptions.

  approxS≡iter-Flow
    : (ωCPO : OmegaCPO CP)
      (FF   : FiniteFirst CP GC ωCPO)
    → ∀ n
    → FiniteFirst.approxS FF n
        ≡
      (let module K = Kleene {CP = CP} ωCPO
           open GuardedClosure GC renaming (Flow to F)
       in K.iter F n)
  approxS≡iter-Flow ωCPO FF zero =
    let open FiniteFirst FF using (base) in base
  approxS≡iter-Flow ωCPO FF (suc n) =
    let
      open FiniteFirst FF using (step)
      open GuardedClosure GC renaming (Flow to F)
    in
    LogOS.Prelude.trans
      (step n)
      (LogOS.Prelude.cong F (approxS≡iter-Flow ωCPO FF n))

  approxS-sup≈μFlow
    : (ωCPO : OmegaCPO CP)
      (FF   : FiniteFirst CP GC ωCPO)
    → (_⊑_ (OmegaCPO.supω ωCPO (FiniteFirst.approxS FF))
           (let module K = Kleene {CP = CP} ωCPO
                open GuardedClosure GC renaming (Flow to F)
            in K.μ F))
      ×
      (_⊑_ (let module K = Kleene {CP = CP} ωCPO
                open GuardedClosure GC renaming (Flow to F)
            in K.μ F)
           (OmegaCPO.supω ωCPO (FiniteFirst.approxS FF)))
  approxS-sup≈μFlow ωCPO FF =
    ( K.supω-mono approxS≤iter
    , K.supω-mono iter≤approxS
    )
    where
      module K = Kleene {CP = CP} ωCPO
      open FiniteFirst FF using (approxS)
      open GuardedClosure GC renaming (Flow to F)

      approxS≤iter : ∀ n → _⊑_ (approxS n) (K.iter F n)
      approxS≤iter n rewrite approxS≡iter-Flow ωCPO FF n = ConPreorder.refl CP

      iter≤approxS : ∀ n → _⊑_ (K.iter F n) (approxS n)
      iter≤approxS n rewrite LogOS.Prelude.sym (approxS≡iter-Flow ωCPO FF n) = ConPreorder.refl CP

  Th*-as-μFlow
    : (ωCPO : OmegaCPO CP)
      (FF   : FiniteFirst CP GC ωCPO)
    → (_⊑_ (GuardedClosure.Th* GC)
           (let module K = Kleene {CP = CP} ωCPO
                open GuardedClosure GC renaming (Flow to F)
            in K.μ F))
      ×
      (_⊑_ (let module K = Kleene {CP = CP} ωCPO
                open GuardedClosure GC renaming (Flow to F)
            in K.μ F)
           (GuardedClosure.Th* GC))
  Th*-as-μFlow ωCPO FF =
    let
      th≤sup , sup≤th = Th*-as-sup ωCPO FF
      sup≤μ  , μ≤sup  = approxS-sup≈μFlow ωCPO FF
    in
    ( ConPreorder.trans CP th≤sup sup≤μ
    , ConPreorder.trans CP μ≤sup sup≤th
    )

  -- Convenience: name the Kleene μ(Flow) and package the above as a single `≈CP`.

  μFlow : (ωCPO : OmegaCPO CP) → Con
  μFlow ωCPO =
    let module K = Kleene {CP = CP} ωCPO
    in K.μ (GuardedClosure.Flow GC)

  Th*≈μFlow
    : (ωCPO : OmegaCPO CP)
      (FF   : FiniteFirst CP GC ωCPO)
    → _≈CP_ CP (GuardedClosure.Th* GC) (μFlow ωCPO)
  Th*≈μFlow ωCPO FF = Th*-as-μFlow ωCPO FF

  Th*≤μFlow
    : (ωCPO : OmegaCPO CP)
      (FF   : FiniteFirst CP GC ωCPO)
    → _⊑_ (GuardedClosure.Th* GC) (μFlow ωCPO)
  Th*≤μFlow ωCPO FF = fst (Th*-as-μFlow ωCPO FF)

  μFlow≤Th*
    : (ωCPO : OmegaCPO CP)
      (FF   : FiniteFirst CP GC ωCPO)
    → _⊑_ (μFlow ωCPO) (GuardedClosure.Th* GC)
  μFlow≤Th* ωCPO FF = snd (Th*-as-μFlow ωCPO FF)

  -- -------------------------------------------------------------------------
  -- Assumption bundle: ωCPO + FiniteFirst for a guarded closure.
  -- -------------------------------------------------------------------------
  --
  -- This is a lightweight “domain-theory kit” that makes theorem statements
  -- read like their intended meaning: “under ωCPO + finite-first, we can talk
  -- about Kleene μ and relate it to the distinguished `Th*`.”

  record MuData : Set (lsuc ℓ) where
    field
      ωCPO : OmegaCPO CP
      FF   : FiniteFirst CP GC ωCPO

  Th*≈μFlowᵈ
    : (D : MuData)
    → _≈CP_ CP (GuardedClosure.Th* GC) (μFlow (MuData.ωCPO D))
  Th*≈μFlowᵈ D = Th*≈μFlow (MuData.ωCPO D) (MuData.FF D)

  Th*≤μFlowᵈ
    : (D : MuData)
    → _⊑_ (GuardedClosure.Th* GC) (μFlow (MuData.ωCPO D))
  Th*≤μFlowᵈ D = Th*≤μFlow (MuData.ωCPO D) (MuData.FF D)

  μFlow≤Th*ᵈ
    : (D : MuData)
    → _⊑_ (μFlow (MuData.ωCPO D)) (GuardedClosure.Th* GC)
  μFlow≤Th*ᵈ D = μFlow≤Th* (MuData.ωCPO D) (MuData.FF D)
