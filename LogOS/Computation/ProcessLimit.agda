{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.ProcessLimit where

-- Process-level “limit semantics” via Kleene μ on ωCPO state preorders.
--
-- The key idea is to model “execution for arbitrarily many steps from a given
-- initial state c” as the Kleene μ of `Step`, but *in the slice preorder above c*.
-- This makes the construction:
-- - uses `c` as a local bottom (rather than the ambient `⊥`),
-- - compatible with lax morphisms (⊑) via μ-fusion,
-- - and assumption-transparent (ωCPO + inflationarity/continuity are explicit).

open import LogOS.Prelude

open import LogOS.Minimal.Con using (ConPreorder; MonoOn)
import LogOS.Minimal.Truth as Truth

open import LogOS.Computation.SchemeCategory using (Process; ProcessHomLax; StepMono)
import LogOS.Minimal.MuFusion as MuFusion

-- --------------------------------------------------------------------------
-- Slice preorder above a chosen base element.

module Slice
  {ℓ : Level}
  (CP : ConPreorder ℓ)
  (c₀ : ConPreorder.Con CP)
  where

  open ConPreorder CP renaming (Con to Con₀; _⊑_ to _⊑₀_; refl to refl₀; trans to trans₀)

  Con : Set ℓ
  Con = Σ Con₀ (λ c → c₀ ⊑₀ c)

  infix 4 _⊑_
  _⊑_ : Con → Con → Set ℓ
  x ⊑ y = proj₁ x ⊑₀ proj₁ y

  CP↑ : ConPreorder ℓ
  CP↑ = record
    { Con  = Con
    ; _⊑_  = _⊑_
    ; refl = λ {c} → refl₀ {c = proj₁ c}
    ; trans = λ {a} {b} {c} → trans₀ {a = proj₁ a} {b = proj₁ b} {c = proj₁ c}
    }

  forget : Con → Con₀
  forget = proj₁

  base≤ : ∀ {x} → c₀ ⊑₀ forget x
  base≤ {x} = proj₂ x

  forget≤ : ∀ {x y} → ConPreorder._⊑_ CP↑ x y → forget x ⊑₀ forget y
  forget≤ x≤y = x≤y

  module GC = Truth.GuardedCore {ℓ = ℓ}
  open GC

  -- Lift an ωCPO structure on `CP` to the slice preorder `CP↑`.
  sliceOmegaCPO
    : OmegaCPO CP
    → OmegaCPO CP↑
  sliceOmegaCPO ω = record
    { ⊥     = c₀ , refl₀ {c = c₀}
    ; isBot = λ c → proj₂ c
    ; supω  = λ f →
        ( supω₀ (λ n → proj₁ (f n))
        , c₀≤sup f
        )
    ; ub    = λ f n → ub₀ (λ k → proj₁ (f k)) n
    ; least = λ f x ubf →
        least₀ (λ k → proj₁ (f k)) (proj₁ x) ubf
    }
    where
      open OmegaCPO ω renaming (supω to supω₀; ub to ub₀; least to least₀)

      c₀≤sup : (f : ℕ → Con) → c₀ ⊑₀ supω₀ (λ n → proj₁ (f n))
      c₀≤sup f =
        trans₀ (proj₂ (f zero)) (ub₀ (λ n → proj₁ (f n)) zero)

  -- Lift an endomap `Step : Con₀ → Con₀` to the slice, assuming inflationarity.
  Step↑
    : (Step : Con₀ → Con₀)
    → (inflStep : ∀ x → x ⊑₀ Step x)
    → Con → Con
  Step↑ Step inflStep (x , c₀≤x) = Step x , trans₀ c₀≤x (inflStep x)

-- --------------------------------------------------------------------------
-- Process-level limit semantics (“run∞”) and transport along lax morphisms.

module For
  {ℓO ℓC ℓQ : Level}
  {Output : Set ℓO}
  (P : Process {ℓO} {ℓC} {ℓQ} Output)
  where

  open Process P

  module GC = Truth.GuardedCore {ℓ = ℓC}

  record LimitData : Set (lsuc ℓC) where
    field
      ωCPO     : GC.OmegaCPO CP
      stepInfl : ∀ c → c ⊑ Step c
      stepMono : StepMono P
      stepSC   : let module K = GC.Kleene ωCPO in K.ScottContinuous Step

  open LimitData public

  -- Infinite-run / limit semantics from an initial state `c`.
  run∞ : (D : LimitData) → Con → Con
  run∞ D c =
    let
      module S = Slice CP c
      ω↑ : GC.OmegaCPO S.CP↑
      ω↑ = S.sliceOmegaCPO (LimitData.ωCPO D)

      module K = GC.Kleene ω↑

      Step↑ : S.Con → S.Con
      Step↑ = S.Step↑ Step (LimitData.stepInfl D)
    in
    proj₁ (K.μ Step↑)

  -- The limit state is a (lax) fixed point of `Step`.
  run∞-fixed
    : (D : LimitData)
    → ∀ c
    → (run∞ D c ⊑ Step (run∞ D c))
      ×
      (Step (run∞ D c) ⊑ run∞ D c)
  run∞-fixed D c = (μ≤Stepμ , Stepμ≤μ)
    where
      module S = Slice CP c
      ω↑ : GC.OmegaCPO S.CP↑
      ω↑ = S.sliceOmegaCPO (LimitData.ωCPO D)

      module K = GC.Kleene ω↑

      Step↑ : S.Con → S.Con
      Step↑ = S.Step↑ Step (LimitData.stepInfl D)

      monoStep↑ : MonoOn S.CP↑ Step↑
      monoStep↑ {c = (x , c≤x)} {d = (y , c≤y)} x≤y =
        LimitData.stepMono D {c = x} {d = y}
          (S.forget≤ {x = (x , c≤x)} {y = (y , c≤y)} x≤y)

      SCStep↑ : K.ScottContinuous Step↑
      SCStep↑ =
        let
          module K₀ = GC.Kleene (LimitData.ωCPO D)
          open K₀.ScottContinuous (LimitData.stepSC D)
        in
        record
          { cont-ω = λ f mono-chain →
              cont-ω (λ n → proj₁ (f n)) mono-chain
          }

      inflStep↑ : ∀ s → ConPreorder._⊑_ S.CP↑ s (Step↑ s)
      inflStep↑ (x , _) = LimitData.stepInfl D x

      μ≤Stepμ : run∞ D c ⊑ Step (run∞ D c)
      μ≤Stepμ =
        let
          μ≤ : ConPreorder._⊑_ S.CP↑ (K.μ Step↑) (Step↑ (K.μ Step↑))
          μ≤ = K.μ-unfold-left Step↑ (λ {c} {d} p → monoStep↑ {c = c} {d = d} p)
        in
        S.forget≤ {x = K.μ Step↑} {y = Step↑ (K.μ Step↑)} μ≤

      Stepμ≤μ : Step (run∞ D c) ⊑ run∞ D c
      Stepμ≤μ =
        let
          le : ConPreorder._⊑_ S.CP↑ (Step↑ (K.μ Step↑)) (K.μ Step↑)
          le = K.μ-unfold-right-infl Step↑ SCStep↑ inflStep↑
        in
        S.forget≤ {x = Step↑ (K.μ Step↑)} {y = K.μ Step↑} le

module TransportLax
  {ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂ : Level}
  {Output : Set ℓO}
  {P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output}
  {P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output}
  (D₁ : For.LimitData P₁)
  (D₂ : For.LimitData P₂)
  (h  : ProcessHomLax P₁ P₂)
  where

  open Process P₁ renaming (Con to Con₁; _⊑_ to _⊑₁_; Step to Step₁)
  open Process P₂ renaming (Con to Con₂; _⊑_ to _⊑₂_; Step to Step₂)

  module GC₁ = Truth.GuardedCore {ℓ = ℓC₁}
  module GC₂ = Truth.GuardedCore {ℓ = ℓC₂}

  map : Con₁ → Con₂
  map = ProcessHomLax.map h

  -- Additional assumption: ω-continuity of the state map.
  cont-map
    : Set (ℓC₁ ⊔ ℓC₂)
  cont-map =
    let
      ω₁ = For.LimitData.ωCPO D₁
      ω₂ = For.LimitData.ωCPO D₂
    in
    ∀ (f : ℕ → Con₁)
      (mono-chain : ∀ n → _⊑₁_ (f n) (f (suc n)))
    → _⊑₂_
        (map (GC₁.OmegaCPO.supω ω₁ f))
        (GC₂.OmegaCPO.supω ω₂ (λ n → map (f n)))

  -- μ-level transport of “infinite run” under a lax process morphism.
  run∞-map≤
    : cont-map
    → ∀ c
    → map (For.run∞ P₁ D₁ c)
      ⊑₂
      For.run∞ P₂ D₂ (map c)
  run∞-map≤ cont c =
    S₂.forget≤
      {x = map↑ (GC₁.Kleene.μ ω↑₁ Step↑₁)}
      {y = GC₂.Kleene.μ ω↑₂ Step↑₂}
      leμ
    where
      module S₁ = Slice (Process.CP P₁) c
      module S₂ = Slice (Process.CP P₂) (map c)

      ω↑₁ : GC₁.OmegaCPO S₁.CP↑
      ω↑₁ = S₁.sliceOmegaCPO (For.LimitData.ωCPO D₁)

      ω↑₂ : GC₂.OmegaCPO S₂.CP↑
      ω↑₂ = S₂.sliceOmegaCPO (For.LimitData.ωCPO D₂)

      Step↑₁ : S₁.Con → S₁.Con
      Step↑₁ = S₁.Step↑ Step₁ (For.LimitData.stepInfl D₁)

      Step↑₂ : S₂.Con → S₂.Con
      Step↑₂ = S₂.Step↑ Step₂ (For.LimitData.stepInfl D₂)

      map↑ : S₁.Con → S₂.Con
      map↑ (x , c≤x) = map x , ProcessHomLax.mono h c≤x

      module MF = MuFusion.For S₁.CP↑ S₂.CP↑

      M : MF.OmegaCPOMap ω↑₁ ω↑₂ map↑
      M =
        record
          { mono-map = λ {x} {y} x≤y → ProcessHomLax.mono h x≤y
          ; strict⊥  = Process.refl P₂
          ; cont-ω   = λ f mono-chain → cont (λ n → proj₁ (f n)) mono-chain
          }

      monoStep↑₂ : MonoOn S₂.CP↑ Step↑₂
      monoStep↑₂ {c = (x , mc≤x)} {d = (y , mc≤y)} x≤y =
        For.LimitData.stepMono D₂ {c = x} {d = y}
          (S₂.forget≤ {x = (x , mc≤x)} {y = (y , mc≤y)} x≤y)

      inflStep↑₁ : ∀ s → ConPreorder._⊑_ S₁.CP↑ s (Step↑₁ s)
      inflStep↑₁ (x , _) = For.LimitData.stepInfl D₁ x

      comm : ∀ s → ConPreorder._⊑_ S₂.CP↑ (map↑ (Step↑₁ s)) (Step↑₂ (map↑ s))
      comm (x , _) = ProcessHomLax.step-comm≤ h x

      leμ : ConPreorder._⊑_ S₂.CP↑ (map↑ (GC₁.Kleene.μ ω↑₁ Step↑₁)) (GC₂.Kleene.μ ω↑₂ Step↑₂)
      leμ =
        MF.μ-fusion≤ M Step↑₁ Step↑₂
          (λ {c} {d} p → monoStep↑₂ {c = c} {d = d} p)
          inflStep↑₁
          comm
