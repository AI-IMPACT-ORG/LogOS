{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.SatMor where

-- Satisfaction morphisms (generic):
-- a map on contexts and constraints that preserves+reflects satisfaction.
--
-- This is the missing “glue” to make ports/adapters compose across *changing*
-- logics, not just between presentations of the same satisfaction relation.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Ports.Semantic.PresentationCore using (SatSystem; satSystem)

-- Convenience aliases for the ubiquitous "no-context" refinements.
Ctx₀ : Set
Ctx₀ = ⊤ {ℓ = lzero}

record SatMor
  {ℓCtx₁ ℓCon₁ ℓSat₁ ℓCtx₂ ℓCon₂ ℓSat₂ : Level}
  (S₁ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₁} {ℓSat = ℓSat₁})
  (S₂ : SatSystem {ℓCtx = ℓCtx₂} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂})
  : Set (lsuc (ℓCtx₁ ⊔ ℓCon₁ ⊔ ℓSat₁ ⊔ ℓCtx₂ ⊔ ℓCon₂ ⊔ ℓSat₂)) where
  open SatSystem S₁ renaming (Ctx to Ctx₁; Con to Con₁; Sat to Sat₁)
  open SatSystem S₂ renaming (Ctx to Ctx₂; Con to Con₂; Sat to Sat₂)
  field
    mapCtx : Ctx₁ → Ctx₂
    mapCon : Con₁ → Con₂
    sat-↔  : ∀ p c → Sat₁ p c ↔ Sat₂ (mapCtx p) (mapCon c)

  -- Projections (make the two directions explicit).
  --
  -- Many “translation” interfaces are one-way (soundness only). In LogOS,
  -- `SatMor` is *conservative*: it preserves and reflects satisfaction.
  sat→ : ∀ p c → Sat₁ p c → Sat₂ (mapCtx p) (mapCon c)
  sat→ p c = Prop.to (sat-↔ p c)

  sat← : ∀ p c → Sat₂ (mapCtx p) (mapCon c) → Sat₁ p c
  sat← p c = Prop.from (sat-↔ p c)

  -- Target satisfaction pulled back along `mapCtx`.
  Sat₂↑ : Ctx₁ → Con₂ → Set ℓSat₂
  Sat₂↑ p c = Sat₂ (mapCtx p) c

  private
    S₂↑ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂}
    S₂↑ = satSystem Ctx₁ Con₂ Sat₂↑

  -- Induced observational relations (keep names explicit at call sites).
  ObsEq₁ : Con₁ → Con₁ → Set (ℓCtx₁ ⊔ ℓSat₁)
  ObsEq₁ = SatSystem.ObsEq S₁

  ObsLe₁ : Con₁ → Con₁ → Set (ℓCtx₁ ⊔ ℓSat₁)
  ObsLe₁ = SatSystem.ObsLe S₁

  Obs≈₁ : Con₁ → Con₁ → Set (ℓCtx₁ ⊔ ℓSat₁)
  Obs≈₁ = SatSystem.Obs≈ S₁

  ObsEq₁↔Obs≈₁ : ∀ {c d} → ObsEq₁ c d ↔ Obs≈₁ c d
  ObsEq₁↔Obs≈₁ {c} {d} = SatSystem.ObsEq↔Obs≈ S₁ {x = c} {y = d}

  ObsEq₂↑ : Con₂ → Con₂ → Set (ℓCtx₁ ⊔ ℓSat₂)
  ObsEq₂↑ = Prop.ObsEqOn Sat₂↑

  ObsLe₂↑ : Con₂ → Con₂ → Set (ℓCtx₁ ⊔ ℓSat₂)
  ObsLe₂↑ = Prop.ObsLeOn Sat₂↑

  Obs≈₂↑ : Con₂ → Con₂ → Set (ℓCtx₁ ⊔ ℓSat₂)
  Obs≈₂↑ = SatSystem.Obs≈ S₂↑

  ObsEq₂↑↔Obs≈₂↑ : ∀ {c d} → ObsEq₂↑ c d ↔ Obs≈₂↑ c d
  ObsEq₂↑↔Obs≈₂↑ {c} {d} = SatSystem.ObsEq↔Obs≈ S₂↑ {x = c} {y = d}

  -- `mapCon` respects the observational equality induced by satisfaction,
  -- relative to the pulled-back target observers.
  mapCon-respects-ObsEq
    : ∀ {c d}
    → ObsEq₁ c d
    → ObsEq₂↑ (mapCon c) (mapCon d)
  mapCon-respects-ObsEq {c} {d} eq p =
    Prop.↔-trans
      (Prop.↔-sym (sat-↔ p c))
      (Prop.↔-trans (eq p) (sat-↔ p d))

  -- Derived: `mapCon` also respects mutual refinement (the canonical `≈`-shaped form).
  mapCon-respects-Obs≈
    : ∀ {c d}
    → Obs≈₁ c d
    → Obs≈₂↑ (mapCon c) (mapCon d)
  mapCon-respects-Obs≈ {c} {d} eq≈ =
    Prop.to ObsEq₂↑↔Obs≈₂↑
      (mapCon-respects-ObsEq (Prop.from ObsEq₁↔Obs≈₁ eq≈))

  -- `mapCon` preserves the observational preorder (soundness direction) after
  -- pulling back the target satisfaction along `mapCtx`.
  mapCon-preserves-ObsLe
    : ∀ {c d}
    → ObsLe₁ c d
    → ObsLe₂↑ (mapCon c) (mapCon d)
  mapCon-preserves-ObsLe {c} {d} le p sat₂ =
    sat→ p d (le p (sat← p c sat₂))

record SatHom
  {ℓCtx₁ ℓCon₁ ℓSat₁ ℓCtx₂ ℓCon₂ ℓSat₂ : Level}
  (S₁ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₁} {ℓSat = ℓSat₁})
  (S₂ : SatSystem {ℓCtx = ℓCtx₂} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂})
  : Set (lsuc (ℓCtx₁ ⊔ ℓCon₁ ⊔ ℓSat₁ ⊔ ℓCtx₂ ⊔ ℓCon₂ ⊔ ℓSat₂)) where
  open SatSystem S₁ renaming (Ctx to Ctx₁; Con to Con₁; Sat to Sat₁)
  open SatSystem S₂ renaming (Ctx to Ctx₂; Con to Con₂; Sat to Sat₂)
  field
    mapCtx : Ctx₁ → Ctx₂
    mapCon : Con₁ → Con₂
    sat-→  : ∀ p c → Sat₁ p c → Sat₂ (mapCtx p) (mapCon c)

  -- Target satisfaction pulled back along `mapCtx`.
  Sat₂↑ : Ctx₁ → Con₂ → Set ℓSat₂
  Sat₂↑ p c = Sat₂ (mapCtx p) c

record SatRefinement
  {ℓCtx ℓCon ℓSat₁ ℓSat₂ : Level}
  (Ctx : Set ℓCtx)
  (Con : Set ℓCon)
  (Sat₁ : Ctx → Con → Set ℓSat₁)
  (Sat₂ : Ctx → Con → Set ℓSat₂)
  : Set (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓSat₁ ⊔ ℓSat₂)) where
  field
    sat-→ : ∀ p c → Sat₁ p c → Sat₂ p c

SatRefinement₀
  : ∀ {ℓCon ℓSat₁ ℓSat₂ : Level}
    (Con : Set ℓCon)
    (Sat₁ : Ctx₀ → Con → Set ℓSat₁)
    (Sat₂ : Ctx₀ → Con → Set ℓSat₂)
  → Set (lsuc (ℓCon ⊔ ℓSat₁ ⊔ ℓSat₂))
SatRefinement₀ Con Sat₁ Sat₂ =
  SatRefinement Ctx₀ Con Sat₁ Sat₂

sat-→₀
  : ∀ {ℓCon ℓSat₁ ℓSat₂}
    {Con : Set ℓCon}
    {Sat₁ : Ctx₀ → Con → Set ℓSat₁}
    {Sat₂ : Ctx₀ → Con → Set ℓSat₂}
  → SatRefinement₀ Con Sat₁ Sat₂
  → ∀ c → Sat₁ tt c → Sat₂ tt c
sat-→₀ r c sat = SatRefinement.sat-→ r tt c sat

satHom-fromSatRefinement
  : ∀ {ℓCtx ℓCon ℓSat₁ ℓSat₂}
    {Ctx : Set ℓCtx} {Con : Set ℓCon}
    {Sat₁ : Ctx → Con → Set ℓSat₁}
    {Sat₂ : Ctx → Con → Set ℓSat₂}
  → SatRefinement Ctx Con Sat₁ Sat₂
  → SatHom (satSystem Ctx Con Sat₁)
           (satSystem Ctx Con Sat₂)
satHom-fromSatRefinement r =
  record
    { mapCtx = λ x → x
    ; mapCon = λ x → x
    ; sat-→  = SatRefinement.sat-→ r
    }

pullbackSatRefinement
  : ∀ {ℓCtx₁ ℓCon₁ ℓSat₁ ℓCtx₂ ℓCon₂ ℓSat₂ ℓSat₂′}
    {Ctx₁ : Set ℓCtx₁} {Con₁ : Set ℓCon₁} {Sat₁ : Ctx₁ → Con₁ → Set ℓSat₁}
    {Ctx₂ : Set ℓCtx₂} {Con₂ : Set ℓCon₂} {Sat₂ : Ctx₂ → Con₂ → Set ℓSat₂}
    {Sat₂′ : Ctx₂ → Con₂ → Set ℓSat₂′}
  → (m : SatHom (satSystem Ctx₁ Con₁ Sat₁)
                (satSystem Ctx₂ Con₂ Sat₂))
  → SatRefinement Ctx₂ Con₂ Sat₂ Sat₂′
  → SatRefinement Ctx₁ Con₁ Sat₁ (λ p c → Sat₂′ (SatHom.mapCtx m p) (SatHom.mapCon m c))
pullbackSatRefinement m r =
  record
    { sat-→ = λ p c sat →
        SatRefinement.sat-→ r (SatHom.mapCtx m p) (SatHom.mapCon m c)
          (SatHom.sat-→ m p c sat)
    }

idSatRefinement
  : ∀ {ℓCtx ℓCon ℓSat : Level}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    (Sat : Ctx → Con → Set ℓSat)
  → SatRefinement Ctx Con Sat Sat
idSatRefinement _ =
  record
    { sat-→  = λ _ _ sat → sat
    }

composeSatRefinement
  : ∀ {ℓCtx ℓCon ℓSat₁ ℓSat₂ ℓSat₃ : Level}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    {Sat₁ : Ctx → Con → Set ℓSat₁}
    {Sat₂ : Ctx → Con → Set ℓSat₂}
    {Sat₃ : Ctx → Con → Set ℓSat₃}
  → SatRefinement Ctx Con Sat₁ Sat₂
  → SatRefinement Ctx Con Sat₂ Sat₃
  → SatRefinement Ctx Con Sat₁ Sat₃
composeSatRefinement r₁ r₂ =
  record
    { sat-→ = λ p c sat → SatRefinement.sat-→ r₂ p c (SatRefinement.sat-→ r₁ p c sat)
    }

satHom-fromSatMor
  : ∀ {ℓCtx₁ ℓCon₁ ℓSat₁ ℓCtx₂ ℓCon₂ ℓSat₂}
    {Ctx₁ : Set ℓCtx₁} {Con₁ : Set ℓCon₁} {Sat₁ : Ctx₁ → Con₁ → Set ℓSat₁}
    {Ctx₂ : Set ℓCtx₂} {Con₂ : Set ℓCon₂} {Sat₂ : Ctx₂ → Con₂ → Set ℓSat₂}
  → SatMor (satSystem Ctx₁ Con₁ Sat₁)
           (satSystem Ctx₂ Con₂ Sat₂)
  → SatHom (satSystem Ctx₁ Con₁ Sat₁)
           (satSystem Ctx₂ Con₂ Sat₂)
satHom-fromSatMor m =
  record
    { mapCtx = SatMor.mapCtx m
    ; mapCon = SatMor.mapCon m
    ; sat-→  = SatMor.sat→ m
    }

idSatMor
  : ∀ {ℓCtx ℓCon ℓSat : Level}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    (Sat : Ctx → Con → Set ℓSat)
  → SatMor (satSystem Ctx Con Sat)
           (satSystem Ctx Con Sat)
idSatMor Sat =
  record
    { mapCtx = λ x → x
    ; mapCon = λ x → x
    ; sat-↔  = λ _ _ → Prop.↔-refl
    }

idSatMorS
  : ∀ {ℓCtx ℓCon ℓSat : Level}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
  → SatMor S S
idSatMorS =
  record
    { mapCtx = λ x → x
    ; mapCon = λ x → x
    ; sat-↔  = λ _ _ → Prop.↔-refl
    }

idSatHom
  : ∀ {ℓCtx ℓCon ℓSat : Level}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    (Sat : Ctx → Con → Set ℓSat)
  → SatHom (satSystem Ctx Con Sat)
           (satSystem Ctx Con Sat)
idSatHom Sat =
  record
    { mapCtx = λ x → x
    ; mapCon = λ x → x
    ; sat-→  = λ _ _ sat → sat
    }

idSatHomS
  : ∀ {ℓCtx ℓCon ℓSat : Level}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
  → SatHom S S
idSatHomS =
  record
    { mapCtx = λ x → x
    ; mapCon = λ x → x
    ; sat-→  = λ _ _ sat → sat
    }

composeSatMor
  : ∀ {ℓCtx₁ ℓCon₁ ℓSat₁ ℓCtx₂ ℓCon₂ ℓSat₂ ℓCtx₃ ℓCon₃ ℓSat₃ : Level}
    {S₁ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₁} {ℓSat = ℓSat₁}}
    {S₂ : SatSystem {ℓCtx = ℓCtx₂} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂}}
    {S₃ : SatSystem {ℓCtx = ℓCtx₃} {ℓCon = ℓCon₃} {ℓSat = ℓSat₃}}
  → SatMor S₁ S₂
  → SatMor S₂ S₃
  → SatMor S₁ S₃
composeSatMor m₁ m₂ =
  record
    { mapCtx = λ p → SatMor.mapCtx m₂ (SatMor.mapCtx m₁ p)
    ; mapCon = λ c → SatMor.mapCon m₂ (SatMor.mapCon m₁ c)
    ; sat-↔  = λ p c →
        Prop.↔-trans
          (SatMor.sat-↔ m₁ p c)
          (SatMor.sat-↔ m₂ (SatMor.mapCtx m₁ p) (SatMor.mapCon m₁ c))
    }

composeSatHom
  : ∀ {ℓCtx₁ ℓCon₁ ℓSat₁ ℓCtx₂ ℓCon₂ ℓSat₂ ℓCtx₃ ℓCon₃ ℓSat₃ : Level}
    {S₁ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₁} {ℓSat = ℓSat₁}}
    {S₂ : SatSystem {ℓCtx = ℓCtx₂} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂}}
    {S₃ : SatSystem {ℓCtx = ℓCtx₃} {ℓCon = ℓCon₃} {ℓSat = ℓSat₃}}
  → SatHom S₁ S₂
  → SatHom S₂ S₃
  → SatHom S₁ S₃
composeSatHom m₁ m₂ =
  record
    { mapCtx = λ p → SatHom.mapCtx m₂ (SatHom.mapCtx m₁ p)
    ; mapCon = λ c → SatHom.mapCon m₂ (SatHom.mapCon m₁ c)
    ; sat-→  = λ p c sat →
        SatHom.sat-→ m₂ (SatHom.mapCtx m₁ p) (SatHom.mapCon m₁ c)
          (SatHom.sat-→ m₁ p c sat)
    }
