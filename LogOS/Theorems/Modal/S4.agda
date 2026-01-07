{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Modal.S4 where

-- A very small, very general “S4 modality” package for LogOS:
-- a monotone, inflationary, idempotent-lax endomap on a preorder.

open import LogOS.Prelude

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPoset)
import LogOS.Minimal.Truth as Truth

open import LogOS.Theorems.Reflection.Projector using (Projector)

record S4Modality {ℓ : Level} (CP : ConPoset ℓ) : Set (lsuc ℓ) where
  open ConPoset CP
  field
    □        : Con → Con
    mono     : ∀ {c c'} → _⊑_ c c' → _⊑_ (□ c) (□ c')
    infl     : ∀ c → _⊑_ c (□ c)          -- T axiom
    idemp-lax : ∀ c → _⊑_ (□ (□ c)) (□ c) -- 4 axiom (lax)

open S4Modality public

-- Idempotence “both ways” is derivable once monotonicity + inflation are present.

idemp-infl
  : ∀ {ℓ} {CP : ConPoset ℓ} (M : S4Modality CP)
    (c : ConPoset.Con CP)
  → ConPoset._⊑_ CP (□ M c) (□ M (□ M c))
idemp-infl {CP = CP} M c =
  let open ConPoset CP
  in mono M (infl M c)

-- A grade-indexed closure yields an S4 modality at the saturation grade `sat`.

fromGradedSat
  : ∀ {ℓ} {Q : QAdapter ℓ} {CP : ConPoset ℓ}
    (G : Truth.GuardedCore.GradedClosure Q CP)
  → S4Modality CP
fromGradedSat {CP = CP} G =
  let open ConPoset CP
      open Truth.GuardedCore.GradedClosure G renaming (mono to monoFlow)
  in record
    { □        = Flow sat
    ; mono     = monoFlow
    ; infl     = infl-sat
    ; idemp-lax = idemp-sat
    }

-- Any grade can be promoted to saturation (general grade-shift lemma).

promoteToSat
  : ∀ {ℓ} {Q : QAdapter ℓ} {CP : ConPoset ℓ}
    (G : Truth.GuardedCore.GradedClosure Q CP)
  → ∀ g c
  → ConPoset._⊑_ CP
      (Truth.GuardedCore.GradedClosure.Flow G g c)
      (Truth.GuardedCore.GradedClosure.Flow G (Truth.GuardedCore.GradedClosure.sat G) c)
promoteToSat {CP = CP} G g c =
  let open ConPoset CP
      open Truth.GuardedCore.GradedClosure G
  in mono-grade (sat-top g) c

-- Any (unguarded) closure step yields an S4 modality on the same constraint preorder.

fromGuardedClosure
  : ∀ {ℓ} {CP : ConPoset ℓ}
    (G : Truth.GuardedCore.GuardedClosure CP)
  → S4Modality CP
fromGuardedClosure {CP = CP} G =
  let open ConPoset CP
      open Truth.GuardedCore.GuardedClosure G renaming (mono to monoFlow; infl to inflFlow; idemp-lax to idempFlow)
  in record
    { □        = Flow
    ; mono     = monoFlow
    ; infl     = inflFlow
    ; idemp-lax = idempFlow
    }

-- The distinguished fixed point witness is a modal fixed point (up to mutual refinement).

Th*-fixed-s4
  : ∀ {ℓ} {CP : ConPoset ℓ}
    (G : Truth.GuardedCore.GuardedClosure CP)
  → let M = fromGuardedClosure G in
    ConPoset._⊑_ CP (Truth.GuardedCore.GuardedClosure.Th* G) (□ M (Truth.GuardedCore.GuardedClosure.Th* G))
    ×
    ConPoset._⊑_ CP (□ M (Truth.GuardedCore.GuardedClosure.Th* G)) (Truth.GuardedCore.GuardedClosure.Th* G)
Th*-fixed-s4 {CP = CP} G =
  let open Truth.GuardedCore.GuardedClosure G
  in Th*-fixed

-- Forgetful view: any S4 modality yields a (lax) projector by dropping monotonicity.

toProjector : ∀ {ℓ} {CP : ConPoset ℓ} → S4Modality CP → Projector CP
toProjector M = record
  { P = □ M
  ; infl = infl M
  ; idemp-lax = idemp-lax M
  }
