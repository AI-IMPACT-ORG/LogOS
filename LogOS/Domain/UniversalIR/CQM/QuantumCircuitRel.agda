{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.CQM.QuantumCircuitRel where

-- A minimal “categorical QM” bridge for the explicit (basis-state) circuit layer:
-- interpret a gate program as a morphism in the Rel model (relations).
--
-- This is deliberately lightweight:
-- - we use the Rel dagger-SMC from `LogOS.Theorems.Meta.CQM`
-- - we interpret a gate-list by its executable action on `Wires`
-- - we expose the key functorial law: concatenation corresponds to composition

open import LogOS.Prelude

open import Data.List using (List; []; _∷_; _++_)

open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.Theorems.Meta.CQM using (Rel; _≈Rel_; DaggerSMC; RelDaggerSMC)
open import LogOS.Domain.UniversalIR.Core.QuantumCircuit
  using (Wires; flipAt; applyCNOT; applyTOFF)

-- Unitary-ish gate fragment (no branching/measurement).
-- (This is the fragment used by the dagger story.)

data Gate : Set where
  GNOP  : Gate
  GX    : ℕ → Gate
  GCNOT : ℕ → ℕ → Gate
  GTOFF : ℕ → ℕ → ℕ → Gate

applyGate : Gate → Wires → Wires
applyGate GNOP ws = ws
applyGate (GX i) ws = flipAt i ws
applyGate (GCNOT c t) ws = applyCNOT c t ws
applyGate (GTOFF a b t) ws = applyTOFF a b t ws

runGates : List Gate → Wires → Wires
runGates []       ws = ws
runGates (g ∷ gs) ws = runGates gs (applyGate g ws)

runGates-++ : ∀ gs₁ gs₂ ws → runGates (gs₁ ++ gs₂) ws ≡ runGates gs₂ (runGates gs₁ ws)
runGates-++ []       gs₂ ws = refl
runGates-++ (g ∷ gs) gs₂ ws = runGates-++ gs gs₂ (applyGate g ws)

-- Denotation into Rel: graph of the executable function.

denote : List Gate → Rel {ℓR = lzero} Wires Wires
denote gs ws ws' = ws' ≡ runGates gs ws

-- Functoriality (sequential): denote (gs₁ ++ gs₂) = denote gs₂ ∘ denote gs₁.
-- We state this using the concrete composition of the Rel DaggerSMC instance.

denote-++ : ∀ gs₁ gs₂ → denote (gs₁ ++ gs₂) ≈Rel (DaggerSMC._∘_ RelDaggerSMC (denote gs₂) (denote gs₁))
denote-++ gs₁ gs₂ ws ws' = intro to from
  where
    to
      : denote (gs₁ ++ gs₂) ws ws'
      → DaggerSMC._∘_ RelDaggerSMC (denote gs₂) (denote gs₁) ws ws'
    to eq =
      (runGates gs₁ ws , (refl , trans eq (runGates-++ gs₁ gs₂ ws)))

    from
      : DaggerSMC._∘_ RelDaggerSMC (denote gs₂) (denote gs₁) ws ws'
      → denote (gs₁ ++ gs₂) ws ws'
    from (m , (mEq , ws'Eq)) =
      trans
        (trans ws'Eq (cong (runGates gs₂) mEq))
        (sym (runGates-++ gs₁ gs₂ ws))

-- Dagger: for deterministic relations (graphs), dagger is just argument swap.

denote† : List Gate → Rel {ℓR = lzero} Wires Wires
denote† gs ws ws' = denote gs ws' ws

denote-dagger : ∀ gs → denote† gs ≈Rel (DaggerSMC._† RelDaggerSMC (denote gs))
denote-dagger gs ws ws' = intro (λ eq → eq) (λ eq → eq)

-- Monoidal product: independent gate programs on independent wire registers.

denote⊗ : List Gate → List Gate → Rel {ℓR = lzero} (Wires × Wires) (Wires × Wires)
denote⊗ gs₁ gs₂ (ws₁ , ws₂) (ws₁' , ws₂') =
  (ws₁' ≡ runGates gs₁ ws₁) × (ws₂' ≡ runGates gs₂ ws₂)

denote-⊗ : ∀ gs₁ gs₂ → denote⊗ gs₁ gs₂ ≈Rel (DaggerSMC._⊗₁_ RelDaggerSMC (denote gs₁) (denote gs₂))
denote-⊗ gs₁ gs₂ (ws₁ , ws₂) (ws₁' , ws₂') = intro (λ p → p) (λ p → p)
