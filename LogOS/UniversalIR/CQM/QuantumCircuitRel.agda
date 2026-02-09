{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.CQM.QuantumCircuitRel where

-- A minimal “categorical QM” bridge for the explicit (basis-state) circuit layer:
-- interpret a gate program as a morphism in the Rel model (relations).
--
-- This is deliberately lightweight:
-- - we use the Rel dagger-SMC from `LogOS.Theorems.Meta.CQM`
-- - we interpret a gate-list by its executable action on `Wires`
-- - we expose the key functorial law: concatenation corresponds to composition

open import LogOS.Prelude

open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.UniversalIR.Encoding using (length)

open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.Theorems.Meta.CQM using (Rel; _≈Rel_; ObsEqRel; ObsEqRel↔≈Rel; DaggerSMC; RelDaggerSMC)
open import LogOS.UniversalIR.Core.QuantumCircuit
  using
    ( Wires; GateProg; gates; gateProgOf; runGateProg; runGateProg-++
    ; runInstrs; runGates-runInstrs
    ; iterQC; iterQC-gateProg; mkQC; wires; _++g_
    ; AllGateBound; WFCircuit; WFCircuit-gateProg
    )

-- Denotation into Rel: graph of the executable function.

denote : GateProg → Rel {ℓR = lzero} Wires Wires
denote gs ws ws' = ws' ≡ runGateProg gs ws

execRel : GateProg → Rel {ℓR = lzero} Wires Wires
execRel gs ws ws' =
  ws' ≡ wires (iterQC (length (gates gs)) (mkQC 0 (length ws) ws (gateProgOf gs)))

-- Gate denotation agrees with the QC-instruction semantics for gate programs.

denote-runInstrs
  : ∀ gs ws ws' → denote gs ws ws' ↔ ws' ≡ runInstrs (gateProgOf gs) ws
denote-runInstrs gs ws ws' = intro to from
  where
    to : denote gs ws ws' → ws' ≡ runInstrs (gateProgOf gs) ws
    to eq = trans eq (runGates-runInstrs (gates gs) ws)

    from : ws' ≡ runInstrs (gateProgOf gs) ws → denote gs ws ws'
    from eq = trans eq (sym (runGates-runInstrs (gates gs) ws))

denote-iterQC
  : ∀ gs → denote gs ≈Rel execRel gs
denote-iterQC gs =
  _↔_.to ObsEqRel↔≈Rel (λ ws ws' → intro (to ws ws') (from ws ws'))
  where
    to : ∀ ws ws' → denote gs ws ws' → execRel gs ws ws'
    to ws _ eq = trans eq (sym (iterQC-gateProg (gates gs) ws))

    from : ∀ ws ws' → execRel gs ws ws' → denote gs ws ws'
    from ws _ eq = trans eq (iterQC-gateProg (gates gs) ws)

-- Gate programs are well-formed when their indices are in range.

wfGateProg
  : ∀ gs ws
  → AllGateBound (length ws) (gates gs)
  → WFCircuit (mkQC 0 (length ws) ws (gateProgOf gs))
wfGateProg gs ws bounds =
  WFCircuit-gateProg (length ws) (gates gs) ws refl bounds


-- Dagger: for deterministic relations (graphs), dagger is just argument swap.

denote† : GateProg → Rel {ℓR = lzero} Wires Wires
denote† gs ws ws' = denote gs ws' ws

denote-dagger : ∀ gs → denote† gs ≈Rel (DaggerSMC._† RelDaggerSMC (denote gs))
denote-dagger gs =
  _↔_.to ObsEqRel↔≈Rel (λ ws ws' → intro (λ eq → eq) (λ eq → eq))

-- Monoidal product: independent gate programs on independent wire registers.

denote⊗ : GateProg → GateProg → Rel {ℓR = lzero} (Wires × Wires) (Wires × Wires)
denote⊗ gs₁ gs₂ (ws₁ , ws₂) (ws₁' , ws₂') =
  (ws₁' ≡ runGateProg gs₁ ws₁) × (ws₂' ≡ runGateProg gs₂ ws₂)

denote-⊗ : ∀ gs₁ gs₂ → denote⊗ gs₁ gs₂ ≈Rel (DaggerSMC._⊗₁_ RelDaggerSMC (denote gs₁) (denote gs₂))
denote-⊗ gs₁ gs₂ =
  _↔_.to ObsEqRel↔≈Rel (λ _ _ → intro (λ p → p) (λ p → p))

-- Functoriality (sequential): denote (g₁ ++g g₂) = denote g₂ ∘ denote g₁.

denote-++
  : ∀ gs₁ gs₂ → denote (gs₁ ++g gs₂) ≈Rel (DaggerSMC._∘_ RelDaggerSMC (denote gs₂) (denote gs₁))
denote-++ gs₁ gs₂ =
  _↔_.to ObsEqRel↔≈Rel (λ ws ws' → intro (to ws ws') (from ws ws'))
  where
    to
      : ∀ ws ws'
      → denote (gs₁ ++g gs₂) ws ws'
      → DaggerSMC._∘_ RelDaggerSMC (denote gs₂) (denote gs₁) ws ws'
    to ws _ eq =
      (runGateProg gs₁ ws , (refl , trans eq (runGateProg-++ gs₁ gs₂ ws)))

    from
      : ∀ ws ws'
      → DaggerSMC._∘_ RelDaggerSMC (denote gs₂) (denote gs₁) ws ws'
      → denote (gs₁ ++g gs₂) ws ws'
    from ws _ (m , (mEq , ws'Eq)) =
      trans
        (trans ws'Eq (cong (runGateProg gs₂) mEq))
        (sym (runGateProg-++ gs₁ gs₂ ws))
