{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.NumberTheory.LFunction.PartitionZetaBridge where

open import LogOS.Prelude

open import LogOS.Prelude.Fin using (Fin)

open import LogOS.Algebra.Ring
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Core as LC
import LogOS.Domain.Opacity.NumberTheory.LFunction.RegulatedPartition as RP

-- A structured “ζ as regulated partition function” interface.
-- The combinatorial part is regulator-local and proven once (`RP.Z-sum≡Z-prod`);
-- any analytic semantics (what it means to remove the regulator and evaluate at s)
-- stays explicit as fields, so downstream GRH artefacts can stay assumption-light.

record PartitionZetaBridge {ℓ : Level}
                           (R  : Ring {ℓ})
                           (LF : LC.LFunction R)
                           : Set (lsuc ℓ) where
  field
    laws : RP.SemiringLaws R

    Mode : Set ℓ

    -- Regulator index and its finite “mode list + exponent cutoff” data.
    Reg      : Set ℓ
    regN     : Reg → ℕ
    regMode  : (r : Reg) → Fin (regN r) → Mode
    regCutoff : (r : Reg) → Fin (regN r) → ℕ

    -- Evaluation: given a spectral parameter u, produce the mode weights (e.g. p ↦ p^{-u}).
    weightAt : Ring.Carrier R → Mode → Ring.Carrier R

    -- Interpretation layer (axiom-exposed): a regulator-free zeta value aligned with L.
    Z∞        : Ring.Carrier R → Ring.Carrier R
    L≡Z∞      : ∀ {u} → LC.LFunction.In LF u → LC.LFunction.L LF u ≡ Z∞ u

  -- Finite regulated approximants (sum/product forms coincide by the generic lemma).
  Zᵣ-sum  : Reg → Ring.Carrier R → Ring.Carrier R
  Zᵣ-sum r u = RP.Z-sum R laws (regN r) (regMode r) (regCutoff r) (weightAt u)

  Zᵣ-prod : Reg → Ring.Carrier R → Ring.Carrier R
  Zᵣ-prod r u = RP.Z-prod R laws (regN r) (regMode r) (regCutoff r) (weightAt u)

  Zᵣ-sum≡prod : ∀ r u → Zᵣ-sum r u ≡ Zᵣ-prod r u
  Zᵣ-sum≡prod r u =
    RP.Z-sum≡Z-prod R laws (regN r) (regMode r) (regCutoff r) (weightAt u)

  -- Completed (regulator-free) value: the partition zeta Z∞ plus the completion
  -- factor from the L-function pack. This matches the textbook “completed zeta /
  -- completed partition function” object Λ (or ξ/Ξ if Gamma includes the symmetric
  -- polynomial factor).

  Λ∞ : Ring.Carrier R → Ring.Carrier R
  Λ∞ u = Ring._*_ R (LC.LFunction.Gamma LF u) (Z∞ u)

  Lambda≡Λ∞ : ∀ {u} → LC.LFunction.In LF u → LC.LFunction.Lambda LF u ≡ Λ∞ u
  Lambda≡Λ∞ {u} inu =
    cong (λ z → Ring._*_ R (LC.LFunction.Gamma LF u) z) (L≡Z∞ inu)
