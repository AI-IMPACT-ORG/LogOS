{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.SecondLaw where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Prelude using (Σ; _,_; _×_; fst; snd; proj₁; proj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

import LogOS.Theorems.Meta.Landauer as Landauer
open import LogOS.Complexity.LCUToLandauer as LCU

-- A LogOS-native “2nd law” layer:
-- we phrase entropy on the *observable carrier* used for LCU/Landauer, without
-- naming category structure.
--
-- Key idea:
-- - local unitarity is exposed as injectivity on observables (already in LCU);
-- - “merging” is observable non-injectivity (already in LCU);
-- - the 2nd law is: any merge forces an entropy increase by at least one unit `L`.
--
-- We keep the order/monoid structure abstract, using only the adapter’s carrier
-- `Scale` and its preorder `_≤s_`, plus the monoid `_·_`.

record SecondLawAssumptions {ℓ : Level}
                            (Sig : LogOSSignature ℓ)
                            (Q   : QAdapter ℓ)
                            : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  open QAdapter Q renaming (Scale to E; _≤s_ to _≤E_; _·_ to _⊙_)
  field
    -- Base physical axioms + observables + cost (LCU pack)
    LCUA : LCUObsAssumptions Sig Q

    -- Entropy functional on observables, valued in the adapter’s Scale carrier.
    Entropy : LCUObsAssumptions.Obs LCUA → E

    -- Entropy is preserved by local unitary evolution.
    unitary-preserves
      : ∀ f → LCUObsAssumptions.LocalUnitary LCUA f
            → ∀ x → Entropy (LCUObsAssumptions.act LCUA f x) ≡ Entropy x

    -- Entropy production lower bound for non-unitary evolution:
    -- if a step is not locally unitary, entropy increases by at least `L`.
    --
    -- This is the “2nd law” axiom in its sharp form; Landauer then becomes a corollary
    -- by taking the cost semantics to measure entropy production.
    nonUnitary→entropy+
      : ∀ f → ¬ (LCUObsAssumptions.LocalUnitary LCUA f)
            → ∀ x → _≤E_ (Entropy x ⊙ LCUObsAssumptions.L LCUA)
                          (Entropy (LCUObsAssumptions.act LCUA f x))

-- Non-vacuity guards: require an explicit merge witness so the 2nd law cannot
-- be satisfied only by degenerate (fully unitary or empty-observable) models.

record SecondLawGuards {ℓ : Level}
                       (Sig : LogOSSignature ℓ)
                       (Q   : QAdapter ℓ)
                       (A   : SecondLawAssumptions Sig Q)
                       : Set (lsuc (lsuc ℓ)) where
  field
    mergeWitness
      : Σ (LogOSSignature.Cosp Sig)
          (λ f → LCU.Merges (SecondLawAssumptions.LCUA A) f)

-- Derived “merge forces entropy increase” theorem (2nd law in a form aligned with Landauer).

merge→entropy+
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (A : SecondLawAssumptions Sig Q)
    (f : LogOSSignature.Cosp Sig)
  → LCU.Merges (SecondLawAssumptions.LCUA A) f
  → Σ (LCUObsAssumptions.Obs (SecondLawAssumptions.LCUA A))
      (λ x → QAdapter._≤s_ Q
               (QAdapter._·_ Q
                 (SecondLawAssumptions.Entropy A x)
                 (LCUObsAssumptions.L (SecondLawAssumptions.LCUA A)))
               (SecondLawAssumptions.Entropy A
                 (LCUObsAssumptions.act (SecondLawAssumptions.LCUA A) f x)))
merge→entropy+ {Sig = Sig} {Q = Q} A f m =
  let
    base = SecondLawAssumptions.LCUA A
    nu : ¬ (LCUObsAssumptions.LocalUnitary base f)
    nu = LCU.merge→¬unitary base f m
    x : LCUObsAssumptions.Obs base
    x = proj₁ m
  in x , SecondLawAssumptions.nonUnitary→entropy+ A f nu x

nonvacuous-entropy+
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (A : SecondLawAssumptions Sig Q)
    (G : SecondLawGuards Sig Q A)
  → Σ (LogOSSignature.Cosp Sig)
      (λ f →
        Σ (LCUObsAssumptions.Obs (SecondLawAssumptions.LCUA A))
          (λ x → QAdapter._≤s_ Q
                   (QAdapter._·_ Q
                     (SecondLawAssumptions.Entropy A x)
                     (LCUObsAssumptions.L (SecondLawAssumptions.LCUA A)))
                   (SecondLawAssumptions.Entropy A
                     (LCUObsAssumptions.act (SecondLawAssumptions.LCUA A) f x))))
nonvacuous-entropy+ {Sig = Sig} {Q = Q} A G =
  let
    f , m = SecondLawGuards.mergeWitness G
    x , le = merge→entropy+ {Sig = Sig} {Q = Q} A f m
  in
  f , (x , le)

-- Observational equality on observables defaults to propositional equality (`≡`).
-- This keeps entropy well-behaved under (trivial) observation equality without
-- committing to a richer observational semantics.

ObsEq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → (A : SecondLawAssumptions Sig Q)
  → LCUObsAssumptions.Obs (SecondLawAssumptions.LCUA A)
  → LCUObsAssumptions.Obs (SecondLawAssumptions.LCUA A)
  → Set ℓ
ObsEq _ x y = x ≡ y

entropy-respects-ObsEq
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → (A : SecondLawAssumptions Sig Q)
  → {x y : LCUObsAssumptions.Obs (SecondLawAssumptions.LCUA A)}
  → ObsEq A x y
  → SecondLawAssumptions.Entropy A x ≡ SecondLawAssumptions.Entropy A y
entropy-respects-ObsEq A eq = cong (SecondLawAssumptions.Entropy A) eq

-- Landauer pack is derivable from the underlying LCU assumptions (already provided).

landauerFromLCU : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                → (A : SecondLawAssumptions Sig Q)
                → Landauer.LandauerAssumptions Sig Q
landauerFromLCU A = LCU.toLandauer (SecondLawAssumptions.LCUA A)
