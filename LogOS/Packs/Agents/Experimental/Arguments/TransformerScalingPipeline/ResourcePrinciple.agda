{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.ResourcePrinciple where

open import LogOS.Prelude

open import LogOS.Prelude using (ℕ; zero; suc; _+_; _*_)
open import LogOS.Prelude.Empty using (⊥; ⊥-elim)
open import LogOS.Prelude.NatLog2 using () renaming (mul to mulℕ)

infix 4 _≢_
_≢_ : ∀ {ℓX : Level} {X : Set ℓX} → X → X → Set ℓX
_≢_ {ℓX = ℓX} x y = x ≡ y → ⊥ {ℓ = ℓX}

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

-- Resource principle and exponent arithmetic used in the scaling-law pipeline.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  record Exponent : Set where
    field
      num : ℕ
      den : ℕ
      den≢0 : den ≢ 0

  nonZeroSuc : ∀ n → suc n ≢ 0
  nonZeroSuc _ ()

  nonZeroMul : ∀ {a b} → a ≢ 0 → b ≢ 0 → a * b ≢ 0
  nonZeroMul {zero} a≢0 _ = ⊥-elim (a≢0 refl)
  nonZeroMul {suc _} {zero} _ b≢0 = ⊥-elim (b≢0 refl)
  nonZeroMul {suc _} {suc _} _ _ = λ ()

  nonZeroAddLeft : ∀ {a b} → a ≢ 0 → a + b ≢ 0
  nonZeroAddLeft {zero} a≢0 = ⊥-elim (a≢0 refl)
  nonZeroAddLeft {suc _} _ = λ ()

  nonZeroOne : 1 ≢ 0
  nonZeroOne = nonZeroSuc zero

  ratio : (num den : ℕ) → den ≢ 0 → Exponent
  ratio num den den≢0 = record { num = num ; den = den ; den≢0 = den≢0 }

  record ResourcePrinciple : Set (lsuc ℓ) where
    field
      alpha : ℕ
      beta : ℕ
      total≢0 : alpha + beta ≢ 0

    total : ℕ
    total = alpha + beta

    computeExponent : Exponent
    computeExponent = ratio beta total total≢0

    dataExponent : Exponent
    dataExponent = ratio alpha total total≢0

    lossExponent : Exponent
    lossExponent = ratio (mulℕ alpha beta) total total≢0

  record ResourceExponents : Set (lsuc ℓ) where
    field
      compute : Exponent
      dataExp : Exponent
      loss : Exponent

  deriveResourceExponents : ResourcePrinciple → ResourceExponents
  deriveResourceExponents R =
    record
      { compute = ResourcePrinciple.computeExponent R
      ; dataExp = ResourcePrinciple.dataExponent R
      ; loss = ResourcePrinciple.lossExponent R
      }

  unitPrinciple : ResourcePrinciple
  unitPrinciple =
    record
      { alpha = 1
      ; beta = 1
      ; total≢0 = nonZeroSuc 1
      }

  unitComputeExponent
    : ResourcePrinciple.computeExponent unitPrinciple
      ≡ ratio 1 2 (nonZeroSuc 1)
  unitComputeExponent = refl

  unitDataExponent
    : ResourcePrinciple.dataExponent unitPrinciple
      ≡ ratio 1 2 (nonZeroSuc 1)
  unitDataExponent = refl

  unitLossExponent
    : ResourcePrinciple.lossExponent unitPrinciple
      ≡ ratio 1 2 (nonZeroSuc 1)
  unitLossExponent = refl

  expAdd : Exponent → Exponent → Exponent
  expAdd e₁ e₂ =
    ratio
      (Exponent.num e₁ * Exponent.den e₂ + Exponent.num e₂ * Exponent.den e₁)
      (Exponent.den e₁ * Exponent.den e₂)
      (nonZeroMul (Exponent.den≢0 e₁) (Exponent.den≢0 e₂))

  expMul : Exponent → Exponent → Exponent
  expMul e₁ e₂ =
    ratio
      (Exponent.num e₁ * Exponent.num e₂)
      (Exponent.den e₁ * Exponent.den e₂)
      (nonZeroMul (Exponent.den≢0 e₁) (Exponent.den≢0 e₂))

  expRecip : (e : Exponent) → Exponent.num e ≢ 0 → Exponent
  expRecip e num≢0 = ratio (Exponent.den e) (Exponent.num e) num≢0

  expDiv : (e₁ e₂ : Exponent) → Exponent.num e₂ ≢ 0 → Exponent
  expDiv e₁ e₂ num≢0 = expMul e₁ (expRecip e₂ num≢0)

  record AnomalousDimension : Set where
    field
      classical : Exponent
      anomaly : Exponent
      observed : Exponent
      relation : observed ≡ expAdd classical anomaly

  record BootstrapConstraint : Set (lsuc ℓ) where
    field
      step : Exponent → Exponent
      fixed : Exponent
      fixedPoint : fixed ≡ step fixed

  bootstrap-anomalous
    : ∀ (P : ResourcePrinciple) (B : BootstrapConstraint) (Δ : Exponent)
    → BootstrapConstraint.fixed B
      ≡ expAdd (ResourcePrinciple.lossExponent P) Δ
    → AnomalousDimension
  bootstrap-anomalous P B Δ rel =
    record
      { classical = ResourcePrinciple.lossExponent P
      ; anomaly = Δ
      ; observed = BootstrapConstraint.fixed B
      ; relation = rel
      }

  record ResourcePrincipleRational : Set (lsuc ℓ) where
    field
      alphaExp : Exponent
      betaExp : Exponent
      totalNum≢0 : Exponent.num (expAdd alphaExp betaExp) ≢ 0

    totalExp : Exponent
    totalExp = expAdd alphaExp betaExp

    computeExponent : Exponent
    computeExponent = expDiv betaExp totalExp totalNum≢0

    dataExponent : Exponent
    dataExponent = expDiv alphaExp totalExp totalNum≢0

    lossExponent : Exponent
    lossExponent = expDiv (expMul alphaExp betaExp) totalExp totalNum≢0

  deriveResourceExponentsRational : ResourcePrincipleRational → ResourceExponents
  deriveResourceExponentsRational R =
    record
      { compute = ResourcePrincipleRational.computeExponent R
      ; dataExp = ResourcePrincipleRational.dataExponent R
      ; loss = ResourcePrincipleRational.lossExponent R
      }

  expNat : ℕ → Exponent
  expNat n = ratio n 1 nonZeroOne

  record SymmetricPrinciple : Set (lsuc ℓ) where
    field
      alphaExp : Exponent
      totalNum≢0 : Exponent.num (expAdd alphaExp alphaExp) ≢ 0

    principle : ResourcePrincipleRational
    principle =
      record
        { alphaExp = alphaExp
        ; betaExp = alphaExp
        ; totalNum≢0 = totalNum≢0
        }

    exponents : ResourceExponents
    exponents = deriveResourceExponentsRational principle

  symmetric-compute=data
    : ∀ (S : SymmetricPrinciple)
    → ResourceExponents.compute (SymmetricPrinciple.exponents S)
      ≡ ResourceExponents.dataExp (SymmetricPrinciple.exponents S)
  symmetric-compute=data S = refl

  cleanPrinciple : ResourcePrincipleRational
  cleanPrinciple =
    record
      { alphaExp = expNat 1
      ; betaExp = expNat 1
      ; totalNum≢0 = nonZeroSuc 1
      }

  cleanExponents : ResourceExponents
  cleanExponents = deriveResourceExponentsRational cleanPrinciple

  symAlphaFromLoss : Exponent → Exponent
  symAlphaFromLoss loss = expMul loss (expNat 2)

  symAlphaNumNonZero
    : ∀ loss → Exponent.num loss ≢ 0
    → Exponent.num (symAlphaFromLoss loss) ≢ 0
  symAlphaNumNonZero _ lossNum≢0 =
    nonZeroMul lossNum≢0 (nonZeroSuc 1)

  symTotalNumNonZero
    : ∀ loss → Exponent.num loss ≢ 0
    → Exponent.num (expAdd (symAlphaFromLoss loss) (symAlphaFromLoss loss)) ≢ 0
  symTotalNumNonZero loss lossNum≢0 =
    let alpha = symAlphaFromLoss loss
        alphaNum≢0 = symAlphaNumNonZero loss lossNum≢0
        termNonZero = nonZeroMul alphaNum≢0 (Exponent.den≢0 alpha)
    in nonZeroAddLeft termNonZero

  symPrincipleFromLoss
    : (loss : Exponent)
    → Exponent.num loss ≢ 0
    → ResourcePrincipleRational
  symPrincipleFromLoss loss lossNum≢0 =
    record
      { alphaExp = symAlphaFromLoss loss
      ; betaExp = symAlphaFromLoss loss
      ; totalNum≢0 = symTotalNumNonZero loss lossNum≢0
      }

  symExponentsFromLoss
    : (loss : Exponent)
    → Exponent.num loss ≢ 0
    → ResourceExponents
  symExponentsFromLoss loss lossNum≢0 =
    deriveResourceExponentsRational (symPrincipleFromLoss loss lossNum≢0)

  chinchillaLossExp : Exponent
  chinchillaLossExp = ratio 1 20 (nonZeroSuc 19)

  chinchillaPrinciple : ResourcePrincipleRational
  chinchillaPrinciple =
    symPrincipleFromLoss chinchillaLossExp nonZeroOne

  chinchillaAlpha : Exponent
  chinchillaAlpha = ResourcePrincipleRational.alphaExp chinchillaPrinciple

  chinchillaBeta : Exponent
  chinchillaBeta = ResourcePrincipleRational.betaExp chinchillaPrinciple

  chinchillaExponents : ResourceExponents
  chinchillaExponents = deriveResourceExponentsRational chinchillaPrinciple

  alphaExp : ResourcePrinciple → Exponent
  alphaExp R = expNat (ResourcePrinciple.alpha R)

  betaExp : ResourcePrinciple → Exponent
  betaExp R = expNat (ResourcePrinciple.beta R)

