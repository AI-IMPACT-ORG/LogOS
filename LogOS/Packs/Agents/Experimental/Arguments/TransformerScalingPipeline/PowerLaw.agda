{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.PowerLaw where

open import LogOS.Prelude

open import LogOS.Prelude using (Σ; _,_; proj₁; proj₂)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.ResourcePrinciple as ResourcePrinciple

-- Power-law and Kaplan-form infrastructure for the pipeline.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module RP = ResourcePrinciple.For K ωCPO
  open RP

  record PowerLawOps : Set (lsuc (lsuc ℓ)) where
    field
      R : Set ℓ
      0# : R
      1# : R
      add : R → R → R
      mul : R → R → R
      inv : R → R
      pow : R → Exponent → R

  record OrderedPowerLawOps : Set (lsuc (lsuc ℓ)) where
    field
      ops : PowerLawOps
      _≤r_ : PowerLawOps.R ops → PowerLawOps.R ops → Set ℓ
      ≤r-refl : ∀ {x} → _≤r_ x x
      ≤r-trans : ∀ {x y z} → _≤r_ x y → _≤r_ y z → _≤r_ x z
      add-mono
        : ∀ {a b c d}
        → _≤r_ a b
        → _≤r_ c d
        → _≤r_ (PowerLawOps.add ops a c) (PowerLawOps.add ops b d)
      mul-mono
        : ∀ {a b c d}
        → _≤r_ a b
        → _≤r_ c d
        → _≤r_ (PowerLawOps.mul ops a c) (PowerLawOps.mul ops b d)
      pow-mono
        : ∀ {a b} → _≤r_ a b → ∀ {e}
        → _≤r_ (PowerLawOps.pow ops a e) (PowerLawOps.pow ops b e)

    infix 4 _≤r_

  record AddSwap (O : OrderedPowerLawOps) : Set (lsuc ℓ) where
    open OrderedPowerLawOps O
    field
      add-swap
        : ∀ a b
        → _≤r_
            (PowerLawOps.add ops a b)
            (PowerLawOps.add ops b a)

  powNeg : ∀ {ops : PowerLawOps} → PowerLawOps.R ops → Exponent → PowerLawOps.R ops
  powNeg {ops} x e =
    let open PowerLawOps ops in
    inv (pow x e)

  record Homogeneous (ops : PowerLawOps) (exp : Exponent)
                     (f : PowerLawOps.R ops → PowerLawOps.R ops)
                     : Set (lsuc (lsuc ℓ)) where
    field
      scale
        : ∀ k x
        → f (PowerLawOps.mul ops k x)
          ≡ PowerLawOps.mul ops (powNeg {ops} k exp) (f x)

  record PowerLawAxiom (ops : PowerLawOps) : Set (lsuc (lsuc ℓ)) where
    field
      characterize
        : ∀ {f exp}
        → Homogeneous ops exp f
        → Σ (PowerLawOps.R ops)
            (λ A → ∀ x → f x ≡ PowerLawOps.mul ops A (powNeg {ops} x exp))

  record PowerLawWitness (ops : PowerLawOps) (exp : Exponent)
                         (f : PowerLawOps.R ops → PowerLawOps.R ops)
                         : Set (lsuc (lsuc ℓ)) where
    field
      A : PowerLawOps.R ops
      form : ∀ x → f x ≡ PowerLawOps.mul ops A (powNeg {ops} x exp)

  record PowerLawBand (O : OrderedPowerLawOps) (exp : Exponent)
                      (f : PowerLawOps.R (OrderedPowerLawOps.ops O)
                           → PowerLawOps.R (OrderedPowerLawOps.ops O))
                      : Set (lsuc (lsuc ℓ)) where
    field
      Alo : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Ahi : PowerLawOps.R (OrderedPowerLawOps.ops O)
      lower
        : ∀ x
        → OrderedPowerLawOps._≤r_ O
            (PowerLawOps.mul (OrderedPowerLawOps.ops O) Alo
              (powNeg {ops = OrderedPowerLawOps.ops O} x exp))
            (f x)
      upper
        : ∀ x
        → OrderedPowerLawOps._≤r_ O
            (f x)
            (PowerLawOps.mul (OrderedPowerLawOps.ops O) Ahi
              (powNeg {ops = OrderedPowerLawOps.ops O} x exp))

  record SeparableHomogeneousLoss (ops : PowerLawOps) : Set (lsuc (lsuc ℓ)) where
    field
      principle : ResourcePrinciple
      loss : PowerLawOps.R ops → PowerLawOps.R ops → PowerLawOps.R ops
      Linf : PowerLawOps.R ops
      f : PowerLawOps.R ops → PowerLawOps.R ops
      g : PowerLawOps.R ops → PowerLawOps.R ops
      sep : ∀ N D → loss N D
            ≡ PowerLawOps.add ops Linf
                (PowerLawOps.add ops (f N) (g D))
      homF : Homogeneous ops (alphaExp principle) f
      homG : Homogeneous ops (betaExp principle) g

  record SeparablePowerLawLoss (ops : PowerLawOps) : Set (lsuc (lsuc ℓ)) where
    field
      principle : ResourcePrinciple
      loss : PowerLawOps.R ops → PowerLawOps.R ops → PowerLawOps.R ops
      Linf : PowerLawOps.R ops
      f : PowerLawOps.R ops → PowerLawOps.R ops
      g : PowerLawOps.R ops → PowerLawOps.R ops
      sep : ∀ N D → loss N D
            ≡ PowerLawOps.add ops Linf
                (PowerLawOps.add ops (f N) (g D))
      powF : PowerLawWitness ops (alphaExp principle) f
      powG : PowerLawWitness ops (betaExp principle) g

  record SeparablePowerLawBandLoss (O : OrderedPowerLawOps) : Set (lsuc (lsuc ℓ)) where
    field
      principle : ResourcePrinciple
      loss : PowerLawOps.R (OrderedPowerLawOps.ops O)
             → PowerLawOps.R (OrderedPowerLawOps.ops O)
             → PowerLawOps.R (OrderedPowerLawOps.ops O)
      Linf : PowerLawOps.R (OrderedPowerLawOps.ops O)
      f : PowerLawOps.R (OrderedPowerLawOps.ops O)
          → PowerLawOps.R (OrderedPowerLawOps.ops O)
      g : PowerLawOps.R (OrderedPowerLawOps.ops O)
          → PowerLawOps.R (OrderedPowerLawOps.ops O)
      sep : ∀ N D → loss N D
            ≡ PowerLawOps.add (OrderedPowerLawOps.ops O) Linf
                (PowerLawOps.add (OrderedPowerLawOps.ops O) (f N) (g D))
      bandF : PowerLawBand O (alphaExp principle) f
      bandG : PowerLawBand O (betaExp principle) g

  record KaplanForm (ops : PowerLawOps) (P : ResourcePrinciple) : Set (lsuc (lsuc ℓ)) where
    field
      loss : PowerLawOps.R ops → PowerLawOps.R ops → PowerLawOps.R ops
      Linf : PowerLawOps.R ops
      A : PowerLawOps.R ops
      B : PowerLawOps.R ops
      form
        : ∀ N D → loss N D
          ≡ PowerLawOps.add ops Linf
              (PowerLawOps.add ops
                (PowerLawOps.mul ops A (powNeg {ops} N (alphaExp P)))
                (PowerLawOps.mul ops B (powNeg {ops} D (betaExp P))))

  record KaplanBounds (O : OrderedPowerLawOps) (P : ResourcePrinciple)
    : Set (lsuc (lsuc ℓ)) where
    field
      loss : PowerLawOps.R (OrderedPowerLawOps.ops O)
             → PowerLawOps.R (OrderedPowerLawOps.ops O)
             → PowerLawOps.R (OrderedPowerLawOps.ops O)
      Linf : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Alo : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Ahi : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Blo : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Bhi : PowerLawOps.R (OrderedPowerLawOps.ops O)
      lower
        : ∀ N D
        → OrderedPowerLawOps._≤r_ O
            (PowerLawOps.add (OrderedPowerLawOps.ops O) Linf
              (PowerLawOps.add (OrderedPowerLawOps.ops O)
                (PowerLawOps.mul (OrderedPowerLawOps.ops O) Alo
                  (powNeg {ops = OrderedPowerLawOps.ops O} N (alphaExp P)))
                (PowerLawOps.mul (OrderedPowerLawOps.ops O) Blo
                  (powNeg {ops = OrderedPowerLawOps.ops O} D (betaExp P)))))
            (loss N D)
      upper
        : ∀ N D
        → OrderedPowerLawOps._≤r_ O
            (loss N D)
            (PowerLawOps.add (OrderedPowerLawOps.ops O) Linf
              (PowerLawOps.add (OrderedPowerLawOps.ops O)
                (PowerLawOps.mul (OrderedPowerLawOps.ops O) Ahi
                  (powNeg {ops = OrderedPowerLawOps.ops O} N (alphaExp P)))
                (PowerLawOps.mul (OrderedPowerLawOps.ops O) Bhi
                  (powNeg {ops = OrderedPowerLawOps.ops O} D (betaExp P)))))

  record ExponentSliceBounds (O : OrderedPowerLawOps) (exp : Exponent)
                             (f : PowerLawOps.R (OrderedPowerLawOps.ops O)
                                  → PowerLawOps.R (OrderedPowerLawOps.ops O))
                             : Set (lsuc (lsuc ℓ)) where
    field
      Linf : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Clo : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Chi : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Alo : PowerLawOps.R (OrderedPowerLawOps.ops O)
      Ahi : PowerLawOps.R (OrderedPowerLawOps.ops O)
      lower
        : ∀ x
        → OrderedPowerLawOps._≤r_ O
            (PowerLawOps.add (OrderedPowerLawOps.ops O) Linf
              (PowerLawOps.add (OrderedPowerLawOps.ops O)
                (PowerLawOps.mul (OrderedPowerLawOps.ops O) Alo
                  (powNeg {ops = OrderedPowerLawOps.ops O} x exp))
                Clo))
            (f x)
      upper
        : ∀ x
        → OrderedPowerLawOps._≤r_ O
            (f x)
            (PowerLawOps.add (OrderedPowerLawOps.ops O) Linf
              (PowerLawOps.add (OrderedPowerLawOps.ops O)
                (PowerLawOps.mul (OrderedPowerLawOps.ops O) Ahi
                  (powNeg {ops = OrderedPowerLawOps.ops O} x exp))
                Chi))

  deriveKaplanForm
    : ∀ {ops : PowerLawOps}
    → (ax : PowerLawAxiom ops)
    → (L : SeparableHomogeneousLoss ops)
    → KaplanForm ops (SeparableHomogeneousLoss.principle L)
  deriveKaplanForm {ops} ax L =
    let open PowerLawOps ops in
    let P = SeparableHomogeneousLoss.principle L
        loss = SeparableHomogeneousLoss.loss L
        Linf = SeparableHomogeneousLoss.Linf L
        f = SeparableHomogeneousLoss.f L
        g = SeparableHomogeneousLoss.g L
        sep = SeparableHomogeneousLoss.sep L
        homF = SeparableHomogeneousLoss.homF L
        homG = SeparableHomogeneousLoss.homG L
        charF = PowerLawAxiom.characterize ax homF
        charG = PowerLawAxiom.characterize ax homG
        A = proj₁ charF
        Af = proj₂ charF
        B = proj₁ charG
        Bg = proj₂ charG
    in
    record
      { loss = loss
      ; Linf = Linf
      ; A = A
      ; B = B
      ; form = λ N D →
          trans
            (sep N D)
            (cong
              (PowerLawOps.add ops Linf)
              (cong₂
                (PowerLawOps.add ops)
                (Af N)
                (Bg D)))
      }

  deriveKaplanBounds
    : ∀ {O : OrderedPowerLawOps}
    → (L : SeparablePowerLawBandLoss O)
    → KaplanBounds O (SeparablePowerLawBandLoss.principle L)
  deriveKaplanBounds {O} L =
    let open OrderedPowerLawOps O in
    let ops = OrderedPowerLawOps.ops O
        P = SeparablePowerLawBandLoss.principle L
        loss = SeparablePowerLawBandLoss.loss L
        Linf = SeparablePowerLawBandLoss.Linf L
        f = SeparablePowerLawBandLoss.f L
        g = SeparablePowerLawBandLoss.g L
        sep = SeparablePowerLawBandLoss.sep L
        bandF = SeparablePowerLawBandLoss.bandF L
        bandG = SeparablePowerLawBandLoss.bandG L
        Alo = PowerLawBand.Alo bandF
        Ahi = PowerLawBand.Ahi bandF
        Blo = PowerLawBand.Alo bandG
        Bhi = PowerLawBand.Ahi bandG
        lowerF = PowerLawBand.lower bandF
        upperF = PowerLawBand.upper bandF
        lowerG = PowerLawBand.lower bandG
        upperG = PowerLawBand.upper bandG
    in
    record
      { loss = loss
      ; Linf = Linf
      ; Alo = Alo
      ; Ahi = Ahi
      ; Blo = Blo
      ; Bhi = Bhi
      ; lower = λ N D →
          let bound =
                add-mono
                  (≤r-refl {x = Linf})
                  (add-mono (lowerF N) (lowerG D))
          in subst
              (λ x → _≤r_
                (PowerLawOps.add ops Linf
                  (PowerLawOps.add ops
                    (PowerLawOps.mul ops Alo
                      (powNeg {ops = ops} N (alphaExp P)))
                    (PowerLawOps.mul ops Blo
                      (powNeg {ops = ops} D (betaExp P)))))
                x)
              (sym (sep N D))
              bound
      ; upper = λ N D →
          let bound =
                add-mono
                  (≤r-refl {x = Linf})
                  (add-mono (upperF N) (upperG D))
          in subst
              (λ x → _≤r_ x
                (PowerLawOps.add ops Linf
                  (PowerLawOps.add ops
                    (PowerLawOps.mul ops Ahi
                      (powNeg {ops = ops} N (alphaExp P)))
                    (PowerLawOps.mul ops Bhi
                      (powNeg {ops = ops} D (betaExp P))))))
              (sym (sep N D))
              bound
      }

  kaplanBounds-sliceN
    : ∀ {O : OrderedPowerLawOps} {P : ResourcePrinciple}
    → (K : KaplanBounds O P)
    → (D : PowerLawOps.R (OrderedPowerLawOps.ops O))
    → ExponentSliceBounds O (alphaExp P)
        (λ N → KaplanBounds.loss K N D)
  kaplanBounds-sliceN {O} {P} K D =
    let ops = OrderedPowerLawOps.ops O in
    record
      { Linf = KaplanBounds.Linf K
      ; Clo = PowerLawOps.mul ops (KaplanBounds.Blo K)
                (powNeg {ops = ops} D (betaExp P))
      ; Chi = PowerLawOps.mul ops (KaplanBounds.Bhi K)
                (powNeg {ops = ops} D (betaExp P))
      ; Alo = KaplanBounds.Alo K
      ; Ahi = KaplanBounds.Ahi K
      ; lower = λ N → KaplanBounds.lower K N D
      ; upper = λ N → KaplanBounds.upper K N D
      }

  kaplanBounds-sliceD
    : ∀ {O : OrderedPowerLawOps} {P : ResourcePrinciple}
    → AddSwap O
    → (K : KaplanBounds O P)
    → (N : PowerLawOps.R (OrderedPowerLawOps.ops O))
    → ExponentSliceBounds O (betaExp P)
        (λ D → KaplanBounds.loss K N D)
  kaplanBounds-sliceD {O} {P} swap K N =
    let open OrderedPowerLawOps O
        ops = OrderedPowerLawOps.ops O

        linf = KaplanBounds.Linf K
        clo =
          PowerLawOps.mul ops (KaplanBounds.Alo K)
            (powNeg {ops = ops} N (alphaExp P))
        chi =
          PowerLawOps.mul ops (KaplanBounds.Ahi K)
            (powNeg {ops = ops} N (alphaExp P))
    in
    record
      { Linf = linf
      ; Clo = clo
      ; Chi = chi
      ; Alo = KaplanBounds.Blo K
      ; Ahi = KaplanBounds.Bhi K
      ; lower = λ D →
          let var =
                PowerLawOps.mul ops (KaplanBounds.Blo K)
                  (powNeg {ops = ops} D (betaExp P))
              inner = AddSwap.add-swap swap var clo
              outer = add-mono (≤r-refl {x = linf}) inner
          in ≤r-trans outer (KaplanBounds.lower K N D)
      ; upper = λ D →
          let var =
                PowerLawOps.mul ops (KaplanBounds.Bhi K)
                  (powNeg {ops = ops} D (betaExp P))
              inner = AddSwap.add-swap swap chi var
              outer = add-mono (≤r-refl {x = linf}) inner
          in ≤r-trans (KaplanBounds.upper K N D) outer
      }

  deriveKaplanForm-witness
    : ∀ {ops : PowerLawOps}
    → (L : SeparablePowerLawLoss ops)
    → KaplanForm ops (SeparablePowerLawLoss.principle L)
  deriveKaplanForm-witness {ops} L =
    let open PowerLawOps ops in
    let P = SeparablePowerLawLoss.principle L
        loss = SeparablePowerLawLoss.loss L
        Linf = SeparablePowerLawLoss.Linf L
        f = SeparablePowerLawLoss.f L
        g = SeparablePowerLawLoss.g L
        sep = SeparablePowerLawLoss.sep L
        powF = SeparablePowerLawLoss.powF L
        powG = SeparablePowerLawLoss.powG L
        A = PowerLawWitness.A powF
        Af = PowerLawWitness.form powF
        B = PowerLawWitness.A powG
        Bg = PowerLawWitness.form powG
    in
    record
      { loss = loss
      ; Linf = Linf
      ; A = A
      ; B = B
      ; form = λ N D →
          trans
            (sep N D)
            (cong
              (PowerLawOps.add ops Linf)
              (cong₂
                (PowerLawOps.add ops)
                (Af N)
                (Bg D)))
      }
