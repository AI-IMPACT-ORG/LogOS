{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.LimitPublicisation where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con using (ConPoset)
open import LogOS.Kernel

import LogOS.Theorems.Meta.CommunicableTruth as Comm

-- A minimal preorder and cofinal-map notion (used to state “schedule independence”).

-- Compatibility wrapper: a “preorder on A” is just a `ConPoset` whose carrier is `A`.
--
-- This keeps older call sites readable (they can write `Preorder A`), while the
-- underlying structure is still the shared `ConPoset`.
record Preorder {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    CP : ConPoset ℓ
    Con≡ : ConPoset.Con CP ≡ A

  open ConPoset CP public

  private
    toCon : A → ConPoset.Con CP
    toCon = subst (λ X → X) (sym Con≡)

  infix 4 _≤_
  _≤_ : A → A → Set ℓ
  a ≤ b = ConPoset._⊑_ CP (toCon a) (toCon b)

  ≤-refl : ∀ {a} → a ≤ a
  ≤-refl {a} = ConPoset.refl CP {c = toCon a}

  ≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans ab bc = ConPoset.trans CP ab bc

record Cofinal {ℓA : Level}
               {A : Set ℓA} {B : Set ℓA}
               (PA : Preorder A)
               (u  : B → A)
               : Set (lsuc ℓA) where
  open Preorder PA
  field
    hit : ∀ a → Σ B (λ b → _≤_ a (u b))

-- The limit truth predicate as a meet/Π of finite regulators.

LimitTruth
  : ∀ {ℓT ℓA ℓX} {A : Set ℓA} {X : Set ℓX}
  → (A → X → Set ℓT) → X → Set (ℓT ⊔ ℓA)
LimitTruth Truthᵢ x = ∀ i → Truthᵢ i x

-- Cofinal invariance for meet-limits, assuming the regulator family is monotone
-- (decreasing) in the index: i ≤ j ⇒ Truthⱼ ⊆ Truthᵢ.

LimitTruth-cofinal
  : ∀ {ℓT ℓA ℓX}
    {B : Set ℓA} {X : Set ℓX}
    {A : Set ℓA}
    (PA : Preorder A)
    (u  : B → A)
    (cof : Cofinal PA u)
    (Truthᵢ : A → X → Set ℓT)
    (antiMono : ∀ {i j} → Preorder._≤_ PA i j → ∀ {x} → Truthᵢ j x → Truthᵢ i x)
  → ∀ {x} → LimitTruth Truthᵢ x ↔ LimitTruth (λ b → Truthᵢ (u b)) x
LimitTruth-cofinal PA u cof Truthᵢ antiMono {x} =
  record
    { to   = λ all b → all (u b)
    ; from = λ all a →
        let b    = proj₁ (Cofinal.hit cof a)
            a≤ub = proj₂ (Cofinal.hit cof a)
        in antiMono a≤ub (all b)
    }

-- “Limit publicisation” at the code level:
-- given a truth predicate TruthK, `Pr` produces the maximal Flow-compatible
-- decode-extensional communicable fragment of TruthK.

LimitPublicisation
  : ∀ {ℓ ℓT ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → Kernel.Code K → Set (ℓ ⊔ ℓT ⊔ lsuc ℓC)
LimitPublicisation {ℓC = ℓC} K TruthK = Comm.Pr {ℓC = ℓC} K TruthK

-- Reflector/coreflector universal property: `Pr TruthK` is itself admissible,
-- and any other admissible communicability predicate factors through it.

Pr-admissible
  : ∀ {ℓ ℓT ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → Comm.AdmissibleComm
      {ℓ = ℓ} {ℓT = ℓT} {ℓC = (ℓ ⊔ ℓT ⊔ lsuc ℓC)}
      K TruthK (Comm.Pr {ℓC = ℓC} K TruthK)
Pr-admissible {ℓC = ℓC} K TruthK =
  Comm.comm⋆-admissible {ℓC = ℓC} K TruthK

Pr-factor
  : ∀ {ℓ ℓT ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
    (CommP  : Kernel.Code K → Set ℓC)
    (A : Comm.AdmissibleComm K TruthK CommP)
  → ∀ {γ} → CommP γ → Comm.Pr {ℓC = ℓC} K TruthK γ
Pr-factor K TruthK CommP A cγ =
  Comm.comm⋆-intro K TruthK CommP A cγ

-- If a truth predicate is itself decode-extensional and Flow-stable,
-- then it is already an admissible communicability predicate for itself.
-- Consequently, it embeds into its own publicisation `Pr`.

TruthK→Pr
  : ∀ {ℓ ℓT}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → Comm.DecodeExtensional′ K TruthK
  → (∀ γ → TruthK γ ↔ TruthK (FlowCode K γ))
  → ∀ {γ} → TruthK γ → Comm.Pr {ℓC = ℓT} K TruthK γ
TruthK→Pr {ℓ = ℓ} {ℓT = ℓT} K TruthK ext stable {γ} tγ =
  Comm.comm⋆-intro K TruthK TruthK A-self tγ
  where
    A-self : Comm.AdmissibleComm {ℓ = ℓ} {ℓT = ℓT} {ℓC = ℓT} K TruthK TruthK
    A-self = record
      { core =
          record
            { ext    = ext
            ; sound  = λ {γ} t → t
            ; stable = stable
            }
      }

-- Universe-lift (1 step): if γ is observable at level ℓC, then it is observable
-- at level `lsuc ℓC` by lifting the witnessing predicate.

Pr-raise
  : ∀ {ℓ ℓT ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → ∀ {γ} → Comm.Pr {ℓC = ℓC} K TruthK γ → Comm.Pr {ℓC = lsuc ℓC} K TruthK γ
Pr-raise {ℓ = ℓ} {ℓT = ℓT} {ℓC = ℓC} K TruthK {γ} (CommP , (A , cγ)) =
  (CommP↑ , (A↑ , up cγ))
  where
    CommP↑ : Kernel.Code K → Set (lsuc ℓC)
    CommP↑ x = Lift (lsuc ℓC) (CommP x)

    up : ∀ {x} → CommP x → CommP↑ x
    up p = lift p

    down : ∀ {x} → CommP↑ x → CommP x
    down p = Lift.lower p

    A↑ : Comm.AdmissibleComm {ℓ = ℓ} {ℓT = ℓT} {ℓC = lsuc ℓC} K TruthK CommP↑
    A↑ = record
      { core =
          record
            { ext    = λ γ₁ γ₂ dec≡ p → up (Comm.AdmissibleComm.ext A γ₁ γ₂ dec≡ (down p))
            ; sound  = λ {γ} p → Comm.AdmissibleComm.sound A (down p)
            ; stable = λ γ′ →
                let st = Comm.AdmissibleComm.stable A γ′
                in record
                  { to   = λ p → up (_↔_.to st (down p))
                  ; from = λ p → up (_↔_.from st (down p))
                  }
            }
      }

-- Cofinal invariance for the publicised limit predicate:
-- if two indexings are cofinal and the truth family is monotone in the index,
-- then the publicised meet-limit is invariant (pointwise ↔).

Pr∞-cofinal
  : ∀ {ℓ ℓT ℓC ℓA}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    {A : Set ℓA} {B : Set ℓA}
    (PA : Preorder A)
    (u  : B → A)
    (cof : Cofinal PA u)
    (Truthᵢ : A → Kernel.Code K → Set ℓT)
    (antiMono : ∀ {i j} → Preorder._≤_ PA i j → ∀ {γ} → Truthᵢ j γ → Truthᵢ i γ)
  → ∀ {γ} →
      Comm.Pr {ℓC = ℓC} K (LimitTruth Truthᵢ) γ
      ↔
      Comm.Pr {ℓC = ℓC} K (LimitTruth (λ b → Truthᵢ (u b))) γ
Pr∞-cofinal {ℓC = ℓC} K PA u cof Truthᵢ antiMono {γ} =
  Comm.Pr-cong {ℓC = ℓC} K (LimitTruth Truthᵢ) (LimitTruth (λ b → Truthᵢ (u b)))
    (LimitTruth-cofinal PA u cof Truthᵢ antiMono)

-- Language/encoding invariance inside a fixed Kernel: any decode-preserving
-- code translation preserves the limit publicisation predicate.

DecodePreserving
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → (Kernel.Code K → Kernel.Code K) → Set ℓ
DecodePreserving K f = ∀ γ → Kernel.decode K (f γ) ≡ Kernel.decode K γ

Pr-naturality
  : ∀ {ℓ ℓT ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
    (f : Kernel.Code K → Kernel.Code K)
  → DecodePreserving K f
  → ∀ {γ} → Comm.Pr {ℓC = ℓC} K TruthK γ ↔ Comm.Pr {ℓC = ℓC} K TruthK (f γ)
Pr-naturality {ℓC = ℓC} K TruthK f pres {γ} =
  record
    { to   = λ p → Comm.comm⋆-ext {ℓC = ℓC} K TruthK γ (f γ) (sym (pres γ)) p
    ; from = λ p → Comm.comm⋆-ext {ℓC = ℓC} K TruthK (f γ) γ (pres γ) p
    }
