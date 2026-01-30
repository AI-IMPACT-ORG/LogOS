{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CommunicableTruth where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.Prelude.Product using (Σ; _,_; proj₁; proj₂; _×_; fst; snd)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
import LogOS.Theorems.Meta.ObserverCore as ObsCore

-- Decode-extensionality, but phrased w.r.t. decoded mutual refinement (`≈` on decoded constraints).

CodeCP
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ConPreorder ℓ
CodeCP K = BulkBoundary.bnd (Kernel.BB K)

DecodeExtensional′
  : ∀ {ℓ ℓP} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (P : Kernel.Code K → Set ℓP)
  → Set (ℓ ⊔ ℓP)
DecodeExtensional′ K P =
  ObsCore.DecodeExtensional≈ (CodeCP K) (Kernel.decode K) P

-- A “communicable truth” predicate Comm is admissible w.r.t. a chosen TruthK when:
-- - it only depends on decode,
-- - it is sound (anything communicable is true),
-- - it is stable under one FlowCode step (predicate-level fixed point).

AdmissibleComm
  : ∀ {ℓ ℓT ℓC : Level}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
    (Comm   : Kernel.Code K → Set ℓC)
  → Set (ℓ ⊔ ℓT ⊔ ℓC)
AdmissibleComm K TruthK Comm =
  ObsCore.Admissible≈ (Kernel.Code K) (CodeCP K) (Kernel.decode K) (FlowCode K) TruthK Comm

-- The “largest communicable truth notion compatible with Flow”:
-- γ is in Comm⋆ iff there exists *some* admissible communicability predicate Comm
-- (sound + decode-extensional + Flow-stable) that contains γ.

Comm⋆
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → Kernel.Code K → Set (ℓ ⊔ ℓT ⊔ lsuc ℓC)
Comm⋆ {ℓC = ℓC} K TruthK =
  ObsCore.Pred⋆≈ {ℓP = ℓC} (CodeCP K) (Kernel.decode K) (FlowCode K) TruthK

-- Naming alias matching the “stable predicate” intuition:
-- StableP⋆ is the maximal Flow-compatible communicable fragment of TruthK.

StableP⋆
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → Kernel.Code K → Set (ℓ ⊔ ℓT ⊔ lsuc ℓC)
StableP⋆ {ℓC = ℓC} K TruthK γ = Comm⋆ {ℓC = ℓC} K TruthK γ

-- Supremum universal property: Comm⋆ is the least upper bound (join) of all
-- admissible communication predicates Comm : Code → Set ℓC (for a fixed ℓC).

comm⋆-leastUpperBound
  : ∀ {ℓ ℓT ℓC ℓX} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
    (X : Kernel.Code K → Set ℓX)
    (ub : ∀ (Comm : Kernel.Code K → Set ℓC)
            (A : AdmissibleComm {ℓ = ℓ} {ℓT = ℓT} {ℓC = ℓC} K TruthK Comm)
          → ∀ {γ} → Comm γ → X γ)
  → ∀ {γ} → Comm⋆ {ℓC = ℓC} K TruthK γ → X γ
comm⋆-leastUpperBound K TruthK X ub (Comm , (A , cγ)) =
  ub Comm A cγ

-- Introduction (largestness): any admissible Comm embeds into Comm⋆.

comm⋆-intro
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
    (Comm : Kernel.Code K → Set ℓC)
    (A : AdmissibleComm {ℓ = ℓ} {ℓT = ℓT} {ℓC = ℓC} K TruthK Comm)
  → ∀ {γ} → Comm γ → Comm⋆ {ℓC = ℓC} K TruthK γ
comm⋆-intro K TruthK Comm A cγ = (Comm , (A , cγ))

-- Elimination: unpack the witness predicate and its admissibility proof.

comm⋆-elim
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
    {γ : Kernel.Code K}
  → Comm⋆ {ℓC = ℓC} K TruthK γ
  → Σ (Kernel.Code K → Set ℓC) (λ Comm →
      AdmissibleComm {ℓ = ℓ} {ℓT = ℓT} {ℓC = ℓC} K TruthK Comm
      × Comm γ)
comm⋆-elim K TruthK h = h

-- Soundness: Comm⋆ is always a sound fragment of TruthK.

comm⋆-sound
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → ∀ {γ} → Comm⋆ {ℓC = ℓC} K TruthK γ → TruthK γ
comm⋆-sound {ℓC = ℓC} K TruthK =
  ObsCore.Pred⋆≈-sound (CodeCP K) (Kernel.decode K) (FlowCode K) TruthK

-- Flow-compatibility: Comm⋆ is stable under FlowCode.

comm⋆-stable
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → ∀ γ → (Comm⋆ {ℓC = ℓC} K TruthK γ) ↔ (Comm⋆ {ℓC = ℓC} K TruthK (FlowCode K γ))
comm⋆-stable {ℓC = ℓC} K TruthK =
  ObsCore.Pred⋆≈-stable (CodeCP K) (Kernel.decode K) (FlowCode K) TruthK

-- Decode-extensionality: if the witness predicate is decode-extensional, so is Comm⋆.

comm⋆-ext
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → DecodeExtensional′ K (Comm⋆ {ℓC = ℓC} K TruthK)
comm⋆-ext {ℓC = ℓC} K TruthK =
  ObsCore.Pred⋆≈-ext (CodeCP K) (Kernel.decode K) (FlowCode K) TruthK

-- Comm⋆ itself is admissible (at a bumped universe for the communicability predicate).
-- This packages the “compatibility with Flow” and “soundness” checks.

comm⋆-admissible
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → AdmissibleComm {ℓ = ℓ} {ℓT = ℓT} {ℓC = (ℓ ⊔ ℓT ⊔ lsuc ℓC)}
      K TruthK (Comm⋆ {ℓC = ℓC} K TruthK)
comm⋆-admissible {ℓC = ℓC} K TruthK =
  ObsCore.Pred⋆≈-admissible (CodeCP K) (Kernel.decode K) (FlowCode K) TruthK

-- Naturality in the chosen truth predicate: if TruthK ⇒ TruthK′, then
-- Comm⋆(TruthK) ⇒ Comm⋆(TruthK′) (same communicability level ℓC).

comm⋆-mono-Truth
  : ∀ {ℓ ℓT ℓT′ ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK  : Kernel.Code K → Set ℓT)
    (TruthK′ : Kernel.Code K → Set ℓT′)
    (monoTruth : ∀ {γ} → TruthK γ → TruthK′ γ)
  → ∀ {γ} → Comm⋆ {ℓC = ℓC} K TruthK γ → Comm⋆ {ℓC = ℓC} K TruthK′ γ
comm⋆-mono-Truth K TruthK TruthK′ monoTruth (Comm , (A , cγ)) =
  (Comm , (A′ , cγ))
  where
    A′ : AdmissibleComm K TruthK′ Comm
    A′ = record
      { ext≈   = ObsCore.Admissible≈.ext≈ A
      ; sound  = λ {γ} c → monoTruth (ObsCore.Admissible≈.sound A c)
      ; stable = ObsCore.Admissible≈.stable A
      }

-- Optional naming: view Comm⋆ as a “projection” (interior operator) that sends
-- a chosen truth predicate TruthK to its maximal Flow-compatible
-- communicable fragment.

Pr
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → Kernel.Code K → Set (ℓ ⊔ ℓT ⊔ lsuc ℓC)
Pr {ℓC = ℓC} K TruthK γ = Comm⋆ {ℓC = ℓC} K TruthK γ

-- Alternative view: `Pr` depends on the step function only up to decoded meaning.
-- Since `FlowCode γ` and `Box (Body γ)` decode to the same boundary constraint,
-- `Pr` can equivalently be read as the largest admissible predicate for the
-- “stabilise-after-body” step.

Pr-BoxBody
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → Kernel.Code K → Set (ℓ ⊔ ℓT ⊔ lsuc ℓC)
Pr-BoxBody {ℓC = ℓC} K TruthK =
  ObsCore.Pred⋆≈ {ℓP = ℓC} (CodeCP K) (Kernel.decode K) (λ γ → Box K (Kernel.Body K γ)) TruthK

Pr↔Pr-BoxBody
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → ∀ {γ} → Pr {ℓC = ℓC} K TruthK γ ↔ Pr-BoxBody {ℓC = ℓC} K TruthK γ
Pr↔Pr-BoxBody {ℓC = ℓC} K TruthK {γ} =
  ST.Pred⋆≈↔ {ℓP = ℓC} TruthK {γ = γ}
  where
    CP = CodeCP K

    eqStep : ∀ γ′ →
      _≈CP_ CP (Kernel.decode K (FlowCode K γ′))
               (Kernel.decode K (Box K (Kernel.Body K γ′)))
    eqStep γ′
      rewrite decode-FlowCode≡decode-BoxBody K γ′
      = (ConPreorder.refl CP , ConPreorder.refl CP)

    module ST =
      ObsCore.StepTransport≈
        CP
        (Kernel.decode K)
        (FlowCode K)
        (λ γ′ → Box K (Kernel.Body K γ′))
        eqStep

-- `Pr` respects pointwise logical equivalence of truth predicates.

Pr-cong
  : ∀ {ℓ ℓT ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK  TruthK′ : Kernel.Code K → Set ℓT)
    (eqv : ∀ {γ} → (TruthK γ) ↔ (TruthK′ γ))
  → ∀ {γ} → Pr {ℓC = ℓC} K TruthK γ ↔ Pr {ℓC = ℓC} K TruthK′ γ
Pr-cong {ℓC = ℓC} K TruthK TruthK′ eqv =
  record
    { to   = comm⋆-mono-Truth K TruthK TruthK′ (_↔_.to eqv)
    ; from = comm⋆-mono-Truth K TruthK′ TruthK (_↔_.from eqv)
    }

-- Idempotence (up to the unavoidable universe bump): projecting twice yields the
-- same communicable fragment. We state it as two implications since `_↔_` is
-- universe-uniform.

Pr-idem-to
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → ∀ {γ} →
      Pr {ℓC = ℓC} K TruthK γ
      → Pr {ℓC = (ℓ ⊔ ℓT ⊔ lsuc ℓC)} K (Pr {ℓC = ℓC} K TruthK) γ
Pr-idem-to {ℓ = ℓ} {ℓT = ℓT} {ℓC = ℓC} K TruthK {γ} tγ =
  comm⋆-intro {ℓT = (ℓ ⊔ ℓT ⊔ lsuc ℓC)} {ℓC = (ℓ ⊔ ℓT ⊔ lsuc ℓC)} K T T A-self tγ
  where
    T : Kernel.Code K → Set (ℓ ⊔ ℓT ⊔ lsuc ℓC)
    T = Pr {ℓC = ℓC} K TruthK

    A-self : AdmissibleComm {ℓ = ℓ} {ℓT = (ℓ ⊔ ℓT ⊔ lsuc ℓC)} {ℓC = (ℓ ⊔ ℓT ⊔ lsuc ℓC)}
              K T T
    A-self = record
      { ext≈   = comm⋆-ext {ℓC = ℓC} K TruthK
      ; sound  = λ {γ} tγ′ → tγ′
      ; stable = comm⋆-stable {ℓC = ℓC} K TruthK
      }

Pr-idem-from
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → ∀ {γ} →
      Pr {ℓC = (ℓ ⊔ ℓT ⊔ lsuc ℓC)} K (Pr {ℓC = ℓC} K TruthK) γ
      → Pr {ℓC = ℓC} K TruthK γ
Pr-idem-from {ℓ = ℓ} {ℓT = ℓT} {ℓC = ℓC} K TruthK {γ} =
  comm⋆-sound {ℓT = (ℓ ⊔ ℓT ⊔ lsuc ℓC)} {ℓC = (ℓ ⊔ ℓT ⊔ lsuc ℓC)} K T
  where
    T : Kernel.Code K → Set (ℓ ⊔ ℓT ⊔ lsuc ℓC)
    T = Pr {ℓC = ℓC} K TruthK

-- “Limit as intersection” is the natural case in many regulator stories:
-- if a property holds for every finite regulator, then it holds for the limit
-- predicate defined as the pointwise intersection of all regulators.
--
-- Technically: `Pr` preserves Π/∧ over a small index type `Idx : Set`.

Pr-Π
  : ∀ {ℓ ℓT ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    {Idx : Set}
    (Truthᵢ : Idx → Kernel.Code K → Set ℓT)
  → ∀ {γ} →
      (∀ i → Pr {ℓC = ℓC} K (Truthᵢ i) γ)
      → Pr {ℓC = ℓC} K (λ γ′ → ∀ i → Truthᵢ i γ′) γ
Pr-Π {ℓ = ℓ} {ℓT = ℓT} {ℓC = ℓC} K {Idx} Truthᵢ {γ} all =
  comm⋆-intro K Truth∞ Comm⋂ A⋂ comm⋂γ
  where
    Truth∞ : Kernel.Code K → Set ℓT
    Truth∞ γ′ = ∀ i → Truthᵢ i γ′

    Commᵢ : Idx → Kernel.Code K → Set ℓC
    Commᵢ i = proj₁ (all i)

    Aᵢ : (i : Idx) → AdmissibleComm K (Truthᵢ i) (Commᵢ i)
    Aᵢ i = fst (proj₂ (all i))

    commᵢγ : (i : Idx) → Commᵢ i γ
    commᵢγ i = snd (proj₂ (all i))

    Comm⋂ : Kernel.Code K → Set ℓC
    Comm⋂ γ′ = ∀ i → Commᵢ i γ′

    comm⋂γ : Comm⋂ γ
    comm⋂γ i = commᵢγ i

    A⋂ : AdmissibleComm K Truth∞ Comm⋂
    A⋂ = record
      { ext≈   = ext⋂
      ; sound  = sound⋂
      ; stable = stable⋂
      }
      where
        ext⋂ : DecodeExtensional′ K Comm⋂
        ext⋂ γ₁ γ₂ dec≈ h i = ObsCore.Admissible≈.ext≈ (Aᵢ i) γ₁ γ₂ dec≈ (h i)

        sound⋂ : ∀ {γ′} → Comm⋂ γ′ → Truth∞ γ′
        sound⋂ {γ′} h i = ObsCore.Admissible≈.sound (Aᵢ i) (h i)

        stable⋂ : ∀ γ′ → (Comm⋂ γ′) ↔ (Comm⋂ (FlowCode K γ′))
        stable⋂ γ′ =
          record
            { to   = λ h i → _↔_.to   (ObsCore.Admissible≈.stable (Aᵢ i) γ′) (h i)
            ; from = λ h i → _↔_.from (ObsCore.Admissible≈.stable (Aᵢ i) γ′) (h i)
            }

-- Safe reflection aliases (kernel-specific, FlowCode-based).
-- These match the literature’s “reflection as sound, stable predicate”.

SafeReflection = AdmissibleComm

Safe⋆ = Comm⋆

-- Kernel-safe reflection matches the generic observer-core safe reflection.
safe⋆-core
  : ∀ {ℓ ℓT ℓC} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (TruthK : Kernel.Code K → Set ℓT)
  → ∀ {γ}
  → Comm⋆ {ℓC = ℓC} K TruthK γ
    ↔ ObsCore.Safe⋆≈ {ℓP = ℓC} (CodeCP K) (Kernel.decode K) (FlowCode K) TruthK γ
safe⋆-core {ℓC = ℓC} K TruthK =
  record
    { to   = λ x → x
    ; from = λ x → x
    }

safe⋆-intro = comm⋆-intro
safe⋆-sound = comm⋆-sound
safe⋆-stable = comm⋆-stable
safe⋆-ext = comm⋆-ext
safe⋆-admissible = comm⋆-admissible
safe⋆-mono-Truth = comm⋆-mono-Truth
