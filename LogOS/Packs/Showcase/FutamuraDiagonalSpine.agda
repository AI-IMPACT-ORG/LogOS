{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Showcase.FutamuraDiagonalSpine where

open import LogOS.Prelude
open import LogOS.Prelude.List using ([]; _∷_)

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Boundary.Port using (BoundaryPort)
open import LogOS.Kernel using (Kernel)
open import LogOS.Syntax.ProofSystem
  using (ProofSystem; Complete; Prov; DecEq; keyValidated; keyValidated-complete)

import LogOS.UniversalIR.Futamura as Futamura
import LogOS.UniversalIR.Core.Minsky as M

import LogOS.Ports.Semantic.CanonicalPorts as Canonical
import LogOS.Ports.Semantic.BoundarySystemIO as BoundarySystemIO
import LogOS.Ports.Semantic.Interlingua as Interlingua
open import LogOS.Ports.Semantic.Core using (boundarySatSystemFromIO)
open import LogOS.Ports.Semantic.SatSystemIO using (SatSystemIO)
import LogOS.Ports.Semantic.SatSystemIO as SatSystemIOₜ
import LogOS.Theorems.Meta.Bootstrapping as Bootstrapping

-- Concrete UniversalIR/Futamura witness: a tiny Minsky program and its staged
-- run theorem instance.
module MinskyRun where

  -- Program: move R1 into R0 by looping DECJZ/INC, then halt.
  add-R1-into-R0 : M.MinskyProg
  add-R1-into-R0 =
    M.mkProg
      ( M.DECJZ M.R1 1 2
      ∷ M.INC M.R0 0
      ∷ M.HALT
      ∷ []
      )

  -- Initial machine state (pc=0, r0=2, r1=3, r2=r3=0).
  init-state : M.MinskyState
  init-state = M.mkState 0 2 3 0 0

  fuel-add : ℕ
  fuel-add = M.fuelAddR1 3

  futamura₁-concrete : _
  futamura₁-concrete =
    Futamura.Minsky.futamura₁-run add-R1-into-R0 init-state fuel-add

  run≡observe-concrete : _
  run≡observe-concrete =
    Futamura.Minsky.run≡observe-simulate add-R1-into-R0 init-state fuel-add

-- Concrete transport surface (for any kernel): bootstrapping and rebasing
-- between canonical code/boundary ports.
module Transport
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  module CP = Canonical.For K
  module Boot = Bootstrapping.For K
  open CP using (B; CodePort; BoundaryPort∂)

  bootstrap-iso-exists = Boot.bootstrap-iso

  private
    suc-injective : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
    suc-injective refl = refl

    decEqℕ : (m n : ℕ) → m ≡ n ⊎ ¬ (m ≡ n)
    decEqℕ zero    zero    = inj₁ refl
    decEqℕ zero    (suc _) = inj₂ (λ ())
    decEqℕ (suc _) zero    = inj₂ (λ ())
    decEqℕ (suc m) (suc n) with decEqℕ m n
    ... | inj₁ eq  = inj₁ (cong suc eq)
    ... | inj₂ neq = inj₂ (λ eq → neq (suc-injective eq))

  -- Fragment port: code with an explicit syntax tag.
  --
  -- The tag is observationally inert (satisfaction depends only on code), but
  -- gives us a concrete, decidable syntactic check in the proof-system layer.
  NatTag : Set ℓ
  NatTag = Lift ℓ ℕ

  decEqNatTag : DecEq NatTag
  decEqNatTag =
    record
      { decEq = decEqNatTag'
      }
    where
      decEqNatTag' : ∀ x y → x ≡ y ⊎ ¬ (x ≡ y)
      decEqNatTag' (lift m) (lift n) with decEqℕ m n
      ... | inj₁ eq  = inj₁ (cong lift eq)
      ... | inj₂ neq = inj₂ (λ where refl → neq refl)

  TaggedCodeForm : Set ℓ
  TaggedCodeForm = NatTag × BoundaryPort.Form CodePort

  TaggedCodePort
    : BoundaryPort {ℓForm = ℓ} Sig Q
        (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B
  TaggedCodePort =
    record
      { Sem =
          record
            { Form = TaggedCodeForm
            ; SatF = λ p x → BoundaryPort.SatF CodePort p (snd x)
            ; Interp = λ c → lift 0 , BoundaryPort.Interp CodePort c
            ; Sat∂≈F = λ p c → BoundaryPort.Sat∂≈F CodePort p c
            }
      ; Import = λ x → BoundaryPort.Import CodePort (snd x)
      ; SatF≈∂ = λ p x → BoundaryPort.SatF≈∂ CodePort p (snd x)
      }

  proverKey : BoundaryPort.Form TaggedCodePort → NatTag
  proverKey = fst

  proverWitness
    : BoundaryPort.Form TaggedCodePort
    → Set ℓ
  proverWitness x = ∀ p → BoundaryPort.SatF TaggedCodePort p x

  proverWitness-sound
    : ∀ x → proverWitness x → (∀ p → BoundaryPort.SatF TaggedCodePort p x)
  proverWitness-sound _ sat = sat

  proverWitness-complete
    : ∀ x → (∀ p → BoundaryPort.SatF TaggedCodePort p x) → proverWitness x
  proverWitness-complete _ sat = sat

  -- Nontrivial checker from the generic key-validated construction.
  taggedProver
    : ProofSystem
        {ℓI = ℓ}
        {ℓP = ℓ}
        {ℓW = ℓ}
        (BoundaryPort.Form TaggedCodePort)
        (λ φ → ∀ p → BoundaryPort.SatF TaggedCodePort p φ)
  taggedProver = keyValidated NatTag decEqNatTag proverKey proverWitness proverWitness-sound

  taggedProver-complete : Complete taggedProver
  taggedProver-complete =
    keyValidated-complete
      NatTag
      decEqNatTag
      proverKey
      proverWitness
      proverWitness-sound
      proverWitness-complete

  modelInput : Set ℓ
  modelInput = LogOSSignature.∂Cosp Sig × BoundaryPort.Form TaggedCodePort

  modelKey : modelInput → NatTag
  modelKey = λ where (_ , φ) → fst φ

  modelPred : modelInput → Set ℓ
  modelPred (p , φ) = BoundaryPort.SatF TaggedCodePort p φ

  modelWitness
    : modelInput
    → Set ℓ
  modelWitness = modelPred

  modelWitness-sound
    : ∀ x → modelWitness x → modelPred x
  modelWitness-sound _ sat = sat

  modelWitness-complete
    : ∀ x → modelPred x → modelWitness x
  modelWitness-complete _ sat = sat

  taggedModelChecker
    : ProofSystem
        {ℓI = ℓ}
        {ℓP = ℓ}
        {ℓW = ℓ}
        modelInput
        modelPred
  taggedModelChecker =
    keyValidated NatTag decEqNatTag modelKey modelWitness modelWitness-sound

  taggedModelChecker-complete : Complete taggedModelChecker
  taggedModelChecker-complete =
    keyValidated-complete
      NatTag
      decEqNatTag
      modelKey
      modelWitness
      modelWitness-sound
      modelWitness-complete

  -- Pull back tools from boundary-port presentation to code-port presentation.
  rebase-to-code
    : ∀ {ℓName ℓForm₂ ℓWProver ℓWModel}
      {Name : Set ℓName}
    → SatSystemIO
        {ℓForm = ℓForm₂}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name
        (boundarySatSystemFromIO B)
    → SatSystemIO
        {ℓForm = ℓ}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name
        (boundarySatSystemFromIO B)
  rebase-to-code = BoundarySystemIO.rebaseToBoundaryPort B CodePort

  -- Pull back tools from code-port presentation to boundary-port presentation.
  rebase-to-boundary
    : ∀ {ℓName ℓForm₂ ℓWProver ℓWModel}
      {Name : Set ℓName}
    → SatSystemIO
        {ℓForm = ℓForm₂}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name
        (boundarySatSystemFromIO B)
    → SatSystemIO
        {ℓForm = ℓ}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name
        (boundarySatSystemFromIO B)
  rebase-to-boundary = BoundarySystemIO.rebaseToBoundaryPort B BoundaryPort∂

  Name₀ : Set
  Name₀ = ⊤

  taggedSystemIO-code
    : SatSystemIO
        {ℓForm = ℓ}
        {ℓWProver = ℓ}
        {ℓWModel = ℓ}
        Name₀
        (boundarySatSystemFromIO B)
  taggedSystemIO-code =
    BoundarySystemIO.systemIOFromBoundaryPort
      B
      TaggedCodePort
      tt
      taggedProver
      taggedModelChecker

  taggedSystemIO-boundary-from-code
    : SatSystemIO
        {ℓForm = ℓ}
        {ℓWProver = ℓ}
        {ℓWModel = ℓ}
        Name₀
        (boundarySatSystemFromIO B)
  taggedSystemIO-boundary-from-code = rebase-to-boundary taggedSystemIO-code

  taggedSystemIO-code-from-boundary
    : SatSystemIO
        {ℓForm = ℓ}
        {ℓWProver = ℓ}
        {ℓWModel = ℓ}
        Name₀
        (boundarySatSystemFromIO B)
  taggedSystemIO-code-from-boundary = rebase-to-code taggedSystemIO-boundary-from-code

  taggedProver-complete-code
    : Complete (SatSystemIOₜ.SatSystemIO.Prover taggedSystemIO-code)
  taggedProver-complete-code = taggedProver-complete

  taggedModelChecker-complete-code
    : Complete (SatSystemIOₜ.SatSystemIO.ModelChecker taggedSystemIO-code)
  taggedModelChecker-complete-code = taggedModelChecker-complete

  taggedProver-complete-boundary-from-code
    : Complete (SatSystemIOₜ.SatSystemIO.Prover taggedSystemIO-boundary-from-code)
  taggedProver-complete-boundary-from-code =
    SatSystemIOₜ.rebase-prover-complete
      (Interlingua.toPresentationC B BoundaryPort∂)
      taggedSystemIO-code
      taggedProver-complete-code

  taggedModelChecker-complete-boundary-from-code
    : Complete (SatSystemIOₜ.SatSystemIO.ModelChecker taggedSystemIO-boundary-from-code)
  taggedModelChecker-complete-boundary-from-code =
    SatSystemIOₜ.rebase-modelChecker-complete
      (Interlingua.toPresentationC B BoundaryPort∂)
      taggedSystemIO-code
      taggedModelChecker-complete-code

  taggedProver-complete-code-from-boundary
    : Complete (SatSystemIOₜ.SatSystemIO.Prover taggedSystemIO-code-from-boundary)
  taggedProver-complete-code-from-boundary =
    SatSystemIOₜ.rebase-prover-complete
      (Interlingua.toPresentationC B CodePort)
      taggedSystemIO-boundary-from-code
      taggedProver-complete-boundary-from-code

  taggedModelChecker-complete-code-from-boundary
    : Complete (SatSystemIOₜ.SatSystemIO.ModelChecker taggedSystemIO-code-from-boundary)
  taggedModelChecker-complete-code-from-boundary =
    SatSystemIOₜ.rebase-modelChecker-complete
      (Interlingua.toPresentationC B CodePort)
      taggedSystemIO-boundary-from-code
      taggedModelChecker-complete-boundary-from-code

  boundary-valid-cert-from-code
    : ∀ (φ : BoundaryPort.Form BoundaryPort∂)
    → (∀ p → BoundaryPort.SatF BoundaryPort∂ p φ)
    → Prov (SatSystemIOₜ.SatSystemIO.Prover taggedSystemIO-boundary-from-code) φ
  boundary-valid-cert-from-code φ satφ =
    Complete.complete taggedProver-complete-boundary-from-code φ satφ

  boundary-sat-cert-from-code
    : ∀ p (φ : BoundaryPort.Form BoundaryPort∂)
    → BoundaryPort.SatF BoundaryPort∂ p φ
    → Prov (SatSystemIOₜ.SatSystemIO.ModelChecker taggedSystemIO-boundary-from-code) (p , φ)
  boundary-sat-cert-from-code p φ sat =
    Complete.complete taggedModelChecker-complete-boundary-from-code (p , φ) sat
