{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.ObservedKernel where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Core using (UCode; UM; UL; UE; UQ; UQC; stepU)
open import LogOS.Domain.UniversalIR.Core.Lambda using (LambdaCode; mkL; stepLC; var)
open import LogOS.Domain.UniversalIR.Core.Minsky using (MinskyCode; mkM; stepM)
open import LogOS.Domain.UniversalIR.Core.Ethereum using (EVMCode; mkE; mem0; stepE)
open import LogOS.Domain.UniversalIR.Core.QuantumOracle using (QuantumCode; mkQ; stepQ)
open import LogOS.Domain.UniversalIR.Core.QuantumCircuit using (QuantumCircuitCode; mkQC; stepQC)
import LogOS.QAdapters.QNatTop as QTop
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Syntax.Prop as Prop
import LogOS.Computation.KernelUniversalProcess as KUP

open import LogOS.Prelude.List using ([])
open import LogOS.Prelude.Nat using (zero)

-- Observation kits: a boundary observation, optionally equipped with
-- a step homomorphism for kernel construction.

record KernelObsKit : Set (lsuc lzero) where
  field
    CPObs : ConPreorder lzero

  open ConPreorder CPObs public using (Con; _⊑_)

  field
    observeU : UCode → Con
    encodeObs : Con → UCode
    observe-encode : ∀ o → observeU (encodeObs o) ≡ o

    obsI : Con

record ObsKit : Set (lsuc lzero) where
  field
    base : KernelObsKit

  open KernelObsKit base public

  field
    obsStep : Con → Con
    obsStep-mono : ∀ {c d} → c ⊑ d → obsStep c ⊑ obsStep d
    obsI-fixed : (obsI ⊑ obsStep obsI) × (obsStep obsI ⊑ obsI)
    observe-step : ∀ γ → observeU (stepU γ) ≡ obsStep (observeU γ)

-- Minimal observation kit: the full code is the observable.
-- This is the smallest homomorphic observation (identity).

CodeObsKit : ObsKit
CodeObsKit =
  record
    { base = record
        { CPObs = record
            { Con = UCode
            ; _⊑_ = _≡_
            ; refl = refl
            ; trans = trans
            }
        ; observeU = λ u → u
        ; encodeObs = λ u → u
        ; observe-encode = λ _ → refl
        ; obsI = UM (mkM zero zero zero zero zero [])
        }
    ; obsStep = stepU
    ; obsStep-mono = λ {c} {d} eq → cong stepU eq
    ; obsI-fixed = (refl , refl)
    ; observe-step = λ _ → refl
    }

-- Lambda-only observation: project to the λ-branch, fall back to a fixed
-- λ-normal form elsewhere. The fallback is chosen so `stepLC` is definitional.

LambdaObsKit : ObsKit
LambdaObsKit =
  let
    l0 : LambdaCode
    l0 = mkL (var zero)
  in
  record
    { base = record
        { CPObs = record
            { Con = LambdaCode
            ; _⊑_ = _≡_
            ; refl = refl
            ; trans = trans
            }
        ; observeU = λ where
            (UL l)  → l
            (UM _)  → l0
            (UE _)  → l0
            (UQ _)  → l0
            (UQC _) → l0
        ; encodeObs = UL
        ; observe-encode = λ _ → refl
        ; obsI = l0
        }
    ; obsStep = stepLC
    ; obsStep-mono = λ {c} {d} eq → cong stepLC eq
    ; obsI-fixed = (refl , refl)
    ; observe-step = λ where
        (UL _)  → refl
        (UM _)  → refl
        (UE _)  → refl
        (UQ _)  → refl
        (UQC _) → refl
    }

-- Minsky-only observation: project to the Minsky branch, fall back to a fixed
-- halted machine elsewhere.

MinskyObsKit : ObsKit
MinskyObsKit =
  let
    m0 = mkM zero zero zero zero zero []
  in
  record
    { base = record
        { CPObs = record
            { Con = MinskyCode
            ; _⊑_ = _≡_
            ; refl = refl
            ; trans = trans
            }
        ; observeU = λ where
            (UM m)  → m
            (UL _)  → m0
            (UE _)  → m0
            (UQ _)  → m0
            (UQC _) → m0
        ; encodeObs = UM
        ; observe-encode = λ _ → refl
        ; obsI = m0
        }
    ; obsStep = stepM
    ; obsStep-mono = λ {c} {d} eq → cong stepM eq
    ; obsI-fixed = (refl , refl)
    ; observe-step = λ where
        (UM _)  → refl
        (UL _)  → refl
        (UE _)  → refl
        (UQ _)  → refl
        (UQC _) → refl
    }

-- Ethereum-only observation: project to the EVM branch, fall back to a halted
-- machine elsewhere.

EthereumObsKit : ObsKit
EthereumObsKit =
  let
    e0 = mkE zero [] mem0 []
  in
  record
    { base = record
        { CPObs = record
            { Con = EVMCode
            ; _⊑_ = _≡_
            ; refl = refl
            ; trans = trans
            }
        ; observeU = λ where
            (UE e)  → e
            (UM _)  → e0
            (UL _)  → e0
            (UQ _)  → e0
            (UQC _) → e0
        ; encodeObs = UE
        ; observe-encode = λ _ → refl
        ; obsI = e0
        }
    ; obsStep = stepE
    ; obsStep-mono = λ {c} {d} eq → cong stepE eq
    ; obsI-fixed = (refl , refl)
    ; observe-step = λ where
        (UE _)  → refl
        (UM _)  → refl
        (UL _)  → refl
        (UQ _)  → refl
        (UQC _) → refl
    }

-- Oracle-only observation: project to the oracle branch, fall back to a fixed
-- halted oracle code elsewhere.

QuantumOracleObsKit : ObsKit
QuantumOracleObsKit =
  let
    q0 : QuantumCode
    q0 = mkQ zero zero zero zero zero [] []
  in
  record
    { base = record
        { CPObs = record
            { Con = QuantumCode
            ; _⊑_ = _≡_
            ; refl = refl
            ; trans = trans
            }
        ; observeU = λ where
            (UQ q)  → q
            (UM _)  → q0
            (UL _)  → q0
            (UE _)  → q0
            (UQC _) → q0
        ; encodeObs = UQ
        ; observe-encode = λ _ → refl
        ; obsI = q0
        }
    ; obsStep = stepQ
    ; obsStep-mono = λ {c} {d} eq → cong stepQ eq
    ; obsI-fixed = (refl , refl)
    ; observe-step = λ where
        (UQ _)  → refl
        (UM _)  → refl
        (UL _)  → refl
        (UE _)  → refl
        (UQC _) → refl
    }

-- Circuit-only observation: project to the circuit branch, fall back to a
-- halted basis-state circuit elsewhere.

QuantumCircuitObsKit : ObsKit
QuantumCircuitObsKit =
  let
    qc0 : QuantumCircuitCode
    qc0 = mkQC zero zero [] []
  in
  record
    { base = record
        { CPObs = record
            { Con = QuantumCircuitCode
            ; _⊑_ = _≡_
            ; refl = refl
            ; trans = trans
            }
        ; observeU = λ where
            (UQC q) → q
            (UM _)  → qc0
            (UL _)  → qc0
            (UE _)  → qc0
            (UQ _)  → qc0
        ; encodeObs = UQC
        ; observe-encode = λ _ → refl
        ; obsI = qc0
        }
    ; obsStep = stepQC
    ; obsStep-mono = λ {c} {d} eq → cong stepQC eq
    ; obsI-fixed = (refl , refl)
    ; observe-step = λ where
        (UQC _) → refl
        (UM _)  → refl
        (UL _)  → refl
        (UE _)  → refl
        (UQ _)  → refl
    }

module ForObsKit (K : ObsKit) where
  open ObsKit K
  module CP = ConPreorder CPObs

  Sig : LogOSSignature lzero
  Sig = record
    { sorts = record { Iface = ⊤ ; Cosp = CP.Con ; ∂Cosp = CP.Con }
    ; cospanOps = record
        { src = λ _ → tt
        ; tgt = λ _ → tt
        ; idC = λ _ → obsI
        ; _∘C_ = λ _ _ → obsI
        ; _⊕C_ = λ _ _ → obsI
        ; _⊗C_ = λ _ _ → obsI
        }
    ; boundaryOps = record
        { src∂ = λ _ → tt
        ; tgt∂ = λ _ → tt
        ; id∂ = λ _ → obsI
        ; _∘∂_ = λ _ _ → obsI
        ; _⊕∂_ = λ _ _ → obsI
        ; _⊗∂_ = λ _ _ → obsI
        ; from∂ = λ x → x
        ; to∂ = λ x → x
        }
    }

  Q : QAdapter lzero
  Q = QTop.QNatTop

  module W = Worlds Sig

  HWorld : W.WorldH Q
  HWorld = record
    { _≤ctx_ = λ w w' → CP._⊑_ w' w
    ; WFlow = λ _ _ → QAdapter.e Q
    ; wflow-refl = λ _ → QAdapter.≤s-refl Q
    ; wflow-trans = λ _ _ _ → QAdapter.≤s-refl Q
    }

  BB : BulkBoundary lzero
  BB = record { bulk = CPObs ; bnd = CPObs }

  MBulk : MonoidalOps (BulkBoundary.bulk BB)
  MBulk =
    record
      { _⊗_ = λ x _ → x
      ; I = obsI
      ; mono⊗ = λ {x} {x'} {y} {y'} x⊑x' _ → x⊑x'
      }

  MBnd : MonoidalOps (BulkBoundary.bnd BB)
  MBnd =
    record
      { _⊗_ = λ x _ → x
      ; I = obsI
      ; mono⊗ = λ {x} {x'} {y} {y'} x⊑x' _ → x⊑x'
      }

  Holo : LaxMonoidalAdjunction BB MBulk MBnd
  Holo =
    record
      { core = record
          { ext = λ x → x
          ; bnd = λ x → x
          ; unit-lax = λ _ → CP.refl
          ; counit-lax = λ _ → CP.refl
          }
      ; ext-⊗-lax = λ _ _ → CP.refl
      ; ext-I-lax = CP.refl
      ; bnd-⊗-lax = λ _ _ → CP.refl
      ; bnd-I-lax = CP.refl
      }

  module HT = Truth.HomotypicalTruth Sig Q HWorld

  HTruth : HT.HLayer BB
  HTruth =
    record
      { Sat_H = λ p c → CP._⊑_ p c
      ; mono-Con = λ {w} {c} {c'} le sat → CP.trans sat le
      ; mono-ctx = λ le sat → CP.trans le sat
      }

  HInv : HT.Invariance BB
  HInv = record { Inv_H = λ c → c ; infl = λ _ → CP.refl ; idemp-lax = λ _ → CP.refl }

  module GT = Truth.GuardedTruth Sig Q

  GTruth : GT.GuardedClosure (BulkBoundary.bnd BB)
  GTruth =
    record
      { Flow = λ c → c
      ; mono = λ le → le
      ; infl = λ _ → CP.refl
      ; idemp-lax = λ _ → CP.refl
      ; Th* = obsI
      ; Th*-fixed = (CP.refl , CP.refl)
      }

  private
    γ*-guard-obs
      : CP._⊑_ (observeU (encodeObs obsI))
          (observeU (stepU (encodeObs obsI)))
        × CP._⊑_ (observeU (stepU (encodeObs obsI)))
          (observeU (encodeObs obsI))
    γ*-guard-obs =
      let
        obsI-dec = observe-encode obsI
        step-dec =
          trans (observe-step (encodeObs obsI)) (cong obsStep obsI-dec)
        fixed' =
          subst
            (λ x → CP._⊑_ obsI x × CP._⊑_ x obsI)
            (sym step-dec)
            obsI-fixed
      in
      subst
        (λ x →
          CP._⊑_ x (observeU (stepU (encodeObs obsI)))
          × CP._⊑_ (observeU (stepU (encodeObs obsI))) x)
        (sym obsI-dec)
        fixed'

  -- Use KernelUniversalProcess.ForKernel on ObsKernel to obtain the
  -- code/boundary processes with stepU and the chosen observation space.
  ObsKernel : Kernel Sig Q
  ObsKernel =
    record
      { shape = record
          { HWorld = HWorld
          ; BB = BB
          ; MBulk = MBulk
          ; MBnd = MBnd
          ; Holo = Holo
          ; HTruth = HTruth
          ; HInv = HInv
          ; Sat_H_bnd = λ p c → CP._⊑_ p c
          ; sat-coh = λ _ _ → Prop.↔-refl
          ; Fml = ⊤
          ; Strict = record { Sat_S = λ w _ → CP._⊑_ w obsI }
          ; TransH = λ _ → obsI
          ; coh-LH = λ _ _ → Prop.↔-refl
          ; Code = UCode
          ; encode = encodeObs
          ; decode = observeU
          ; Guard = λ γ → γ
          ; Body = stepU
          ; γ* = encodeObs obsI
          ; reify = λ γ → γ
          ; Body∂ = obsStep
          }
      ; GTruth = GTruth
      ; laws = record
          { shapeLaws = record
              { decode∘encode = observe-encode
              ; γ*-guard = γ*-guard-obs
              ; reify-decode = λ _ → refl
              ; body-decode = observe-step
              }
          ; mono-Body∂ = obsStep-mono
          ; mono-Flow = λ {c} {d} le → le
          ; guard-decode = λ _ → refl
          ; decode-γ* = observe-encode obsI
          }
      }

  module Process where
    module KP = KUP.ForKernel ObsKernel
    open KP public

module Ports (K : ObsKit) where
  module OK = ForObsKit K
  import LogOS.Ports.Semantic.CanonicalPorts as CP

  module KPorts = CP.For OK.ObsKernel
  open KPorts public
