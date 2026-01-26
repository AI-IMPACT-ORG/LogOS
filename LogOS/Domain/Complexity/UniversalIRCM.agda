{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.UniversalIRCM where

open import LogOS.Prelude
open import LogOS.Computation.Blum using (Blum)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel.Graded

open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TruthRoute

open import LogOS.Domain.UniversalIR.Task as Task using (PATask)
open import LogOS.Domain.UniversalIR.Core using (UCode)
open import LogOS.Domain.UniversalIR.Blum as UBlum using (BlumU)
open import LogOS.Domain.UniversalIR.Schemes as UIS using
  ( UProcess
  ; minskyScheme
  ; lambdaScheme
  ; ethereumScheme
  ; oracleScheme
  ; quantumCircuitScheme
  )
import LogOS.Domain.UniversalIR.Pack as UIPack
import LogOS.Domain.UniversalIR.Size as USize

import LogOS.Computation.SchemeCategory as Cat
import LogOS.Computation.Scheme as Sch

-- Example computation surface: UniversalIR as a StandardCM-style interface.
-- This is a convenience pack, not a canonical assumption.

-- A StandardCM-like interface, but over the *real* UniversalIR `UCode` carrier
-- (not the tiny `Models.Universality.Core.UCode` used elsewhere).
record StandardCMᴵᴿ {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    Input  : Set ℓ
    size   : Input → ℕ

    encD   : Input → UCode
    encV   : Input → UCode
    encVW  : Input → UCode → UCode
    wsize  : UCode → ℕ

    -- Blum time relations for deterministic vs verifier runs.
    BlumD  : Blum UCode
    BlumV  : Blum UCode

    poly   : (ℕ → ℕ) → Set ℓ

open StandardCMᴵᴿ public

-- TruthRoute-style runtime classes over UniversalIR `UCode` ------------------
--
-- Kernel-native: the route is instantiated by supplying a graded kernel and
-- a grade-bound map (ℕ → grade).

module TR
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (toCodeK : UCode → GradedKernel.Code K)
  (fromCodeK : GradedKernel.Code K → UCode)
  (gradeBound : ℕ → QAdapter.Scale Q)
  (M : StandardCMᴵᴿ {ℓ}) where
  open StandardCMᴵᴿ M renaming
    ( Input  to Inputᵀ
    ; size   to sizeᵀ
    ; encD   to encDᵀ
    ; encV   to encVᵀ
    ; encVW  to encVWᵀ
    ; BlumD  to BlumDᵀ
    ; BlumV  to BlumVᵀ
    ; poly   to polyᵀ
    )

  private
    CodeK : Set ℓ
    CodeK = GradedKernel.Code K

    detRunK : Inputᵀ → CodeK
    detRunK x = toCodeK (encDᵀ x)

    verRunK : Inputᵀ → CodeK
    verRunK x = toCodeK (encVᵀ x)

    verRunWithK : Inputᵀ → CodeK → CodeK
    verRunWithK x w = toCodeK (encVWᵀ x (fromCodeK w))

  DetRun : Inputᵀ → CodeK
  DetRun = detRunK

  VerRun : Inputᵀ → CodeK
  VerRun = verRunK

  VerRunWith : Inputᵀ → CodeK → CodeK
  VerRunWith = verRunWithK

  module G = TruthRoute.UniformNatFromRuns
    K
    Inputᵀ
    sizeᵀ
    detRunK
    verRunK
    verRunWithK
    polyᵀ
    gradeBound

  open G public

-- A small “presentation switch”: same universal dynamics, different compilation schemes.
data Brand : Set where
  minsky lambda ethereum oracle quantumCircuit : Brand

choice : Brand → Cat.Choice PATask UProcess
choice minsky = UIS.minskyChoice
choice lambda = UIS.lambdaChoice
choice ethereum = UIS.ethereumChoice
choice oracle = UIS.oracleChoice
choice quantumCircuit = UIS.quantumCircuitChoice

compile : Brand → PATask → UCode
compile b = Cat.Choice.compile (choice b)

fuel : Brand → PATask → ℕ
fuel b = Cat.Choice.fuel (choice b)

-- A `StandardCM` instance for a chosen brand/scheme over the real UniversalIR `UCode`.
-- Witness plumbing uses a structural `UCode` size (still unused for `PATask`).
mkIRCM : PolyPred → Brand → StandardCMᴵᴿ
mkIRCM Pℕ b =
  record
    { Input = PATask
    ; size  = USize.sizePATask

    ; encD  = compile b
    ; encV  = compile b
    ; encVW = λ x _ → compile b x
    ; wsize = USize.ucodeSize

    ; BlumD = BlumU
    ; BlumV = BlumU

    ; poly  = PolyPred.isPoly Pℕ
    }

-- --------------------------------------------------------------------------
-- Integration point with the CS-style universality story:
--
-- For the PA fragment (`PATask`), the concrete representation schemes
-- (Minsky/λ/EVM/Oracle/Circuit) are meaning-invariant: they compute the same
-- observed output (but generally with different cost profiles).
--
-- Extract the run-equality witnesses from the universality pack.

minsky≡lambda-run
  : UIPack.Pack
  → Sch.RunEq UIS.minskyScheme UIS.lambdaScheme
minsky≡lambda-run P = UIPack.minskyLambdaEq (UIPack.claimOf P)

lambda≡ethereum-run
  : UIPack.Pack
  → Sch.RunEq UIS.lambdaScheme UIS.ethereumScheme
lambda≡ethereum-run P = UIPack.lambdaEthereumEq (UIPack.claimOf P)

minsky≡ethereum-run
  : UIPack.Pack
  → Sch.RunEq UIS.minskyScheme UIS.ethereumScheme
minsky≡ethereum-run P = UIPack.minskyEthereumEq (UIPack.claimOf P)

ethereum≡oracle-run
  : UIPack.Pack
  → Sch.RunEq UIS.ethereumScheme UIS.oracleScheme
ethereum≡oracle-run P = UIPack.ethereumOracleEq (UIPack.claimOf P)

oracle≡circuit-run
  : UIPack.Pack
  → Sch.RunEq UIS.oracleScheme UIS.quantumCircuitScheme
oracle≡circuit-run P = UIPack.oracleCircuitEq (UIPack.claimOf P)
