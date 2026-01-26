{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.MeasurementCapacity where

open import LogOS.Prelude

open import LogOS.Prelude.Nat using (ℕ; zero; suc)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; z≤n; s≤s; trans≤ℕ; ≤ℕ-refl; weakenRight; antisym≤ℕ) public

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.Telemetry using (TelemetryTrace; ProgramTelemetryPort)
open import LogOS.Syntax.Prop using (⊥)
open import LogOS.Ports.Semantic.SatMor using (SatRefinement₀; sat-→₀)

open import LogOS.Domain.Complexity.LCUToLandauer as LCU
open import LogOS.Domain.Complexity.HartleyEntropy using (H₀)
import LogOS.Domain.Complexity.DataProcessingInequality as DPI
import LogOS.Prelude.NatLog2 as NatLog2

open NatLog2 public using (plusR; mul)
open NatLog2 using (exp₂; log₂-mono; log₂-exp₂; plusR-monoL; plusR-monoR; mul-monoR)

-- A LogOS-native “measurement capacity” pack:
-- it bounds how much *classical information* can be extracted (classicalized)
-- per local event, under locality/causality constraints.
--
-- This stays compatible with reversible computation:
-- unitary/reversible dynamics can run arbitrarily long; only classicalization is charged.

-- “Extractable classical info” is abstracted as a natural number.
-- Models can instantiate this with (log of) distinguishable outcomes, mutual information, etc.
-- For a fully internal, computable notion of “log in bits” on ℕ, see `LogOS.Prelude.NatLog2.log₂`.

-- Monotonicity of addition and multiplication w.r.t. ≤ℕ (needed for time/throughput bridges).

suc≢zero : ∀ {n} → suc n ≡ 0 → ⊥ {lzero}
suc≢zero ()

monoPlusL : ∀ {a b} → a ≤ℕ b → ∀ c → plusR a c ≤ℕ plusR b c
monoPlusL = plusR-monoL

lePlusR : ∀ a c → a ≤ℕ plusR a c
lePlusR = NatLog2.lePlusR

monoPlusR : ∀ {c d} → c ≤ℕ d → ∀ a → plusR a c ≤ℕ plusR a d
monoPlusR = plusR-monoR

monoMul : ∀ k {a b} → a ≤ℕ b → mul k a ≤ℕ mul k b
monoMul = mul-monoR

record MeasurementCapacity {ℓ : Level}
                           (Sig : LogOSSignature ℓ)
                           (Q   : QAdapter ℓ)
                           : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  field
    LCUA : LCUObsAssumptions Sig Q

    -- Locality/causality as abstract constraints (kept opaque here).
    Locality  : Set ℓ
    Causality : Set ℓ

    -- A per-program count of classicalization/measurement events.
    meas : Cosp → ℕ

    -- Classical information extracted by a program (in bits, say).
    info : Cosp → ℕ

    -- Capacity bound: each measurement event yields at most κ bits.
    κ : ℕ
    info-ref : SatRefinement₀ Cosp
                (λ _ _ → ⊤ {ℓ = lzero})
                (λ _ f → info f ≤ℕ mul κ (meas f))

    -- Reversibility compatibility: local-unitary programs need no measurements.
    unitary-ref : SatRefinement₀ Cosp
                  (λ _ f → LCUObsAssumptions.LocalUnitary LCUA f)
                  (λ _ f → meas f ≡ 0)

  info≤κ·meas : ∀ f → info f ≤ℕ mul κ (meas f)
  info≤κ·meas f = sat-→₀ info-ref f tt

  unitary→meas0 : ∀ f → LCUObsAssumptions.LocalUnitary LCUA f → meas f ≡ 0
  unitary→meas0 f u = sat-→₀ unitary-ref f u

  -- Derived: unitary programs extract zero classical information.
  unitary→info0 : ∀ f → LCUObsAssumptions.LocalUnitary LCUA f → info f ≡ 0
  unitary→info0 f u =
    let
      meas0 = unitary→meas0 f u
      info≤0 : info f ≤ℕ mul κ 0
      info≤0 = subst (λ n → info f ≤ℕ mul κ n) meas0 (info≤κ·meas f)
    in antisym≤ℕ info≤0 z≤n

  -- Derived: zero measurements imply zero classical information.
  meas0→info0 : ∀ f → meas f ≡ 0 → info f ≡ 0
  meas0→info0 f meas0 =
    let
      info≤0 : info f ≤ℕ mul κ 0
      info≤0 = subst (λ n → info f ≤ℕ mul κ n) meas0 (info≤κ·meas f)
    in antisym≤ℕ info≤0 z≤n

-- Non-vacuity guards: explicit witnesses that measurements and information
-- extraction are possible (avoid degenerate instantiations).

record MeasurementCapacityGuards {ℓ : Level}
                                 (Sig : LogOSSignature ℓ)
                                 (Q   : QAdapter ℓ)
                                 (cap : MeasurementCapacity Sig Q)
                                 : Set (lsuc (lsuc ℓ)) where
  field
    measWitness : Σ (LogOSSignature.Cosp Sig) (λ f → Σ ℕ (λ k → MeasurementCapacity.meas cap f ≡ suc k))
    infoWitness : Σ (LogOSSignature.Cosp Sig) (λ f → Σ ℕ (λ k → MeasurementCapacity.info cap f ≡ suc k))

meas-nonzero
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {cap : MeasurementCapacity Sig Q}
  → MeasurementCapacityGuards Sig Q cap
  → Σ (LogOSSignature.Cosp Sig) (λ f → MeasurementCapacity.meas cap f ≡ 0 → ⊥ {lzero})
meas-nonzero G =
  let
    f , k , eq = MeasurementCapacityGuards.measWitness G
  in
  f , (λ meas0 → suc≢zero (trans (sym eq) meas0))

info-nonzero
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {cap : MeasurementCapacity Sig Q}
  → MeasurementCapacityGuards Sig Q cap
  → Σ (LogOSSignature.Cosp Sig) (λ f → MeasurementCapacity.info cap f ≡ 0 → ⊥ {lzero})
info-nonzero G =
  let
    f , k , eq = MeasurementCapacityGuards.infoWitness G
  in
  f , (λ info0 → suc≢zero (trans (sym eq) info0))

-- Turn an “outcome count fits under 2^(budget)” bound into a `MeasurementCapacity`
-- whose `info` is literally Hartley entropy `H₀` of the outcome count.
--
-- This is a defensible bridge:
--   outcomes(f) ≤ 2^(κ·meas(f))  ⇒  log₂(outcomes(f)) ≤ κ·meas(f)
--
-- No probabilistic/shannonian structure is assumed: everything is over ℕ.

fromOutcomeBound
  : ∀ {ℓ : Level}
    (Sig : LogOSSignature ℓ)
    (Q   : QAdapter ℓ)
    (LCUA : LCU.LCUObsAssumptions Sig Q)
  → (Locality  : Set ℓ)
  → (Causality : Set ℓ)
  → (meas      : LogOSSignature.Cosp Sig → ℕ)
  → (outcomes  : LogOSSignature.Cosp Sig → ℕ)
  → (κ         : ℕ)
  → (outcomes≤2^κ·meas : ∀ f → outcomes f ≤ℕ exp₂ (mul κ (meas f)))
  → (unitary-ref : SatRefinement₀ (LogOSSignature.Cosp Sig)
                    (λ _ f → LCU.LCUObsAssumptions.LocalUnitary LCUA f)
                    (λ _ f → meas f ≡ 0))
  → MeasurementCapacity Sig Q
fromOutcomeBound {ℓ} Sig Q LCUA Locality Causality meas outcomes κ outcomes≤2^κ·meas unitary-ref =
  record
    { LCUA = LCUA
    ; Locality = Locality
    ; Causality = Causality
    ; meas = meas
    ; info = λ f → H₀ (outcomes f)
    ; κ = κ
    ; info-ref =
        record
          { sat-→ = λ _ f _ →
              trans≤ℕ
                (log₂-mono (outcomes≤2^κ·meas f))
                (subst
                  (λ x → H₀ (exp₂ (mul κ (meas f))) ≤ℕ x)
                  (log₂-exp₂ (mul κ (meas f)))
                  ≤ℕ-refl)
          }
    ; unitary-ref = unitary-ref
    }

-- -------------------------------------------------------------------------
-- Non-unitary capacity: a light generalization of measurement capacity.
-- -------------------------------------------------------------------------

record NonUnitaryCapacity {ℓ : Level}
                          (Sig : LogOSSignature ℓ)
                          (Q   : QAdapter ℓ)
                          : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  field
    LCUA : LCU.LCUObsAssumptions Sig Q

    nuEvents : Cosp → ℕ
    info : Cosp → ℕ

    κ : ℕ
    info-ref : SatRefinement₀ Cosp
                (λ _ _ → ⊤ {ℓ = lzero})
                (λ _ f → info f ≤ℕ mul κ (nuEvents f))

    unitary-ref : SatRefinement₀ Cosp
                  (λ _ f → LCU.LCUObsAssumptions.LocalUnitary LCUA f)
                  (λ _ f → nuEvents f ≡ 0)

  info≤κ·nu : ∀ f → info f ≤ℕ mul κ (nuEvents f)
  info≤κ·nu f = sat-→₀ info-ref f tt

  unitary→nu0 : ∀ f → LCU.LCUObsAssumptions.LocalUnitary LCUA f → nuEvents f ≡ 0
  unitary→nu0 f u = sat-→₀ unitary-ref f u

  -- Derived: zero non-unitary events imply zero extractable information.
  nu0→info0 : ∀ f → nuEvents f ≡ 0 → info f ≡ 0
  nu0→info0 f nu0 =
    let
      info≤0 : info f ≤ℕ mul κ 0
      info≤0 = subst (λ n → info f ≤ℕ mul κ n) nu0 (info≤κ·nu f)
    in antisym≤ℕ info≤0 z≤n

  -- Derived: unitary programs extract zero classical information.
  unitary→info0 : ∀ f → LCU.LCUObsAssumptions.LocalUnitary LCUA f → info f ≡ 0
  unitary→info0 f u = nu0→info0 f (unitary→nu0 f u)

record NonUnitaryCapacityGuards {ℓ : Level}
                                (Sig : LogOSSignature ℓ)
                                (Q   : QAdapter ℓ)
                                (cap : NonUnitaryCapacity Sig Q)
                                : Set (lsuc (lsuc ℓ)) where
  field
    nuWitness : Σ (LogOSSignature.Cosp Sig) (λ f → Σ ℕ (λ k → NonUnitaryCapacity.nuEvents cap f ≡ suc k))
    infoWitness : Σ (LogOSSignature.Cosp Sig) (λ f → Σ ℕ (λ k → NonUnitaryCapacity.info cap f ≡ suc k))

nu-nonzero
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {cap : NonUnitaryCapacity Sig Q}
  → NonUnitaryCapacityGuards Sig Q cap
  → Σ (LogOSSignature.Cosp Sig) (λ f → NonUnitaryCapacity.nuEvents cap f ≡ 0 → ⊥ {lzero})
nu-nonzero G =
  let
    f , k , eq = NonUnitaryCapacityGuards.nuWitness G
  in
  f , (λ nu0 → suc≢zero (trans (sym eq) nu0))

info-nonzero-nu
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {cap : NonUnitaryCapacity Sig Q}
  → NonUnitaryCapacityGuards Sig Q cap
  → Σ (LogOSSignature.Cosp Sig) (λ f → NonUnitaryCapacity.info cap f ≡ 0 → ⊥ {lzero})
info-nonzero-nu G =
  let
    f , k , eq = NonUnitaryCapacityGuards.infoWitness G
  in
  f , (λ info0 → suc≢zero (trans (sym eq) info0))

measurementAsNonUnitary
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    → MeasurementCapacity Sig Q
    → NonUnitaryCapacity Sig Q
measurementAsNonUnitary cap =
  record
    { LCUA        = MeasurementCapacity.LCUA cap
    ; nuEvents    = MeasurementCapacity.meas cap
    ; info        = MeasurementCapacity.info cap
    ; κ           = MeasurementCapacity.κ cap
    ; info-ref =
        record
          { sat-→ = λ _ f _ → MeasurementCapacity.info≤κ·meas cap f
          }
    ; unitary-ref =
        record
          { sat-→ = λ _ f u → MeasurementCapacity.unitary→meas0 cap f u
          }
    }

-- -------------------------------------------------------------------------
-- Telemetry alignment: tie measurement capacity to boundary program traces.
-- -------------------------------------------------------------------------

record TelemetryCapacityBridge {ℓ ℓT : Level}
                               (Sig : LogOSSignature ℓ)
                               (Q   : QAdapter ℓ)
                               {W   : Worlds.WorldH Sig Q}
                               {BB  : BulkBoundary ℓ}
                               {H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
                               (B   : BoundaryIO Sig Q W BB H)
                               (T   : TelemetryTrace ℓT)
                               (P   : ProgramTelemetryPort Sig Q W BB H B T)
                               (cap : MeasurementCapacity Sig Q)
                               : Set (lsuc (ℓ ⊔ ℓT)) where
  open LogOSSignature Sig
  open TelemetryTrace T
  open ProgramTelemetryPort P

  field
    trace→meas : Trace → ℕ
    trace→info : Trace → ℕ

    meas-from-telemetry
      : ∀ f → MeasurementCapacity.meas cap f ≡ trace→meas (observe-∂ (to∂ f))
    info-from-telemetry
      : ∀ f → MeasurementCapacity.info cap f ≡ trace→info (observe-∂ (to∂ f))

TraceInfoMono
  : ∀ {ℓT}
  → (T : TelemetryTrace ℓT)
  → (TelemetryTrace.Trace T → ℕ)
  → Set ℓT
TraceInfoMono T info =
  ∀ {x y} → TelemetryTrace._⊑T_ T x y → info x ≤ℕ info y

-- DPI derived from telemetry: if channels coarsen traces and trace-info is
-- monotone, then the induced information on programs satisfies DPI.

dpiFromTelemetry
  : ∀ {ℓ ℓT}
    {Sig : LogOSSignature ℓ}
    {Q   : QAdapter ℓ}
    {W   : Worlds.WorldH Sig Q}
    {BB  : BulkBoundary ℓ}
    {H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B   : BoundaryIO Sig Q W BB H)
    (T   : TelemetryTrace ℓT)
    (P   : ProgramTelemetryPort Sig Q W BB H B T)
    (cap : MeasurementCapacity Sig Q)
    (bridge : TelemetryCapacityBridge Sig Q B T P cap)
  → TraceInfoMono T (TelemetryCapacityBridge.trace→info bridge)
  → (contract
      : ∀ (C : DPI.Channel (LogOSSignature.Cosp Sig)) (f : LogOSSignature.Cosp Sig)
      → TelemetryTrace._⊑T_ T
          (ProgramTelemetryPort.observe-∂ P
            (LogOSSignature.to∂ Sig (DPI.Channel.run C f)))
          (ProgramTelemetryPort.observe-∂ P
            (LogOSSignature.to∂ Sig f)))
  → ∀ (C : DPI.Channel (LogOSSignature.Cosp Sig)) (f : LogOSSignature.Cosp Sig)
  → MeasurementCapacity.info cap (DPI.Channel.run C f)
    ≤ℕ
    MeasurementCapacity.info cap f
dpiFromTelemetry {Sig = Sig} B T P cap bridge traceMono contract C f =
  let
    open TelemetryCapacityBridge bridge
    t1 = ProgramTelemetryPort.observe-∂ P (LogOSSignature.to∂ Sig (DPI.Channel.run C f))
    t2 = ProgramTelemetryPort.observe-∂ P (LogOSSignature.to∂ Sig f)
    step : trace→info t1 ≤ℕ trace→info t2
    step = traceMono (contract C f)
  in
  subst
    (λ n → n ≤ℕ MeasurementCapacity.info cap f)
    (sym (info-from-telemetry (DPI.Channel.run C f)))
    (subst
      (λ n → trace→info t1 ≤ℕ n)
      (sym (info-from-telemetry f))
      step)

-- Specialized DPI: a single channel that coarsens traces yields DPI for that channel.

dpiFromTelemetryChannel
  : ∀ {ℓ ℓT}
    {Sig : LogOSSignature ℓ}
    {Q   : QAdapter ℓ}
    {W   : Worlds.WorldH Sig Q}
    {BB  : BulkBoundary ℓ}
    {H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B   : BoundaryIO Sig Q W BB H)
    (T   : TelemetryTrace ℓT)
    (P   : ProgramTelemetryPort Sig Q W BB H B T)
    (cap : MeasurementCapacity Sig Q)
    (bridge : TelemetryCapacityBridge Sig Q B T P cap)
  → TraceInfoMono T (TelemetryCapacityBridge.trace→info bridge)
  → (C : DPI.Channel (LogOSSignature.Cosp Sig))
  → (contract
      : ∀ f
      → TelemetryTrace._⊑T_ T
          (ProgramTelemetryPort.observe-∂ P
            (LogOSSignature.to∂ Sig (DPI.Channel.run C f)))
          (ProgramTelemetryPort.observe-∂ P
            (LogOSSignature.to∂ Sig f)))
  → ∀ f
  → MeasurementCapacity.info cap (DPI.Channel.run C f)
    ≤ℕ
    MeasurementCapacity.info cap f
dpiFromTelemetryChannel {Sig = Sig} B T P cap bridge traceMono C contract f =
  let
    open TelemetryCapacityBridge bridge
    t1 = ProgramTelemetryPort.observe-∂ P (LogOSSignature.to∂ Sig (DPI.Channel.run C f))
    t2 = ProgramTelemetryPort.observe-∂ P (LogOSSignature.to∂ Sig f)
    step : trace→info t1 ≤ℕ trace→info t2
    step = traceMono (contract f)
  in
  subst
    (λ n → n ≤ℕ MeasurementCapacity.info cap f)
    (sym (info-from-telemetry (DPI.Channel.run C f)))
    (subst
      (λ n → trace→info t1 ≤ℕ n)
      (sym (info-from-telemetry f))
      step)

-- DPI bundle: observational coarsening + trace monotonicity yields DPI.

record TelemetryDPI {ℓ ℓT : Level}
                    (Sig : LogOSSignature ℓ)
                    (Q   : QAdapter ℓ)
                    {W   : Worlds.WorldH Sig Q}
                    {BB  : BulkBoundary ℓ}
                    {H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
                    (B   : BoundaryIO Sig Q W BB H)
                    (T   : TelemetryTrace ℓT)
                    (P   : ProgramTelemetryPort Sig Q W BB H B T)
                    (cap : MeasurementCapacity Sig Q)
                    : Set (lsuc (ℓ ⊔ ℓT)) where
  field
    bridge : TelemetryCapacityBridge Sig Q B T P cap
    traceInfoMono : TraceInfoMono T (TelemetryCapacityBridge.trace→info bridge)
    contract
      : ∀ (C : DPI.Channel (LogOSSignature.Cosp Sig)) (f : LogOSSignature.Cosp Sig)
      → TelemetryTrace._⊑T_ T
          (ProgramTelemetryPort.observe-∂ P
            (LogOSSignature.to∂ Sig (DPI.Channel.run C f)))
          (ProgramTelemetryPort.observe-∂ P
            (LogOSSignature.to∂ Sig f))

  dpi
    : ∀ (C : DPI.Channel (LogOSSignature.Cosp Sig)) (f : LogOSSignature.Cosp Sig)
    → MeasurementCapacity.info cap (DPI.Channel.run C f)
      ≤ℕ
      MeasurementCapacity.info cap f
  dpi = dpiFromTelemetry B T P cap bridge traceInfoMono contract
