{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Learning.RGFlow.Info where

-- Optional information-theoretic refinements for `RGFlow`.
--
-- Rationale: keep `RGFlow.Core` lightweight so docs builds don’t pull in the
-- complexity/physics stack unless explicitly requested.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.ConAlg using (ConAlg)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.Telemetry using (TelemetryTrace; ProgramTelemetryPort)
open import LogOS.Prelude using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import LogOS.Prelude.NatOrder using (_≤ℕ_)

open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Boundary.FromGradedKernel as GBoundary

import LogOS.Packs.Agents.Experimental.Learning.RGFlow.Core as Core
import LogOS.Complexity.MeasurementCapacity as MC
import LogOS.Complexity.DataProcessingInequality as DPI

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module CoreFor = Core.For K ωCPO
  open CoreFor public

  open QAdapter Q using (Time; τ)
  open LogOSSignature Sig using (Cosp)
  open μ using (_⊑_)
  open ConAlg conAlg using (_⊗∂_; I∂)

  boundaryIO = GBoundary.boundaryIO K

  -- -----------------------------------------------------------------------
  -- Information-theoretic refinements (CFT-inspired).
  -- -----------------------------------------------------------------------

  record InfoToTime : Set (lsuc (lsuc ℓ)) where
    field
      toTime : ℕ → Time
      mono : ∀ {m n} → m ≤ℕ n → QAdapter._≤s_ Q (τ (toTime m)) (τ (toTime n))
      add : ∀ m n → toTime (m +ℕ n) ≡ QAdapter._+_ Q (toTime m) (toTime n)
      zeroT : toTime zero ≡ QAdapter.zero Q

  record InfoCFunction {g : QAdapter.Scale Q} (s : RGStep g) : Set (lsuc (lsuc ℓ)) where
    field
      capacity : MC.MeasurementCapacity Sig Q
      channel : DPI.Channel Cosp
      obs : Policy → Cosp
      obs-step : ∀ c → obs (applyRG s c) ≡ DPI.Channel.run channel (obs c)
      mono : ∀ {c d}
           → _⊑_ c d
           → MC.MeasurementCapacity.info capacity (obs c)
             ≤ℕ
             MC.MeasurementCapacity.info capacity (obs d)
      dpi : ∀ f
           → MC.MeasurementCapacity.info capacity (DPI.Channel.run channel f)
             ≤ℕ
             MC.MeasurementCapacity.info capacity f

  record InfoCFunctionFromTelemetry {g : QAdapter.Scale Q} (s : RGStep g)
                                    {ℓT : Level} (T : TelemetryTrace ℓT)
                                    : Set (lsuc (lsuc (ℓ ⊔ ℓT))) where
    field
      capacity : MC.MeasurementCapacity Sig Q
      telemetry : ProgramTelemetryPort Sig Q _ _ _ boundaryIO T
      bridge : MC.TelemetryCapacityBridge Sig Q boundaryIO T telemetry capacity
      traceInfoMono : MC.TraceInfoMono T (MC.TelemetryCapacityBridge.trace→info bridge)
      channel : DPI.Channel Cosp
      obs : Policy → Cosp
      obs-step : ∀ c → obs (applyRG s c) ≡ DPI.Channel.run channel (obs c)
      mono : ∀ {c d}
           → _⊑_ c d
           → MC.MeasurementCapacity.info capacity (obs c)
             ≤ℕ
             MC.MeasurementCapacity.info capacity (obs d)
      contract
        : ∀ f
        → TelemetryTrace._⊑T_ T
            (ProgramTelemetryPort.observe-∂ telemetry
              (LogOSSignature.to∂ Sig (DPI.Channel.run channel f)))
            (ProgramTelemetryPort.observe-∂ telemetry
              (LogOSSignature.to∂ Sig f))

  infoC-from-telemetry
    : ∀ {g} {s : RGStep g} {ℓT : Level} {T : TelemetryTrace ℓT}
    → InfoCFunctionFromTelemetry s T
    → InfoCFunction s
  infoC-from-telemetry {s = s} {T = T} F =
    record
      { capacity = InfoCFunctionFromTelemetry.capacity F
      ; channel = InfoCFunctionFromTelemetry.channel F
      ; obs = InfoCFunctionFromTelemetry.obs F
      ; obs-step = InfoCFunctionFromTelemetry.obs-step F
      ; mono = InfoCFunctionFromTelemetry.mono F
      ; dpi = λ f →
          MC.dpiFromTelemetryChannel boundaryIO T
            (InfoCFunctionFromTelemetry.telemetry F)
            (InfoCFunctionFromTelemetry.capacity F)
            (InfoCFunctionFromTelemetry.bridge F)
            (InfoCFunctionFromTelemetry.traceInfoMono F)
            (InfoCFunctionFromTelemetry.channel F)
            (InfoCFunctionFromTelemetry.contract F)
            f
      }

  infoC-step
    : ∀ {g} {s : RGStep g}
    → (F : InfoCFunction s)
    → ∀ c
    → MC.MeasurementCapacity.info (InfoCFunction.capacity F)
        (InfoCFunction.obs F (applyRG s c))
      ≤ℕ
      MC.MeasurementCapacity.info (InfoCFunction.capacity F)
        (InfoCFunction.obs F c)
  infoC-step {s = s} F c =
    let open InfoCFunction F in
    subst
      (λ x → MC.MeasurementCapacity.info capacity x
             ≤ℕ
             MC.MeasurementCapacity.info capacity (obs c))
      (sym (obs-step c))
      (dpi (obs c))

  infoC-iter
    : ∀ {g} {s : RGStep g}
    → (F : InfoCFunction s)
    → ∀ n
    → MC.MeasurementCapacity.info (InfoCFunction.capacity F)
        (InfoCFunction.obs F (rg-iter s (suc n)))
      ≤ℕ
      MC.MeasurementCapacity.info (InfoCFunction.capacity F)
        (InfoCFunction.obs F (rg-iter s n))
  infoC-iter {s = s} F n = infoC-step F (rg-iter s n)

  infoC-step-from-telemetry
    : ∀ {g} {s : RGStep g} {ℓT : Level} {T : TelemetryTrace ℓT}
    → (F : InfoCFunctionFromTelemetry s T)
    → ∀ c
    → MC.MeasurementCapacity.info (InfoCFunctionFromTelemetry.capacity F)
        (InfoCFunctionFromTelemetry.obs F (applyRG s c))
      ≤ℕ
      MC.MeasurementCapacity.info (InfoCFunctionFromTelemetry.capacity F)
        (InfoCFunctionFromTelemetry.obs F c)
  infoC-step-from-telemetry F c =
    infoC-step (infoC-from-telemetry F) c

  infoC-iter-from-telemetry
    : ∀ {g} {s : RGStep g} {ℓT : Level} {T : TelemetryTrace ℓT}
    → (F : InfoCFunctionFromTelemetry s T)
    → ∀ n
    → MC.MeasurementCapacity.info (InfoCFunctionFromTelemetry.capacity F)
        (InfoCFunctionFromTelemetry.obs F (rg-iter s (suc n)))
      ≤ℕ
      MC.MeasurementCapacity.info (InfoCFunctionFromTelemetry.capacity F)
        (InfoCFunctionFromTelemetry.obs F (rg-iter s n))
  infoC-iter-from-telemetry F n =
    infoC-iter (infoC-from-telemetry F) n

  c-from-info
    : ∀ {g} {s : RGStep g}
    → InfoToTime
    → InfoCFunction s
    → CFunction s
  c-from-info IT F =
    record
      { cfun = λ c → InfoToTime.toTime IT
                   (MC.MeasurementCapacity.info (InfoCFunction.capacity F)
                     (InfoCFunction.obs F c))
      ; mono = λ {c} {d} le →
          InfoToTime.mono IT (InfoCFunction.mono F le)
      ; step = λ c →
          InfoToTime.mono IT (infoC-step F c)
      }

  c-from-info-telemetry
    : ∀ {g} {s : RGStep g} {ℓT : Level} {T : TelemetryTrace ℓT}
    → InfoToTime
    → InfoCFunctionFromTelemetry s T
    → CFunction s
  c-from-info-telemetry IT F =
    c-from-info IT (infoC-from-telemetry F)

  record InfoAFunction {g : QAdapter.Scale Q} (s : RGStep g) : Set (lsuc (lsuc ℓ)) where
    field
      capacity : MC.MeasurementCapacity Sig Q
      channel : DPI.Channel Cosp
      obs : Policy → Cosp
      obs-step : ∀ c → obs (applyRG s c) ≡ DPI.Channel.run channel (obs c)
      mono : ∀ {c d}
           → _⊑_ c d
           → MC.MeasurementCapacity.info capacity (obs c)
             ≤ℕ
             MC.MeasurementCapacity.info capacity (obs d)
      dpi : ∀ f
           → MC.MeasurementCapacity.info capacity (DPI.Channel.run channel f)
             ≤ℕ
             MC.MeasurementCapacity.info capacity f
      tensor : ∀ c d
             → MC.MeasurementCapacity.info capacity (obs (c ⊗∂ d))
               ≤ℕ
               MC.MeasurementCapacity.info capacity (obs c)
               +ℕ
               MC.MeasurementCapacity.info capacity (obs d)
      unit : MC.MeasurementCapacity.info capacity (obs I∂) ≤ℕ zero

  a-from-info
    : ∀ {g} {s : RGStep g}
    → InfoToTime
    → InfoAFunction s
    → AFunction s
  a-from-info IT F =
    record
      { afun = λ c → InfoToTime.toTime IT
                   (MC.MeasurementCapacity.info (InfoAFunction.capacity F)
                     (InfoAFunction.obs F c))
      ; mono = λ {c} {d} le →
          InfoToTime.mono IT (InfoAFunction.mono F le)
      ; step = λ c →
          let open InfoAFunction F in
          InfoToTime.mono IT
            (subst
              (λ x → MC.MeasurementCapacity.info capacity x
                     ≤ℕ
                     MC.MeasurementCapacity.info capacity (obs c))
              (sym (obs-step c))
              (dpi (obs c)))
      ; tensor = λ c d →
          let m = MC.MeasurementCapacity.info (InfoAFunction.capacity F) (InfoAFunction.obs F c)
              n = MC.MeasurementCapacity.info (InfoAFunction.capacity F) (InfoAFunction.obs F d)
              step = InfoToTime.mono IT (InfoAFunction.tensor F c d)
          in subst
               (λ x → QAdapter._≤s_ Q
                        (τ (InfoToTime.toTime IT
                          (MC.MeasurementCapacity.info (InfoAFunction.capacity F)
                            (InfoAFunction.obs F (c ⊗∂ d)))))
                        (τ x))
               (InfoToTime.add IT m n)
               step
      ; unit =
          let le = InfoToTime.mono IT (InfoAFunction.unit F)
          in subst (λ x → QAdapter._≤s_ Q
                           (τ (InfoToTime.toTime IT
                             (MC.MeasurementCapacity.info (InfoAFunction.capacity F)
                               (InfoAFunction.obs F I∂))))
                           (τ x))
                   (InfoToTime.zeroT IT)
                   le
      }
