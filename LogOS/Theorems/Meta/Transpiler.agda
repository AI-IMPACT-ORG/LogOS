{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Transpiler where

-- General transpiler theorem: any port adapter is the unique translation
-- determined by boundary satisfaction, hence a pass correct up to satisfaction
-- equivalence (↔).

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.Port using (BoundaryPort)
open import LogOS.Boundary.Telemetry
open import LogOS.Syntax.Prop as Prop

import LogOS.Ports.Semantic.Interoperability as Interop
open import LogOS.Ports.Semantic.PresentationCore using (PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor)
open import LogOS.Ports.Semantic.PresentationCore using (SatSystem)
import LogOS.Ports.Semantic.HeteroInterlinguaCore as HeteroCore
import LogOS.Boundary.Budget as Budget

record Iso
  {ℓ : Level}
  {ℓForm₁ ℓForm₂ : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
  (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  : Set (lsuc (ℓ ⊔ ℓForm₁ ⊔ ℓForm₂)) where
  field
    to   : Interop.PortAdapter B P₁ P₂
    from : Interop.PortAdapter B P₂ P₁
    to∘from≈id
      : Interop.For.Adapter≈ B P₂ P₂
          (Interop.composeAdapter B P₂ P₁ P₂ from to)
          (Interop.idAdapter B P₂)
    from∘to≈id
      : Interop.For.Adapter≈ B P₁ P₁
          (Interop.composeAdapter B P₁ P₂ P₁ to from)
          (Interop.idAdapter B P₁)

module Pipeline
  {ℓ : Level}
  {ℓForm₁ ℓForm₂ ℓForm₃ : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
  (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  (P₃ : BoundaryPort {ℓForm = ℓForm₃} Sig Q W BB H B)
  where

  pipeline
    : Interop.PortAdapter B P₁ P₂
    → Interop.PortAdapter B P₂ P₃
    → Interop.PortAdapter B P₁ P₃
  pipeline A B₁ = Interop.composeAdapter B P₁ P₂ P₃ A B₁

  pipeline-correct
    : ∀ A B₁ p φ
    → Prop._↔_
        (BoundaryPort.SatF P₁ p φ)
        (BoundaryPort.SatF P₃ p (Interop.PortAdapter.map (pipeline A B₁) φ))
  pipeline-correct A B₁ = Interop.PortAdapter.preserves-Sat (pipeline A B₁)

module For
  {ℓ : Level}
  {ℓForm₁ ℓForm₂ : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
  (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  where

  open Interop using (PortAdapter)
  module I = Interop.For B P₁ P₂

  record Transpiler : Set (lsuc (ℓ ⊔ ℓForm₁ ⊔ ℓForm₂)) where
    field
      pass : PortAdapter B P₁ P₂

  transpiler-from-adapter : PortAdapter B P₁ P₂ → Transpiler
  transpiler-from-adapter A = record { pass = A }

  transpiler-from-pass : PortAdapter B P₁ P₂ → Transpiler
  transpiler-from-pass = transpiler-from-adapter

  canonical-transpiler : Transpiler
  canonical-transpiler = transpiler-from-adapter I.canonicalAdapter

  transpiler-correct
    : ∀ (T : Transpiler) p φ
    → Prop._↔_
        (BoundaryPort.SatF P₁ p φ)
        (BoundaryPort.SatF P₂ p (PortAdapter.map (Transpiler.pass T) φ))
  transpiler-correct T = PortAdapter.preserves-Sat (Transpiler.pass T)

  transpiler-unique
    : ∀ (T : Transpiler)
    → I.Adapter≈ (Transpiler.pass T) I.canonicalAdapter
  transpiler-unique T = I.adapter-unique (Transpiler.pass T)

  -- Type-soundness view: any transpiler preserves judgments at a chosen observer.
  module TypeSoundness (T : Transpiler) where
    preserves-typing
      : ∀ p φ
      → BoundaryPort.SatF P₁ p φ
      → BoundaryPort.SatF P₂ p (PortAdapter.map (Transpiler.pass T) φ)
    preserves-typing p φ =
      Prop.to (transpiler-correct T p φ)

    reflects-typing
      : ∀ p φ
      → BoundaryPort.SatF P₂ p (PortAdapter.map (Transpiler.pass T) φ)
      → BoundaryPort.SatF P₁ p φ
    reflects-typing p φ =
      Prop.from (transpiler-correct T p φ)

  record SoundPass : Set (lsuc (ℓ ⊔ ℓForm₁ ⊔ ℓForm₂)) where
    field
      pass : Interop.PortRefinement B P₁ P₂

  sound-from-adapter : PortAdapter B P₁ P₂ → SoundPass
  sound-from-adapter A = record { pass = Interop.refinement-from-adapter B A }

  sound-correct
    : ∀ (S : SoundPass) p φ
    → BoundaryPort.SatF P₁ p φ
    → BoundaryPort.SatF P₂ p (Interop.PortRefinement.map (SoundPass.pass S) φ)
  sound-correct S p φ =
    Interop.PortRefinement.preserves-Sat (SoundPass.pass S) p φ

module Hetero
  {ℓCtx₁ ℓCon₁ ℓForm₁ ℓSat₁ : Level}
  {S₁ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₁} {ℓSat = ℓSat₁}}
  {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
  {S₂ : SatSystem {ℓCtx = ℓCtx₂} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂}}
  (m  : SatMor S₁ S₂)
  (P₁ : PresentationC {ℓForm = ℓForm₁} S₁)
  (P₂ : PresentationC {ℓForm = ℓForm₂} S₂)
  where

  module H = HeteroCore.For m P₁ P₂
  module P1 = PresentationC P₁
  module P2 = PresentationC P₂

  record Transpiler : Set (lsuc (ℓCtx₁ ⊔ ℓCtx₂ ⊔ ℓForm₁ ⊔ ℓForm₂ ⊔ ℓSat₁ ⊔ ℓSat₂)) where
    field
      pass : P1.Form → P2.Form
      preserves : H.SemPreserving pass

  transpiler-from-translation
    : ∀ (t : P1.Form → P2.Form)
    → H.SemPreserving t
    → Transpiler
  transpiler-from-translation t pres =
    record
      { pass = t
      ; preserves = pres
      }

  transpiler-from-pass
    : ∀ (t : P1.Form → P2.Form)
    → H.SemPreserving t
    → Transpiler
  transpiler-from-pass = transpiler-from-translation

  canonical-transpiler : Transpiler
  canonical-transpiler =
    transpiler-from-translation H.translate H.translate-preserves-Sat

  transpiler-correct
    : ∀ (T : Transpiler) p φ
    → Prop._↔_ (P1.SatF p φ) (H.SatF₂↑ p (Transpiler.pass T φ))
  transpiler-correct T = Transpiler.preserves T

  transpiler-unique
    : ∀ (T : Transpiler)
    → H.Trans≈ (Transpiler.pass T) H.translate
  transpiler-unique T =
    H.translate-unique (Transpiler.pass T) (Transpiler.preserves T)

module Telemetry
  {ℓ : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  (T : TelemetryTrace ℓ)
  (P : ProgramTelemetryPort Sig Q W BB H B T)
  {ℓForm₁ ℓForm₂ : Level}
  (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
  (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  where

  module Bgt = Budget.For Sig Q W BB H B T P
  open TelemetryTrace T using (Trace; _⊑T_; transT)
  open Bgt using (Budget; budget-from-trace; BudgetCosp)

  record BudgetedPass
    (A : Interop.PortAdapter B P₁ P₂)
    : Set (lsuc (ℓ ⊔ ℓForm₁ ⊔ ℓForm₂)) where
    field
      budget : Budget
      correct : ∀ p φ
        → Prop._↔_
            (BoundaryPort.SatF P₁ p φ)
            (BoundaryPort.SatF P₂ p (Interop.PortAdapter.map A φ))

  budgeted-from-trace
    : ∀ (A : Interop.PortAdapter B P₁ P₂)
    → Trace
    → BudgetedPass A
  budgeted-from-trace A t =
    record
      { budget = budget-from-trace t
      ; correct = Interop.PortAdapter.preserves-Sat A
      }

  budget-weakening
    : ∀ {b b'}
    → b ⊑T b'
    → ∀ w
    → BudgetCosp b w
    → BudgetCosp b' w
  budget-weakening {b} {b'} b≤b' w bw = transT bw b≤b'

  budget-from-trace-weakening
    : ∀ {b b'}
    → b ⊑T b'
    → ∀ w
    → budget-from-trace b w
    → budget-from-trace b' w
  budget-from-trace-weakening = budget-weakening

module TelemetryPipeline
  {ℓ : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  (T : TelemetryTrace ℓ)
  (P : ProgramTelemetryPort Sig Q W BB H B T)
  {ℓForm₁ ℓForm₂ ℓForm₃ : Level}
  (P₁ : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
  (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  (P₃ : BoundaryPort {ℓForm = ℓForm₃} Sig Q W BB H B)
  where

  module T12 = Telemetry B T P P₁ P₂
  module T23 = Telemetry B T P P₂ P₃
  module T13 = Telemetry B T P P₁ P₃

  Budget∧ : T12.Bgt.Budget → T23.Bgt.Budget → T13.Bgt.Budget
  Budget∧ b₁ b₂ w = b₁ w × b₂ w

  budgeted-pipeline
    : ∀ {A B₁}
    → T12.BudgetedPass A
    → T23.BudgetedPass B₁
    → T13.BudgetedPass (Interop.composeAdapter B P₁ P₂ P₃ A B₁)
  budgeted-pipeline {A} {B₁} bp₁ bp₂ =
    record
      { budget = Budget∧ (T12.BudgetedPass.budget bp₁) (T23.BudgetedPass.budget bp₂)
      ; correct = Interop.PortAdapter.preserves-Sat
          (Interop.composeAdapter B P₁ P₂ P₃ A B₁)
      }
