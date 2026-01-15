{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Bootstrapping where

-- Bootstrapping check: the kernel's own code port bootstraps into its boundary port.
-- This is not a bespoke “compiler”: it is the canonical interlingua translation
-- between two presentations of the same boundary satisfaction.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop
open import Data.Product using (_×_; _,_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel
import LogOS.Kernel.Core as Core
import LogOS.Kernel.Graded as GK
import LogOS.Kernel.Graded.ToKernel as GradedToKernel

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port
open import LogOS.Boundary.Telemetry
import LogOS.Boundary.Budget as Budget

import LogOS.Ports.Semantic.Interoperability as Interop
import LogOS.Ports.Semantic.Interlingua as Interlingua
import LogOS.Ports.Semantic.VacuityGuards as Vacuity
import LogOS.Ports.Semantic.CanonicalPorts as Canonical
import LogOS.Theorems.CategoryTheory.Port2Cat as Port2Catₜ
import LogOS.Theorems.Meta.Transpiler as Transpiler

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  module CP = Canonical.For K
  open CP using (B; CodePort; BoundaryPort∂)
  open BulkBoundary (Kernel.BB K) using (Con_bnd)

  -- Bootstrapping viewpoint: stage0 = boundary port, stage1 = code port.
  Stage0Port : BoundaryPort {ℓForm = ℓ} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B
  Stage0Port = BoundaryPort∂

  Stage1Port : BoundaryPort {ℓForm = ℓ} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B
  Stage1Port = CodePort

  -- Bootstrap: code (stage1) -> boundary (stage0).
  bootstrap : Interop.PortAdapter B Stage1Port Stage0Port
  bootstrap = Interop.For.canonicalAdapter B Stage1Port Stage0Port

  bootstrap≡canonical
    : bootstrap ≡ Interop.For.canonicalAdapter B Stage1Port Stage0Port
  bootstrap≡canonical = refl

  bootstrap≈canonical
    : Interop.For.Adapter≈ B Stage1Port Stage0Port
        bootstrap (Interop.For.canonicalAdapter B Stage1Port Stage0Port)
  bootstrap≈canonical =
    let module I = Interop.For B Stage1Port Stage0Port in
    I.adapter-unique bootstrap

  bootstrap-correct
    : ∀ p γ
    → BoundaryPort.SatF Stage1Port p γ
        ↔ BoundaryPort.SatF Stage0Port p (Interop.PortAdapter.map bootstrap γ)
  bootstrap-correct = Interop.PortAdapter.preserves-Sat bootstrap

  -- Unbootstrap: boundary (stage0) -> code (stage1) (uses encode).
  unbootstrap : Interop.PortAdapter B Stage0Port Stage1Port
  unbootstrap =
    record
      { map = Kernel.encode K
      ; preserves-Sat = BoundaryPort.Sat∂≈F CodePort
      }

  unbootstrap≈canonical
    : Interop.For.Adapter≈ B Stage0Port Stage1Port
        unbootstrap (Interop.For.canonicalAdapter B Stage0Port Stage1Port)
  unbootstrap≈canonical =
    let module I = Interop.For B Stage0Port Stage1Port in
    I.adapter-unique unbootstrap

  unbootstrap-correct
    : ∀ p c
    → BoundaryPort.SatF Stage0Port p c
        ↔ BoundaryPort.SatF Stage1Port p (Interop.PortAdapter.map unbootstrap c)
  unbootstrap-correct = Interop.PortAdapter.preserves-Sat unbootstrap

  -- Round-trip (stage0/boundary): decode ∘ encode ≈ id.
  bootstrap∘unbootstrap : Interop.PortAdapter B Stage0Port Stage0Port
  bootstrap∘unbootstrap =
    Interop.composeAdapter B Stage0Port Stage1Port Stage0Port unbootstrap bootstrap

  bootstrap∘unbootstrap≈id
    : Interop.For.Adapter≈ B Stage0Port Stage0Port
        bootstrap∘unbootstrap (Interop.idAdapter B Stage0Port)
  bootstrap∘unbootstrap≈id p c =
    let
      module IBC = Interop.For B Stage0Port Stage1Port
      module ICB = Interop.For B Stage1Port Stage0Port

      step₀ =
        Interop.composeAdapter-cong B Stage0Port Stage1Port Stage0Port
          {A = unbootstrap} {A' = IBC.canonicalAdapter}
          {B₁ = bootstrap} {B₁' = ICB.canonicalAdapter}
          unbootstrap≈canonical bootstrap≈canonical

      step₁ : ∀ p c →
        BoundaryPort.SatF Stage0Port p
          (Interop.PortAdapter.map
            (Interop.composeAdapter B Stage0Port Stage1Port Stage0Port
              IBC.canonicalAdapter ICB.canonicalAdapter)
            c)
          ↔
        BoundaryPort.SatF Stage0Port p
          (Interop.PortAdapter.map
            (Interop.For.canonicalAdapter B Stage0Port Stage0Port)
            c)
      step₁ p c =
        Prop.↔-sym (Interop.canonicalAdapter≈comp B Stage0Port Stage1Port Stage0Port p c)

      step₂ : ∀ p c →
        BoundaryPort.SatF Stage0Port p
          (Interop.PortAdapter.map
            (Interop.For.canonicalAdapter B Stage0Port Stage0Port)
            c)
          ↔
        BoundaryPort.SatF Stage0Port p
          (Interop.PortAdapter.map (Interop.idAdapter B Stage0Port) c)
      step₂ p c = Interop.canonicalAdapter≈id B Stage0Port p c
    in
    Prop.↔-trans (step₀ p c) (Prop.↔-trans (step₁ p c) (step₂ p c))

  -- Round-trip (stage1/code): encode ∘ decode ≈ id (observationally).
  unbootstrap∘bootstrap : Interop.PortAdapter B Stage1Port Stage1Port
  unbootstrap∘bootstrap =
    Interop.composeAdapter B Stage1Port Stage0Port Stage1Port bootstrap unbootstrap

  unbootstrap∘bootstrap≈id
    : Interop.For.Adapter≈ B Stage1Port Stage1Port
        unbootstrap∘bootstrap (Interop.idAdapter B Stage1Port)
  unbootstrap∘bootstrap≈id p γ =
    let
      module ICB = Interop.For B Stage1Port Stage0Port
      module IBC = Interop.For B Stage0Port Stage1Port

      step₀ =
        Interop.composeAdapter-cong B Stage1Port Stage0Port Stage1Port
          {A = bootstrap} {A' = ICB.canonicalAdapter}
          {B₁ = unbootstrap} {B₁' = IBC.canonicalAdapter}
          bootstrap≈canonical unbootstrap≈canonical

      step₁ : ∀ p γ →
        BoundaryPort.SatF Stage1Port p
          (Interop.PortAdapter.map
            (Interop.composeAdapter B Stage1Port Stage0Port Stage1Port
              ICB.canonicalAdapter IBC.canonicalAdapter)
            γ)
          ↔
        BoundaryPort.SatF Stage1Port p
          (Interop.PortAdapter.map
            (Interop.For.canonicalAdapter B Stage1Port Stage1Port)
            γ)
      step₁ p γ =
        Prop.↔-sym (Interop.canonicalAdapter≈comp B Stage1Port Stage0Port Stage1Port p γ)

      step₂ : ∀ p γ →
        BoundaryPort.SatF Stage1Port p
          (Interop.PortAdapter.map
            (Interop.For.canonicalAdapter B Stage1Port Stage1Port)
            γ)
          ↔
        BoundaryPort.SatF Stage1Port p
          (Interop.PortAdapter.map (Interop.idAdapter B Stage1Port) γ)
      step₂ p γ = Interop.canonicalAdapter≈id B Stage1Port p γ
    in
    Prop.↔-trans (step₀ p γ) (Prop.↔-trans (step₁ p γ) (step₂ p γ))

  -- Port-level equivalence: bootstrap and unbootstrap are quasi-inverses up to `Adapter≈`.
  BootstrapIso
    : (P₁ P₂ : BoundaryPort {ℓForm = ℓ} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B)
    → Set (lsuc ℓ)
  BootstrapIso = Transpiler.Iso B

  bootstrap-iso : BootstrapIso Stage1Port Stage0Port
  bootstrap-iso =
    record
      { to = bootstrap
      ; from = unbootstrap
      ; to∘from≈id = bootstrap∘unbootstrap≈id
      ; from∘to≈id = unbootstrap∘bootstrap≈id
      }

  -- Transpiler view: bootstrapping is a canonical adapter instance.
  module AsTranspiler where
    module T = Transpiler.For B Stage1Port Stage0Port
    module TBack = Transpiler.For B Stage0Port Stage1Port
    open T public using (Transpiler)

    bootstrap-transpiler : T.Transpiler
    bootstrap-transpiler = T.transpiler-from-adapter bootstrap

    bootstrap-transpiler≡canonical : bootstrap-transpiler ≡ T.canonical-transpiler
    bootstrap-transpiler≡canonical = refl

    unbootstrap-transpiler : TBack.Transpiler
    unbootstrap-transpiler = TBack.transpiler-from-adapter unbootstrap

  -- Phase distinction: any adapter between stages is observationally unique.
  stage1→stage0-unique
    : ∀ (A : Interop.PortAdapter B Stage1Port Stage0Port)
    → Interop.For.Adapter≈ B Stage1Port Stage0Port A bootstrap
  stage1→stage0-unique A p γ =
    let module I = Interop.For B Stage1Port Stage0Port in
    Prop.↔-trans (I.adapter-unique A p γ)
      (Prop.↔-sym (bootstrap≈canonical p γ))

  stage0→stage1-unique
    : ∀ (A : Interop.PortAdapter B Stage0Port Stage1Port)
    → Interop.For.Adapter≈ B Stage0Port Stage1Port A unbootstrap
  stage0→stage1-unique A p c =
    let module I = Interop.For B Stage0Port Stage1Port in
    Prop.↔-trans (I.adapter-unique A p c)
      (Prop.↔-sym (unbootstrap≈canonical p c))

  -- Refinement view: stage semantics agree via the adapters.
  stage1-refines-stage0
    : ∀ p γ
    → BoundaryPort.SatF Stage1Port p γ
        ↔ BoundaryPort.SatF Stage0Port p (Interop.PortAdapter.map bootstrap γ)
  stage1-refines-stage0 = bootstrap-correct

  stage0-refines-stage1
    : ∀ p c
    → BoundaryPort.SatF Stage0Port p c
        ↔ BoundaryPort.SatF Stage1Port p (Interop.PortAdapter.map unbootstrap c)
  stage0-refines-stage1 = unbootstrap-correct

  -- Pass composition: adapters form pipelines with correctness by construction.
  module Pipeline
    {ℓForm₂ ℓForm₃ : Level}
    (P₂ : BoundaryPort {ℓForm = ℓForm₂} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B)
    (P₃ : BoundaryPort {ℓForm = ℓForm₃} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B)
    where
    module P = Transpiler.Pipeline B Stage1Port P₂ P₃
    open P public

  -- 2-category packaging: bootstrap as a 1-cell with a named 2-cell.
  module Port2Cat where
    module P = Port2Catₜ.For {ℓForm = ℓ} B
    open Port2Catₜ.Port2Cat P.Port2Cat-instance

    bootstrap₁ : Hom Stage1Port Stage0Port
    bootstrap₁ = bootstrap

    bootstrap≈refl : bootstrap₁ ⇒ bootstrap₁
    bootstrap≈refl = id⇒ bootstrap₁

  -- Closure/effect transport: boundary endomaps commute with bootstrapping.
  module Closure where
    module I = Interlingua.For B Stage1Port Stage0Port
    open I public using (Respects≈∂)

    bootstrap-closure-naturality
      : ∀ (F : Con_bnd → Con_bnd)
      → Respects≈∂ F
      → ∀ p γ
      → BoundaryPort.SatF Stage0Port p (I.translate (BoundaryPort.Extend Stage1Port F γ))
          ↔
        BoundaryPort.SatF Stage0Port p (BoundaryPort.Extend Stage0Port F (I.translate γ))
    bootstrap-closure-naturality F extF p γ =
      I.ported-closure-naturality F extF p γ

  -- Vacuity guard: encode is injective (uses decode∘encode).
  encode-injective : ∀ {c d}
    → Kernel.encode K c ≡ Kernel.encode K d
    → c ≡ d
  encode-injective {c} {d} eq =
    trans
      (sym (Kernel.decode∘encode K c))
      (trans (cong (Kernel.decode K) eq) (Kernel.decode∘encode K d))

  module VacuityGuards
    (G : Vacuity.PortVacuityGuards B BoundaryPort∂)
    where
    open Vacuity.PortVacuityGuards G

    unbootstrap-guards
      : Vacuity.AdapterVacuityGuards B Stage0Port Stage1Port unbootstrap
    unbootstrap-guards =
      record
        { p = p
        ; φ₀ = φ₀
        ; φ₁ = φ₁
        ; sat₀ = sat₀
        ; unsat₁ = unsat₁
        ; φ₀≢φ₁ = import-distinct
        ; map-distinct = λ eq → import-distinct (encode-injective eq)
        }

  -- External port handshake: canonical adapter factors through the bootstrap adapter.
  module Handshake
    (P : BoundaryPort {ℓForm = ℓ} Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B)
    where

    canonical-from-stage1 : Interop.PortAdapter B Stage1Port P
    canonical-from-stage1 = Interop.For.canonicalAdapter B Stage1Port P

    canonical-from-stage0 : Interop.PortAdapter B Stage0Port P
    canonical-from-stage0 = Interop.For.canonicalAdapter B Stage0Port P

    factors-through-bootstrap
      : Interop.For.Adapter≈ B Stage1Port P
          canonical-from-stage1
          (Interop.composeAdapter B Stage1Port Stage0Port P bootstrap canonical-from-stage0)
    factors-through-bootstrap p φ =
      Interlingua.translate-comp B Stage1Port Stage0Port P p φ

  -- Telemetry-bundled check: bootstrap + trace-derived budget.
  module Telemetry
    (T : TelemetryTrace ℓ)
    (P : ProgramTelemetryPort Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B T)
    where
    module Bgt =
      Budget.For Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) B T P
    module TP = Transpiler.Telemetry B T P Stage1Port Stage0Port
    open TelemetryTrace T using (Trace)
    open Bgt using (Budget; budget-from-trace)
    open TP public using (budget-weakening; budget-from-trace-weakening)

    record BudgetedBootstrap : Set (lsuc ℓ) where
      field
        adapter : Interop.PortAdapter B Stage1Port Stage0Port
        budget  : Budget
        correct : ∀ p γ
          → BoundaryPort.SatF Stage1Port p γ
              ↔ BoundaryPort.SatF Stage0Port p (Interop.PortAdapter.map adapter γ)

    budgeted-from-trace : Trace → BudgetedBootstrap
    budgeted-from-trace t =
      record
        { adapter = bootstrap
        ; budget = budget-from-trace t
        ; correct = bootstrap-correct
        }

    -- Telemetry is observational only: traces do not alter the adapter semantics.
    adapter-irrelevant
      : ∀ t t'
      → BudgetedBootstrap.adapter (budgeted-from-trace t)
        ≡ BudgetedBootstrap.adapter (budgeted-from-trace t')
    adapter-irrelevant _ _ = refl

    telemetry-erasure
      : ∀ t p γ
      → BoundaryPort.SatF Stage1Port p γ
          ↔ BoundaryPort.SatF Stage0Port p
              (Interop.PortAdapter.map
                (BudgetedBootstrap.adapter (budgeted-from-trace t))
                γ)
    telemetry-erasure t = BudgetedBootstrap.correct (budgeted-from-trace t)

    bootstrap-with-trace
      : Trace
      → Interop.PortAdapter B Stage1Port Stage0Port × Budget
    bootstrap-with-trace t = bootstrap , budget-from-trace t

module FromGradedKernel
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GK.GradedKernel Sig Q)
  (stepSat : GradedToKernel.StepIsSat K)
  (bm : Core.BodyMonotoneShape (GK.GradedKernel.shape K))
  where

  K₀ : Kernel Sig Q
  K₀ = GradedToKernel.asKernel K stepSat bm

  module Base = For K₀
  open Base public
