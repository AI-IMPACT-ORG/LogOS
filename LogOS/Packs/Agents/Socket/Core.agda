{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.Core where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.ConAlg using (ConAlg)
open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.MultiIO using (MultiBoundaryIO; defaultMultiBoundaryIOFromBoundaryIO)
open import LogOS.Boundary.Port using (BoundaryPort; canonicalPort)
open import LogOS.Syntax.Prop as Prop

open import LogOS.API.Assumptions.Core using (LogicCore; coreFromKernel)
open import LogOS.Kernel using (Kernel)
open import LogOS.Kernel.ConAlgOf using (conAlgOf)
import LogOS.Boundary.FromKernel as LKBoundary

import LogOS.Minimal.ConstraintsOverSig as ConOverSig
import LogOS.Computation.SchemeCategory as Cat
import LogOS.Computation.Scheme as Sch

open import LogOS.Packs.Agents.Socket.Ports using (AgentPorts)
open import LogOS.Packs.Agents.Socket.Contracts using (AgentContracts)

-- The AgentSocket ties together:
-- - one logic kernel (the semantic “object”),
-- - designated interface ports,
-- - a functorial contract language + a valuation of its atoms into boundary constraints,
-- - and a chosen computational scheme interface (compiler + fuel) into a common process.
--
-- The output surface is boundary constraints: this makes monitoring/auditing
-- compositional and keeps the pack “opacity-native” (everything is observable
-- only up to boundary satisfaction).

record AgentSocket
  {ℓ ℓTask : Level}
  (Sig  : LogOSSignature ℓ)
  (Q    : QAdapter ℓ)
  (Task : Set ℓTask)
  : Set (lsuc (lsuc (ℓ ⊔ ℓTask))) where

  open LogOSSignature Sig

  field
    LK    : Kernel Sig Q
    ports : AgentPorts Sig

  core : LogicCore {ℓ}
  core = coreFromKernel LK

  open BulkBoundary (Kernel.BB LK) public using (Con_bnd; _⊑bnd_)

  field
    -- Atom valuation: what does an interface-atom *mean* as a boundary constraint?
    val∂ : Iface → Con_bnd

    -- Contracts in the functorial free syntax.
    C    : AgentContracts Sig

    -- Shared process surface and the selected “framework interface”.
    P      : Cat.Process {ℓO = ℓ} {ℓC = ℓ} {ℓQ = ℓ} Con_bnd
    interface : Cat.Interface Task P

  -- -----------------------------------------------------------------------
  -- Derived: contract interpretation into boundary constraints.
  -- -----------------------------------------------------------------------

  conAlg : ConAlg {ℓ}
  conAlg = conAlgOf LK

  ⟦_⟧ : ConOverSig.Con∂ Sig → Con_bnd
  ⟦ c ⟧ = ConOverSig.interp∂ conAlg val∂ c

  SafetySem : Con_bnd
  SafetySem = ⟦ AgentContracts.Safety C ⟧

  ObjectiveSem : Con_bnd
  ObjectiveSem = ⟦ AgentContracts.Objective C ⟧

  AssumesSem : Con_bnd
  AssumesSem = ⟦ AgentContracts.Assumes C ⟧

  -- -----------------------------------------------------------------------
  -- Derived: the chosen scheme (for interoperability via SchemeCategory).
  -- -----------------------------------------------------------------------

  S : Sch.Scheme Task Con_bnd
  S = Cat.schemeFromInterface P interface

  -- -----------------------------------------------------------------------
  -- Derived: a BoundaryIO view of the socket (for observational equality `Obs≈`
  -- and ports/adapters tooling).
  -- -----------------------------------------------------------------------

  boundaryIO : BoundaryIO Sig Q (Kernel.HWorld LK) (Kernel.BB LK) (Kernel.HTruth LK)
  boundaryIO = LKBoundary.boundaryIO LK

  -- Role-indexed boundary view (all roles share the same `BoundaryIO` by default).
  multiBoundaryIO
    : (Role : Set ℓ)
    → MultiBoundaryIO Role Sig Q (Kernel.HWorld LK) (Kernel.BB LK) (Kernel.HTruth LK)
  multiBoundaryIO Role = defaultMultiBoundaryIOFromBoundaryIO {Role = Role} boundaryIO

  -- Canonical boundary presentation: formulas are just boundary constraints.
  --
  -- This lets you apply the ports/adapters tooling (interlingua, `Obs≈`) directly
  -- to the socket without additional scaffolding.
  canonicalBoundaryPort
    : BoundaryPort {ℓForm = ℓ} Sig Q (Kernel.HWorld LK) (Kernel.BB LK) (Kernel.HTruth LK) boundaryIO
  canonicalBoundaryPort = canonicalPort boundaryIO

  -- Contract language as a boundary port, parameterized by an explicit
  -- reflection of constraints back into the free contract syntax.
  --
  -- This keeps the directionality honest: contracts interpret into constraints,
  -- and any embedding of constraints into syntax is an explicit assumption.

  contractBoundaryPort
    : (reflect : Con_bnd → ConOverSig.Con∂ Sig)
    → (reflect-sound
        : ∀ p c
        → BoundaryIO.Sat∂ boundaryIO p c
            ↔ BoundaryIO.Sat∂ boundaryIO p (⟦ reflect c ⟧))
    → BoundaryPort {ℓForm = ℓ} Sig Q (Kernel.HWorld LK) (Kernel.BB LK) (Kernel.HTruth LK) boundaryIO
  contractBoundaryPort reflect reflect-sound =
    record
      { Sem =
          record
            { Form = ConOverSig.Con∂ Sig
            ; SatF = λ p φ → BoundaryIO.Sat∂ boundaryIO p (⟦ φ ⟧)
            ; Interp = reflect
            ; Sat∂≈F = reflect-sound
            }
      ; Import = ⟦_⟧
      ; SatF≈∂ = λ _ _ → Prop.↔-refl
      }

open AgentSocket public
