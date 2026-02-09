{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.NontrivialPortsSpine where

-- Single witness module used by multiple surface tests:
-- proves the “meaningful boundary” records are inhabited and interact well with
-- the stable ports/adapters spine (no accidental vacuity collapse).

open import LogOS.Prelude

open import LogOS.Ports.Semantic.Meaningful as Meaningful
open import LogOS.Ports.Semantic.Interoperability using (idAdapter)
open import LogOS.Boundary.Port using (canonicalPort)
import LogOS.Ports.Semantic.VacuityGuards as Vac

open import Tests.MeaningfulModels as MM

meaningfulB₀ : MeaningfulBoundaryIO MM.B₀
meaningfulB₀ = portGuards→meaningfulBoundaryIO MM.Port₀ MM.portGuards₀

canonicalPortGuards₀ : Vac.PortVacuityGuards MM.B₀ (canonicalPort MM.B₀)
canonicalPortGuards₀ = meaningfulBoundaryIO→canonicalPortGuards MM.B₀ meaningfulB₀

canonicalIdAdapterGuards₀
  : Vac.AdapterVacuityGuards
      MM.B₀
      (canonicalPort MM.B₀)
      (canonicalPort MM.B₀)
      (idAdapter MM.B₀ (canonicalPort MM.B₀))
canonicalIdAdapterGuards₀ =
  record
    { p = MeaningfulBoundaryIO.p meaningfulB₀
    ; φ₀ = MeaningfulBoundaryIO.c₀ meaningfulB₀
    ; φ₁ = MeaningfulBoundaryIO.c₁ meaningfulB₀
    ; sat₀ = MeaningfulBoundaryIO.sat₀ meaningfulB₀
    ; unsat₁ = MeaningfulBoundaryIO.unsat₁ meaningfulB₀
    ; map-distinct = MeaningfulBoundaryIO.c₀≢c₁ meaningfulB₀
    }

