{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.WFGraph.Surface where

open import LogOS.Prelude

open import LogOS.Domain.SetTheory.ChoiceAxiom as AC using (AxiomOfChoice)
open import LogOS.Domain.SetTheory.Dsl using (ZFDsl)
open import LogOS.Domain.SetTheory.FormulaFromDefinable as FromDef using (toZFAxiomsᶠ)
open import LogOS.Domain.SetTheory.FormulaPack using (ZFAxiomsᶠ; ZFCAxiomsᶠ)
open import LogOS.Domain.SetTheory.FromZFAxioms using (toCumulativeHierarchy)
open import LogOS.Domain.SetTheory.FullUpgradeFromDefinable as FullUpg
  using (PredicateRepresentable; FunctionGraphRepresentable)
open import LogOS.Domain.SetTheory.LimitPack using (CumulativeHierarchy)
open import LogOS.Domain.SetTheory.Pack using (ZFAxioms; ZFCAxioms)
open import LogOS.Domain.SetTheory.StageToCHFromHierarchy using (StageToCH-fromCH)
open import LogOS.Domain.SetTheory.CumulativeSurface using (stageToSurface)

open import LogOS.Domain.ZFC.WFGraph.Structure using (WFGraphStructure)
import LogOS.Domain.ZFC.WFGraph.ZFC as ZFC

-- Single entrypoint for “WF-graph sets inside LogOS”.
--
-- This module is intentionally a thin façade:
-- it reuses the existing WFGraph ZF development and exports a convenient bundle
-- of surfaces at two layers:
--
-- - `Definable`: a definable/coded ZF(+Infinity) pack (Metamath-style schemata),
-- - `Full`: upgrade to full textbook Separation/Replacement under explicit
--   representability assumptions, then expose `ZFAxioms` / `StageToCH` / `ZFDsl`.

module Definable
  {ℓ : Level}
  (W : WFGraphStructure ℓ)
  where

  open WFGraphStructure W
  module Base = ZFC.ForZFC G S Ext P Fnd
  open Base using (K; zfᵈ; zfᵈNoInf)

  -- Definable-ZF(+Infinity) pack (core / Metamath-style route).
  -- Full Separation/Replacement can be upgraded explicitly via `FullZF` below.

  zfᵈ-Core = zfᵈ

  -- Metamath-style formula-pack view of the same definable ZF(+Infinity) pack:
  -- predicates are interpreted by membership in `⟦ φ ⟧`, and relations by `Graph`.
  zfᶠ : ZFAxiomsᶠ K
  zfᶠ = toZFAxiomsᶠ zfᵈ

module Full
  {ℓ : Level}
  (W : WFGraphStructure ℓ)
  (PR : PredicateRepresentable (ZFC.ForZFC.zfᵈ {ℓ = ℓ} (WFGraphStructure.G W)
                                         (WFGraphStructure.S W)
                                         (WFGraphStructure.Ext W)
                                         (WFGraphStructure.P W)
                                         (WFGraphStructure.Fnd W)))
  (FR : FunctionGraphRepresentable (ZFC.ForZFC.zfᵈ {ℓ = ℓ} (WFGraphStructure.G W)
                                         (WFGraphStructure.S W)
                                         (WFGraphStructure.Ext W)
                                         (WFGraphStructure.P W)
                                         (WFGraphStructure.Fnd W)))
  where

  open WFGraphStructure W
  module Base = ZFC.ForZFC G S Ext P Fnd
  open Base using (K; zfᵈ)

  zf : ZFAxioms K
  zf =
    let module U = Base.FullZF PR FR in
    U.zf

  CH : CumulativeHierarchy K
  CH = toCumulativeHierarchy K zf

  stageToCH = StageToCH-fromCH K CH

  surface : ZFDsl K
  surface = stageToSurface K stageToCH

  -- Formula-pack view (lives at the definable layer; independent of PR/FR).
  zfᶠ : ZFAxiomsᶠ K
  zfᶠ = toZFAxiomsᶠ zfᵈ

  -- ZFC (ZF + Choice) is available if you additionally supply a witness of AC.
  module WithChoice
    (choice : AxiomOfChoice (ZFAxioms.SetU zf) (ZFAxioms._∈_ zf) (ZFAxioms._≈_ zf) (ZFAxioms.pairing zf))
    where
    zfc : ZFCAxioms K
    zfc = record { zf = zf ; AC = choice }

    -- Formula-pack ZFC view (same Choice witness, but with coded schemata).
    zfcᶠ : ZFCAxiomsᶠ K
    zfcᶠ = record { zf = zfᶠ ; AC = choice }
