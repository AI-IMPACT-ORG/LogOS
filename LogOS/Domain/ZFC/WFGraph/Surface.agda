{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.WFGraph.Surface where

open import LogOS.Prelude
open import LogOS.Kernel using (kernelLike-fromKernel)

open import LogOS.Domain.ZFC.SetTheory.ChoiceAxiom as AC using (AxiomOfChoice)
open import LogOS.Domain.ZFC.SetTheory.Dsl using (ZFDsl)
open import LogOS.Domain.ZFC.SetTheory.FormulaFromDefinable as FromDef using (toZFAxiomsᶠ)
open import LogOS.Domain.ZFC.SetTheory.FormulaPack using (ZFAxiomsᶠ; ZFCAxiomsᶠ)
open import LogOS.Domain.ZFC.SetTheory.FromZFAxioms using (toCumulativeHierarchy)
open import LogOS.Domain.ZFC.SetTheory.FullUpgradeFromDefinable as FullUpg
  using (PredicateRepresentable; FunctionGraphRepresentable)
open import LogOS.Domain.ZFC.SetTheory.LimitPack using (CumulativeHierarchy)
open import LogOS.Domain.ZFC.SetTheory.Pack using (ZFAxioms; ZFCAxioms)
open import LogOS.Domain.ZFC.SetTheory.StageToCHFromHierarchy using (StageToCH-fromCH)
open import LogOS.Domain.ZFC.SetTheory.CumulativeSurface using (stageToSurface)

open import LogOS.Domain.ZFC.WFGraph.Structure using (WFGraphStructure)
import LogOS.Domain.ZFC.WFGraph.ZFC as ZFC
import LogOS.Domain.ZFC.WFGraph.FormulaPack as Formula
import LogOS.Domain.ZFC.WFGraph.Textbook as Textbookₜ

-- Single entrypoint for “WF-graph sets inside LogOS”.
--
-- This module is intentionally a thin façade:
-- it reuses the existing WFGraph ZF development and exports a convenient bundle
-- of surfaces at two layers:
--
-- - `Definable`: a definable/coded ZF(+Infinity) pack (Metamath-style schemata),
-- - `Full`: upgrade to full textbook Separation/Replacement under explicit
--   representability assumptions, then expose `ZFAxioms` / `StageToCH` / `ZFDsl`.
-- - `Textbook`: full textbook ZF/ZFC directly from `sup` formation (no
--   representability-by-codes layer).

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

  zf : ZFAxioms (kernelLike-fromKernel K)
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
    zfc : ZFCAxioms (kernelLike-fromKernel K)
    zfc = record { zf = zf ; AC = choice }

    -- Formula-pack ZFC view (same Choice witness, but with coded schemata).
    zfcᶠ : ZFCAxiomsᶠ K
    zfcᶠ = record { zf = zfᶠ ; AC = choice }

-- Textbook ZF/ZFC: derive full Separation/Replacement directly from the WFGraph
-- `supN` operator (no representability assumptions). Choice remains explicit.

module Textbook
  {ℓ : Level}
  (W : WFGraphStructure ℓ)
  where
  module T = Textbookₜ.ForZFC W
  open T public

-- Formula-coded ZF(+Infinity) surface: schemata range over genuine first-order
-- formulas (with explicit parameters encoded in the code) and `decode` maps
-- those formulas to their extensions in the WFGraph universe.

module FormulaCoded
  {ℓ : Level}
  (W : WFGraphStructure ℓ)
  where

  open WFGraphStructure W
  module Base = Formula.ForZFC G S Ext P Fnd

  open Base public using (Sig; Q; K; zfᶠ)
