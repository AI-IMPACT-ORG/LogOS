{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.APISurface where

-- Pin a small number of “headline” surface types so docs/public names cannot
-- silently drift to weaker/stronger statements.

open import LogOS.Prelude
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel)

import LogOS.Complexity.LCUToLandauer as LCU
import LogOS.Packs.Complexity.Experimental.PhysicsOfInformation as POI

import LogOS.Theorems.Meta.LandauerIO as LandauerIO
import LogOS.InfoTheory.Shannon.DPI as ShannonDPI
import LogOS.UniversalIR.Task as UTask
import LogOS.UniversalIR.Schemes as USchemes
import LogOS.Packs.UniversalIR.Agreement as UAgree

import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat

import LogOS.ZFC.SetU.WFGraphCore as WFCore
import LogOS.ZFC.SetU.GraphTreeBridge as GraphBridge
import LogOS.ZFC.WFGraph.Mostowski as Mostowski
import LogOS.Packs.Opacity.Experimental.Core as Opacity
import LogOS.Packs.Agents.Safety.NoTotalAuditor as NoTotalAuditor
open import LogOS.Domain.Opacity.NumberTheory.HP.Interface using (HPInterface)
import LogOS.Theorems.Meta.SpectralSeparationOutput as SSO

open import LogOS.Syntax.Prop using (¬_)
open import LogOS.Theorems.Meta.Assumptions.Diagonal using (TruthDiagonal; TruthDiagonalC)
open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Con using (BulkBoundary)
import LogOS.Minimal.Truth as Truth

-- --------------------------------------------------------------------------
-- Second law (merge ⇒ entropy increase)
-- --------------------------------------------------------------------------

merge-implies-entropy-increase-typed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (A : POI.SecondLawAssumptions Sig Q)
    (f : LogOSSignature.Cosp Sig)
  → LCU.Merges (POI.SecondLawAssumptions.LCUA A) f
  → Σ (LCU.LCUObsAssumptions.Obs (POI.SecondLawAssumptions.LCUA A))
      (λ x → QAdapter._≤s_ Q
               (QAdapter._·_ Q
                 (POI.SecondLawAssumptions.Entropy A x)
                 (LCU.LCUObsAssumptions.L (POI.SecondLawAssumptions.LCUA A)))
               (POI.SecondLawAssumptions.Entropy A
                 (LCU.LCUObsAssumptions.act (POI.SecondLawAssumptions.LCUA A) f x)))
merge-implies-entropy-increase-typed = POI.merge-implies-entropy-increase

-- --------------------------------------------------------------------------
-- LandauerIO (irreversible I/O cost lower bound)
-- --------------------------------------------------------------------------

irreversible-io-cost-lower-bound-typed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    (B : BoundaryIO Sig Q W BB H)
    (A : LandauerIO.LandauerIOAssumptions Sig Q W BB H B)
    (f : LogOSSignature.Cosp Sig)
  → LandauerIO.LandauerIOAssumptions.MergesIO A f
  → QAdapter._≤s_ Q (LandauerIO.LandauerIOAssumptions.L A) (LandauerIO.LandauerIOAssumptions.cost A f)
irreversible-io-cost-lower-bound-typed = POI.irreversible-io-cost-lower-bound

-- --------------------------------------------------------------------------
-- UniversalIR (five-paradigm agreement)
-- --------------------------------------------------------------------------

five-paradigm-minsky≈lambda-typed
  : (t : UTask.PATask)
  → Sch.run USchemes.minskyMachineScheme t ≡ Sch.run USchemes.lambdaMachineScheme t
five-paradigm-minsky≈lambda-typed =
  UAgree.ParadigmsRunEq.minsky≈lambda UAgree.five-paradigm-agreement

-- --------------------------------------------------------------------------
-- Shannon DPI (KL divergence)
-- --------------------------------------------------------------------------

KL-DPI-typed
  : ∀ (DF : ShannonDPI.DPIFacts) {m n : ℕ}
    (K : (let module D = ShannonDPI.For DF in D.C.KernelPos m n))
    (P Q : (let module D = ShannonDPI.For DF in D.C.DistPos m))
  → (let module D = ShannonDPI.For DF in
        (ShannonDPI.DPIFacts._≤_ DF)
          (D.KLfun
            (D.push (D.C.KernelPos.ker K) (D.C.DistPos.p P))
            (D.push (D.C.KernelPos.ker K) (D.C.DistPos.p Q)))
          (D.KLfun (D.C.DistPos.p P) (D.C.DistPos.p Q)))
KL-DPI-typed = ShannonDPI.For.KL-DPI

-- --------------------------------------------------------------------------
-- Agents (no total auditor)
-- --------------------------------------------------------------------------

no-total-auditor-typed
  : ∀ {ℓO ℓC ℓQ : Level} {Output : Set ℓO}
    (P : Cat.Process {ℓO = ℓO} {ℓC = ℓC} {ℓQ = ℓQ} Output)
  → (let module N = NoTotalAuditor.ForProcess P in
        (Aud : N.A.Auditor)
      → TruthDiagonalC (Cat.Process.Con P) (N.G.SpectralSeparationOutputC.HasSeparation (N.toSSO Aud))
      → ¬ (∀ s → N.G.SpectralSeparationOutputC.HasSeparation (N.toSSO Aud) s))
no-total-auditor-typed P =
  let module N = NoTotalAuditor.ForProcess P in
  N.no-total-auditor

-- --------------------------------------------------------------------------
-- Opacity (HP oracle not total)
-- --------------------------------------------------------------------------

hp-oracle-no-total-function-typed
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (HP : HPInterface K)
  → (let module HPO = Opacity.HPOpacity.For K HP in
        (O : HPO.OpFixedOracle)
      → TruthDiagonal K (SSO.SpectralSeparationOutput.HasSeparation (HPO.toSSO O))
      → ¬ (∀ γ → SSO.SpectralSeparationOutput.HasSeparation (HPO.toSSO O) γ))
hp-oracle-no-total-function-typed K HP =
  let module HPO = Opacity.HPOpacity.For K HP in
  HPO.hp-oracle-no-total-function

-- --------------------------------------------------------------------------
-- ZFC (Mostowski collapse: edge transport)
-- --------------------------------------------------------------------------

mostowski-collapse-edge→-typed
  : ∀ {ℓ}
    (G : WFCore.WFGraph ℓ)
    (S : GraphBridge.SupStructure G)
  → (let module M = Mostowski.For G S in
        ∀ {x y}
        → (e : WFCore.WFGraph.Edge G x y)
        → WFCore.WFGraph.Edge G (M.collapse x) (M.collapseChild e))
mostowski-collapse-edge→-typed G S =
  let module M = Mostowski.For G S in
  M.collapse-edge→
