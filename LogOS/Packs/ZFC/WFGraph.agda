{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.ZFC.WFGraph where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.API.Assumptions.Core using (LogicCore; coreFromKernel)
import LogOS.Packs.Assumptions.ZFC as AssumpZFC

open import LogOS.ZFC.SetTheory.ChoiceAxiom as AC using (AxiomOfChoice)
open import LogOS.ZFC.SetTheory.Cumulative using (StageToCH)
open import LogOS.ZFC.SetTheory.DefinablePack using (ZFAxiomsᵈ)
open import LogOS.ZFC.SetTheory.Dsl using (ZFDsl)
open import LogOS.ZFC.SetTheory.FormulaPack using (ZFAxiomsᶠ; ZFCAxiomsᶠ)
open import LogOS.ZFC.SetTheory.FullUpgradeFromDefinable as FullUpg
  using (PredicateRepresentable; FunctionGraphRepresentable)
open import LogOS.ZFC.SetTheory.LimitPack using (CumulativeHierarchy)
open import LogOS.ZFC.SetTheory.Pack using (ZFAxioms; ZFCAxioms)

open import LogOS.ZFC.WFGraph.Structure public using (WFGraphStructure)
import LogOS.ZFC.MembershipGraphSemantics as MGS
import LogOS.ZFC.WFGraph.Surface as Surf
import LogOS.ZFC.WFGraph.ZFC as WFZFC
import LogOS.ZFC.WFGraph.Mostowski as Mostowskiₜ
import LogOS.Theorems.Meta.ApplicationKit as AppKit

private
  zfᵈFromStructure
    : ∀ {ℓ : Level}
      (W : WFGraphStructure ℓ)
    → let
        open WFGraphStructure W
        module Z = WFZFC.ForZFC G S Ext P Fnd
      in ZFAxiomsᵈ Z.K
  zfᵈFromStructure W =
    let open WFGraphStructure W in
    WFZFC.ForZFC.zfᵈ G S Ext P Fnd

record KernelWithCore
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  : Set (lsuc (lsuc ℓ)) where
  field
    K : Kernel Sig Q
  core : LogicCore {ℓ}
  core = coreFromKernel K

record StructureAssumptions {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    W : WFGraphStructure ℓ

record FullRouteAssumptions {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    W  : WFGraphStructure ℓ
    PR : PredicateRepresentable (zfᵈFromStructure W)
    FR : FunctionGraphRepresentable (zfᵈFromStructure W)

-- Standard pack skeleton (uniform API) for the WFGraph ZF/ZFC route.
--
-- Each layer is presented as an Assumptions/Claim/Pack/mkPack quartet:
-- - Definable: coded schemata (ZFAxiomsᵈ / ZFAxiomsᶠ)
-- - Full: upgrade to full meta-level schemata (ZFAxioms) under explicit representability
-- - WithChoice: ZFC = ZF + explicit AC witness (ZFCAxioms and ZFCAxiomsᶠ)

module Definable where
  Assumptions = StructureAssumptions

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open StructureAssumptions A
    module D = Surf.Definable W
    field
      base : KernelWithCore {ℓ} {Sig = D.Base.Sig} {Q = D.Base.Q}
    open KernelWithCore base public using (K; core)
    field
      zfᵈ : ZFAxiomsᵈ K
      zfᶠ : ZFAxiomsᶠ K

  derive : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Claim {ℓ} A
  derive A =
    let
      open StructureAssumptions A
      module D = Surf.Definable W
    in
    record
      { base = record { K = D.Base.K }
      ; zfᵈ = D.Base.zfᵈ
      ; zfᶠ = D.zfᶠ
      }

  module Q {ℓ : Level} = AppKit.MakeDerived (Assumptions {ℓ}) (Claim {ℓ}) derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

module FormulaCoded where
  Assumptions = StructureAssumptions

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open StructureAssumptions A
    module F = Surf.FormulaCoded W
    field
      base : KernelWithCore {ℓ} {Sig = F.Sig} {Q = F.Q}
    open KernelWithCore base public using (K; core)
    field
      zfᶠ : ZFAxiomsᶠ K

  derive : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Claim {ℓ} A
  derive A =
    let
      open StructureAssumptions A
      module F = Surf.FormulaCoded W
    in
    record
      { base = record { K = F.K }
      ; zfᶠ = F.zfᶠ
      }

  module Q {ℓ : Level} = AppKit.MakeDerived (Assumptions {ℓ}) (Claim {ℓ}) derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

module Full where
  Assumptions = FullRouteAssumptions

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open FullRouteAssumptions A
    module F = Surf.Full W PR FR
    field
      base     : KernelWithCore {ℓ} {Sig = F.Base.Sig} {Q = F.Base.Q}
    open KernelWithCore base public using (K; core)
    field
      zf       : ZFAxioms (kernelLike-fromKernel K)
      zfᶠ      : ZFAxiomsᶠ K
      CH       : CumulativeHierarchy K
      stageToCH : StageToCH K
      surface  : ZFDsl K
    zfBundle : AssumpZFC.ZFBundle core
    zfBundle = record { zf = zf }

  derive : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Claim {ℓ} A
  derive A =
    let
      open FullRouteAssumptions A
      module F = Surf.Full W PR FR
    in
    record
      { base     = record { K = F.Base.K }
      ; zf       = F.zf
      ; zfᶠ      = F.zfᶠ
      ; CH       = F.CH
      ; stageToCH = F.stageToCH
      ; surface  = F.surface
      }

  module Q {ℓ : Level} = AppKit.MakeDerived (Assumptions {ℓ}) (Claim {ℓ}) derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

-- Textbook ZF from WFGraph `sup` formation (full schemata, no PR/FR layer).
module TextbookZF where
  Assumptions = StructureAssumptions

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open StructureAssumptions A
    module T = Surf.Textbook W
    field
      base     : KernelWithCore {ℓ} {Sig = T.Sig} {Q = T.Q}
    open KernelWithCore base public using (K; core)
    field
      zf       : ZFAxioms (kernelLike-fromKernel K)
      CH       : CumulativeHierarchy K
      stageToCH : StageToCH K
      surface  : ZFDsl K
    zfBundle : AssumpZFC.ZFBundle core
    zfBundle = record { zf = zf }

  derive : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Claim {ℓ} A
  derive A =
    let
      open StructureAssumptions A
      module T = Surf.Textbook W
    in
    record
      { base     = record { K = T.K }
      ; zf       = T.zf
      ; CH       = T.CH
      ; stageToCH = T.stageToCH
      ; surface  = T.surface
      }

  module Q {ℓ : Level} = AppKit.MakeDerived (Assumptions {ℓ}) (Claim {ℓ}) derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

-- Textbook ZFC = textbook ZF + explicit Choice witness.
module TextbookZFC where
  record Assumptions {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
    field
      structure : StructureAssumptions {ℓ}
      choice : let
                 open StructureAssumptions structure
                 module T = Surf.Textbook W
               in
               AxiomOfChoice (ZFAxioms.SetU T.zf) (ZFAxioms._∈_ T.zf) (ZFAxioms._≈_ T.zf) (ZFAxioms.pairing T.zf)

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open Assumptions A
    open StructureAssumptions structure renaming (W to W)
    module T = Surf.Textbook W
    module C = T.WithChoice choice
    field
      base     : KernelWithCore {ℓ} {Sig = T.Sig} {Q = T.Q}
    open KernelWithCore base public using (K; core)
    field
      zfc      : ZFCAxioms (kernelLike-fromKernel K)
      CH       : CumulativeHierarchy K
      stageToCH : StageToCH K
      surface  : ZFDsl K
    zfcBundle : AssumpZFC.ZFCBundle core
    zfcBundle = record { zfc = zfc }

  derive : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Claim {ℓ} A
  derive A =
    let
      open Assumptions A
      open StructureAssumptions structure renaming (W to W)
      module T = Surf.Textbook W
      module C = T.WithChoice choice
    in
    record
      { base     = record { K = T.K }
      ; zfc      = C.zfc
      ; CH       = T.CH
      ; stageToCH = T.stageToCH
      ; surface  = T.surface
      }

  module Q {ℓ : Level} = AppKit.MakeDerived (Assumptions {ℓ}) (Claim {ℓ}) derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

module WithChoice where
  record Assumptions {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
    field
      full : FullRouteAssumptions {ℓ}
      choice : let
                 open FullRouteAssumptions full
                 module F = Surf.Full W PR FR
               in
               AxiomOfChoice (ZFAxioms.SetU F.zf) (ZFAxioms._∈_ F.zf) (ZFAxioms._≈_ F.zf) (ZFAxioms.pairing F.zf)

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open Assumptions A
    open FullRouteAssumptions full renaming (W to W; PR to PR; FR to FR)
    module F = Surf.Full W PR FR
    module C = F.WithChoice choice
    field
      base     : KernelWithCore {ℓ} {Sig = F.Base.Sig} {Q = F.Base.Q}
    open KernelWithCore base public using (K; core)
    field
      zfc      : ZFCAxioms (kernelLike-fromKernel K)
      zfcᶠ     : ZFCAxiomsᶠ K
      CH       : CumulativeHierarchy K
      stageToCH : StageToCH K
      surface  : ZFDsl K
    zfcBundle : AssumpZFC.ZFCBundle core
    zfcBundle = record { zfc = zfc }

  derive : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Claim {ℓ} A
  derive A =
    let
      open Assumptions A
      open FullRouteAssumptions full renaming (W to W; PR to PR; FR to FR)
      module F = Surf.Full W PR FR
      module C = F.WithChoice choice
    in
    record
      { base     = record { K = F.Base.K }
      ; zfc      = C.zfc
      ; zfcᶠ     = C.zfcᶠ
      ; CH       = F.CH
      ; stageToCH = F.stageToCH
      ; surface  = F.surface
      }

  module Q {ℓ : Level} = AppKit.MakeDerived (Assumptions {ℓ}) (Claim {ℓ}) derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

-- Membership-is-edge packaging (lightweight, graph-first semantics).
module MembershipGraph where
  module For {ℓ : Level} (W : WFGraphStructure ℓ) where
    MG : MGS.MembershipGraph {ℓ}
    MG = MGS.fromStructure W

    open MGS.MembershipGraph MG public using (G; S; Ext; Pow; Fnd)

    module M = MGS.For MG
    module Mostowski = Mostowskiₜ.For G S
    open M public using (Sig; Q; K; zfᵈNoInf; zfᵈ; mem-graph; mem-graphᵈ)

-- Semantic aliases for the three WFGraph layers.
module ZFᶠ = Definable
module ZFᶠ-Formula = FormulaCoded
module ZF = Full
module ZFC = WithChoice
module ZF-Textbook = TextbookZF
module ZFC-Textbook = TextbookZFC

module Mostowski = Mostowskiₜ
