{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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

open import LogOS.Domain.ZFC.SetTheory.ChoiceAxiom as AC using (AxiomOfChoice)
open import LogOS.Domain.ZFC.SetTheory.Cumulative using (StageToCH)
open import LogOS.Domain.ZFC.SetTheory.DefinablePack using (ZFAxiomsᵈ)
open import LogOS.Domain.ZFC.SetTheory.Dsl using (ZFDsl)
open import LogOS.Domain.ZFC.SetTheory.FormulaPack using (ZFAxiomsᶠ; ZFCAxiomsᶠ)
open import LogOS.Domain.ZFC.SetTheory.FullUpgradeFromDefinable as FullUpg
  using (PredicateRepresentable; FunctionGraphRepresentable)
open import LogOS.Domain.ZFC.SetTheory.LimitPack using (CumulativeHierarchy)
open import LogOS.Domain.ZFC.SetTheory.Pack using (ZFAxioms; ZFCAxioms)

open import LogOS.Domain.ZFC.WFGraph.Structure public using (WFGraphStructure)
import LogOS.Domain.ZFC.MembershipGraphSemantics as MGS
import LogOS.Domain.ZFC.WFGraph.Surface as Surf
import LogOS.Domain.ZFC.WFGraph.ZFC as WFZFC
import LogOS.Domain.ZFC.WFGraph.Mostowski as Mostowskiₜ
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

-- Standard pack skeleton (uniform API) for the WFGraph ZF/ZFC route.
--
-- Each layer is presented as an Assumptions/Claim/Pack/mkPack quartet:
-- - Definable: coded schemata (ZFAxiomsᵈ / ZFAxiomsᶠ)
-- - Full: upgrade to full meta-level schemata (ZFAxioms) under explicit representability
-- - WithChoice: ZFC = ZF + explicit AC witness (ZFCAxioms and ZFCAxiomsᶠ)

module Definable where
  record Assumptions {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
    field
      W : WFGraphStructure ℓ

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open Assumptions A
    module D = Surf.Definable W
    field
      K   : Kernel (D.Base.Sig) (D.Base.Q)
      zfᵈ : ZFAxiomsᵈ K
      zfᶠ : ZFAxiomsᶠ K
    core : LogicCore {ℓ}
    core = coreFromKernel K

  derive : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Claim {ℓ} A
  derive A =
    let
      open Assumptions A
      module D = Surf.Definable W
    in
    record
      { K   = D.Base.K
      ; zfᵈ = D.Base.zfᵈ
      ; zfᶠ = D.zfᶠ
      }

  module Q {ℓ : Level} = AppKit.MakeDerived (Assumptions {ℓ}) (Claim {ℓ}) derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

module FormulaCoded where
  record Assumptions {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
    field
      W : WFGraphStructure ℓ

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open Assumptions A
    module F = Surf.FormulaCoded W
    field
      K   : Kernel F.Sig F.Q
      zfᶠ : ZFAxiomsᶠ K
    core : LogicCore {ℓ}
    core = coreFromKernel K

  derive : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Claim {ℓ} A
  derive A =
    let
      open Assumptions A
      module F = Surf.FormulaCoded W
    in
    record
      { K   = F.K
      ; zfᶠ = F.zfᶠ
      }

  module Q {ℓ : Level} = AppKit.MakeDerived (Assumptions {ℓ}) (Claim {ℓ}) derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

module Full where
  record Assumptions {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
    field
      W  : WFGraphStructure ℓ
      PR : PredicateRepresentable (zfᵈFromStructure W)
      FR : FunctionGraphRepresentable (zfᵈFromStructure W)

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open Assumptions A
    module F = Surf.Full W PR FR
    field
      K        : Kernel (F.Base.Sig) (F.Base.Q)
      zf       : ZFAxioms (kernelLike-fromKernel K)
      zfᶠ      : ZFAxiomsᶠ K
      CH       : CumulativeHierarchy K
      stageToCH : StageToCH K
      surface  : ZFDsl K
    core : LogicCore {ℓ}
    core = coreFromKernel K
    zfBundle : AssumpZFC.ZFBundle core
    zfBundle = record { zf = zf }

  derive : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Claim {ℓ} A
  derive A =
    let
      open Assumptions A
      module F = Surf.Full W PR FR
    in
    record
      { K        = F.Base.K
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
  record Assumptions {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
    field
      W : WFGraphStructure ℓ

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open Assumptions A
    module T = Surf.Textbook W
    field
      K        : Kernel T.Sig T.Q
      zf       : ZFAxioms (kernelLike-fromKernel K)
      CH       : CumulativeHierarchy K
      stageToCH : StageToCH K
      surface  : ZFDsl K
    core : LogicCore {ℓ}
    core = coreFromKernel K
    zfBundle : AssumpZFC.ZFBundle core
    zfBundle = record { zf = zf }

  derive : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Claim {ℓ} A
  derive A =
    let
      open Assumptions A
      module T = Surf.Textbook W
    in
    record
      { K        = T.K
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
      W : WFGraphStructure ℓ
      choice : let module T = Surf.Textbook W in
               AxiomOfChoice (ZFAxioms.SetU T.zf) (ZFAxioms._∈_ T.zf) (ZFAxioms._≈_ T.zf) (ZFAxioms.pairing T.zf)

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open Assumptions A
    module T = Surf.Textbook W
    module C = T.WithChoice choice
    field
      K        : Kernel T.Sig T.Q
      zfc      : ZFCAxioms (kernelLike-fromKernel K)
      CH       : CumulativeHierarchy K
      stageToCH : StageToCH K
      surface  : ZFDsl K
    core : LogicCore {ℓ}
    core = coreFromKernel K
    zfcBundle : AssumpZFC.ZFCBundle core
    zfcBundle = record { zfc = zfc }

  derive : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Claim {ℓ} A
  derive A =
    let
      open Assumptions A
      module T = Surf.Textbook W
      module C = T.WithChoice choice
    in
    record
      { K        = T.K
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
      W  : WFGraphStructure ℓ
      PR : PredicateRepresentable (zfᵈFromStructure W)
      FR : FunctionGraphRepresentable (zfᵈFromStructure W)
      choice : let module F = Surf.Full W PR FR in
               AxiomOfChoice (ZFAxioms.SetU F.zf) (ZFAxioms._∈_ F.zf) (ZFAxioms._≈_ F.zf) (ZFAxioms.pairing F.zf)

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open Assumptions A
    module F = Surf.Full W PR FR
    module C = F.WithChoice choice
    field
      K        : Kernel (F.Base.Sig) (F.Base.Q)
      zfc      : ZFCAxioms (kernelLike-fromKernel K)
      zfcᶠ     : ZFCAxiomsᶠ K
      CH       : CumulativeHierarchy K
      stageToCH : StageToCH K
      surface  : ZFDsl K
    core : LogicCore {ℓ}
    core = coreFromKernel K
    zfcBundle : AssumpZFC.ZFCBundle core
    zfcBundle = record { zfc = zfc }

  derive : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Claim {ℓ} A
  derive A =
    let
      open Assumptions A
      module F = Surf.Full W PR FR
      module C = F.WithChoice choice
    in
    record
      { K        = F.Base.K
      ; zfc      = C.zfc
      ; zfcᶠ     = C.zfcᶠ
      ; CH       = F.CH
      ; stageToCH = F.stageToCH
      ; surface  = F.surface
      }

  module Q {ℓ : Level} = AppKit.MakeDerived (Assumptions {ℓ}) (Claim {ℓ}) derive
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

-- Membership-is-edge packaging (thin, graph-first semantics).
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
