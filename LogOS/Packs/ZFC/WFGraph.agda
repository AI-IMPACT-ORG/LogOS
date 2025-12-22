{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.ZFC.WFGraph where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Domain.SetTheory.ChoiceAxiom as AC using (AxiomOfChoice)
open import LogOS.Domain.SetTheory.Cumulative using (StageToCH)
open import LogOS.Domain.SetTheory.DefinablePack using (ZFAxiomsᵈ)
open import LogOS.Domain.SetTheory.Dsl using (ZFDsl)
open import LogOS.Domain.SetTheory.FormulaPack using (ZFAxiomsᶠ; ZFCAxiomsᶠ)
open import LogOS.Domain.SetTheory.FullUpgradeFromDefinable as FullUpg
  using (PredicateRepresentable; FunctionGraphRepresentable)
open import LogOS.Domain.SetTheory.LimitPack using (CumulativeHierarchy)
open import LogOS.Domain.SetTheory.Pack using (ZFAxioms; ZFCAxioms)

open import LogOS.Domain.ZFC.WFGraph.Structure public using (WFGraphStructure)
import LogOS.Domain.ZFC.WFGraph.Surface as Surf
import LogOS.Domain.ZFC.WFGraph.ZFC as WFZFC

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

  record Pack {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    field
      claim : Claim A
    open Claim claim public

  mkPack : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Pack A
  mkPack A =
    let open Assumptions A
        module D = Surf.Definable W
    in
    record
      { claim = record
          { K   = D.Base.K
          ; zfᵈ = D.Base.zfᵈ
          ; zfᶠ = D.zfᶠ
          }
      }

module Full where
  record Assumptions {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
    field
      W  : WFGraphStructure ℓ
      PR : PredicateRepresentable (WFZFC.ForZFC.zfᵈ (WFGraphStructure.G W)
                                             (WFGraphStructure.S W)
                                             (WFGraphStructure.Ext W)
                                             (WFGraphStructure.P W)
                                             (WFGraphStructure.Fnd W))
      FR : FunctionGraphRepresentable (WFZFC.ForZFC.zfᵈ (WFGraphStructure.G W)
                                             (WFGraphStructure.S W)
                                             (WFGraphStructure.Ext W)
                                             (WFGraphStructure.P W)
                                             (WFGraphStructure.Fnd W))

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open Assumptions A
    module F = Surf.Full W PR FR
    field
      K        : Kernel (F.Base.Sig) (F.Base.Q)
      zf       : ZFAxioms K
      zfᶠ      : ZFAxiomsᶠ K
      CH       : CumulativeHierarchy K
      stageToCH : StageToCH K
      surface  : ZFDsl K

  record Pack {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    field
      claim : Claim A
    open Claim claim public

  mkPack : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Pack A
  mkPack A =
    let open Assumptions A
        module F = Surf.Full W PR FR
    in
    record
      { claim = record
          { K        = F.Base.K
          ; zf       = F.zf
          ; zfᶠ      = F.zfᶠ
          ; CH       = F.CH
          ; stageToCH = F.stageToCH
          ; surface  = F.surface
          }
      }

module WithChoice where
  record Assumptions {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
    field
      W  : WFGraphStructure ℓ
      PR : PredicateRepresentable (WFZFC.ForZFC.zfᵈ (WFGraphStructure.G W)
                                             (WFGraphStructure.S W)
                                             (WFGraphStructure.Ext W)
                                             (WFGraphStructure.P W)
                                             (WFGraphStructure.Fnd W))
      FR : FunctionGraphRepresentable (WFZFC.ForZFC.zfᵈ (WFGraphStructure.G W)
                                             (WFGraphStructure.S W)
                                             (WFGraphStructure.Ext W)
                                             (WFGraphStructure.P W)
                                             (WFGraphStructure.Fnd W))
      choice : let module F = Surf.Full W PR FR in
               AxiomOfChoice (ZFAxioms.SetU F.zf) (ZFAxioms._∈_ F.zf) (ZFAxioms._≈_ F.zf) (ZFAxioms.pairing F.zf)

  record Claim {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    open Assumptions A
    module F = Surf.Full W PR FR
    module C = F.WithChoice choice
    field
      K        : Kernel (F.Base.Sig) (F.Base.Q)
      zfc      : ZFCAxioms K
      zfcᶠ     : ZFCAxiomsᶠ K
      CH       : CumulativeHierarchy K
      stageToCH : StageToCH K
      surface  : ZFDsl K

  record Pack {ℓ : Level} (A : Assumptions {ℓ}) : Set (lsuc (lsuc ℓ)) where
    field
      claim : Claim A
    open Claim claim public

  mkPack : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Pack A
  mkPack A =
    let open Assumptions A
        module F = Surf.Full W PR FR
        module C = F.WithChoice choice
    in
    record
      { claim = record
          { K        = F.Base.K
          ; zfc      = C.zfc
          ; zfcᶠ     = C.zfcᶠ
          ; CH       = F.CH
          ; stageToCH = F.stageToCH
          ; surface  = F.surface
          }
      }

-- Semantic aliases for the three WFGraph layers.
module ZFᶠ = Definable
module ZF = Full
module ZFC = WithChoice
