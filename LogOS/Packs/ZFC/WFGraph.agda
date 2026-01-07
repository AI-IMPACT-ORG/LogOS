{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.ZFC.WFGraph where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

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
import LogOS.Domain.ZFC.WFGraph.Surface as Surf
import LogOS.Domain.ZFC.WFGraph.ZFC as WFZFC
import LogOS.Theorems.Meta.QuartetCore as Quartet

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

  module Q {ℓ : Level} = Quartet.Make (Assumptions {ℓ}) (Claim {ℓ})
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Pack {ℓ}
  mkPack A =
    Q.mkPack
      (λ A →
        let
          open Assumptions A
          module D = Surf.Definable W
        in
        record
          { K   = D.Base.K
          ; zfᵈ = D.Base.zfᵈ
          ; zfᶠ = D.zfᶠ
          })
      A

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

  module Q {ℓ : Level} = Quartet.Make (Assumptions {ℓ}) (Claim {ℓ})
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Pack {ℓ}
  mkPack A =
    Q.mkPack
      (λ A →
        let
          open Assumptions A
          module F = Surf.FormulaCoded W
        in
        record
          { K   = F.K
          ; zfᶠ = F.zfᶠ
          })
      A

module Full where
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
      zf       : ZFAxioms K
      zfᶠ      : ZFAxiomsᶠ K
      CH       : CumulativeHierarchy K
      stageToCH : StageToCH K
      surface  : ZFDsl K

  module Q {ℓ : Level} = Quartet.Make (Assumptions {ℓ}) (Claim {ℓ})
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Pack {ℓ}
  mkPack A =
    let open Assumptions A
        module F = Surf.Full W PR FR
    in
    Q.mkPack
      (λ _ →
        record
          { K        = F.Base.K
          ; zf       = F.zf
          ; zfᶠ      = F.zfᶠ
          ; CH       = F.CH
          ; stageToCH = F.stageToCH
          ; surface  = F.surface
          })
      A

module WithChoice where
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
      zfc      : ZFCAxioms K
      zfcᶠ     : ZFCAxiomsᶠ K
      CH       : CumulativeHierarchy K
      stageToCH : StageToCH K
      surface  : ZFDsl K

  module Q {ℓ : Level} = Quartet.Make (Assumptions {ℓ}) (Claim {ℓ})
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : ∀ {ℓ : Level} (A : Assumptions {ℓ}) → Pack {ℓ}
  mkPack A =
    let open Assumptions A
        module F = Surf.Full W PR FR
        module C = F.WithChoice choice
    in
    Q.mkPack
      (λ _ →
        record
          { K        = F.Base.K
          ; zfc      = C.zfc
          ; zfcᶠ     = C.zfcᶠ
          ; CH       = F.CH
          ; stageToCH = F.stageToCH
          ; surface  = F.surface
          })
      A

-- Semantic aliases for the three WFGraph layers.
module ZFᶠ = Definable
module ZFᶠ-Formula = FormulaCoded
module ZF = Full
module ZFC = WithChoice
