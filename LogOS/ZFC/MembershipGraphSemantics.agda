{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.MembershipGraphSemantics where

-- A compact, graph-first ZF(ZFC) packaging: membership is exactly the edge
-- relation of a well-founded graph, with ZF axioms built from Sup/Power/Ext.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.API.Kernel

open import LogOS.ZFC.SetU.WFGraphCore using (WFGraph)
open import LogOS.ZFC.SetU.GraphTreeBridge using (SupStructure)
open import LogOS.ZFC.WFGraph.Structure using (WFGraphStructure)
open import LogOS.ZFC.WFGraph.Model
  using (PowersetStructure; ExtensionalityStructure; FoundationStructure)
import LogOS.ZFC.WFGraph.Model as Model
import LogOS.ZFC.WFGraph.ZFC as ZFC
open import LogOS.ZFC.SetTheory.DefinablePackNoInfinity using (ZFAxiomsᵈ-NoInf)
open import LogOS.ZFC.SetTheory.DefinablePack using (ZFAxiomsᵈ)

record MembershipGraph {ℓ : Level} : Set (lsuc ℓ) where
  field
    G   : WFGraph ℓ
    S   : SupStructure G
    Ext : ExtensionalityStructure G
    Pow : PowersetStructure G S
    Fnd : FoundationStructure G

open MembershipGraph public

fromStructure : ∀ {ℓ : Level} → WFGraphStructure ℓ → MembershipGraph {ℓ}
fromStructure W =
  let open WFGraphStructure W renaming
        ( G   to Gw
        ; S   to Sw
        ; Ext to Extw
        ; P   to Pw
        ; Fnd to Fndw
        )
  in
  record
    { G   = Gw
    ; S   = Sw
    ; Ext = Extw
    ; Pow = Pw
    ; Fnd = Fndw
    }

module For {ℓ : Level} (M : MembershipGraph {ℓ}) where
  open MembershipGraph M renaming
    ( G   to Gm
    ; S   to Sm
    ; Ext to Extm
    ; Pow to Powm
    ; Fnd to Fndm
    )
  open WFGraph Gm renaming (Edge to E)

  Sig : LogOSSignature ℓ
  Sig = Model.Sig Gm Sm Extm Powm Fndm

  Q : QAdapter ℓ
  Q = Model.Q Gm Sm Extm Powm Fndm

  K : Kernel Sig Q
  K = Model.K Gm Sm Extm Powm Fndm

  zfᵈNoInf : ZFAxiomsᵈ-NoInf K
  zfᵈNoInf = Model.zfᵈNoInf Gm Sm Extm Powm Fndm

  module Z = ZFC.ForZFC Gm Sm Extm Powm Fndm

  zfᵈ : ZFAxiomsᵈ K
  zfᵈ = Z.zfᵈ

  -- Membership is literally edge adjacency in the graph semantics.
  mem-graph
    : ∀ z x → ZFAxiomsᵈ-NoInf._∈_ zfᵈNoInf z x ↔ E x z
  mem-graph _ _ = Prop.↔-refl

  mem-graphᵈ
    : ∀ z x → ZFAxiomsᵈ._∈_ zfᵈ z x ↔ E x z
  mem-graphᵈ _ _ = Prop.↔-refl
