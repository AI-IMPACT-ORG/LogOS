{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.WFGraph.ZFC where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; fst; snd)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Domain.ZFC.SetTheory.DefinablePack using (ZFAxiomsᵈ)
open import LogOS.Domain.ZFC.SetTheory.DefinablePackNoInfinity using (ZFAxiomsᵈ-NoInf)
open import LogOS.Domain.ZFC.SetTheory.Pack using (ZFAxioms)
open import LogOS.Domain.ZFC.SetTheory.FullUpgradeFromDefinable as Full
  using (PredicateRepresentable; FunctionGraphRepresentable)

open import LogOS.Domain.ZFC.SetU.IterativeSetTree using (Natℓ; zero; sucℓ)
open import LogOS.Domain.ZFC.SetU.WFGraphCore using (WFGraph)
open import LogOS.Domain.ZFC.SetU.GraphTreeBridge using (SupStructure)
open import LogOS.Domain.ZFC.WFGraph.Model
  using (PowersetStructure; ExtensionalityStructure; FoundationStructure)

-- End-to-end: build a definable-ZF(+Infinity) pack over the WF-graph kernel by providing
-- an explicit ω node (as a sup of iterated successors of ∅).

module ForZFC {ℓ : Level}
              (G   : WFGraph ℓ)
              (S   : SupStructure G)
              (Ext : ExtensionalityStructure G)
              (P   : PowersetStructure G S)
              (Fnd : FoundationStructure G)
              where

  open WFGraph G renaming (Node to N; Edge to E)
  open SupStructure S renaming (supN to supNₛ; mem-sup↔ to mem-sup↔ₛ)

  Sig : LogOSSignature ℓ
  Sig = LogOS.Domain.ZFC.WFGraph.Model.Sig G S Ext P Fnd

  Q : QAdapter ℓ
  Q = LogOS.Domain.ZFC.WFGraph.Model.Q G S Ext P Fnd

  K : Kernel Sig Q
  K = LogOS.Domain.ZFC.WFGraph.Model.K G S Ext P Fnd

  zfᵈNoInf : ZFAxiomsᵈ-NoInf K
  zfᵈNoInf = LogOS.Domain.ZFC.WFGraph.Model.zfᵈNoInf G S Ext P Fnd

  open ZFAxiomsᵈ-NoInf zfᵈNoInf

  emptyN : N
  emptyN = LogOS.Domain.ZFC.WFGraph.Model.emptyN G S Ext P Fnd

  succN : N → N
  succN = LogOS.Domain.ZFC.WFGraph.Model.succN G S Ext P Fnd

  vnN : Natℓ {ℓ} → N
  vnN zero = emptyN
  vnN (sucℓ n) = succN (vnN n)

  ωN : N
  ωN = supNₛ (Natℓ {ℓ}) vnN

  mem-ωN↔ : ∀ z → E ωN z ↔ Σ (Natℓ {ℓ}) (λ n → vnN n ≡ z)
  mem-ωN↔ z = mem-sup↔ₛ {I = Natℓ {ℓ}} {f = vnN} {y = z}

  infinity-ωN
    : ∀ z →
      (z ∈ ωN)
        ↔ ((z ≈ zeroS) ⊎ (Σ SetU (λ y → y ∈ ωN × (z ≈ succ y))))
  infinity-ωN z =
    intro (to z) (from z)
    where
      to : ∀ z → z ∈ ωN → (z ≈ zeroS) ⊎ (Σ SetU (λ y → y ∈ ωN × (z ≈ succ y)))
      to z ez with _↔_.to (mem-ωN↔ z) ez
      ... | (zero , pr) =
        inj₁ (sym pr)
      ... | (sucℓ n , pr) =
        inj₂
          ( vnN n
          , ( _↔_.from (mem-ωN↔ (vnN n)) (n , refl)
            , sym pr
            )
          )

      from
        : ∀ z →
          (z ≈ zeroS) ⊎ (Σ SetU (λ y → y ∈ ωN × (z ≈ succ y)))
          → z ∈ ωN
      from z (inj₁ z≡0) =
        subst (λ t → E ωN t) (sym z≡0)
          (_↔_.from (mem-ωN↔ emptyN) (zero , refl))
      from z (inj₂ (y , (y∈ω , z≡sy))) with _↔_.to (mem-ωN↔ y) y∈ω
      ... | (n , pr) =
        let
          sy≡z : succN y ≡ z
          sy≡z = sym z≡sy

          sn≡z : vnN (sucℓ n) ≡ z
          sn≡z = trans (cong succN pr) sy≡z
        in
        _↔_.from (mem-ωN↔ z) (sucℓ n , sn≡z)

  zfᵈ : ZFAxiomsᵈ K
  zfᵈ = record
    { SetU   = SetU
    ; _∈_    = _∈_
    ; _≈_    = _≈_
    ; refl≈  = refl≈
    ; sym≈   = sym≈
    ; trans≈ = trans≈
    ; ⟦_⟧     = ⟦_⟧
    ; by-decode≈ = by-decode≈
    ; extensionality = extensionality
    ; mem-ext = mem-ext
    ; mem-congL = mem-congL
    ; empty = empty
    ; pairing = pairing
    ; union = union
    ; powerset = powerset
    ; zeroS = zeroS
    ; zeroS-empty = zeroS-empty
    ; succ  = succ
    ; mem-succ↔ = mem-succ↔
    ; infinity = ωN , infinity-ωN
    ; separationᵈ = separationᵈ
    ; Graph = Graph
    ; replacementᵈ = replacementᵈ
    ; foundation = foundation
    }

  -- Optional “full ZF” upgrade: make representability of *all* predicates/functions
  -- explicit, then upgrade the definable schemata into the textbook ones.

  module FullZF
    (PR : PredicateRepresentable zfᵈ)
    (FR : FunctionGraphRepresentable zfᵈ)
    where

    zf : ZFAxioms K
    zf = Full.Upgrade.ZF zfᵈ PR FR
