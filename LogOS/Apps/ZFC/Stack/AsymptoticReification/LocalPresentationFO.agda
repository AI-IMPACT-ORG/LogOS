{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.LocalPresentationFO where

-- FO witnesses generated from a presentation's existing local generators.
--
-- This packages the repeated iterative-tree pattern one level up:
-- - Separation from a small classifier on existing generators,
-- - Replacement from a functional assignment on existing generators,
-- - staging supplied separately via a "this presented set is admissible at
--   some stage" witness constructor.
--
-- Refinement-first discipline:
-- - the generic Replacement story is phrased using image membership up to `_≈_`
--   and formula transport along `_≈_`,
-- - extensional collapse is only one *adapter* that can build those weaker
--   interfaces.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)

import LogOS.LT.Presentation.GeneratedImage as Img
import LogOS.LT.Presentation.GeneratedSubobject.Core as Gen

import LogOS.Apps.ZFC.Stack.AsymptoticReification.FOFromReification as AR
open import LogOS.Apps.ZFC.Stack.AsymptoticReification.StagedAdmissibility using
  ( StagedPredicateReification
  ; staged→restricted
  )
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Proof.Syntax as Syn

module ForPresentation
  {ℓ ℓIx ℓCls : Level}
  (B : Tower.ZFStackBase {ℓ})
  (S : StagedPredicateReification (Tower.ZFStackBase.ctx B))
  (G : Gen.LocalGenerators
         (Tower.ZFStackBase.SetU B)
         (Tower.ZFStackBase._∈_ B)
         (Tower.ZFStackBase._≈_ B)
         ℓIx)
  (Sub : Gen.GeneratedSubobjects G ℓCls)
  (Im : Img.GeneratedImages G)
  where

  open Tower.ZFStackBase B using (SetU; _∈_; _≈_; sym≈; ≡→≈)
  module FO = AR.FO B (staged→restricted S)
  module StageFO = AR.StagedFO B S
  open StagedPredicateReification S using (Stage; ReifiableAt)
  module LG = Gen.LocalGenerators G

  ExtensionalCollapse : Set ℓ
  ExtensionalCollapse = ∀ {x y : SetU} → x ≈ y → x ≡ y

  SourceMembership : Set _
  SourceMembership = Gen.LocalGenerators SetU _∈_ _≈_ ℓIx

  RefinedGeneratedSubobjects : Set _
  RefinedGeneratedSubobjects = Gen.GeneratedSubobjects G ℓCls

  RefinedGeneratedImages : Set _
  RefinedGeneratedImages = Img.GeneratedImages G

  record PredicateTransport : Set (lsuc ℓ) where
    field
      transportHead≈
        : ∀ (P : Syn.Formula) (ρ : FO.FB.Valuation)
        → (x z z′ : SetU)
        → z ≈ z′
        → FO.FB.evalFormula P (FO.FB.extend z (FO.FB.extend x ρ))
        → FO.FB.evalFormula P (FO.FB.extend z′ (FO.FB.extend x ρ))

  record RelationTransport : Set (lsuc ℓ) where
    field
      transportLeft≈
        : ∀ (R₀ : Syn.Formula) (ρ : FO.FB.Valuation)
        → (u u′ z : SetU)
        → u ≈ u′
        → FO.FB.evalFormula R₀ (FO.FB.extend u (FO.FB.extend z ρ))
        → FO.FB.evalFormula R₀ (FO.FB.extend u′ (FO.FB.extend z ρ))

      transportRight≈
        : ∀ (R₀ : Syn.Formula) (ρ : FO.FB.Valuation)
        → (u z z′ : SetU)
        → z ≈ z′
        → FO.FB.evalFormula R₀ (FO.FB.extend u (FO.FB.extend z ρ))
        → FO.FB.evalFormula R₀ (FO.FB.extend u (FO.FB.extend z′ ρ))

  strictPredicateTransport
    : ExtensionalCollapse
    → PredicateTransport
  strictPredicateTransport extensionality =
    record
      { transportHead≈ =
          λ P ρ x z z′ z≈z′ evalz →
            subst
              (λ w → FO.FB.evalFormula P (FO.FB.extend w (FO.FB.extend x ρ)))
              (extensionality z≈z′)
              evalz
      }

  strictRelationTransport
    : ExtensionalCollapse
    → RelationTransport
  strictRelationTransport extensionality =
    record
      { transportLeft≈ =
          λ R₀ ρ u u′ z u≈u′ rel →
            subst
              (λ w → FO.FB.evalFormula R₀ (FO.FB.extend w (FO.FB.extend z ρ)))
              (extensionality u≈u′)
              rel
      ; transportRight≈ =
          λ R₀ ρ u z z′ z≈z′ rel →
            subst
              (λ w → FO.FB.evalFormula R₀ (FO.FB.extend u (FO.FB.extend w ρ)))
              (extensionality z≈z′)
              rel
      }

  record StageClassifier : Set (lsuc (lsuc (ℓ ⊔ ℓIx ⊔ ℓCls))) where
    field
      stageOf
        : ∀ {P}
        → (x : SetU)
        → (∀ z → z ∈ x ↔ P z)
        → Σ Stage (λ i → ReifiableAt i P)

  open StageClassifier public using (stageOf)

  SepSpec
    : (P : Syn.Formula)
    → FO.FB.Valuation
    → (x : SetU)
    → LG.Ix x
    → Set ℓ
  SepSpec P ρ x i =
    FO.FB.evalFormula P (FO.FB.extend (LG.elemAt x i) (FO.FB.extend x ρ))

  record SepClassifier : Set (lsuc (lsuc (ℓ ⊔ ℓIx ⊔ ℓCls))) where
    field
      sepClassifier
        : (P : Syn.Formula)
        → (ρ : FO.FB.Valuation)
        → Gen.SmallClassifier G ℓCls ℓ (SepSpec P ρ)

  sepSet
    : RefinedGeneratedSubobjects
    → SepClassifier
    → (P : Syn.Formula)
    → FO.FB.Valuation
    → SetU
    → SetU
  sepSet S≈ C P ρ x =
    Gen.classifiedGenerate
      S≈
      (SepClassifier.sepClassifier C P ρ)
      x

  sepSet-spec
    : (transport : PredicateTransport)
    → (S≈ : RefinedGeneratedSubobjects)
    → ∀ (C : SepClassifier) (P : Syn.Formula) (ρ : FO.FB.Valuation) (x z : SetU)
    → (z ∈ sepSet S≈ C P ρ x) ↔ FO.SepPred P ρ x z
  sepSet-spec transport S≈ C P ρ x z =
    intro
      to
      from
    where
      module T = PredicateTransport transport
      module M = Gen.LocalGenerators G
      module SGen = Gen.GeneratedSubobjects S≈
      module Class = Gen.SmallClassifier (SepClassifier.sepClassifier C P ρ)

      EvalAt : SetU → Set ℓ
      EvalAt u = FO.FB.evalFormula P (FO.FB.extend u (FO.FB.extend x ρ))

      to : z ∈ sepSet S≈ C P ρ x → FO.SepPred P ρ x z
      to z∈ with SGen.outOfGenerated≈ (Class.code x) z∈
      ... | (i , (ci , z≈child)) =
        let
          z∈x : z ∈ x
          z∈x = M.memberIn≈ i z≈child

          child-eval : EvalAt (LG.elemAt x i)
          child-eval = _↔_.to (Class.code-spec x i) ci

          z-eval : EvalAt z
          z-eval = T.transportHead≈ P ρ x (LG.elemAt x i) z (sym≈ z≈child) child-eval
        in
        z∈x , z-eval

      from : FO.SepPred P ρ x z → z ∈ sepSet S≈ C P ρ x
      from (z∈x , z-eval) with M.memberOut≈ z∈x
      ... | (i , z≈child) =
        let
          child-eval : EvalAt (LG.elemAt x i)
          child-eval = T.transportHead≈ P ρ x z (LG.elemAt x i) z≈child z-eval

          ci : Class.code x i
          ci = _↔_.from (Class.code-spec x i) child-eval
        in
        SGen.intoGenerated≈ (Class.code x) i ci z≈child

  repAssign
    : (R₀ : Syn.Formula)
    → (ρ : FO.FB.Valuation)
    → (x : SetU)
    → FO.FB.FunctionalOnX R₀ ρ x
    → LG.Ix x
    → SetU
  repAssign R₀ ρ x fun i =
    proj₁ (fun (LG.elemAt x i) (LG.memberIn i refl))

  repAssign-rel
    : ∀ (R₀ : Syn.Formula) (ρ : FO.FB.Valuation) (x : SetU)
    → (fun : FO.FB.FunctionalOnX R₀ ρ x)
    → (i : LG.Ix x)
    → FO.FB.evalFormula R₀
        (FO.FB.extend (LG.elemAt x i) (FO.FB.extend (repAssign R₀ ρ x fun i) ρ))
  repAssign-rel R₀ ρ x fun i with fun (LG.elemAt x i) (LG.memberIn i refl)
  ... | _ , (rel , _) = rel

  repAssign-unique
    : ∀ (R₀ : Syn.Formula) (ρ : FO.FB.Valuation) (x : SetU)
    → (fun : FO.FB.FunctionalOnX R₀ ρ x)
    → (i : LG.Ix x)
    → ∀ z
    → FO.FB.evalFormula R₀ (FO.FB.extend (LG.elemAt x i) (FO.FB.extend z ρ))
    → z ≈ repAssign R₀ ρ x fun i
  repAssign-unique R₀ ρ x fun i with fun (LG.elemAt x i) (LG.memberIn i refl)
  ... | _ , (_ , uniq) = uniq

  repSet
    : RefinedGeneratedImages
    → (R₀ : Syn.Formula)
    → (ρ : FO.FB.Valuation)
    → (x : SetU)
    → FO.FB.FunctionalOnX R₀ ρ x
    → SetU
  repSet I≈ R₀ ρ x fun =
    Img.GeneratedImages.generateImage I≈ x (repAssign R₀ ρ x fun)

  repSet-spec
    : (transport : RelationTransport)
    → (I≈ : RefinedGeneratedImages)
    → ∀ (R₀ : Syn.Formula) (ρ : FO.FB.Valuation) (x z : SetU)
    → (fun : FO.FB.FunctionalOnX R₀ ρ x)
    → (z ∈ repSet I≈ R₀ ρ x fun) ↔ FO.RepPred R₀ ρ x z
  repSet-spec transport I≈ R₀ ρ x z fun =
    intro
      to
      from
    where
      module I = Img.GeneratedImages I≈
      module T = RelationTransport transport

      EvalAt : SetU → SetU → Set ℓ
      EvalAt u w = FO.FB.evalFormula R₀ (FO.FB.extend u (FO.FB.extend w ρ))

      to : z ∈ repSet I≈ R₀ ρ x fun → FO.RepPred R₀ ρ x z
      to z∈rep with I.outOfGeneratedImage≈ (repAssign R₀ ρ x fun) z∈rep
      ... | (i , z≈img) =
        let
          u : SetU
          u = LG.elemAt x i

          u∈x : u ∈ x
          u∈x = LG.memberIn i refl

          rel-u-img : EvalAt u (repAssign R₀ ρ x fun i)
          rel-u-img = repAssign-rel R₀ ρ x fun i

          rel-u-z : EvalAt u z
          rel-u-z =
            T.transportRight≈
              R₀ ρ u (repAssign R₀ ρ x fun i) z (sym≈ z≈img) rel-u-img
        in
        u , (u∈x , rel-u-z)

      from : FO.RepPred R₀ ρ x z → z ∈ repSet I≈ R₀ ρ x fun
      from (u , (u∈x , rel-u-z)) with LG.memberOut≈ u∈x
      ... | (i , u≈child) =
        let
          child-rel-z : EvalAt (LG.elemAt x i) z
          child-rel-z =
            T.transportLeft≈ R₀ ρ u (LG.elemAt x i) z u≈child rel-u-z

          z≈img : z ≈ repAssign R₀ ρ x fun i
          z≈img = repAssign-unique R₀ ρ x fun i z child-rel-z
        in
        I.intoGeneratedImage≈ (repAssign R₀ ρ x fun) i z≈img

  record FORepresentability : Set (lsuc (lsuc (ℓ ⊔ ℓIx ⊔ ℓCls))) where
    field
      sepClassifier : SepClassifier

  sepAt
    : StageClassifier
    → PredicateTransport
    → RefinedGeneratedSubobjects
    → FORepresentability
    → ∀ (P : Syn.Formula) (ρ : FO.FB.Valuation) (x : SetU)
    → Σ Stage (λ i → ReifiableAt i (FO.SepPred P ρ x))
  sepAt stages transport S≈ RF P ρ x =
    stageOf stages (sepSet S≈ (FORepresentability.sepClassifier RF) P ρ x)
      (sepSet-spec transport S≈ (FORepresentability.sepClassifier RF) P ρ x)

  repAt
    : RelationTransport
    → RefinedGeneratedImages
    → StageClassifier
    → ∀ (R₀ : Syn.Formula) (ρ : FO.FB.Valuation) (x : SetU)
    → FO.FB.FunctionalOnX R₀ ρ x
    → Σ Stage (λ i → ReifiableAt i (FO.RepPred R₀ ρ x))
  repAt transport I≈ stages R₀ ρ x fun =
    stageOf stages (repSet I≈ R₀ ρ x fun)
      (λ z → repSet-spec transport I≈ R₀ ρ x z fun)

  stagedFOWitnesses
    : PredicateTransport
    → RefinedGeneratedSubobjects
    → RelationTransport
    → RefinedGeneratedImages
    → StageClassifier
    → FORepresentability
    → StageFO.StagedFOWitnesses
  stagedFOWitnesses predTransport S≈ transport I≈ stages RF =
    record
      { sepAt = sepAt stages predTransport S≈ RF
      ; repAt = repAt transport I≈ stages
      }

  foWitnesses
    : PredicateTransport
    → RefinedGeneratedSubobjects
    → RelationTransport
    → RefinedGeneratedImages
    → StageClassifier
    → FORepresentability
    → FO.FOWitnesses
  foWitnesses predTransport S≈ transport I≈ stages RF =
    StageFO.foWitnesses (stagedFOWitnesses predTransport S≈ transport I≈ stages RF)
