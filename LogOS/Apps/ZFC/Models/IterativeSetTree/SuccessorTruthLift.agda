{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.SuccessorTruthLift where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.ConPreorder using (refl⊑)
open import LogOS.Host.Level using (Lift; lift; lower)
import LogOS.LT.Presentation.GeneratedImage as GenImage
import LogOS.LT.Presentation.GeneratedSubobject.Core as GenSub

import LogOS.Apps.ZFC.Stack.AsymptoticReification as AR
import LogOS.Apps.ZFC.Stack.AsymptoticReification.CrossStageFOFromReification as CSFO
import LogOS.Apps.ZFC.Stack.AsymptoticReification.CrossStageReificationPort as CSR
import LogOS.Apps.ZFC.Stack.AsymptoticReification.LateCollapseTower as LCT
import LogOS.Apps.ZFC.Proof.Syntax as Syn
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

import LogOS.Apps.ZFC.Models.IterativeSetTree as IST
import LogOS.Apps.ZFC.Models.IterativeSetTree.Context as Ctx
import LogOS.Apps.ZFC.Models.IterativeSetTree.GeneratedSubtree as Subtree
import LogOS.Apps.ZFC.Models.IterativeSetTree.HierarchyInfinity as Inf
import LogOS.Apps.ZFC.Models.IterativeSetTree.PresentationAdapters as Adapt
import LogOS.Apps.ZFC.Models.IterativeSetTree.StagedReification as Stage
import LogOS.Apps.ZFC.Models.IterativeSetTree.WellFounded as Wf
import LogOS.Apps.ZFC.Stack.WellFounded as WF

module For
  {ℓ : Level}
  (H₀ : Stage.StageAssumptionsᵛ {ℓ})
  where

  open Stage.StageAssumptionsᵛ H₀ renaming (collapse to collapse₀)
  open Stage.ExtensionalCollapseᵛ collapse₀ renaming (extensionalityᵛ to extensionalityᵛ₀)

  private
    C₀ : ZF.SetContext {lsuc ℓ}
    C₀ = Ctx.ctxᵛ {ℓ}

    C₁ : ZF.SetContext {lsuc (lsuc ℓ)}
    C₁ = Ctx.ctxᵛ {lsuc ℓ}

  module LowStage = Stage.For H₀
  module LowInfinity = Inf.For H₀

  stagedPredicateReification₀ : AR.StagedPredicateReification C₀
  stagedPredicateReification₀ = LowStage.stagedPredicateReificationᵛ

  restrictedPredicateReification₀ : AR.PredicateReification C₀
  restrictedPredicateReification₀ = AR.staged→restricted stagedPredicateReification₀

  module R₀ = AR.PredicateReification restrictedPredicateReification₀
  module LowTower = LCT.For C₀ restrictedPredicateReification₀

  private
    module Mem₀ = ZF.SetContext C₀
    module Mem₁ = ZF.SetContext C₁

  module LowerAdapt = Adapt.For collapse₀
  module LowGen = GenSub.LocalGenerators LowerAdapt.localGeneratorsᵛ

  collapseFlow₀ : LowTower.FlowCollapse
  collapseFlow₀ _ = refl⊑ R₀.PredBnd

  module Collapse₀ = LowTower.WithFlowCollapse collapseFlow₀

  liftᵛ : IST.V {ℓ} → IST.V {lsuc ℓ}
  liftᵛ (IST.sup I f) = IST.sup (Lift (lsuc ℓ) I) (λ i → liftᵛ (f (lower i)))

  lowerIdxᵛ
    : ∀ {x : IST.V {ℓ}}
    → IST.Idx (liftᵛ x)
    → IST.Idx x
  lowerIdxᵛ {x = IST.sup I f} = lower

  elemAt↓
    : (x : IST.V {ℓ})
    → IST.Idx (liftᵛ x)
    → IST.V {ℓ}
  elemAt↓ x i↑ = IST.elemAt x (lowerIdxᵛ {x = x} i↑)

  liftIdx
    : ∀ (x : IST.V {ℓ})
    → IST.Idx x
    → IST.Idx (liftᵛ x)
  liftIdx (IST.sup _ _) = lift

  lowerIdxᵛ-liftIdx
    : ∀ (x : IST.V {ℓ})
    → (i : IST.Idx x)
    → lowerIdxᵛ {x = x} (liftIdx x i) ≡ i
  lowerIdxᵛ-liftIdx (IST.sup _ _) _ = refl

  elemAt↓-liftIdx
    : ∀ (x : IST.V {ℓ})
    → (i : IST.Idx x)
    → elemAt↓ x (liftIdx x i) ≡ IST.elemAt x i
  elemAt↓-liftIdx x i = cong (IST.elemAt x) (lowerIdxᵛ-liftIdx x i)

  member↓
    : (x : IST.V {ℓ})
    → (i↑ : IST.Idx (liftᵛ x))
    → elemAt↓ x i↑ IST.∈ᵛ x
  member↓ x i↑ = IST.memberIn (lowerIdxᵛ {x = x} i↑) refl

  lowerIdx
    : ∀ (x : IST.V {ℓ})
    → IST.Idx (liftᵛ x)
    → IST.Idx x
  lowerIdx x = lowerIdxᵛ {x = x}

  elemAt-lift
    : ∀ (x : IST.V {ℓ})
    → (i : IST.Idx x)
    → IST.elemAt (liftᵛ x) (liftIdx x i) ≡ liftᵛ (IST.elemAt x i)
  elemAt-lift (IST.sup _ _) _ = refl

  elemAt↓-lift
    : ∀ (x : IST.V {ℓ})
    → (i↑ : IST.Idx (liftᵛ x))
    → IST.elemAt (liftᵛ x) i↑ ≡ liftᵛ (elemAt↓ x i↑)
  elemAt↓-lift (IST.sup _ _) _ = refl

  lift-memberIn
    : ∀ {x z : IST.V {ℓ}}
    → z IST.∈ᵛ x
    → liftᵛ z IST.∈ᵛ liftᵛ x
  lift-memberIn {x = x} z∈ with IST.memberOut z∈
  ... | (i , eq) =
    IST.memberIn
      (liftIdx x i)
      (trans (cong liftᵛ eq) (sym (elemAt-lift x i)))

  lift≈
    : ∀ {x y : IST.V {ℓ}}
    → WF.Acc IST._∈ᵛ_ x
    → WF.Acc IST._∈ᵛ_ y
    → liftᵛ x ≡ liftᵛ y
    → Mem₀._≈_ x y
  lift≈ {x = IST.sup I f} {y = IST.sup J g} (WF.acc stepx) (WF.acc stepy) eq = to , from
    where
      to : ∀ z → z IST.∈ᵛ IST.sup I f → z IST.∈ᵛ IST.sup J g
      to z z∈x with subst (λ t → liftᵛ z IST.∈ᵛ t) eq (lift-memberIn z∈x)
      ... | (j↑ , eqz) =
        let
          z≈gj : Mem₀._≈_ z (g (lowerIdx (IST.sup J g) j↑))
          z≈gj =
            lift≈
              (stepx z z∈x)
              (stepy
                (g (lowerIdx (IST.sup J g) j↑))
                (IST.memberIn (lowerIdx (IST.sup J g) j↑) refl))
              eqz

          z≡gj : z ≡ g (lowerIdx (IST.sup J g) j↑)
          z≡gj = extensionalityᵛ₀ z≈gj
        in
        lowerIdx (IST.sup J g) j↑ , z≡gj

      from : ∀ z → z IST.∈ᵛ IST.sup J g → z IST.∈ᵛ IST.sup I f
      from z z∈y with subst (λ t → liftᵛ z IST.∈ᵛ t) (sym eq) (lift-memberIn z∈y)
      ... | (i↑ , eqz) =
        let
          z≈fi : Mem₀._≈_ z (f (lowerIdx (IST.sup I f) i↑))
          z≈fi =
            lift≈
              (stepy z z∈y)
              (stepx
                (f (lowerIdx (IST.sup I f) i↑))
                (IST.memberIn (lowerIdx (IST.sup I f) i↑) refl))
              eqz

          z≡fi : z ≡ f (lowerIdx (IST.sup I f) i↑)
          z≡fi = extensionalityᵛ₀ z≈fi
        in
        lowerIdx (IST.sup I f) i↑ , z≡fi

  lift-memberOut
    : ∀ {x z : IST.V {ℓ}}
    → liftᵛ z IST.∈ᵛ liftᵛ x
    → z IST.∈ᵛ x
  lift-memberOut {x = x} {z = z} z∈ with IST.memberOut z∈
  ... | (i↑ , eq) =
    let
      z≈child : Mem₀._≈_ z (elemAt↓ x i↑)
      z≈child =
        lift≈
          (Wf.wfᵛ z)
          (Wf.wfᵛ (elemAt↓ x i↑))
          (trans eq (elemAt↓-lift x i↑))
    in
    LowGen.memberIn≈ (lowerIdx x i↑) z≈child

  lift-reflect≈
    : ∀ {x y : IST.V {ℓ}}
    → Mem₁._≈_ (liftᵛ x) (liftᵛ y)
    → Mem₀._≈_ x y
  lift-reflect≈ {x} {y} (xy , yx) = to , from
    where
      to : ∀ z → z IST.∈ᵛ x → z IST.∈ᵛ y
      to z z∈ = lift-memberOut (xy (liftᵛ z) (lift-memberIn z∈))

      from : ∀ z → z IST.∈ᵛ y → z IST.∈ᵛ x
      from z z∈ = lift-memberOut (yx (liftᵛ z) (lift-memberIn z∈))

  crossStagePredicateReificationᵛ : CSR.CrossStagePredicateReification C₀ C₁
  crossStagePredicateReificationᵛ =
    record
      { embed = liftᵛ
      ; Reifiable = λ P →
          Lift (lsuc (lsuc (lsuc ℓ)))
            (Σ (IST.V {lsuc ℓ}) (λ x → ∀ z → (liftᵛ z IST.∈ᵛ x) ↔ P z))
      ; reify = λ _ w → proj₁ (lower w)
      ; mem-reify↔ = λ _ w z → proj₂ (lower w) z
      }

  module WithLiftedImages (collapse₁ : Stage.ExtensionalCollapseᵛ {lsuc ℓ}) where
    module UpperAdapt = Adapt.For collapse₁
    module LiftedAdapt = Adapt.LiftedFor collapse₁
    module UpperLG = GenSub.LocalGenerators UpperAdapt.localGeneratorsᵛ
    module UpperSub = GenSub.GeneratedSubobjects UpperAdapt.generatedSubtreesᵛ
    module UpperIm = GenImage.GeneratedImages UpperAdapt.generatedImagesᵛ

    upperElemAt-lift
      : ∀ (x : IST.V {ℓ})
      → (i : IST.Idx x)
      → UpperLG.elemAt (liftᵛ x) (liftIdx x i) ≡ liftᵛ (IST.elemAt x i)
    upperElemAt-lift x i = elemAt-lift x i

    upperElemAt↓-lift
      : ∀ (x : IST.V {ℓ})
      → (i↑ : IST.Idx (liftᵛ x))
      → UpperLG.elemAt (liftᵛ x) i↑ ≡ liftᵛ (elemAt↓ x i↑)
    upperElemAt↓-lift x i↑ = elemAt↓-lift x i↑

    upperMemberOutLift
      : ∀ {x : IST.V {ℓ}} {u : IST.V {lsuc ℓ}}
      → u IST.∈ᵛ liftᵛ x
      → Σ (IST.V {ℓ}) (λ z → z IST.∈ᵛ x × Mem₁._≈_ u (liftᵛ z))
    upperMemberOutLift {x} {u} u∈ = go (UpperLG.memberOut≈ u∈)
      where
        go
          : Σ (IST.Idx (liftᵛ x)) (λ i↑ → Mem₁._≈_ u (UpperLG.elemAt (liftᵛ x) i↑))
          → Σ (IST.V {ℓ}) (λ z → z IST.∈ᵛ x × Mem₁._≈_ u (liftᵛ z))
        go (i↑ , u≈child↑) =
          elemAt↓ x i↑ , member↓ x i↑ ,
            subst (λ w → Mem₁._≈_ u w) (upperElemAt↓-lift x i↑) u≈child↑

    module ForBase (B₀ : LowTower.BaseAssumptions) where
      module Bundle₀ = Collapse₀.ForBase B₀

      private
        B : Tower.ZFStackBase {lsuc ℓ}
        B = Bundle₀.base

      module FO↑ = CSFO.CrossStageFO B C₁ crossStagePredicateReificationᵛ

      open Tower.ZFStackBase B using (SetU; _∈_; _≈_; sym≈)

      record RelationTransport₀ : Set (lsuc (lsuc ℓ)) where
        field
          transportLeft≈
            : ∀ (R₀ : Syn.Formula) (ρ : FO↑.FB.Valuation)
            → (u u′ z : SetU)
            → u ≈ u′
            → FO↑.FB.evalFormula R₀ (FO↑.FB.extend u (FO↑.FB.extend z ρ))
            → FO↑.FB.evalFormula R₀ (FO↑.FB.extend u′ (FO↑.FB.extend z ρ))

          transportRight≈
            : ∀ (R₀ : Syn.Formula) (ρ : FO↑.FB.Valuation)
            → (u z z′ : SetU)
            → z ≈ z′
            → FO↑.FB.evalFormula R₀ (FO↑.FB.extend u (FO↑.FB.extend z ρ))
            → FO↑.FB.evalFormula R₀ (FO↑.FB.extend u (FO↑.FB.extend z′ ρ))

      strictRelationTransport₀ : RelationTransport₀
      strictRelationTransport₀ =
        record
          { transportLeft≈ =
              λ R₀ ρ u u′ z u≈u′ rel →
                subst
                  (λ w → FO↑.FB.evalFormula R₀ (FO↑.FB.extend w (FO↑.FB.extend z ρ)))
                  (extensionalityᵛ₀ u≈u′)
                  rel
          ; transportRight≈ =
              λ R₀ ρ u z z′ z≈z′ rel →
                subst
                  (λ w → FO↑.FB.evalFormula R₀ (FO↑.FB.extend u (FO↑.FB.extend w ρ)))
                  (extensionalityᵛ₀ z≈z′)
                  rel
          }

      lift-preserves≈
        : ∀ {x y : IST.V {ℓ}}
        → Mem₀._≈_ x y
        → Mem₁._≈_ (liftᵛ x) (liftᵛ y)
      lift-preserves≈ {x} {y} xy = lift-preserves≈-wf (Wf.wfᵛ x) (Wf.wfᵛ y) xy
        where
          lift-preserves≈-wf
            : ∀ {x y : IST.V {ℓ}}
            → WF.Acc IST._∈ᵛ_ x
            → WF.Acc IST._∈ᵛ_ y
            → Mem₀._≈_ x y
            → Mem₁._≈_ (liftᵛ x) (liftᵛ y)
          lift-preserves≈-wf {x} {y} (WF.acc stepx) (WF.acc stepy) (xy , yx) = to , from
            where
              lowerToMemberOut
                : ∀ {z : IST.V {ℓ}}
                → z IST.∈ᵛ x
                → Σ (IST.Idx y) (λ j → Mem₀._≈_ z (LowGen.elemAt y j))
              lowerToMemberOut {z} z∈x = LowGen.memberOut≈ (xy z z∈x)

              lowerFromMemberOut
                : ∀ {z : IST.V {ℓ}}
                → z IST.∈ᵛ y
                → Σ (IST.Idx x) (λ j → Mem₀._≈_ z (LowGen.elemAt x j))
              lowerFromMemberOut {z} z∈y = LowGen.memberOut≈ (yx z z∈y)

              to : ∀ u → u IST.∈ᵛ liftᵛ x → u IST.∈ᵛ liftᵛ y
              to u u∈ with upperMemberOutLift {x = x} u∈
              ... | (z , z∈x , u≈liftz) with lowerToMemberOut z∈x
              ... | (j , z≈ychild) =
                let
                  ychild∈y : LowGen.elemAt y j IST.∈ᵛ y
                  ychild∈y = LowGen.memberIn j refl

                  liftz≈ychild : Mem₁._≈_ (liftᵛ z) (liftᵛ (LowGen.elemAt y j))
                  liftz≈ychild =
                    lift-preserves≈-wf
                      (stepx z z∈x)
                      (stepy (LowGen.elemAt y j) ychild∈y)
                      z≈ychild

                  liftz≈ychild↑ : Mem₁._≈_ (liftᵛ z) (UpperLG.elemAt (liftᵛ y) (liftIdx y j))
                  liftz≈ychild↑ =
                    Mem₁.trans≈
                      liftz≈ychild
                      (Mem₁.≡→≈ (sym (upperElemAt-lift y j)))
                in
                UpperLG.memberIn≈
                  (liftIdx y j)
                  ( (λ z z∈u → fst liftz≈ychild↑ z (fst u≈liftz z z∈u))
                  , (λ z z∈child → snd u≈liftz z (snd liftz≈ychild↑ z z∈child))
                  )

              from : ∀ u → u IST.∈ᵛ liftᵛ y → u IST.∈ᵛ liftᵛ x
              from u u∈ with upperMemberOutLift {x = y} u∈
              ... | (z , z∈y , u≈liftz) with lowerFromMemberOut z∈y
              ... | (j , z≈xchild) =
                let
                  xchild∈x : LowGen.elemAt x j IST.∈ᵛ x
                  xchild∈x = LowGen.memberIn j refl

                  liftz≈xchild : Mem₁._≈_ (liftᵛ z) (liftᵛ (LowGen.elemAt x j))
                  liftz≈xchild =
                    lift-preserves≈-wf
                      (stepy z z∈y)
                      (stepx (LowGen.elemAt x j) xchild∈x)
                      z≈xchild

                  liftz≈xchild↑ : Mem₁._≈_ (liftᵛ z) (UpperLG.elemAt (liftᵛ x) (liftIdx x j))
                  liftz≈xchild↑ =
                    Mem₁.trans≈
                      liftz≈xchild
                      (Mem₁.≡→≈ (sym (upperElemAt-lift x j)))
                in
                UpperLG.memberIn≈
                  (liftIdx x j)
                  ( (λ z z∈u → fst liftz≈xchild↑ z (fst u≈liftz z z∈u))
                  , (λ z z∈child → snd u≈liftz z (snd liftz≈xchild↑ z z∈child))
                  )

      sepPred↑
        : (P : Syn.Formula)
        → FO↑.FB.Valuation
        → (x : SetU)
        → IST.Idx (liftᵛ x) → Set (lsuc ℓ)
      sepPred↑ P ρ x i↑ =
        FO↑.FB.evalFormula P
          (FO↑.FB.extend (IST.elemAt x (lowerIdxᵛ {x = x} i↑)) (FO↑.FB.extend x ρ))

      sepSet↑
        : (P : Syn.Formula)
        → FO↑.FB.Valuation
        → SetU
        → IST.V {lsuc ℓ}
      sepSet↑ P ρ x = Subtree.filterᵛ (liftᵛ x) (sepPred↑ P ρ x)

      sepSet↑-spec
        : ∀ (P : Syn.Formula) (ρ : FO↑.FB.Valuation) (x z : SetU)
        → (liftᵛ z IST.∈ᵛ sepSet↑ P ρ x) ↔ FO↑.SepPred P ρ x z
      sepSet↑-spec P ρ x z =
        intro
          to
          from
        where
          EvalAtAt : SetU → SetU → Set (lsuc ℓ)
          EvalAtAt x′ u = FO↑.FB.evalFormula P (FO↑.FB.extend u (FO↑.FB.extend x′ ρ))

          transportEvalAt
            : ∀ {x′ u u′ : SetU}
            → u ≈ u′
            → EvalAtAt x′ u
            → EvalAtAt x′ u′
          transportEvalAt {x′} u≈u′ =
            subst (EvalAtAt x′) (extensionalityᵛ₀ u≈u′)

          EvalAt : SetU → Set (lsuc ℓ)
          EvalAt = EvalAtAt x

          transportEval
            : ∀ {u u′ : SetU}
            → u ≈ u′
            → EvalAt u
            → EvalAt u′
          transportEval = transportEvalAt {x′ = x}

          to : liftᵛ z IST.∈ᵛ sepSet↑ P ρ x → FO↑.SepPred P ρ x z
          to z∈ with Subtree.filter-memberOut (sepPred↑ P ρ x) z∈
          ... | (i↑ , (child-eval , liftz≡child↑)) =
            let
              liftz≈child : Mem₁._≈_ (liftᵛ z) (liftᵛ (elemAt↓ x i↑))
              liftz≈child =
                Mem₁.≡→≈ (trans liftz≡child↑ (elemAt↓-lift x i↑))

              z≈child : z ≈ elemAt↓ x i↑
              z≈child = lift-reflect≈ liftz≈child

              z∈x : z ∈ x
              z∈x = LowGen.memberIn≈ (lowerIdxᵛ {x = x} i↑) z≈child

              z-eval : EvalAt z
              z-eval = transportEval (Mem₀.sym≈ z≈child) child-eval
            in
            z∈x , z-eval

          fromAt
            : ∀ (x′ : SetU)
            → FO↑.SepPred P ρ x′ z
            → liftᵛ z IST.∈ᵛ sepSet↑ P ρ x′
          fromAt (IST.sup I f) (z∈x′ , z-eval′) with LowGen.memberOut≈ z∈x′
          ... | (i , z≈child) =
            LiftedAdapt.liftedFilterMemberIn
              liftᵛ
              liftIdx
              elemAt-lift
              lift-preserves≈
              (sepPred↑ P ρ (IST.sup I f))
              i
              (transportEvalAt {x′ = IST.sup I f} z≈child z-eval′)
              z≈child

          from
            : FO↑.SepPred P ρ x z
            → liftᵛ z IST.∈ᵛ sepSet↑ P ρ x
          from = fromAt x

      repAssign↑
        : (R₀ : Syn.Formula)
        → (ρ : FO↑.FB.Valuation)
        → (x : SetU)
        → FO↑.FB.FunctionalOnX R₀ ρ x
        → IST.Idx (liftᵛ x)
        → IST.V {lsuc ℓ}
      repAssign↑ R₀ ρ x fun i↑ =
        liftᵛ (proj₁ (fun (elemAt↓ x i↑) (member↓ x i↑)))

      repAssign-rel
        : ∀ (R₀ : Syn.Formula) (ρ : FO↑.FB.Valuation) (x : SetU)
        → (fun : FO↑.FB.FunctionalOnX R₀ ρ x)
        → (i↑ : IST.Idx (liftᵛ x))
        → FO↑.FB.evalFormula R₀
            (FO↑.FB.extend (elemAt↓ x i↑)
              (FO↑.FB.extend
                (proj₁ (fun (elemAt↓ x i↑) (member↓ x i↑)))
                ρ))
      repAssign-rel R₀ ρ x fun i↑ with fun (elemAt↓ x i↑) (member↓ x i↑)
      ... | _ , (rel , _) = rel

      repAssign-unique
        : ∀ (R₀ : Syn.Formula) (ρ : FO↑.FB.Valuation) (x : SetU)
        → (fun : FO↑.FB.FunctionalOnX R₀ ρ x)
        → (i↑ : IST.Idx (liftᵛ x))
        → ∀ z
        → FO↑.FB.evalFormula R₀
            (FO↑.FB.extend (elemAt↓ x i↑) (FO↑.FB.extend z ρ))
        → z ≈ proj₁ (fun (elemAt↓ x i↑) (member↓ x i↑))
      repAssign-unique R₀ ρ x fun i↑ with fun (elemAt↓ x i↑) (member↓ x i↑)
      ... | _ , (_ , uniq) = uniq

      repSet↑
        : (R₀ : Syn.Formula)
        → (ρ : FO↑.FB.Valuation)
        → (x : SetU)
        → FO↑.FB.FunctionalOnX R₀ ρ x
        → IST.V {lsuc ℓ}
      repSet↑ R₀ ρ x fun = UpperIm.generateImage (liftᵛ x) (repAssign↑ R₀ ρ x fun)

      repSet↑-spec
        : ∀ (R₀ : Syn.Formula) (ρ : FO↑.FB.Valuation) (x z : SetU)
        → (fun : FO↑.FB.FunctionalOnX R₀ ρ x)
        → (liftᵛ z IST.∈ᵛ repSet↑ R₀ ρ x fun) ↔ FO↑.RepPred R₀ ρ x z
      repSet↑-spec R₀ ρ x z fun =
        intro
          to
          from
        where
          module T = RelationTransport₀ strictRelationTransport₀

          EvalAt : SetU → SetU → Set (lsuc ℓ)
          EvalAt u w = FO↑.FB.evalFormula R₀ (FO↑.FB.extend u (FO↑.FB.extend w ρ))

          to : liftᵛ z IST.∈ᵛ repSet↑ R₀ ρ x fun → FO↑.RepPred R₀ ρ x z
          to z∈ with UpperIm.outOfGeneratedImage≈ (repAssign↑ R₀ ρ x fun) z∈
          ... | (i↑ , liftz≈img) =
            let
              u : SetU
              u = elemAt↓ x i↑

              u∈x : u ∈ x
              u∈x = member↓ x i↑

              img-lower : SetU
              img-lower = proj₁ (fun u u∈x)

              z≈img : z ≈ img-lower
              z≈img = lift-reflect≈ liftz≈img

              rel-u-img : EvalAt u img-lower
              rel-u-img = repAssign-rel R₀ ρ x fun i↑

              rel-u-z : EvalAt u z
              rel-u-z =
                T.transportRight≈
                  R₀
                  ρ
                  u
                  img-lower
                  z
                  (sym≈ z≈img)
                  rel-u-img
            in
            u , (u∈x , rel-u-z)

          fromAt
            : ∀ {u : SetU}
            → Σ (IST.Idx x) (λ i → u ≈ LowGen.elemAt x i)
            → EvalAt u z
            → liftᵛ z IST.∈ᵛ repSet↑ R₀ ρ x fun
          fromAt {u} (i , u≈child) rel-u-z =
            let
              child-rel-z : EvalAt (LowGen.elemAt x i) z
              child-rel-z =
                T.transportLeft≈ R₀ ρ u (LowGen.elemAt x i) z u≈child rel-u-z

              child∈x : elemAt↓ x (liftIdx x i) ∈ x
              child∈x = member↓ x (liftIdx x i)

              child-rel-z↑ : EvalAt (elemAt↓ x (liftIdx x i)) z
              child-rel-z↑ =
                subst (λ u' → EvalAt u' z) (sym (elemAt↓-liftIdx x i)) child-rel-z

              z≈img : z ≈ proj₁ (fun (elemAt↓ x (liftIdx x i)) child∈x)
              z≈img =
                repAssign-unique
                  R₀
                  ρ
                  x
                  fun
                  (liftIdx x i)
                  z
                  child-rel-z↑

              liftz≈liftimg : Mem₁._≈_ (liftᵛ z) (liftᵛ (proj₁ (fun (elemAt↓ x (liftIdx x i)) child∈x)))
              liftz≈liftimg = lift-preserves≈ z≈img
            in
            UpperIm.intoGeneratedImage≈ (repAssign↑ R₀ ρ x fun) (liftIdx x i) liftz≈liftimg

          from : FO↑.RepPred R₀ ρ x z → liftᵛ z IST.∈ᵛ repSet↑ R₀ ρ x fun
          from (u , (u∈x , rel-u-z)) = fromAt (LowGen.memberOut≈ u∈x) rel-u-z

      foWitnesses↑ : FO↑.CrossStageFOWitnesses
      foWitnesses↑ =
        record
          { sepReifiable = λ P ρ x → lift (sepSet↑ P ρ x , sepSet↑-spec P ρ x)
          ; repReifiable = λ R₀ ρ x fun → lift (repSet↑ R₀ ρ x fun , λ z → repSet↑-spec R₀ ρ x z fun)
          }
