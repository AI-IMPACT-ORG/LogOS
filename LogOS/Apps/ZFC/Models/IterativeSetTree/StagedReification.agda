{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.StagedReification where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.Flow using (idClosure)

open import LogOS.Apps.ZFC.Stack.Boundary using (PredicateBoundary)
import LogOS.Apps.ZFC.SetTheory.MembershipLaws as MemLaws
import LogOS.Apps.ZFC.Stack.AsymptoticReification as AR
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

import LogOS.Apps.ZFC.Models.IterativeSetTree as IST
import LogOS.Apps.ZFC.Models.IterativeSetTree.Context as Ctx
import LogOS.Apps.ZFC.Models.IterativeSetTree.Rank as Rank

private
  module Memᵛ {ℓ : Level} = MemLaws.Laws {SetU = IST.V {ℓ}} IST._∈ᵛ_

Extensionalityᵛ : ∀ {ℓ : Level} → Set (lsuc ℓ)
Extensionalityᵛ {ℓ} = ∀ {x y : IST.V {ℓ}} → Memᵛ._≈_ x y → x ≡ y

record ExtensionalCollapseᵛ {ℓ : Level} : Set (lsuc ℓ) where
  field
    extensionalityᵛ : Extensionalityᵛ {ℓ}

open ExtensionalCollapseᵛ public

record PowersetStructureᵛ {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    powersetᵛ : IST.V {ℓ} → IST.V {ℓ}
    powersetᵛ-spec
      : ∀ x z
      → (IST._∈ᵛ_ z (powersetᵛ x)) ↔ (∀ w → IST._∈ᵛ_ w z → IST._∈ᵛ_ w x)

open PowersetStructureᵛ public

record StageAssumptionsᵛ {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    collapse : ExtensionalCollapseᵛ {ℓ}
    powersetStructureᵛ : PowersetStructureᵛ {ℓ}

open StageAssumptionsᵛ public

module For {ℓ : Level} (A : StageAssumptionsᵛ {ℓ}) where
  open StageAssumptionsᵛ A
    renaming
      ( collapse to collapseᵛA
      ; powersetStructureᵛ to powersetStructureᵛA
      )
  open ExtensionalCollapseᵛ collapseᵛA
    renaming
      ( extensionalityᵛ to extensionalityᵛA
      )
  open PowersetStructureᵛ powersetStructureᵛA
    renaming
      ( powersetᵛ to powersetᵛA
      ; powersetᵛ-spec to powersetᵛ-specA
      )

  private
    C : ZF.SetContext {lsuc ℓ}
    C = Ctx.ctxᵛ {ℓ}

    module C = ZF.SetContext C

    SetU : Set (lsuc ℓ)
    SetU = C.SetU

    PredBnd : ConPreorder (lsuc (lsuc ℓ)) (lsuc ℓ)
    PredBnd = PredicateBoundary SetU

    Predicate : Set (lsuc (lsuc ℓ))
    Predicate = Con PredBnd

    EmptyPred : Predicate
    EmptyPred _ = ⊥

    PairPred : SetU → SetU → Predicate
    PairPred x y z = (C._≈_ z x) ⊎ (C._≈_ z y)

    UnionPred : SetU → Predicate
    UnionPred x z = Σ SetU (λ y → (C._∈_ y x) × (C._∈_ z y))

    PowersetPred : SetU → Predicate
    PowersetPred x z = ∀ w → C._∈_ w z → C._∈_ w x

    ReifiableAt
      : Rank.RankV {ℓ}
      → Predicate
      → Set (lsuc (lsuc ℓ))
    ReifiableAt i P =
      Σ SetU (λ x → (Rank.rankᵛ x Rank.≤ʳ i) × (∀ z → (C._∈_ z x) ↔ P z))

    emptyᵛ-spec : ∀ z → (C._∈_ z IST.emptyᵛ) ↔ EmptyPred z
    emptyᵛ-spec z = intro (λ ()) (λ ())

    pairᵛ-spec
      : ∀ x y z
      → (C._∈_ z (IST.pairᵛ x y)) ↔ PairPred x y z
    pairᵛ-spec x y z =
      intro
        to
        from
      where
        to : C._∈_ z (IST.pairᵛ x y) → PairPred x y z
        to (inj₁ _ , eq) = inj₁ (C.≡→≈ eq)
        to (inj₂ _ , eq) = inj₂ (C.≡→≈ eq)

        from : PairPred x y z → C._∈_ z (IST.pairᵛ x y)
        from (inj₁ z≈x) = inj₁ ttℓ , extensionalityᵛA z≈x
        from (inj₂ z≈y) = inj₂ ttℓ , extensionalityᵛA z≈y

    unionᵛ-spec
      : ∀ x z
      → (C._∈_ z (IST.unionᵛ x)) ↔ UnionPred x z
    unionᵛ-spec (IST.sup I f) z =
      intro
        to
        from
      where
        to : C._∈_ z (IST.unionᵛ (IST.sup I f)) → UnionPred (IST.sup I f) z
        to ((i , j) , eq) =
          f i , ((i , refl) , IST.memberIn j eq)

        from : UnionPred (IST.sup I f) z → C._∈_ z (IST.unionᵛ (IST.sup I f))
        from (y , ((i , y≡fi) , zy)) =
          let
            zy' : C._∈_ z (f i)
            zy' = subst (λ y' → C._∈_ z y') y≡fi zy

            out : Σ (IST.Idx (f i)) (λ j' → z ≡ IST.elemAt (f i) j')
            out = IST.memberOut zy'
          in
          ( (i , proj₁ out)
          , proj₂ out
          )

    powersetᵛ-stage
      : ∀ x
      → Σ (Rank.RankV {ℓ}) (λ i → ReifiableAt i (PowersetPred x))
    powersetᵛ-stage x =
      let
        p = powersetᵛA x
      in
      Rank.rankᵛ p , (p , (Rank.≤ʳ-refl , powersetᵛ-specA x))

  rankStageCPᵛ : ConPreorder (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))
  rankStageCPᵛ =
    record
      { Con = Rank.RankV {ℓ}
      ; _⊑_ = Rank._≤ʳ_
      ; refl = Rank.≤ʳ-refl
      ; trans = Rank.≤ʳ-trans
      }

  stagedPredicateReificationᵛ : AR.StagedPredicateReification C
  stagedPredicateReificationᵛ =
    record
      { GC = idClosure PredBnd
      ; stageCP = rankStageCPᵛ
      ; ReifiableAt = ReifiableAt
      ; monoReifiableAt = λ i≤j (x , (rx≤i , spec)) → x , (Rank.≤ʳ-trans rx≤i i≤j , spec)
      ; reifyAt = λ _ _ w → proj₁ w
      ; mem-reifyAt↔ = λ _ _ w z → snd (proj₂ w) z
      ; emptyAt = Rank.rankᵛ IST.emptyᵛ , (IST.emptyᵛ , (Rank.≤ʳ-refl , emptyᵛ-spec))
      ; pairAt = λ x y →
          Rank.rankᵛ (IST.pairᵛ x y)
          , (IST.pairᵛ x y , (Rank.≤ʳ-refl , pairᵛ-spec x y))
      ; unionAt = λ x →
          Rank.rankᵛ (IST.unionᵛ x)
          , (IST.unionᵛ x , (Rank.≤ʳ-refl , unionᵛ-spec x))
      ; powersetAt = powersetᵛ-stage
      }
