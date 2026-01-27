{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Truth where

open import LogOS.Prelude
open import LogOS.Prelude.Product using (_×_; _,_; fst; snd)
open import LogOS.Base.Signature
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Closure
open import LogOS.Minimal.Adapter
import LogOS.Syntax.Prop as Prop

-- Minimal S/H/G truth interfaces with explicit laxness

module StrictTruth {ℓ : Level} (Sig : LogOSSignature ℓ) where
  open LogOSSignature Sig
  -- Strict layer interface, supplied by models when needed
  record StrictLayer (Fml : Set ℓ) : Set (lsuc ℓ) where
    field
      Sat_S : Cosp → Fml → Set ℓ

  -- Semantic entailment on the strict layer (all observations).
  EntailsS : ∀ {Fml : Set ℓ} → StrictLayer Fml → Fml → Fml → Set ℓ
  EntailsS S φ ψ =
    ∀ (w : Cosp)
    → StrictLayer.Sat_S S w φ
    → StrictLayer.Sat_S S w ψ

  -- Budget predicates on observations.
  Budget : Set (lsuc ℓ)
  Budget = Cosp → Set ℓ

  -- Budgeted entailment: restrict to observations satisfying `B`.
  EntailsS-budget
    : ∀ {Fml : Set ℓ}
    → StrictLayer Fml
    → Budget
    → Fml → Fml → Set ℓ
  EntailsS-budget S B φ ψ =
    ∀ (w : Cosp)
    → B w
    → StrictLayer.Sat_S S w φ
    → StrictLayer.Sat_S S w ψ

module HomotypicalTruth {ℓ : Level}
                        (Sig : LogOSSignature ℓ)
                        (Q   : QAdapter ℓ)
                        (WH  : Worlds.WorldH Sig Q)
                        where
  open LogOSSignature Sig
  open Worlds Sig
  open QAdapter Q
  open Worlds.WorldH WH using (_≤ctx_)
  -- Constraints and satisfaction in H-tier
  record HLayer (BB : BulkBoundary ℓ) : Set (lsuc ℓ) where
    open BulkBoundary BB
    field
      Sat_H : Cosp → Con_bnd → Set ℓ
      -- Monotonicities (Kripke + constraint)
      mono-Con  : ∀ {w c c'} → _⊑bnd_ c c' → Sat_H w c → Sat_H w c'
      mono-ctx  : ∀ {w w' c} → _≤ctx_ w w' → Sat_H w c → Sat_H w' c

  -- Observational preorder on H-tier constraints (by satisfaction).

  ObsLeH
    : ∀ {BB : BulkBoundary ℓ}
    → HLayer BB
    → BulkBoundary.Con_bnd BB
    → BulkBoundary.Con_bnd BB
    → Set ℓ
  ObsLeH {BB = BB} H c d =
    ∀ w → HLayer.Sat_H H w c → HLayer.Sat_H H w d

  ObsHPreorder
    : ∀ {BB : BulkBoundary ℓ}
    → HLayer BB
    → ConPreorder ℓ
  ObsHPreorder {BB = BB} H =
    let open BulkBoundary BB in
    record
      { Con = Con_bnd
      ; _⊑_ = ObsLeH H
      ; refl = λ {c} w sat → sat
      ; trans = λ cd de w sat → de w (cd w sat)
      }

  ObsEqH
    : ∀ {BB : BulkBoundary ℓ}
    → HLayer BB
    → BulkBoundary.Con_bnd BB
    → BulkBoundary.Con_bnd BB
    → Set ℓ
  ObsEqH H c d = Prop.ObsEqOn (HLayer.Sat_H H) c d

  module ObsEqH-Kit {BB : BulkBoundary ℓ} (H : HLayer BB) where
    open Prop.ObsEqKit (Prop.obsEqKit (HLayer.Sat_H H)) public

  ObsEqH↔ObsLeH
    : ∀ {BB : BulkBoundary ℓ}
    → (H : HLayer BB)
    → {c d : BulkBoundary.Con_bnd BB}
    → Prop._↔_
        (ObsEqH H c d)
        (Prop._∧_ (ObsLeH H c d) (ObsLeH H d c))
  ObsEqH↔ObsLeH H {c} {d} =
    Prop.ObsEqOn↔ObsLeOn {Sat = HLayer.Sat_H H} {x = c} {y = d}

  -- Non-vacuity guard: `Sat_H` distinguishes at least two constraints.
  --
  -- Many kernel/model instances intentionally take `Sat_H = ⊤` for scaffolding,
  -- in which case `ObsLeH`/`ObsEqH` collapse. This guard provides a reusable
  -- witness that the induced observational preorder is nontrivial.

  record VacuousHLayer {BB : BulkBoundary ℓ} (H : HLayer BB) : Set (lsuc ℓ) where
    open BulkBoundary BB
    field
      satAll : ∀ w c → HLayer.Sat_H H w c

  record NonVacuousHLayer {BB : BulkBoundary ℓ} (H : HLayer BB) : Set (lsuc ℓ) where
    open BulkBoundary BB
    field
      w : Cosp
      c₀ c₁ : Con_bnd
      sat₀ : HLayer.Sat_H H w c₀
      unsat₁ : Prop.¬ (HLayer.Sat_H H w c₁)

    ¬ObsLe : Prop.¬ (ObsLeH H c₀ c₁)
    ¬ObsLe le = unsat₁ (le w sat₀)

    ¬ObsEq : Prop.¬ (ObsEqH H c₀ c₁)
    ¬ObsEq eq = ¬ObsLe (fst (Prop.to (ObsEqH↔ObsLeH H) eq))

  distinguishes→¬ObsLeH
    : ∀ {BB : BulkBoundary ℓ}
      {H : HLayer BB}
      {c d : BulkBoundary.Con_bnd BB}
      (w : Cosp)
    → HLayer.Sat_H H w c
    → Prop.¬ (HLayer.Sat_H H w d)
    → Prop.¬ (ObsLeH H c d)
  distinguishes→¬ObsLeH w satc unsatd le = unsatd (le w satc)

  -- Invariance closure (lax)
  record Invariance (BB : BulkBoundary ℓ) : Set (lsuc ℓ) where
    open BulkBoundary BB
    field
      -- Axiom: invariance closure on constraints
      Inv_H        : Con_bnd → Con_bnd
      -- Axiom: inflationary c ≤ Inv_H c
      infl         : ∀ c → _⊑bnd_ c (Inv_H c)
      -- Axiom: idempotent up to ⊑ Inv_H (Inv_H c) ≤ Inv_H c
      idemp-lax    : ∀ c → _⊑bnd_ (Inv_H (Inv_H c)) (Inv_H c)

  -- If Inv_H is monotone, it defines a closure operator (nucleus-like).
  InvH-Closure
    : ∀ {BB : BulkBoundary ℓ}
    → (I : Invariance BB)
    → MonoOn (BulkBoundary.bnd BB) (Invariance.Inv_H I)
    → ClosureOp (BulkBoundary.bnd BB)
  InvH-Closure {BB = BB} I monoI =
    record
      { cl        = Invariance.Inv_H I
      ; mono      = monoI
      ; infl      = Invariance.infl I
      ; idemp-lax = Invariance.idemp-lax I
      }

  -- Optional strengthening: bundle monotonicity so `Inv_H` can be used as a
  -- genuine closure/nucleus operator.

  record InvarianceMono (BB : BulkBoundary ℓ) : Set (lsuc ℓ) where
    field
      core : Invariance BB
      mono-Inv_H : MonoOn (BulkBoundary.bnd BB) (Invariance.Inv_H core)

    open Invariance core public

    Inv_H-Closure : ClosureOp (BulkBoundary.bnd BB)
    Inv_H-Closure = InvH-Closure core mono-Inv_H

  -- Bulk/boundary lax adjunction
  open import LogOS.Minimal.Adjunction using (LaxAdjunction; LaxMonoidalAdjunction)

module GuardedCore {ℓ : Level} where

  -- Guarded closure with a (lax) fixed point Th*
  record GuardedClosure (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
    open ConPreorder CP
    field
      -- Axiom: global flow step
      Flow        : Con → Con
      -- Axiom: monotone; inflationary; idempotent up to ⊑
      mono        : ∀ {c c'} → _⊑_ c c' → _⊑_ (Flow c) (Flow c')
      infl        : ∀ c → _⊑_ c (Flow c)
      idemp-lax   : ∀ c → _⊑_ (Flow (Flow c)) (Flow c)
      -- Axiom: chosen (lax) fixed point witness via inequalities.
      -- Leastness / induction principles are derived separately once additional
      -- domain structure (e.g. ωCPO + finite-first approximants) is provided.
      Th*         : Con
      Th*-fixed   : (_⊑_ (Th*) (Flow Th*)) × (_⊑_ (Flow Th*) Th*)
      -- Approximants Th₀, Th₁, … and dcpo structure can be provided by models

  -- Forget the distinguished fixed-point witness: a guarded closure always yields a
  -- plain closure operator.
  closureOfGuardedClosure
    : ∀ {CP : ConPreorder ℓ}
    → GuardedClosure CP → ClosureOp CP
  closureOfGuardedClosure G =
    record
      { cl        = GuardedClosure.Flow G
      ; mono      = GuardedClosure.mono G
      ; infl      = GuardedClosure.infl G
      ; idemp-lax = GuardedClosure.idemp-lax G
      }

  -- Flow homomorphism (lax): map ∘ F₁ ⊑ F₂ ∘ map.
  --
  -- Note: monotonicity of `map` itself (w.r.t. `_⊑_`) is intentionally not part
  -- of this record; it is usually supplied by the surrounding structure (e.g.
  -- kernel/constraint algebra homs provide a `MonoMap` separately).
  record FlowHom (CP₁ CP₂ : ConPreorder ℓ)
                 (G₁ : GuardedClosure CP₁)
                 (G₂ : GuardedClosure CP₂)
                 (map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂)
                 : Set (lsuc ℓ) where
    open ConPreorder CP₂ using (_⊑_)
    open GuardedClosure G₁ renaming (Flow to F₁)
    open GuardedClosure G₂ renaming (Flow to F₂)
    field
      preserves-F  : ∀ c → _⊑_ (map (F₁ c)) (F₂ (map c))

  -- Optional strengthening: the flow homomorphism also transports the chosen
  -- stabilised truth witness `Th*` as an inequality.
  record FlowHomStable (CP₁ CP₂ : ConPreorder ℓ)
                       (G₁ : GuardedClosure CP₁)
                       (G₂ : GuardedClosure CP₂)
                       (map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂)
                       : Set (lsuc ℓ) where
    open ConPreorder CP₂ using (_⊑_)
    open GuardedClosure G₁ renaming (Th* to Th₁)
    open GuardedClosure G₂ renaming (Th* to Th₂)
    field
      flow-hom     : FlowHom CP₁ CP₂ G₁ G₂ map
      preserves-Th : _⊑_ (map Th₁) Th₂

    open FlowHom flow-hom public

  -- Convenience bundle: a flow homomorphism together with monotonicity of `map`.

  record FlowHomMono (CP₁ CP₂ : ConPreorder ℓ)
                     (G₁ : GuardedClosure CP₁)
                     (G₂ : GuardedClosure CP₂)
                     (map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂)
                     : Set (lsuc ℓ) where
    field
      flow-hom  : FlowHom CP₁ CP₂ G₁ G₂ map
      mono-map : MonoMap CP₁ CP₂ map

    open FlowHom flow-hom public

  -- Composition of monotone flow homomorphisms.

  composeFlowHomMono
    : ∀ {CP₁ CP₂ CP₃ : ConPreorder ℓ}
      {G₁ : GuardedClosure CP₁}
      {G₂ : GuardedClosure CP₂}
      {G₃ : GuardedClosure CP₃}
      {f : ConPreorder.Con CP₁ → ConPreorder.Con CP₂}
      {g : ConPreorder.Con CP₂ → ConPreorder.Con CP₃}
    → FlowHomMono CP₁ CP₂ G₁ G₂ f
    → FlowHomMono CP₂ CP₃ G₂ G₃ g
    → FlowHomMono CP₁ CP₃ G₁ G₃ (λ x → g (f x))
  composeFlowHomMono {CP₁ = CP₁} {CP₂ = CP₂} {CP₃ = CP₃} {f = f} {g = g} hf hg =
    let
      open FlowHomMono hf renaming (flow-hom to hf-core; mono-map to mono-f)
      open FlowHomMono hg renaming (flow-hom to hg-core; mono-map to mono-g)
      open FlowHom hf-core renaming (preserves-F to preserves-Ff)
      open FlowHom hg-core renaming (preserves-F to preserves-Fg)
    in
    record
      { flow-hom =
          record
            { preserves-F = λ c →
                ConPreorder.trans CP₃
                  (mono-g (preserves-Ff c))
                  (preserves-Fg (f c))
            }
      ; mono-map =
          compMonoMap {CP₁ = CP₁} {CP₂ = CP₂} {CP₃ = CP₃} {f = f} {g = g}
            mono-f
            mono-g
      }

  -- Identity (lax) flow homomorphism.

  idFlowHom
    : ∀ {CP : ConPreorder ℓ}
      (G : GuardedClosure CP)
    → FlowHom CP CP G G (λ x → x)
  idFlowHom {CP = CP} _ =
    record
      { preserves-F  = λ _ → ConPreorder.refl CP }

  idFlowHomStable
    : ∀ {CP : ConPreorder ℓ}
      (G : GuardedClosure CP)
    → FlowHomStable CP CP G G (λ x → x)
  idFlowHomStable {CP = CP} G =
    record
      { flow-hom     = idFlowHom {CP = CP} G
      ; preserves-Th = ConPreorder.refl CP
      }

  idFlowHomMono
    : ∀ {CP : ConPreorder ℓ}
      (G : GuardedClosure CP)
    → FlowHomMono CP CP G G (λ x → x)
  idFlowHomMono {CP = CP} G =
    record
      { flow-hom  = idFlowHom {CP = CP} G
      ; mono-map = idMonoMap {CP = CP}
      }

  -- Transport: a flow homomorphism induces a closure homomorphism between the
  -- induced (unguarded) closure operators.

  closureHomOfFlowHom
    : ∀ {CP₁ CP₂ : ConPreorder ℓ}
      {G₁ : GuardedClosure CP₁}
      {G₂ : GuardedClosure CP₂}
      {map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂}
    → FlowHom CP₁ CP₂ G₁ G₂ map
    → ClosureHom CP₁ CP₂ (closureOfGuardedClosure G₁) (closureOfGuardedClosure G₂) map
  closureHomOfFlowHom fh =
    record { preserves-cl = FlowHom.preserves-F fh }

  closureHomMonoOfFlowHomMono
    : ∀ {CP₁ CP₂ : ConPreorder ℓ}
      {G₁ : GuardedClosure CP₁}
      {G₂ : GuardedClosure CP₂}
      {map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂}
    → FlowHomMono CP₁ CP₂ G₁ G₂ map
    → ClosureHomMono CP₁ CP₂ (closureOfGuardedClosure G₁) (closureOfGuardedClosure G₂) map
  closureHomMonoOfFlowHomMono fh =
    mkClosureHomMono
      (FlowHomMono.mono-map fh)
      (closureHomOfFlowHom (FlowHomMono.flow-hom fh))

  -- Graded guarded closure: grade-indexed flow + saturation grade for fixed points.
  record GradedClosure (Q : QAdapter ℓ)
                       (CP : ConPreorder ℓ)
                       : Set (lsuc ℓ) where
    open QAdapter Q renaming (Scale to Grade; _≤s_ to _≤g_; _·_ to _∙_; e to ε)
    open ConPreorder CP
    field
      Flow       : Grade → Con → Con
      mono       : ∀ {g c c'} → _⊑_ c c' → _⊑_ (Flow g c) (Flow g c')
      mono-grade : ∀ {g g'} → _≤g_ g g' → ∀ c → _⊑_ (Flow g c) (Flow g' c)
      -- Grade order convention: `comp-lax` witnesses one-step composition as
      -- `Flow g' (Flow g c) ⊑ Flow (g ∙ g') c`.
      comp-lax   : ∀ g g' c → _⊑_ (Flow g' (Flow g c)) (Flow (g ∙ g') c)

      sat        : Grade
      sat-top    : ∀ g → _≤g_ g sat
      infl-sat   : ∀ c → _⊑_ c (Flow sat c)
      idemp-sat  : ∀ c → _⊑_ (Flow sat (Flow sat c)) (Flow sat c)
      Th*        : Con
      Th*-fixed  : (_⊑_ Th* (Flow sat Th*)) × (_⊑_ (Flow sat Th*) Th*)

  -- Saturation grade induces a (plain) closure operator.
  closureOfGradedClosure-sat
    : ∀ {Q : QAdapter ℓ} {CP : ConPreorder ℓ}
    → GradedClosure Q CP → ClosureOp CP
  closureOfGradedClosure-sat GC =
    record
      { cl        = GradedClosure.Flow GC (GradedClosure.sat GC)
      ; mono      = λ {c} {c'} le → GradedClosure.mono GC le
      ; infl      = GradedClosure.infl-sat GC
      ; idemp-lax = GradedClosure.idemp-sat GC
      }

  -- Lax grade morphism (monotone, monoid-compatible).
  record GradeHom (Q₁ Q₂ : QAdapter ℓ) : Set (lsuc ℓ) where
    module Q1 = QAdapter Q₁
    module Q2 = QAdapter Q₂
    field
      map      : Q1.Scale → Q2.Scale
      mono     : ∀ {g g'} → Q1._≤s_ g g' → Q2._≤s_ (map g) (map g')
      unit-lax : Q2._≤s_ Q2.e (map Q1.e)
      mul-lax  : ∀ g g' → Q2._≤s_ (Q2._·_ (map g) (map g')) (map (Q1._·_ g g'))
      -- Lax finite-join preservation (quantale “additive” structure).
      --
      -- The inequality direction is chosen to match the library’s “upper envelope”
      -- reading of joins: mapping a combined budget should be at least as large
      -- as combining mapped budgets.
      join-lax : ∀ g g' → Q2._≤s_ (Q2._⊔s_ (map g) (map g')) (map (Q1._⊔s_ g g'))
      bot-lax  : Q2._≤s_ Q2.⊥s (map Q1.⊥s)

  -- Small builder: extend a monoid-lax grade map to a lax quantale hom by
  -- deriving the join/bottom laws from monotonicity + finite joins.
  mkGradeHom
    : ∀ {Q₁ Q₂ : QAdapter ℓ}
      (map : QAdapter.Scale Q₁ → QAdapter.Scale Q₂)
      (mono : ∀ {g g'} → QAdapter._≤s_ Q₁ g g' → QAdapter._≤s_ Q₂ (map g) (map g'))
      (unit-lax : QAdapter._≤s_ Q₂ (QAdapter.e Q₂) (map (QAdapter.e Q₁)))
      (mul-lax  : ∀ g g' →
                  QAdapter._≤s_ Q₂
                    (QAdapter._·_ Q₂ (map g) (map g'))
                    (map (QAdapter._·_ Q₁ g g')))
      → GradeHom Q₁ Q₂
  mkGradeHom {Q₁ = Q₁} {Q₂ = Q₂} map mono unit-lax mul-lax =
    record
      { map = map
      ; mono = mono
      ; unit-lax = unit-lax
      ; mul-lax = mul-lax
      ; join-lax = joinLax
      ; bot-lax  = QAdapter.⊥s-least Q₂ (map (QAdapter.⊥s Q₁))
      }
    where
      joinLax
        : ∀ g g'
          → QAdapter._≤s_ Q₂
              (QAdapter._⊔s_ Q₂ (map g) (map g'))
              (map (QAdapter._⊔s_ Q₁ g g'))
      joinLax g g' =
        QAdapter.⊔s-least Q₂
          (mono (QAdapter.⊔s-ub₁ Q₁ g g'))
          (mono (QAdapter.⊔s-ub₂ Q₁ g g'))

  -- Identity and composition for grade morphisms.
  --
  -- These live in the minimal core so higher layers (kernel morphisms, bridges)
  -- can compose grade maps without re-proving quantale/monoid coherence.

  idGradeHom : ∀ {Q : QAdapter ℓ} → GradeHom Q Q
  idGradeHom {Q} =
    mkGradeHom (λ g → g) (λ le → le)
      (QAdapter.≤s-refl Q)
      (λ _ _ → QAdapter.≤s-refl Q)

  composeGradeHom
    : ∀ {Q₁ Q₂ Q₃ : QAdapter ℓ}
      → GradeHom Q₁ Q₂
      → GradeHom Q₂ Q₃
      → GradeHom Q₁ Q₃
  composeGradeHom {Q₁ = Q₁} {Q₂ = Q₂} {Q₃ = Q₃} φ ψ =
    record
      { map      = mapComp
      ; mono     = monoComp
      ; unit-lax = unitComp
      ; mul-lax  = mulComp
      ; join-lax = joinComp
      ; bot-lax  = botComp
      }
    where
      open GradeHom φ renaming
        ( map      to map₁
        ; mono     to mono₁
        ; unit-lax to unit₁
        ; mul-lax  to mul₁
        ; join-lax to join₁
        ; bot-lax  to bot₁
        )
      open GradeHom ψ renaming
        ( map      to map₂
        ; mono     to mono₂
        ; unit-lax to unit₂
        ; mul-lax  to mul₂
        ; join-lax to join₂
        ; bot-lax  to bot₂
        )

      mapComp : QAdapter.Scale Q₁ → QAdapter.Scale Q₃
      mapComp g = map₂ (map₁ g)

      monoComp : ∀ {g g'} → QAdapter._≤s_ Q₁ g g' → QAdapter._≤s_ Q₃ (mapComp g) (mapComp g')
      monoComp le = mono₂ (mono₁ le)

      unitComp : QAdapter._≤s_ Q₃ (QAdapter.e Q₃) (mapComp (QAdapter.e Q₁))
      unitComp =
        QAdapter.≤s-trans Q₃
          unit₂
          (mono₂ unit₁)

      mulComp
        : ∀ g g'
          → QAdapter._≤s_ Q₃
              (QAdapter._·_ Q₃ (mapComp g) (mapComp g'))
              (mapComp (QAdapter._·_ Q₁ g g'))
      mulComp g g' =
        QAdapter.≤s-trans Q₃
          (mul₂ (map₁ g) (map₁ g'))
          (mono₂ (mul₁ g g'))

      joinComp
        : ∀ g g'
          → QAdapter._≤s_ Q₃
              (QAdapter._⊔s_ Q₃ (mapComp g) (mapComp g'))
              (mapComp (QAdapter._⊔s_ Q₁ g g'))
      joinComp g g' =
        QAdapter.≤s-trans Q₃
          (join₂ (map₁ g) (map₁ g'))
          (mono₂ (join₁ g g'))

      botComp : QAdapter._≤s_ Q₃ (QAdapter.⊥s Q₃) (mapComp (QAdapter.⊥s Q₁))
      botComp =
        QAdapter.≤s-trans Q₃
          bot₂
          (mono₂ bot₁)

  -- Graded flow homomorphism (same grade carrier).
  record GradedFlowHom {Q : QAdapter ℓ}
                       (CP₁ CP₂ : ConPreorder ℓ)
                       (G₁ : GradedClosure Q CP₁)
                       (G₂ : GradedClosure Q CP₂)
                       (map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂)
                       : Set (lsuc ℓ) where
    open ConPreorder CP₂ using (_⊑_)
    open GradedClosure G₁ renaming (Flow to F₁)
    open GradedClosure G₂ renaming (Flow to F₂)
    field
      preserves-F  : ∀ g c → _⊑_ (map (F₁ g c)) (F₂ g (map c))

  -- Optional strengthening: transport the chosen stabilised truth witness `Th*`.
  record GradedFlowHomStable {Q : QAdapter ℓ}
                             (CP₁ CP₂ : ConPreorder ℓ)
                             (G₁ : GradedClosure Q CP₁)
                             (G₂ : GradedClosure Q CP₂)
                             (map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂)
                             : Set (lsuc ℓ) where
    open ConPreorder CP₂ using (_⊑_)
    open GradedClosure G₁ renaming (Th* to Th₁)
    open GradedClosure G₂ renaming (Th* to Th₂)
    field
      flow-hom     : GradedFlowHom CP₁ CP₂ G₁ G₂ map
      preserves-Th : _⊑_ (map Th₁) Th₂

    open GradedFlowHom flow-hom public

  -- Graded flow homomorphism with a grade morphism.
  record GradedFlowHomWithGrade {Q₁ Q₂ : QAdapter ℓ}
                                (CP₁ CP₂ : ConPreorder ℓ)
                                (G₁ : GradedClosure Q₁ CP₁)
                                (G₂ : GradedClosure Q₂ CP₂)
                                (φ : GradeHom Q₁ Q₂)
                                (map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂)
                                : Set (lsuc ℓ) where
    open ConPreorder CP₂ using (_⊑_)
    open GradedClosure G₁ renaming (Flow to F₁; Th* to Th₁; sat to sat₁)
    open GradedClosure G₂ renaming (Flow to F₂; Th* to Th₂; sat to sat₂)
    open GradeHom φ renaming (map to grade-map)
    field
      preserves-F  : ∀ g c → _⊑_ (map (F₁ g c)) (F₂ (grade-map g) (map c))
      sat≤         : QAdapter._≤s_ Q₂ (grade-map sat₁) sat₂

  -- Forget grading by taking the saturation grade.
  forgetGradedClosure
    : ∀ {Q : QAdapter ℓ} {CP : ConPreorder ℓ}
    → GradedClosure Q CP
    → GuardedClosure CP
  forgetGradedClosure {Q = Q} {CP = CP} GC =
    record
      { Flow      = Flow sat
      ; mono      = λ {c} {c'} le → GradedClosure.mono GC {g = sat} le
      ; infl      = infl-sat
      ; idemp-lax = idemp-sat
      ; Th*       = Th*
      ; Th*-fixed = Th*-fixed
      }
    where
      open GradedClosure GC

  -- Forget grading for graded flow homomorphisms (use saturation grades).

  forgetGradedFlowHom
    : ∀ {Q : QAdapter ℓ}
      {CP₁ CP₂ : ConPreorder ℓ}
      {G₁ : GradedClosure Q CP₁}
      {G₂ : GradedClosure Q CP₂}
      {map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂}
    → GradedFlowHom {Q = Q} CP₁ CP₂ G₁ G₂ map
    → FlowHom CP₁ CP₂ (forgetGradedClosure G₁) (forgetGradedClosure G₂) map
  forgetGradedFlowHom {CP₂ = CP₂} {G₁ = G₁} {G₂ = G₂} {map = f} h =
    let
      open GradedClosure G₁ renaming (sat to sat₁)
      open GradedClosure G₂ renaming (mono-grade to mono-grade₂; sat-top to sat-top₂)
      open GradedFlowHom h
    in
    record
      { preserves-F = λ c →
          ConPreorder.trans CP₂
            (preserves-F sat₁ c)
            (mono-grade₂ (sat-top₂ sat₁) (f c))
      }

  forgetGradedFlowHomWithGrade
    : ∀ {Q₁ Q₂ : QAdapter ℓ}
      {CP₁ CP₂ : ConPreorder ℓ}
      {G₁ : GradedClosure Q₁ CP₁}
      {G₂ : GradedClosure Q₂ CP₂}
      {φ : GradeHom Q₁ Q₂}
      {map : ConPreorder.Con CP₁ → ConPreorder.Con CP₂}
    → GradedFlowHomWithGrade {Q₁ = Q₁} {Q₂ = Q₂} CP₁ CP₂ G₁ G₂ φ map
    → FlowHom CP₁ CP₂ (forgetGradedClosure G₁) (forgetGradedClosure G₂) map
  forgetGradedFlowHomWithGrade {CP₂ = CP₂} {G₁ = G₁} {G₂ = G₂} {map = f} h =
    let
      open GradedClosure G₁ renaming (sat to sat₁)
      open GradedClosure G₂ renaming (mono-grade to mono-grade₂)
      open GradedFlowHomWithGrade h
    in
    record
      { preserves-F = λ c →
          ConPreorder.trans CP₂
            (preserves-F sat₁ c)
            (mono-grade₂ sat≤ (f c))
      }

  -- Optional ω-CPO structure (finite-first via ω-approximants, Scott continuity)
  record OmegaCPO (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
    open ConPreorder CP
    field
      ⊥      : Con
      isBot  : ∀ c → _⊑_ ⊥ c
      supω   : (ℕ → Con) → Con
      ub     : ∀ (f : ℕ → Con) (n : ℕ) → _⊑_ (f n) (supω f)
      least  : ∀ (f : ℕ → Con) (x : Con) → (∀ n → _⊑_ (f n) x) → _⊑_ (supω f) x

  -- Generic Kleene μ-calculus on a boundary preorder:
  -- define μ as the ω-sup of approximants from ⊥, and derive Park/least-pre-fixed
  -- point induction. This is independent of any distinguished `Th*`.

  module Kleene
    {CP : ConPreorder ℓ}
    (ωCPO : OmegaCPO CP)
    where
    open ConPreorder CP
    open OmegaCPO ωCPO

    -- Iteration from ⊥ (Kleene approximants).
    iter : (Con → Con) → ℕ → Con
    iter F zero    = ⊥
    iter F (suc n) = F (iter F n)

    μ : (Con → Con) → Con
    μ F = supω (iter F)

    -- “Unfold-left”: μF is always below one more step (no continuity needed).
    μ-unfold-left
      : (F : Con → Con)
      → MonoOn CP F
      → _⊑_ (μ F) (F (μ F))
    μ-unfold-left F monoF =
      least (iter F) (F (μ F)) ubF
      where
        ubF : ∀ n → _⊑_ (iter F n) (F (μ F))
        ubF zero = isBot (F (μ F))
        ubF (suc n) = monoF (ub (iter F) n)

    -- Park/least-pre-fixed-point induction for μF.
    μ-induction
      : (F : Con → Con)
      → MonoOn CP F
      → ∀ c → _⊑_ (F c) c → _⊑_ (μ F) c
    μ-induction F monoF c pre =
      least (iter F) c (iter≤c pre)
      where
        iter≤c : _⊑_ (F c) c → ∀ n → _⊑_ (iter F n) c
        iter≤c _ zero = isBot c
        iter≤c pre (suc n) =
          ConPreorder.trans CP (monoF (iter≤c pre n)) pre

    -- Scott-continuity (lax) for an endomap on an ωCPO preorder.
    record ScottContinuous (F : Con → Con) : Set (lsuc ℓ) where
      field
        cont-ω : ∀ (f : ℕ → Con)
                 (mono-chain : ∀ n → _⊑_ (f n) (f (suc n)))
               → _⊑_ (F (supω f)) (supω (λ n → F (f n)))

    -- Supremum monotonicity: pointwise refinement lifts to supω.
    supω-mono
      : ∀ {f g : ℕ → Con}
      → (∀ n → _⊑_ (f n) (g n))
      → _⊑_ (supω f) (supω g)
    supω-mono {f} {g} f≤g =
      least f (supω g) (λ n → ConPreorder.trans CP (f≤g n) (ub g n))

    -- Scott-continuity is stable under composition of monotone maps.
    ScottContinuous-comp
      : ∀ {F G : Con → Con}
      → MonoOn CP F
      → ScottContinuous F
      → MonoOn CP G
      → ScottContinuous G
      → ScottContinuous (λ x → F (G x))
    ScottContinuous-comp {F = F} {G = G} monoF SCF monoG SCG =
      record
        { cont-ω = λ f mono-chain →
            ConPreorder.trans CP
              (monoF (ScottContinuous.cont-ω SCG f mono-chain))
              (ScottContinuous.cont-ω SCF (λ n → G (f n)) (λ n → monoG (mono-chain n)))
        }

    -- Monotone comparison of Kleene μ along a pointwise refinement.
    μ-mono
      : ∀ {F G : Con → Con}
      → MonoOn CP G
      → (∀ c → _⊑_ (F c) (G c))
      → _⊑_ (μ F) (μ G)
    μ-mono monoG leFG =
      supω-mono (iter-mono monoG leFG)
      where
        iter-mono
          : ∀ {F G : Con → Con}
          → MonoOn CP G
          → (∀ c → _⊑_ (F c) (G c))
          → ∀ n → _⊑_ (iter F n) (iter G n)
        iter-mono {F = F} {G = G} _ _ zero = ConPreorder.refl CP
        iter-mono {F = F} {G = G} monoG' leFG' (suc n) =
          ConPreorder.trans CP
            (leFG' (iter F n))
            (monoG' (iter-mono monoG' leFG' n))

    -- Tail-sup is always bounded by the full sup: sup (f ∘ suc) ⊑ sup f.
    supω-tail≤
      : (f : ℕ → Con)
      → _⊑_ (supω (λ n → f (suc n))) (supω f)
    supω-tail≤ f =
      least (λ n → f (suc n)) (supω f) (λ n → ub f (suc n))

    -- Any inflationary endomap yields an increasing Kleene chain.
    iter-mono-chain-infl
      : (F : Con → Con)
      → (inflF : ∀ c → _⊑_ c (F c))
      → ∀ n → _⊑_ (iter F n) (iter F (suc n))
    iter-mono-chain-infl F inflF zero =
      isBot (F ⊥)
    iter-mono-chain-infl F inflF (suc n) =
      inflF (iter F (suc n))

    -- “Unfold-right”: under Scott continuity (and any chosen chain witness),
    -- μF is also a pre-fixed point: F (μF) ⊑ μF.
    μ-unfold-right
      : (F : Con → Con)
      → ScottContinuous F
      → (mono-chain : ∀ n → _⊑_ (iter F n) (iter F (suc n)))
      → _⊑_ (F (μ F)) (μ F)
    μ-unfold-right F SC mono-chain =
      ConPreorder.trans CP step₁ step₂
      where
        open ScottContinuous SC
        step₁ : _⊑_ (F (μ F)) (supω (λ n → F (iter F n)))
        step₁ = cont-ω (iter F) mono-chain

        step₂ : _⊑_ (supω (λ n → F (iter F n))) (μ F)
        step₂ =
          -- F (iter n) is definitionally iter (suc n)
          supω-tail≤ (iter F)

    -- Turnkey version: derive the chain witness from inflationarity.
    μ-unfold-right-infl
      : (F : Con → Con)
      → ScottContinuous F
      → (inflF : ∀ c → _⊑_ c (F c))
      → _⊑_ (F (μ F)) (μ F)
    μ-unfold-right-infl F SC inflF =
      μ-unfold-right F SC (iter-mono-chain-infl F inflF)

  -- Optional continuity and finite-first specification, layered over GuardedClosure
  record FiniteFirst (CP : ConPreorder ℓ)
                      (GC : GuardedClosure CP)
                      (ωCPO : OmegaCPO CP)
                      : Set (lsuc ℓ) where
    open ConPreorder CP
    open GuardedClosure GC renaming (Flow to F; Th* to Th⋆)
    open OmegaCPO ωCPO
    field
      approx0  : Con
      approxS  : (ℕ → Con)
      base     : approxS zero ≡ ⊥
      step     : ∀ n → approxS (suc n) ≡ F (approxS n)
      Th⋆-as-sup : (_⊑_ Th⋆ (supω approxS)) × (_⊑_ (supω approxS) Th⋆)
      -- Scott continuity (lax) w.r.t. ω-chains
      cont-ω : ∀ (f : ℕ → Con)
                (mono-chain : ∀ n → _⊑_ (f n) (f (suc n))) →
                _⊑_ (F (supω f)) (supω (λ n → F (f n)))

  -- Induction principle (lax μ-induction) under FiniteFirst
  μ-induction
    : ∀ {CP : ConPreorder ℓ}
      (GC : GuardedClosure CP)
      (ωCPO : OmegaCPO CP)
      (FF : FiniteFirst CP GC ωCPO)
      (c : ConPreorder.Con CP)
      → ConPreorder._⊑_ CP (GuardedClosure.Flow GC c) c
      → ConPreorder._⊑_ CP (GuardedClosure.Th* GC) c
  μ-induction {CP} GC ωCPO FF c pre =
    ConPreorder.trans CP p sup≤c
    where
      open ConPreorder CP
      open GuardedClosure GC renaming (Flow to F; Th* to Th⋆)
      open OmegaCPO ωCPO
      open FiniteFirst FF renaming (approxS to A; base to baseEq; step to stepEq; Th⋆-as-sup to supineq)
      -- Show each approximant ≤ c by induction on n
      chain : (n : ℕ) → _⊑_ (A n) c
      chain zero = subst (λ x → _⊑_ x c) (sym baseEq) (isBot c)
      chain (suc n) =
        subst (λ x → _⊑_ x c)
              (sym (stepEq n))
              (ConPreorder.trans CP (GuardedClosure.mono GC (chain n)) pre)
      sup≤c = least A c (λ n → chain n)
      pq : (_⊑_ Th⋆ (supω A)) × (_⊑_ (supω A) Th⋆)
      pq = supineq
      p : _⊑_ Th⋆ (supω A)
      p = fst pq
      q : _⊑_ (supω A) Th⋆
      q = snd pq

module GuardedTruth {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) where
  open LogOSSignature Sig
  open Worlds Sig
  open GuardedCore {ℓ} public
