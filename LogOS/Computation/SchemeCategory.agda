{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.SchemeCategory where

open import LogOS.Prelude

open import LogOS.Minimal.Con using (ConPreorder; MonoOn)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.ScaleOps using (ScaleOps; BudgetOps)
import LogOS.Minimal.Truth as Truth

import LogOS.Computation.Scheme as Sch
open import LogOS.Computation.Core using (iterate; iterate-mono)
import LogOS.Computation.Core as CompCore
module StepSim = CompCore.StepSimulation
open import LogOS.Boundary.Telemetry using (TelemetryTrace)

-- A “process” is the part of a `Scheme` that is shared by many paradigms:
-- state carrier + dynamics + closure operator + observation + cost algebra.
--
-- A “choice” then supplies a compiler + a fuel bound into that shared process.

record Process {ℓO ℓC ℓQ : Level} (Output : Set ℓO) : Set (lsuc (ℓO ⊔ ℓC ⊔ ℓQ)) where
  field
    CP       : ConPreorder ℓC
    Step     : ConPreorder.Con CP → ConPreorder.Con CP
    Close     : Sch.Closure CP
    decode   : ConPreorder.Con CP → Output
    Q        : QAdapter ℓQ
    stepCost : ConPreorder.Con CP → QAdapter.Scale Q

  open ConPreorder CP public using (Con; _⊑_; refl; trans)
  open Sch.Closure Close public renaming
    ( cl        to close
    ; mono      to close-mono
    ; infl      to close-infl
    ; idemp-lax to close-idemp-lax
    )
  open QAdapter Q public using (Scale; _≤s_; _·_; e)

scalePreorder
  : ∀ {ℓQ : Level}
    (Q : QAdapter ℓQ)
  → ConPreorder ℓQ
scalePreorder Q =
  record
    { Con = QAdapter.Scale Q
    ; _⊑_ = QAdapter._≤s_ Q
    ; refl = QAdapter.≤s-refl Q
    ; trans = QAdapter.≤s-trans Q
    }

costExecP
  : ∀ {ℓO ℓC ℓQ} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
  → ℕ → Process.Con P → QAdapter.Scale (Process.Q P)
costExecP P zero    c = QAdapter.e (Process.Q P)
costExecP P (suc n) c =
  QAdapter._·_ (Process.Q P) (Process.stepCost P c) (costExecP P n (Process.Step P c))

processTelemetry
  : ∀ {ℓO ℓC ℓQ : Level}
    {Output : Set ℓO}
  → Process {ℓO} {ℓC} {ℓQ} Output
  → TelemetryTrace ℓQ
processTelemetry P =
  record { trace = scalePreorder (Process.Q P) }

execTelemetry
  : ∀ {ℓO ℓC ℓQ : Level}
    {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
  → ℕ → Process.Con P → TelemetryTrace.Trace (processTelemetry P)
execTelemetry P = costExecP P

withinBudget
  : ∀ {ℓO ℓC ℓQ : Level}
    {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
  → ℕ → Process.Con P → QAdapter.Scale (Process.Q P) → Set ℓQ
withinBudget P n c b =
  QAdapter._≤s_ (Process.Q P) (execTelemetry P n c) b

processOf
  : ∀ {ℓI ℓO ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    → Sch.Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output
    → Process {ℓO} {ℓC} {ℓQ} Output
processOf S =
  record
    { CP       = Sch.Scheme.CP S
    ; Step     = Sch.Scheme.Step S
    ; Close     = Sch.Scheme.Close S
    ; decode   = Sch.Scheme.decode S
    ; Q        = Sch.Scheme.Q S
    ; stepCost = Sch.Scheme.stepCost S
    }

processWithDecode
  : ∀ {ℓO ℓO' ℓC ℓQ}
    {Output : Set ℓO} {Output' : Set ℓO'}
    → (P : Process {ℓO} {ℓC} {ℓQ} Output)
    → (Process.Con P → Output')
    → Process {ℓO'} {ℓC} {ℓQ} Output'
processWithDecode P decode' =
  record
    { CP       = Process.CP P
    ; Step     = Process.Step P
    ; Close     = Process.Close P
    ; decode   = decode'
    ; Q        = Process.Q P
    ; stepCost = Process.stepCost P
    }

processWithCost
  : ∀ {ℓO ℓC ℓQ ℓQ'}
    {Output : Set ℓO}
    → (P : Process {ℓO} {ℓC} {ℓQ} Output)
    → (Q' : QAdapter ℓQ')
    → (Process.Con P → QAdapter.Scale Q')
    → Process {ℓO} {ℓC} {ℓQ'} Output
processWithCost P Q' stepCost' =
  record
    { CP       = Process.CP P
    ; Step     = Process.Step P
    ; Close     = Process.Close P
    ; decode   = Process.decode P
    ; Q        = Q'
    ; stepCost = stepCost'
    }

record Choice
  {ℓI ℓO ℓC ℓQ : Level}
  (Input : Set ℓI)
  {Output : Set ℓO}
  (P : Process {ℓO} {ℓC} {ℓQ} Output)
  : Set (lsuc (ℓI ⊔ ℓO ⊔ ℓC ⊔ ℓQ)) where
  open Process P
  field
    compile : Input → Con
    fuel    : Input → ℕ

schemeFromChoice
  : ∀ {ℓI ℓO ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
    → Choice Input P
    → Sch.Scheme Input Output
schemeFromChoice P C =
  record
    { CP       = Process.CP P
    ; Step     = Process.Step P
    ; Close     = Process.Close P
    ; compile  = Choice.compile C
    ; fuel     = Choice.fuel C
    ; decode   = Process.decode P
    ; Q        = Process.Q P
    ; stepCost = Process.stepCost P
    }

-- Morphisms between processes: structure-preserving translations of states
-- (and optionally a cost comparison).

record ProcessHom
  {ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂ : Level}
  {Output : Set ℓO}
  (P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output)
  (P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output)
  : Set (lsuc (ℓO ⊔ ℓC₁ ⊔ ℓQ₁ ⊔ ℓC₂ ⊔ ℓQ₂)) where
  open Process P₁ renaming (Con to Con₁; _⊑_ to _⊑₁_; Step to Step₁; close to norm₁; decode to decode₁)
  open Process P₂ renaming (Con to Con₂; _⊑_ to _⊑₂_; Step to Step₂; close to norm₂; decode to decode₂)
  field
    map     : Con₁ → Con₂
    mono    : ∀ {x y} → x ⊑₁ y → map x ⊑₂ map y
    step-comm : ∀ c → map (Step₁ c) ≡ Step₂ (map c)
    norm-comm : ∀ c → map (norm₁ c) ≡ norm₂ (map c)
    decode-comm : ∀ c → decode₂ (map c) ≡ decode₁ c

ProcessHom→StepSim
  : ∀ {ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂ : Level}
    {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output}
  → ProcessHom P₁ P₂
  → StepSim.StepSim
      (Process.Con P₁) (Process.Con P₂)
      (Process.Step P₁) (Process.Step P₂)
ProcessHom→StepSim h =
  record
    { map       = ProcessHom.map h
    ; step-comm = ProcessHom.step-comm h
    }

-- Lax process morphism: commute with step/normalisation up to the target preorder.
--
-- This is the right notion when your underlying dynamics are only preserved
-- “up to flow/closure” (e.g. under `KernelHomFlow`, where preservation is an inequality).

record ProcessHomLax
  {ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂ : Level}
  {Output : Set ℓO}
  (P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output)
  (P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output)
  : Set (lsuc (ℓO ⊔ ℓC₁ ⊔ ℓQ₁ ⊔ ℓC₂ ⊔ ℓQ₂)) where
  open Process P₁ renaming (Con to Con₁; _⊑_ to _⊑₁_; Step to Step₁; close to norm₁; decode to decode₁)
  open Process P₂ renaming (Con to Con₂; _⊑_ to _⊑₂_; Step to Step₂; close to norm₂; decode to decode₂)
  field
    map       : Con₁ → Con₂
    mono      : ∀ {x y} → x ⊑₁ y → map x ⊑₂ map y
    step-comm≤ : ∀ c → map (Step₁ c) ⊑₂ Step₂ (map c)
    norm-comm≤ : ∀ c → map (norm₁ c) ⊑₂ norm₂ (map c)
    decode-comm : ∀ c → decode₂ (map c) ≡ decode₁ c

ProcessHom→Lax
  : ∀ {ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output}
  → ProcessHom P₁ P₂ → ProcessHomLax P₁ P₂
ProcessHom→Lax {ℓC₂ = ℓC₂} {P₁ = P₁} {P₂ = P₂} h =
  let
    open ProcessHom h
    le₂ : Process.Con P₂ → Process.Con P₂ → Set ℓC₂
    le₂ = Process._⊑_ P₂

    refl₂ : ∀ {x} → le₂ x x
    refl₂ = Process.refl P₂
  in
  record
    { map        = map
    ; mono       = mono
    ; step-comm≤ = λ c → subst (λ z → le₂ (map (Process.Step P₁ c)) z) (step-comm c) refl₂
    ; norm-comm≤ = λ c → subst (λ z → le₂ (map (Process.close P₁ c)) z) (norm-comm c) refl₂
    ; decode-comm = decode-comm
    }

idProcessHomLax
  : ∀ {ℓO ℓC ℓQ} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
  → ProcessHomLax P P
idProcessHomLax P =
  record
    { map        = λ c → c
    ; mono       = λ p → p
    ; step-comm≤ = λ _ → Process.refl P
    ; norm-comm≤ = λ _ → Process.refl P
    ; decode-comm = λ _ → refl
    }

infixr 9 _∘ProcessHomLax_

_∘ProcessHomLax_
  : ∀ {ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂ ℓC₃ ℓQ₃} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output}
    {P₃ : Process {ℓO} {ℓC₃} {ℓQ₃} Output}
  → ProcessHomLax P₂ P₃ → ProcessHomLax P₁ P₂ → ProcessHomLax P₁ P₃
_∘ProcessHomLax_ {P₃ = P₃} g f =
  let
    open ProcessHomLax g renaming
      ( map         to mapg
      ; mono        to monog
      ; step-comm≤  to stepg
      ; norm-comm≤  to normg
      ; decode-comm to decodeg
      )
    open ProcessHomLax f renaming
      ( map         to mapf
      ; mono        to monof
      ; step-comm≤  to stepf
      ; norm-comm≤  to normf
      ; decode-comm to decodef
      )
  in
  record
    { map = λ c → mapg (mapf c)
    ; mono = λ p → monog (monof p)
    ; step-comm≤ = λ c →
        let trans⊑ = Process.trans P₃ in trans⊑ (monog (stepf c)) (stepg (mapf c))
    ; norm-comm≤ = λ c →
        let trans⊑ = Process.trans P₃ in trans⊑ (monog (normf c)) (normg (mapf c))
    ; decode-comm = λ c → LogOS.Prelude.trans (decodeg (mapf c)) (decodef c)
    }

mapChoice
  : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
    {Input : Set ℓI} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output}
    → ProcessHom P₁ P₂ → Choice Input P₁ → Choice Input P₂
mapChoice h C =
  record
    { compile = λ x → ProcessHom.map h (Choice.compile C x)
    ; fuel    = Choice.fuel C
    }

mapChoiceLax
  : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
    {Input : Set ℓI} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output}
    → ProcessHomLax P₁ P₂ → Choice Input P₁ → Choice Input P₂
mapChoiceLax h C =
  record
    { compile = λ x → ProcessHomLax.map h (Choice.compile C x)
    ; fuel    = Choice.fuel C
    }

-- Cost-aware process morphism (small, high-leverage):
-- requires step-cost compatibility on mapped states. This is enough to
-- transport “computes within budget” statements across paradigms.

record ProcessHomCost
  {ℓO ℓC₁ ℓC₂ ℓQ : Level}
  {Output : Set ℓO}
  (P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output)
  (P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output)
  : Set (lsuc (ℓO ⊔ ℓC₁ ⊔ ℓC₂ ⊔ ℓQ)) where
  open Process P₁ renaming (Con to Con₁; Step to Step₁; stepCost to cost₁; Q to Q₁)
  open Process P₂ renaming (Con to Con₂; Step to Step₂; stepCost to cost₂; Q to Q₂)
  field
    hom : ProcessHom P₁ P₂
    Q-comm : Q₂ ≡ Q₁
    stepCost-comm
      : ∀ c
      → subst (λ Q → QAdapter.Scale Q) Q-comm (cost₂ (ProcessHom.map hom c))
        ≡ cost₁ c

open ProcessHomCost public

-- Cast helpers for the “same-Q up to propositional equality” story.
-- These keep proofs readable by localising the `subst (λ Q → ...)` noise.

castScale→
  : ∀ {ℓO ℓC₁ ℓC₂ ℓQ} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
  → ProcessHomCost P₁ P₂
  → QAdapter.Scale (Process.Q P₁)
  → QAdapter.Scale (Process.Q P₂)
castScale→ hc =
  subst (λ Q → QAdapter.Scale Q) (sym (ProcessHomCost.Q-comm hc))

castScale←
  : ∀ {ℓO ℓC₁ ℓC₂ ℓQ} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
  → ProcessHomCost P₁ P₂
  → QAdapter.Scale (Process.Q P₂)
  → QAdapter.Scale (Process.Q P₁)
castScale← hc =
  subst (λ Q → QAdapter.Scale Q) (ProcessHomCost.Q-comm hc)

castOps→
  : ∀ {ℓO ℓC₁ ℓC₂ ℓQ} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
  → ProcessHomCost P₁ P₂
  → ScaleOps (Process.Q P₁)
  → ScaleOps (Process.Q P₂)
castOps→ hc =
  subst (λ Q → ScaleOps Q) (sym (ProcessHomCost.Q-comm hc))

-- Cost transport across *different* Q adapters, via a lax grade morphism.
--
-- This is the “right” transport in the kernel setting: costs live in a quantale,
-- and comparisons between different quantales are typically lax (monoid/quantale
-- homomorphisms are inequalities, not equalities).

record ProcessHomCostWithGrade
  {ℓO ℓC₁ ℓC₂ ℓQ : Level}
  {Output : Set ℓO}
  (P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output)
  (P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output)
  : Set (lsuc (ℓO ⊔ ℓC₁ ⊔ ℓC₂ ⊔ ℓQ)) where
  open Process P₁ renaming (Con to Con₁; Step to Step₁; stepCost to cost₁; Q to Q₁)
  open Process P₂ renaming (Con to Con₂; Step to Step₂; stepCost to cost₂; Q to Q₂)
  field
    hom   : ProcessHom P₁ P₂
    grade : Truth.GuardedCore.GradeHom Q₁ Q₂

    -- One-step cost transport (lax): the cost of a mapped step is bounded by the
    -- grade-map image of the source step cost.
    stepCost≤
      : ∀ c
      → QAdapter._≤s_ Q₂
          (cost₂ (ProcessHom.map hom c))
          (Truth.GuardedCore.GradeHom.map grade (cost₁ c))

open ProcessHomCostWithGrade public

-- Old-style (same-Q) cost morphisms embed into lax grade-transport morphisms.
-- This lets downstream code use the grade-aware lemmas uniformly.

ProcessHomCost→WithGrade
  : ∀ {ℓO ℓC₁ ℓC₂ ℓQ} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
  → ProcessHomCost P₁ P₂
  → ProcessHomCostWithGrade P₁ P₂
ProcessHomCost→WithGrade {P₁ = P₁} {P₂ = P₂} (record { hom = h ; Q-comm = refl ; stepCost-comm = stepCostComm }) =
  record
    { hom = h
    ; grade = Truth.GuardedCore.idGradeHom
    ; stepCost≤ = λ c →
        subst
          (λ z → QAdapter._≤s_ (Process.Q P₂) z (Process.stepCost P₁ c))
          (sym (stepCostComm c))
          (QAdapter.≤s-refl (Process.Q P₂))
    }

-- Budget transport primitives (no global “quantale laws” required):
-- we only need that step-costs commute on mapped states.

iterStep
  : ∀ {ℓO ℓC ℓQ} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
  → ℕ → Process.Con P → Process.Con P
iterStep P n c =
  iterate (record { Step = Process.Step P ; Halts = λ _ → Topℓ }) n c

StepMono
  : ∀ {ℓO ℓC ℓQ} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
  → Set ℓC
StepMono P = MonoOn (Process.CP P) (Process.Step P)

-- Execute for the number of steps induced by a scale budget.
--
-- This is the standard “machines are schemes” bridge:
-- - the scheme (grade) lives in `QAdapter.Scale (Process.Q P)`;
-- - `ScaleOps` interprets that grade as a time budget, then a discrete step budget;
-- - execution is just iterating the machine step.
run≤
  : ∀ {ℓO ℓC ℓQ} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
    (Ops : ScaleOps (Process.Q P))
  → QAdapter.Scale (Process.Q P)
  → Process.Con P
  → Process.Con P
run≤ P Ops g c =
  iterStep P (ScaleOps.steps Ops (ScaleOps.budget Ops g)) c

run≤ᵇ
  : ∀ {ℓO ℓC ℓQ} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
    (Ops : BudgetOps (Process.Q P))
  → QAdapter.Scale (Process.Q P)
  → Process.Con P
  → Process.Con P
run≤ᵇ P Ops = run≤ P (BudgetOps.Ops Ops)

-- If two grades induce the same step budget, they induce the same execution.
--
-- This is the precise form of “time and additional resource axes are
-- independent”: any component of `Scale` that is *not read* by `ScaleOps`
-- cannot affect the execution trace (only the cost bounds).
run≤-stepsEq
  : ∀ {ℓO ℓC ℓQ} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
    (Ops : ScaleOps (Process.Q P))
  → ∀ {g g'} c
  → ScaleOps.steps Ops (ScaleOps.budget Ops g)
    ≡ ScaleOps.steps Ops (ScaleOps.budget Ops g')
  → run≤ P Ops g c ≡ run≤ P Ops g' c
run≤-stepsEq P Ops c eq = cong (λ n → iterStep P n c) eq

iterStep-map
  : ∀ {ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output}
    (h : ProcessHom P₁ P₂)
  → ∀ n c → ProcessHom.map h (iterStep P₁ n c) ≡ iterStep P₂ n (ProcessHom.map h c)
iterStep-map {P₁ = P₁} {P₂ = P₂} h n c =
  StepSim.iterateStep-map (Process.Step P₁) (Process.Step P₂) (ProcessHom→StepSim h) n c

iterStep-map≤
  : ∀ {ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output}
    (h : ProcessHomLax P₁ P₂)
    (stepMono₂ : StepMono P₂)
  → ∀ n c
  → Process._⊑_ P₂
      (ProcessHomLax.map h (iterStep P₁ n c))
      (iterStep P₂ n (ProcessHomLax.map h c))
iterStep-map≤ {P₁ = P₁} {P₂ = P₂} h stepMono₂ zero    _ =
  Process.refl P₂
iterStep-map≤ {P₁ = P₁} {P₂ = P₂} h stepMono₂ (suc n) c =
  Process.trans P₂ ih step≤
  where
    ih
      : Process._⊑_ P₂
          (ProcessHomLax.map h (iterStep P₁ n (Process.Step P₁ c)))
          (iterStep P₂ n (ProcessHomLax.map h (Process.Step P₁ c)))
    ih = iterStep-map≤ {P₁ = P₁} {P₂ = P₂} h stepMono₂ n (Process.Step P₁ c)

    step≤
      : Process._⊑_ P₂
          (iterStep P₂ n (ProcessHomLax.map h (Process.Step P₁ c)))
          (iterStep P₂ n (Process.Step P₂ (ProcessHomLax.map h c)))
    step≤ =
      iterate-mono (Process.CP P₂) (Process.Step P₂) stepMono₂ n (ProcessHomLax.step-comm≤ h c)

-- Representation invariance (CT sneak peek):
-- a structure-preserving process morphism transports grade-indexed execution.
--
-- This is the key “machines are schemes” lemma: if two presentations commute
-- with `Step`, then they commute with “run within a scheme index g”.
run≤-map
  : ∀ {ℓO ℓC₁ ℓC₂ ℓQ} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCost P₁ P₂)
  → ∀ (Ops : ScaleOps (Process.Q P₁))
      (g : QAdapter.Scale (Process.Q P₁))
      (c : Process.Con P₁)
  → ProcessHom.map (ProcessHomCost.hom hc) (run≤ P₁ Ops g c)
    ≡ run≤ P₂
        (castOps→ hc Ops)
        (castScale→ hc g)
        (ProcessHom.map (ProcessHomCost.hom hc) c)
run≤-map {P₁ = P₁} {P₂ = P₂}
  (record { hom = h ; Q-comm = refl ; stepCost-comm = _ }) Ops g c =
  iterStep-map {P₁ = P₁} {P₂ = P₂} h (ScaleOps.steps Ops (ScaleOps.budget Ops g)) c

run≤-meaning-comm
  : ∀ {ℓO ℓC₁ ℓC₂ ℓQ} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCost P₁ P₂)
  → ∀ (Ops : ScaleOps (Process.Q P₁))
      (g : QAdapter.Scale (Process.Q P₁))
      (c : Process.Con P₁)
  → Process.decode P₂
      (Process.close P₂
        (run≤ P₂
          (castOps→ hc Ops)
          (castScale→ hc g)
          (ProcessHom.map (ProcessHomCost.hom hc) c)))
    ≡ Process.decode P₁ (Process.close P₁ (run≤ P₁ Ops g c))
run≤-meaning-comm {P₁ = P₁} {P₂ = P₂}
  hc@(record { hom = h ; Q-comm = refl ; stepCost-comm = _ }) Ops g c =
  let
    open Process P₁ renaming (close to norm₁; decode to dec₁) hiding (refl; trans)
    open Process P₂ renaming (close to norm₂; decode to dec₂) hiding (refl; trans)
    r = run≤ P₁ Ops g c
  in
  LogOS.Prelude.trans
    (cong (λ x → dec₂ (norm₂ x)) (sym (run≤-map hc Ops g c)))
    (LogOS.Prelude.trans
      (cong dec₂ (sym (ProcessHom.norm-comm h r)))
      (ProcessHom.decode-comm h (norm₁ r)))

costExecP≡costExec
  : ∀ {ℓI ℓO ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
    (C : Choice Input P)
  → ∀ n c
  → costExecP P n c ≡ Sch.Scheme.costExec (schemeFromChoice P C) n c
costExecP≡costExec P C zero    _ = refl
costExecP≡costExec P C (suc n) c =
  cong
    (λ t → QAdapter._·_ (Process.Q P) (Process.stepCost P c) t)
    (costExecP≡costExec P C n (Process.Step P c))

costExecP-map≤
  : ∀ {ℓO ℓC₁ ℓC₂ ℓQ} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCostWithGrade P₁ P₂)
  → ∀ n c
  → QAdapter._≤s_ (Process.Q P₂)
      (costExecP P₂ n (ProcessHom.map (ProcessHomCostWithGrade.hom hc) c))
      (Truth.GuardedCore.GradeHom.map (ProcessHomCostWithGrade.grade hc) (costExecP P₁ n c))
costExecP-map≤ {P₁ = P₁} {P₂ = P₂} hc n c =
  go n c
  where
    h = ProcessHomCostWithGrade.hom hc
    φ = ProcessHomCostWithGrade.grade hc
    open Truth.GuardedCore.GradeHom φ renaming (map to mapg; mono to monog; unit-lax to unitl; mul-lax to mull)

    Q₁ = Process.Q P₁
    Q₂ = Process.Q P₂

    _≤₁_ = QAdapter._≤s_ Q₁
    _≤₂_ = QAdapter._≤s_ Q₂
    trans₂ = QAdapter.≤s-trans Q₂
    ·-mono₂ = QAdapter.·-mono Q₂

    go
      : ∀ n c
      → _≤₂_
          (costExecP P₂ n (ProcessHom.map h c))
          (mapg (costExecP P₁ n c))
    go zero    _ = unitl
    go (suc n) c =
      let
        c₂ = ProcessHom.map h c

        step₂≡ : ProcessHom.map h (Process.Step P₁ c) ≡ Process.Step P₂ c₂
        step₂≡ = ProcessHom.step-comm h c

        ih₀ : _≤₂_
               (costExecP P₂ n (Process.Step P₂ c₂))
               (mapg (costExecP P₁ n (Process.Step P₁ c)))
        ih₀ =
          subst
            (λ z → _≤₂_ (costExecP P₂ n z) (mapg (costExecP P₁ n (Process.Step P₁ c))))
            step₂≡
            (go n (Process.Step P₁ c))

        stepCost₀ : _≤₂_
                      (Process.stepCost P₂ c₂)
                      (mapg (Process.stepCost P₁ c))
        stepCost₀ = ProcessHomCostWithGrade.stepCost≤ hc c

        step≤ : _≤₂_
                  (QAdapter._·_ Q₂ (Process.stepCost P₂ c₂) (costExecP P₂ n (Process.Step P₂ c₂)))
                  (QAdapter._·_ Q₂ (mapg (Process.stepCost P₁ c)) (mapg (costExecP P₁ n (Process.Step P₁ c))))
        step≤ = ·-mono₂ stepCost₀ ih₀

        mul≤ : _≤₂_
                 (QAdapter._·_ Q₂ (mapg (Process.stepCost P₁ c)) (mapg (costExecP P₁ n (Process.Step P₁ c))))
                 (mapg (QAdapter._·_ Q₁ (Process.stepCost P₁ c) (costExecP P₁ n (Process.Step P₁ c))))
        mul≤ = mull (Process.stepCost P₁ c) (costExecP P₁ n (Process.Step P₁ c))
      in
      trans₂ step≤ mul≤

costExecP-map
  : ∀ {ℓO ℓC₁ ℓC₂ ℓQ} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCost P₁ P₂)
  → ∀ n c
  → castScale← hc (costExecP P₂ n (ProcessHom.map (ProcessHomCost.hom hc) c))
    ≡ costExecP P₁ n c
costExecP-map {P₁ = P₁} {P₂ = P₂}
  (record { hom = h ; Q-comm = refl ; stepCost-comm = stepCostComm }) n c =
  go n c
  where
    go
      : ∀ n c → costExecP P₂ n (ProcessHom.map h c) ≡ costExecP P₁ n c
    go zero    _ = refl
    go (suc n) c =
      trans
        (cong
          (λ x →
            QAdapter._·_
              (Process.Q P₁)
              x
              (costExecP P₂ n (Process.Step P₂ (ProcessHom.map h c))))
          (stepCostComm c))
        (cong
          (λ z →
            QAdapter._·_
              (Process.Q P₁)
              (Process.stepCost P₁ c)
              z)
          (trans
            (cong (costExecP P₂ n) (sym (ProcessHom.step-comm h c)))
            (go n (Process.Step P₁ c))))

-- ==========================================================================
-- Budgeted execution transport (new: operational, “machines are schemes”)
--
-- `ComputesWithin-map` transports a full close+decode story.
-- Here we expose the lower-level operational layer:
-- - reachability after n steps, and
-- - the accumulated cost of those n steps within a budget.
--
-- This is the minimal abstraction needed to make “budgets are compositional”
-- visible across different presentations of the same process.
-- ==========================================================================

ExecWithin-map-grade
  : ∀ {ℓI ℓO ℓC₁ ℓC₂ ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCostWithGrade P₁ P₂)
    (C  : Choice Input P₁)
  → ∀ n c (b : QAdapter.Scale (Process.Q P₁)) c'
  → Sch.ExecWithin (schemeFromChoice P₁ C) n c b c'
  → Sch.ExecWithin
      (schemeFromChoice P₂ (mapChoice (ProcessHomCostWithGrade.hom hc) C))
      n
      (ProcessHom.map (ProcessHomCostWithGrade.hom hc) c)
      (Truth.GuardedCore.GradeHom.map (ProcessHomCostWithGrade.grade hc) b)
      (ProcessHom.map (ProcessHomCostWithGrade.hom hc) c')

ExecWithin-map
  : ∀ {ℓI ℓO ℓC₁ ℓC₂ ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCost P₁ P₂)
    (C  : Choice Input P₁)
  → ∀ n c (b : QAdapter.Scale (Process.Q P₁)) c'
  → Sch.ExecWithin (schemeFromChoice P₁ C) n c b c'
  → Sch.ExecWithin
      (schemeFromChoice P₂ (mapChoice (ProcessHomCost.hom hc) C))
      n
      (ProcessHom.map (ProcessHomCost.hom hc) c)
      (castScale→ hc b)
      (ProcessHom.map (ProcessHomCost.hom hc) c')
ExecWithin-map {P₁ = P₁} {P₂ = P₂}
  hc@(record { hom = h ; Q-comm = refl ; stepCost-comm = _ })
  C n c b c' ew =
  ExecWithin-map-grade (ProcessHomCost→WithGrade hc) C n c b c' ew

-- Lax-grade variant: transport budgeted executions across different Q adapters.
--
-- Budgets are mapped using the grade morphism.

ExecWithin-map-grade {P₁ = P₁} {P₂ = P₂} hc C n c b c' (reach , cost≤) =
  reach₂ , cost≤₂
  where
    h = ProcessHomCostWithGrade.hom hc
    φ = ProcessHomCostWithGrade.grade hc
    open Truth.GuardedCore.GradeHom φ renaming (map to mapg; mono to monog)

    S₁ = schemeFromChoice P₁ C
    S₂ = schemeFromChoice P₂ (mapChoice h C)

    map = ProcessHom.map h

    reach₂ : iterate (Sch.Scheme.Comp S₂) n (map c) ≡ map c'
    reach₂ =
      LogOS.Prelude.trans
        (sym (iterStep-map h n c))
        (cong map reach)

    cost≤₂ : QAdapter._≤s_ (Sch.Scheme.Q S₂) (Sch.Scheme.costExec S₂ n (map c)) (mapg b)
    cost≤₂ =
      QAdapter.≤s-trans (Sch.Scheme.Q S₂)
        p₂
        (monog cost≤)
      where
        eq₁ : costExecP P₁ n c ≡ Sch.Scheme.costExec S₁ n c
        eq₁ = costExecP≡costExec P₁ C n c

        eq₂ : costExecP P₂ n (map c) ≡ Sch.Scheme.costExec S₂ n (map c)
        eq₂ = costExecP≡costExec P₂ (mapChoice h C) n (map c)

        p₀ : QAdapter._≤s_ (Sch.Scheme.Q S₂) (costExecP P₂ n (map c)) (mapg (costExecP P₁ n c))
        p₀ = costExecP-map≤ hc n c

        p₁ : QAdapter._≤s_ (Sch.Scheme.Q S₂) (Sch.Scheme.costExec S₂ n (map c)) (mapg (costExecP P₁ n c))
        p₁ =
          subst
            (λ z → QAdapter._≤s_ (Sch.Scheme.Q S₂) z (mapg (costExecP P₁ n c)))
            eq₂
            p₀

        p₂ : QAdapter._≤s_ (Sch.Scheme.Q S₂) (Sch.Scheme.costExec S₂ n (map c)) (mapg (Sch.Scheme.costExec S₁ n c))
        p₂ =
          subst
            (λ z → QAdapter._≤s_ (Sch.Scheme.Q S₂) (Sch.Scheme.costExec S₂ n (map c)) z)
            (cong mapg eq₁)
            p₁

ReachesWithin-map
  : ∀ {ℓI ℓO ℓC₁ ℓC₂ ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCost P₁ P₂)
    (C  : Choice Input P₁)
  → ∀ c (b : QAdapter.Scale (Process.Q P₁)) c'
  → Sch.ReachesWithin (schemeFromChoice P₁ C) c b c'
  → Sch.ReachesWithin
      (schemeFromChoice P₂ (mapChoice (ProcessHomCost.hom hc) C))
      (ProcessHom.map (ProcessHomCost.hom hc) c)
      (castScale→ hc b)
      (ProcessHom.map (ProcessHomCost.hom hc) c')
ReachesWithin-map {P₁ = P₁} {P₂ = P₂}
  hc@(record { hom = h ; Q-comm = refl ; stepCost-comm = _ })
  C c b c' (n , ew) =
  n , ExecWithin-map hc C n c b c' ew

ReachesWithin-map-grade
  : ∀ {ℓI ℓO ℓC₁ ℓC₂ ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCostWithGrade P₁ P₂)
    (C  : Choice Input P₁)
  → ∀ c (b : QAdapter.Scale (Process.Q P₁)) c'
  → Sch.ReachesWithin (schemeFromChoice P₁ C) c b c'
  → Sch.ReachesWithin
      (schemeFromChoice P₂ (mapChoice (ProcessHomCostWithGrade.hom hc) C))
      (ProcessHom.map (ProcessHomCostWithGrade.hom hc) c)
      (Truth.GuardedCore.GradeHom.map (ProcessHomCostWithGrade.grade hc) b)
      (ProcessHom.map (ProcessHomCostWithGrade.hom hc) c')
ReachesWithin-map-grade hc C c b c' (n , ew) =
  n , ExecWithin-map-grade hc C n c b c' ew

-- Cost commutation for mapped choices (analogue of `run-comm`).
--
-- This is the easiest way to make “budget transport” explicit without needing
-- halting/normalisation proofs: the total fuel-bounded cost is preserved
-- (up to the `Q-comm` coercion).

cost-comm
  : ∀ {ℓI ℓO ℓC₁ ℓC₂ ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCost P₁ P₂)
    (C  : Choice Input P₁)
  → ∀ x →
    castScale← hc (Sch.cost (schemeFromChoice P₂ (mapChoice (ProcessHomCost.hom hc) C)) x)
      ≡ Sch.cost (schemeFromChoice P₁ C) x
cost-comm {P₁ = P₁} {P₂ = P₂}
  hc C x =
  lemma
  where
    h = ProcessHomCost.hom hc

    S₁ = schemeFromChoice P₁ C
    S₂ = schemeFromChoice P₂ (mapChoice h C)

    n : ℕ
    n = Choice.fuel C x

    c : Process.Con P₁
    c = Choice.compile C x

    c₂ : Process.Con P₂
    c₂ = Sch.Scheme.compile S₂ x

    eq₁ : costExecP P₁ n c ≡ Sch.Scheme.costExec S₁ n c
    eq₁ = costExecP≡costExec P₁ C n c

    eq₂ : costExecP P₂ n c₂ ≡ Sch.Scheme.costExec S₂ n c₂
    eq₂ = costExecP≡costExec P₂ (mapChoice h C) n c₂

    lemma
      : castScale← hc (Sch.cost S₂ x) ≡ Sch.cost S₁ x
    lemma =
      trans
        (cong (castScale← hc) (sym eq₂))
        (trans
          (costExecP-map hc n c)
          eq₁)

ComputesWithin-map-grade
  : ∀ {ℓI ℓO ℓC₁ ℓC₂ ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCostWithGrade P₁ P₂)
    (C  : Choice Input P₁)
  → ∀ x (b : QAdapter.Scale (Process.Q P₁)) y
  → Sch.Scheme.ComputesWithin (schemeFromChoice P₁ C) x b y
  → Sch.Scheme.ComputesWithin
      (schemeFromChoice P₂ (mapChoice (ProcessHomCostWithGrade.hom hc) C))
      x
      (Truth.GuardedCore.GradeHom.map (ProcessHomCostWithGrade.grade hc) b)
      y

ComputesWithin-map
  : ∀ {ℓI ℓO ℓC₁ ℓC₂ ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCost P₁ P₂)
    (C  : Choice Input P₁)
  → ∀ x (b : QAdapter.Scale (Process.Q P₁)) y
  → Sch.Scheme.ComputesWithin (schemeFromChoice P₁ C) x b y
  → Sch.Scheme.ComputesWithin
      (schemeFromChoice P₂ (mapChoice (ProcessHomCost.hom hc) C))
      x
      (castScale→ hc b)
      y
ComputesWithin-map {P₁ = P₁} {P₂ = P₂}
  hc@(record { hom = h ; Q-comm = refl ; stepCost-comm = _ })
  C x b y proof =
  ComputesWithin-map-grade (ProcessHomCost→WithGrade hc) C x b y proof

ComputesWithin-map-grade {P₁ = P₁} {P₂ = P₂} hc C x b y proof =
  go proof
  where
    h = ProcessHomCostWithGrade.hom hc
    φ = ProcessHomCostWithGrade.grade hc
    open Truth.GuardedCore.GradeHom φ renaming (map to mapg)

    S₁ = schemeFromChoice P₁ C
    S₂ = schemeFromChoice P₂ (mapChoice h C)

    go
      : Sch.Scheme.ComputesWithin S₁ x b y
      → Sch.Scheme.ComputesWithin S₂ x (mapg b) y
    go (c' , (n , (reach , (halt₁ , cost≤))) , outEq) =
      c₂ , (n , (reach₂ , (halt₂ , cost≤₂))) , outEq₂
      where
        c₂ = ProcessHom.map h c'

        reach₂-cost≤₂
          : Sch.ExecWithin S₂ n (Sch.Scheme.compile S₂ x) (mapg b) c₂
        reach₂-cost≤₂ =
          ExecWithin-map-grade hc C n (Sch.Scheme.compile S₁ x) b c' (reach , cost≤)

        reach₂ : Sch.exec S₂ n x ≡ c₂
        reach₂ = fst reach₂-cost≤₂

        cost≤₂ : QAdapter._≤s_ (Sch.Scheme.Q S₂) (Sch.Scheme.costAt S₂ n x) (mapg b)
        cost≤₂ = snd reach₂-cost≤₂

        halt₂ : Sch.Scheme.Step S₂ c₂ ≡ c₂
        halt₂ =
          trans
            (sym (ProcessHom.step-comm h c'))
            (cong (ProcessHom.map h) halt₁)

        outEq₂ : Sch.Scheme.decode S₂ (Sch.Scheme.close S₂ c₂) ≡ y
        outEq₂ =
          trans
            (cong (Sch.Scheme.decode S₂) (sym (ProcessHom.norm-comm h c')))
            (trans
              (ProcessHom.decode-comm h (Sch.Scheme.close S₁ c'))
              outEq)

-- Simulation preserves semantics (unbounded, fuel-free):
-- a process homomorphism transports `ComputesTo` proofs from one representation
-- to another (textbook “correctness of simulation” shape).

ComputesTo-map
  : ∀ {ℓI ℓO ℓC₁ ℓC₂ ℓQ₁ ℓQ₂}
    {Input : Set ℓI} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output}
    (h  : ProcessHom P₁ P₂)
    (C  : Choice Input P₁)
  → ∀ x y
  → Sch.Scheme.ComputesTo (schemeFromChoice P₁ C) x y
  → Sch.Scheme.ComputesTo (schemeFromChoice P₂ (mapChoice h C)) x y
ComputesTo-map {P₁ = P₁} {P₂ = P₂} h C x y proof =
  go proof
  where
    S₁ = schemeFromChoice P₁ C
    S₂ = schemeFromChoice P₂ (mapChoice h C)

    exec-map
      : ∀ n x → ProcessHom.map h (Sch.exec S₁ n x) ≡ Sch.exec S₂ n x
    exec-map n x = iterStep-map h n (Sch.Scheme.compile S₁ x)

    go
      : Sch.Scheme.ComputesTo S₁ x y
      → Sch.Scheme.ComputesTo S₂ x y
    go (c' , (n , (reach , halt₁)) , outEq) =
      c₂ , (n , (reach₂ , halt₂)) , outEq₂
      where
        c₂ = ProcessHom.map h c'

        reach₂ : Sch.exec S₂ n x ≡ c₂
        reach₂ =
          trans
            (sym (exec-map n x))
            (cong (ProcessHom.map h) reach)

        halt₂ : Sch.Scheme.Step S₂ c₂ ≡ c₂
        halt₂ =
          trans
            (sym (ProcessHom.step-comm h c'))
            (cong (ProcessHom.map h) halt₁)

        outEq₂ : Sch.Scheme.decode S₂ (Sch.Scheme.close S₂ c₂) ≡ y
        outEq₂ =
          trans
            (cong (Sch.Scheme.decode S₂) (sym (ProcessHom.norm-comm h c')))
            (trans
              (ProcessHom.decode-comm h (Sch.Scheme.close S₁ c'))
              outEq)

idProcessHom
  : ∀ {ℓO ℓC ℓQ} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
    → ProcessHom P P
idProcessHom P =
  record
    { map = λ c → c
    ; mono = λ p → p
    ; step-comm = λ _ → refl
    ; norm-comm = λ _ → refl
    ; decode-comm = λ _ → refl
    }

infixr 9 _∘ProcessHom_

_∘ProcessHom_
  : ∀ {ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂ ℓC₃ ℓQ₃} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output}
    {P₃ : Process {ℓO} {ℓC₃} {ℓQ₃} Output}
    → ProcessHom P₂ P₃ → ProcessHom P₁ P₂ → ProcessHom P₁ P₃
_∘ProcessHom_ g f =
  let
    open ProcessHom g renaming
      ( map        to mapg
      ; mono       to monog
      ; step-comm  to stepg
      ; norm-comm  to normg
      ; decode-comm to decodeg
      )
    open ProcessHom f renaming
      ( map        to mapf
      ; mono       to monof
      ; step-comm  to stepf
      ; norm-comm  to normf
      ; decode-comm to decodef
      )
  in
  record
    { map = λ c → mapg (mapf c)
    ; mono = λ p → monog (monof p)
    ; step-comm = λ c → trans (cong mapg (stepf c)) (stepg (mapf c))
    ; norm-comm = λ c → trans (cong mapg (normf c)) (normg (mapf c))
    ; decode-comm = λ c → trans (decodeg (mapf c)) (decodef c)
    }

-- --------------------------------------------------------------------------
-- Category façade (minimal, no-law packaging)
--
-- `ProcessHom` is the morphism notion for “machines as schemes”.
-- This façade names the categorical structure so downstream code can speak in a
-- standard way (objects/processes, morphisms/simulations, identity, composition)
-- without re-importing implementation details.

module ProcessCategory where
  infixr 9 _∘_
  _∘_ = _∘ProcessHom_
  id  = idProcessHom

module ProcessCategoryLax where
  infixr 9 _∘_
  _∘_ = _∘ProcessHomLax_
  id  = idProcessHomLax

-- Semantics façade (textbook CS shape):
-- simulations are morphisms, and semantics is invariant under morphisms.
--
-- This groups the key “bite” lemmas in one predictable place.

module Semantics where
  Exec≤ = run≤
  Exec≤-natural = run≤-map
  Exec≤-stepsEq = run≤-stepsEq

  Meaning≤-natural = run≤-meaning-comm

  Choice-natural-lax = mapChoiceLax
  ExecTrace-natural-lax = iterStep-map≤
  --
  -- Note: lax morphisms only transport *execution traces* (preorder reachability).
  -- The `ComputesTo`/`ComputesWithin` notions use equality-based halting and
  -- normalisation, so their preservation is stated for strict `ProcessHom`.

  ExecWithin-natural = ExecWithin-map
  ReachesWithin-natural = ReachesWithin-map

  ComputesTo-natural = ComputesTo-map
  ComputesWithin-natural = ComputesWithin-map

  ExecWithin-natural-grade = ExecWithin-map-grade
  ReachesWithin-natural-grade = ReachesWithin-map-grade
  ComputesWithin-natural-grade = ComputesWithin-map-grade
-- A small but useful derived lemma: if you have a process morphism and you run
-- a choice against P₁, then mapping its *normalised execution trace* into P₂
-- preserves the observed output.
--
-- (This is the core compositional fact used to factor “paradigms” through a
-- shared universal process.)

run-comm
  : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
    {Input : Set ℓI} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ₁} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ₂} Output}
    (h : ProcessHom P₁ P₂)
    (C : Choice Input P₁)
    → ∀ x → Sch.run (schemeFromChoice P₂ (mapChoice h C)) x ≡ Sch.run (schemeFromChoice P₁ C) x
run-comm {P₁ = P₁} {P₂ = P₂} h C x = lemma
  where
    S₁ = schemeFromChoice P₁ C
    S₂ = schemeFromChoice P₂ (mapChoice h C)

    open Process P₁ renaming (Con to Con₁; Step to Step₁; close to norm₁; decode to decode₁) hiding (refl; trans)
    open Process P₂ renaming (Con to Con₂; Step to Step₂; close to norm₂; decode to decode₂) hiding (refl; trans)

    iterate-map
      : ∀ n c → ProcessHom.map h (iterate (Sch.Scheme.Comp S₁) n c)
              ≡ iterate (Sch.Scheme.Comp S₂) n (ProcessHom.map h c)
    iterate-map zero    _ = refl
    iterate-map (suc n) c =
      trans
        (iterate-map n (Step₁ c))
        (cong (iterate (Sch.Scheme.Comp S₂) n)
              (ProcessHom.step-comm h c))

    exec-map
      : ∀ n x → ProcessHom.map h (Sch.exec S₁ n x) ≡ Sch.exec S₂ n x
    exec-map n x = iterate-map n (Sch.Scheme.compile S₁ x)

    n : ℕ
    n = Choice.fuel C x

    map-norm-exec
      : ProcessHom.map h (norm₁ (Sch.exec S₁ n x)) ≡ norm₂ (Sch.exec S₂ n x)
    map-norm-exec =
      trans
        (ProcessHom.norm-comm h (Sch.exec S₁ n x))
        (cong norm₂ (exec-map n x))

    lemma : Sch.run S₂ x ≡ Sch.run S₁ x
    lemma =
      trans
        (cong decode₂ (sym map-norm-exec))
        (ProcessHom.decode-comm h (norm₁ (Sch.exec S₁ n x)))
