{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.SchemeCategory where

open import LogOS.Prelude

open import LogOS.Minimal.Con using (ConPoset)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.ScaleOps using (ScaleOps)

import LogOS.Computation.Scheme as Sch
open import LogOS.Computation.Core using (iterate)

-- A “process” is the part of a `Scheme` that is shared by many paradigms:
-- state carrier + dynamics + renormaliser + observation + cost algebra.
--
-- A “choice” then supplies a compiler + a fuel bound into that shared process.

record Process {ℓO ℓC ℓQ : Level} (Output : Set ℓO) : Set (lsuc (ℓO ⊔ ℓC ⊔ ℓQ)) where
  field
    CP       : ConPoset ℓC
    Step     : ConPoset.Con CP → ConPoset.Con CP
    Norm     : Sch.Closure CP
    decode   : ConPoset.Con CP → Output
    Q        : QAdapter ℓQ
    stepCost : ConPoset.Con CP → QAdapter.Scale Q

  open ConPoset CP public using (Con; _⊑_; refl; trans)
  open Sch.Closure Norm public renaming
    ( normalize  to normalize
    ; mono       to normalize-mono
    ; infl       to normalize-infl
    ; idemp-lax  to normalize-idemp-lax
    )
  open QAdapter Q public using (Scale; _≤s_; _·_; e)

processOf
  : ∀ {ℓI ℓO ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    → Sch.Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output
    → Process {ℓO} {ℓC} {ℓQ} Output
processOf S =
  record
    { CP       = Sch.Scheme.CP S
    ; Step     = Sch.Scheme.Step S
    ; Norm     = Sch.Scheme.Norm S
    ; decode   = Sch.Scheme.decode S
    ; Q        = Sch.Scheme.Q S
    ; stepCost = Sch.Scheme.stepCost S
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
    ; Norm     = Process.Norm P
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
  open Process P₁ renaming (Con to Con₁; _⊑_ to _⊑₁_; Step to Step₁; normalize to norm₁; decode to decode₁)
  open Process P₂ renaming (Con to Con₂; _⊑_ to _⊑₂_; Step to Step₂; normalize to norm₂; decode to decode₂)
  field
    map     : Con₁ → Con₂
    mono    : ∀ {x y} → x ⊑₁ y → map x ⊑₂ map y
    step-comm : ∀ c → map (Step₁ c) ≡ Step₂ (map c)
    norm-comm : ∀ c → map (norm₁ c) ≡ norm₂ (map c)
    decode-comm : ∀ c → decode₂ (map c) ≡ decode₁ c

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

-- Budget transport primitives (no global “quantale laws” required):
-- we only need that step-costs commute on mapped states.

iterStep
  : ∀ {ℓO ℓC ℓQ} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
  → ℕ → Process.Con P → Process.Con P
iterStep P n c =
  iterate (record { Step = Process.Step P ; Halts = λ _ → Topℓ }) n c

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
iterStep-map {P₁ = P₁} {P₂ = P₂} h zero    _ = refl
iterStep-map {P₁ = P₁} {P₂ = P₂} h (suc n) c =
  LogOS.Prelude.trans
    (iterStep-map {P₁ = P₁} {P₂ = P₂} h n (Process.Step P₁ c))
    (cong (iterStep P₂ n) (ProcessHom.step-comm h c))

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
        (subst (λ Q → ScaleOps Q) (sym (ProcessHomCost.Q-comm hc)) Ops)
        (subst (λ Q → QAdapter.Scale Q) (sym (ProcessHomCost.Q-comm hc)) g)
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
      (Process.normalize P₂
        (run≤ P₂
          (subst (λ Q → ScaleOps Q) (sym (ProcessHomCost.Q-comm hc)) Ops)
          (subst (λ Q → QAdapter.Scale Q) (sym (ProcessHomCost.Q-comm hc)) g)
          (ProcessHom.map (ProcessHomCost.hom hc) c)))
    ≡ Process.decode P₁ (Process.normalize P₁ (run≤ P₁ Ops g c))
run≤-meaning-comm {P₁ = P₁} {P₂ = P₂}
  hc@(record { hom = h ; Q-comm = refl ; stepCost-comm = _ }) Ops g c =
  let
    open Process P₁ renaming (normalize to norm₁; decode to dec₁) hiding (refl; trans)
    open Process P₂ renaming (normalize to norm₂; decode to dec₂) hiding (refl; trans)
    r = run≤ P₁ Ops g c
  in
  LogOS.Prelude.trans
    (cong (λ x → dec₂ (norm₂ x)) (sym (run≤-map hc Ops g c)))
    (LogOS.Prelude.trans
      (cong dec₂ (sym (ProcessHom.norm-comm h r)))
      (ProcessHom.decode-comm h (norm₁ r)))

costExecP
  : ∀ {ℓO ℓC ℓQ} {Output : Set ℓO}
    (P : Process {ℓO} {ℓC} {ℓQ} Output)
  → ℕ → Process.Con P → QAdapter.Scale (Process.Q P)
costExecP P zero    c = QAdapter.e (Process.Q P)
costExecP P (suc n) c =
  QAdapter._·_ (Process.Q P) (Process.stepCost P c) (costExecP P n (Process.Step P c))

costExecP-map
  : ∀ {ℓO ℓC₁ ℓC₂ ℓQ} {Output : Set ℓO}
    {P₁ : Process {ℓO} {ℓC₁} {ℓQ} Output}
    {P₂ : Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : ProcessHomCost P₁ P₂)
  → ∀ n c
  → subst
      (λ Q → QAdapter.Scale Q)
      (ProcessHomCost.Q-comm hc)
      (costExecP P₂ n (ProcessHom.map (ProcessHomCost.hom hc) c))
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
-- `ComputesWithin-map` transports a full normalize+decode story.
-- Here we expose the lower-level operational layer:
-- - reachability after n steps, and
-- - the accumulated cost of those n steps within a budget.
--
-- This is the minimal abstraction needed to make “budgets are compositional”
-- visible across different presentations of the same process.
-- ==========================================================================

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
      (subst (λ Q → QAdapter.Scale Q) (sym (ProcessHomCost.Q-comm hc)) b)
      (ProcessHom.map (ProcessHomCost.hom hc) c')
ExecWithin-map {P₁ = P₁} {P₂ = P₂}
  (record { hom = h ; Q-comm = refl ; stepCost-comm = stepCostComm })
  C n c b c' (reach , cost≤) =
  reach₂ , cost≤₂
  where
    S₁ = schemeFromChoice P₁ C
    S₂ = schemeFromChoice P₂ (mapChoice h C)

    map = ProcessHom.map h
    step₁ = Sch.Scheme.Step S₁
    step₂ = Sch.Scheme.Step S₂

    iter-map
      : ∀ n c
      → map (iterate (Sch.Scheme.Comp S₁) n c)
        ≡ iterate (Sch.Scheme.Comp S₂) n (map c)
    iter-map zero    _ = refl
    iter-map (suc n) c =
      LogOS.Prelude.trans
        (iter-map n (step₁ c))
        (cong (iterate (Sch.Scheme.Comp S₂) n) (ProcessHom.step-comm h c))

    reach₂ : iterate (Sch.Scheme.Comp S₂) n (map c) ≡ map c'
    reach₂ =
      LogOS.Prelude.trans
        (sym (iter-map n c))
        (cong map reach)

    costExec-map
      : ∀ n c
      → Sch.Scheme.costExec S₂ n (map c)
        ≡ Sch.Scheme.costExec S₁ n c
    costExec-map zero    _ = refl
    costExec-map (suc n) c =
      LogOS.Prelude.trans
        (cong
          (λ sc →
            QAdapter._·_
              (Sch.Scheme.Q S₁)
              sc
              (Sch.Scheme.costExec S₂ n (step₂ (map c))))
          (stepCostComm c))
        (cong
          (λ z →
            QAdapter._·_
              (Sch.Scheme.Q S₁)
              (Sch.Scheme.stepCost S₁ c)
              z)
          (LogOS.Prelude.trans
            (cong (Sch.Scheme.costExec S₂ n) (sym (ProcessHom.step-comm h c)))
            (costExec-map n (step₁ c))))

    costEq : Sch.Scheme.costExec S₂ n (map c) ≡ Sch.Scheme.costExec S₁ n c
    costEq = costExec-map n c

    cost≤₂ : QAdapter._≤s_ (Sch.Scheme.Q S₂) (Sch.Scheme.costExec S₂ n (map c)) b
    cost≤₂ =
      subst
        (λ z → QAdapter._≤s_ (Sch.Scheme.Q S₂) z b)
        (sym costEq)
        cost≤

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
      (subst (λ Q → QAdapter.Scale Q) (sym (ProcessHomCost.Q-comm hc)) b)
      (ProcessHom.map (ProcessHomCost.hom hc) c')
ReachesWithin-map {P₁ = P₁} {P₂ = P₂}
  hc@(record { hom = h ; Q-comm = refl ; stepCost-comm = _ })
  C c b c' (n , ew) =
  n , ExecWithin-map hc C n c b c' ew

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
    subst (λ Q → QAdapter.Scale Q) (ProcessHomCost.Q-comm hc)
      (Sch.cost (schemeFromChoice P₂ (mapChoice (ProcessHomCost.hom hc) C)) x)
      ≡ Sch.cost (schemeFromChoice P₁ C) x
cost-comm {P₁ = P₁} {P₂ = P₂}
  (record { hom = h ; Q-comm = refl ; stepCost-comm = stepCostComm })
  C x =
  costEq
  where
    S₁ = schemeFromChoice P₁ C
    S₂ = schemeFromChoice P₂ (mapChoice h C)

    step₁ = Sch.Scheme.Step S₁
    step₂ = Sch.Scheme.Step S₂

    _·_ = QAdapter._·_ (Sch.Scheme.Q S₁)

    costExec-map
      : ∀ n c → Sch.Scheme.costExec S₂ n (ProcessHom.map h c) ≡ Sch.Scheme.costExec S₁ n c
    costExec-map zero    _ = refl
    costExec-map (suc n) c =
      trans
        (cong
          (λ sc → _·_ sc (Sch.Scheme.costExec S₂ n (step₂ (ProcessHom.map h c))))
          (stepCostComm c))
        (cong
          (λ z → _·_ (Sch.Scheme.stepCost S₁ c) z)
          (trans
            (cong (Sch.Scheme.costExec S₂ n) (sym (ProcessHom.step-comm h c)))
            (costExec-map n (step₁ c))))

    n : ℕ
    n = Choice.fuel C x

    c : Sch.Scheme.Con S₁
    c = Choice.compile C x

    costAtEq : Sch.Scheme.costAt S₂ n x ≡ Sch.Scheme.costAt S₁ n x
    costAtEq = costExec-map n c

    costEq : Sch.cost S₂ x ≡ Sch.cost S₁ x
    costEq = costAtEq

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
      (subst (λ Q → QAdapter.Scale Q) (sym (ProcessHomCost.Q-comm hc)) b)
      y
ComputesWithin-map {P₁ = P₁} {P₂ = P₂}
  hc@(record { hom = h ; Q-comm = refl ; stepCost-comm = stepCostComm })
  C x b y proof =
  go proof
  where
    S₁ = schemeFromChoice P₁ C
    S₂ = schemeFromChoice P₂ (mapChoice h C)

    go
      : Sch.Scheme.ComputesWithin S₁ x b y
      → Sch.Scheme.ComputesWithin S₂ x b y
    go (c' , (n , (reach , (halt₁ , cost≤))) , outEq) =
      c₂ , (n , (reach₂ , (halt₂ , cost≤₂))) , outEq₂
      where
        c₂ = ProcessHom.map h c'

        reach₂-cost≤₂
          : Sch.ExecWithin S₂ n (Sch.Scheme.compile S₂ x) b c₂
        reach₂-cost≤₂ =
          ExecWithin-map hc C n (Sch.Scheme.compile S₁ x) b c' (reach , cost≤)

        reach₂ : Sch.exec S₂ n x ≡ c₂
        reach₂ = fst reach₂-cost≤₂

        cost≤₂ : QAdapter._≤s_ (Sch.Scheme.Q S₂) (Sch.Scheme.costAt S₂ n x) b
        cost≤₂ = snd reach₂-cost≤₂

        halt₂ : Sch.Scheme.Step S₂ c₂ ≡ c₂
        halt₂ =
          trans
            (sym (ProcessHom.step-comm h c'))
            (cong (ProcessHom.map h) halt₁)

        outEq₂ : Sch.Scheme.decode S₂ (Sch.Scheme.normalize S₂ c₂) ≡ y
        outEq₂ =
          trans
            (cong (Sch.Scheme.decode S₂) (sym (ProcessHom.norm-comm h c')))
            (trans
              (ProcessHom.decode-comm h (Sch.Scheme.normalize S₁ c'))
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

        outEq₂ : Sch.Scheme.decode S₂ (Sch.Scheme.normalize S₂ c₂) ≡ y
        outEq₂ =
          trans
            (cong (Sch.Scheme.decode S₂) (sym (ProcessHom.norm-comm h c')))
            (trans
              (ProcessHom.decode-comm h (Sch.Scheme.normalize S₁ c'))
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

-- Semantics façade (textbook CS shape):
-- simulations are morphisms, and semantics is invariant under morphisms.
--
-- This groups the key “bite” lemmas in one predictable place.

module Semantics where
  Exec≤ = run≤
  Exec≤-natural = run≤-map
  Exec≤-stepsEq = run≤-stepsEq

  Meaning≤-natural = run≤-meaning-comm

  ExecWithin-natural = ExecWithin-map
  ReachesWithin-natural = ReachesWithin-map

  ComputesTo-natural = ComputesTo-map
  ComputesWithin-natural = ComputesWithin-map
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

    open Process P₁ renaming (Con to Con₁; Step to Step₁; normalize to norm₁; decode to decode₁) hiding (refl; trans)
    open Process P₂ renaming (Con to Con₂; Step to Step₂; normalize to norm₂; decode to decode₂) hiding (refl; trans)

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
