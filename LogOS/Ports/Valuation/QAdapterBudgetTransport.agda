{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.QAdapterBudgetTransport where

-- Algebraic strengthening of the numeric bus: graded/time budget transport.
--
-- The plain budget bus (`LogOS.Ports.Universality.Budget`, `.../BudgetBus2Cat.agda`)
-- only compares budget observations by refinement. This module strengthens the
-- story when the budget boundary comes from a `QAdapter`:
--
-- - every adapter/translation can carry an explicit *grade* (scale) or *time*
--   label, and
-- - grades compose by the `QAdapter` multiplication (time composes by `+` via a chosen `QClock` and τ),
-- - yielding explicit iteration bounds for endomaps.
--
-- This keeps the v1.1 kernel core unchanged: refinements remain observational (base `LOG`: boundary-driven `_⇒∂_`)
-- and independent of budgets.
--
-- Polarity note:
-- `_≤s_ a b` means the right-hand side is at least as permissive/strong as the
-- left-hand side. Budget bounds therefore read rightward: target observations
-- are bounded above by source observations multiplied by an explicit grade.
-- This module uses the actual quantitative order `_≤s_`; refinement-style
-- order notation such as `≼` is intentionally kept for non-quantitative
-- boundary refinement elsewhere in the library.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (_≈_; ≡→≈)
open import LogOS.LT.Kernel using (Kernel; Code)
open import LogOS.LT.Hom.Core using (KernelHom; idKernelHom; _∘_; mapCode)
open import LogOS.LT.Iteration using (traceCode)
open import LogOS.LT.Stage.SuccessorChain using (Stageω; zero; suc)
open import LogOS.Ports.CriticalParameter using (CriticalCut; SharpCut; principalCut; principalSharpCut)
open import LogOS.Ports.Universality.Budget using (BudgetPort; budgetReadout)
open import LogOS.Ports.Valuation.QAdapter using (QAdapter; QClock)
open import LogOS.Ports.Valuation.ScaleBoundary using (ScaleBoundary)
open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale; ScaleJoinPrequantale)
open import LogOS.Ports.Valuation.EngineeringDimension using (GradedTransport; pow; iterBound; idGradedTransport; composeGradedTransport)

-- Budget readout of code into the `QAdapter` scale.
budgetμ
  : ∀ {ℓCode ℓQ : Level}
    {Q : QAdapter ℓQ}
    {CodeType : Set ℓCode}
  → BudgetPort CodeType (ScaleBoundary Q)
  → CodeType → QAdapter.Scale Q
budgetμ BK γ = budgetReadout BK γ

-- --------------------------------------------------------------------------
-- Scale-graded transport (general; time-graded transport is a special case).

record QBudgetTransport
  {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
  (Q : QAdapter ℓQ)
  {K K' : Kernel ℓKernelCon ℓKernelRel ℓCode}
  (sourceBudget : BudgetPort (Code K) (ScaleBoundary Q))
  (targetBudget : BudgetPort (Code K') (ScaleBoundary Q))
  (translator : KernelHom K K')
  : Set (lsuc (ℓCode ⊔ ℓQ)) where
  field
    base
      : GradedTransport
          (ScaleJoinPrequantale Q)
          (budgetμ {Q = Q} sourceBudget)
          (budgetμ {Q = Q} targetBudget)
          (mapCode translator)

  open GradedTransport base public using (grade)
    renaming (graded to budget-graded)

open QBudgetTransport public

transportGradeCutLe
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
    {Q : QAdapter ℓQ}
    {K K' : Kernel ℓKernelCon ℓKernelRel ℓCode}
    {sourceBudget : BudgetPort (Code K) (ScaleBoundary Q)}
    {targetBudget : BudgetPort (Code K') (ScaleBoundary Q)}
    {translator : KernelHom K K'}
  → (Tg : QBudgetTransport Q sourceBudget targetBudget translator)
  → CriticalCut (ScaleBoundary Q)
      (λ observedGrade → QAdapter._≤s_ Q (grade Tg) observedGrade)
transportGradeCutLe {Q = Q} Tg =
  principalCut (ScaleBoundary Q) (grade Tg)

transportGradeSharpCutLe
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
    {Q : QAdapter ℓQ}
    {K K' : Kernel ℓKernelCon ℓKernelRel ℓCode}
    {sourceBudget : BudgetPort (Code K) (ScaleBoundary Q)}
    {targetBudget : BudgetPort (Code K') (ScaleBoundary Q)}
    {translator : KernelHom K K'}
  → (Tg : QBudgetTransport Q sourceBudget targetBudget translator)
  → SharpCut (ScaleBoundary Q)
      (λ observedGrade → QAdapter._≤s_ Q (grade Tg) observedGrade)
transportGradeSharpCutLe {Q = Q} Tg =
  principalSharpCut (ScaleBoundary Q) (grade Tg)

idQBudgetTransport
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
    (Q : QAdapter ℓQ)
    {K : Kernel ℓKernelCon ℓKernelRel ℓCode}
  → (BK : BudgetPort (Code K) (ScaleBoundary Q))
  → QBudgetTransport Q BK BK (idKernelHom K)
idQBudgetTransport Q BK =
  record
    { base = idGradedTransport (ScaleJoinPrequantale Q) (budgetμ {Q = Q} BK)
    }

composeQBudgetTransport
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
    (Q : QAdapter ℓQ)
    {K₁ K₂ K₃ : Kernel ℓKernelCon ℓKernelRel ℓCode}
    {f : KernelHom K₁ K₂}
    {g : KernelHom K₂ K₃}
    {BK₁ : BudgetPort (Code K₁) (ScaleBoundary Q)}
    {BK₂ : BudgetPort (Code K₂) (ScaleBoundary Q)}
    {BK₃ : BudgetPort (Code K₃) (ScaleBoundary Q)}
  → QBudgetTransport Q BK₁ BK₂ f
  → QBudgetTransport Q BK₂ BK₃ g
  → QBudgetTransport Q BK₁ BK₃ (g ∘ f)
composeQBudgetTransport Q {f = f} {g = g} {BK₁ = BK₁} {BK₂ = BK₂} {BK₃ = BK₃} tf tg =
  record
    { base = composeGradedTransport (ScaleJoinPrequantale Q) (base tf) (base tg)
    }

-- --------------------------------------------------------------------------
-- Time-graded transport (special case: grade = τ time).

record QTimeBudgetTransport
  {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
  (Q : QAdapter ℓQ)
  (T : QClock Q)
  {K K' : Kernel ℓKernelCon ℓKernelRel ℓCode}
  (sourceBudget : BudgetPort (Code K) (ScaleBoundary Q))
  (targetBudget : BudgetPort (Code K') (ScaleBoundary Q))
  (translator : KernelHom K K')
  : Set (lsuc (ℓCode ⊔ ℓQ)) where
  field
    time : QClock.Time T
    transport : QBudgetTransport Q sourceBudget targetBudget translator

  open QBudgetTransport transport public
    renaming (grade to transport-grade; budget-graded to budget-graded-base)

  field
    grade-is-time : transport-grade ≡ QClock.τ T time

  -- Direction note: the right side is stronger/entails the left
  -- (budget does not increase beyond the chosen time grade).
  budget-timed
    : (sourceCode : Code K)
    → QAdapter._≤s_ Q
        (budgetμ {Q = Q} targetBudget (mapCode translator sourceCode))
        (QAdapter._·_ Q (budgetμ {Q = Q} sourceBudget sourceCode) (QClock.τ T time))
  budget-timed sourceCode =
    QAdapter.≤s-trans Q
      (budget-graded-base sourceCode)
      (QAdapter.·-mono
        Q
        (QAdapter.≤s-refl Q {a = budgetμ {Q = Q} sourceBudget sourceCode})
        (fst (≡→≈ {CP = ScaleBoundary Q} grade-is-time)))

open QTimeBudgetTransport public

transportTimeGradeCutLe
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
    {Q : QAdapter ℓQ}
    (T : QClock Q)
    {K K' : Kernel ℓKernelCon ℓKernelRel ℓCode}
    {BK : BudgetPort (Code K) (ScaleBoundary Q)}
    {BK' : BudgetPort (Code K') (ScaleBoundary Q)}
    {h : KernelHom K K'}
  → (Tb : QTimeBudgetTransport Q T BK BK' h)
  → CriticalCut (ScaleBoundary Q)
      (λ observedGrade → QAdapter._≤s_ Q (transport-grade Tb) observedGrade)
transportTimeGradeCutLe {Q = Q} T Tb =
  principalCut (ScaleBoundary Q) (transport-grade Tb)

transportTimeGradeSharpCutLe
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
    {Q : QAdapter ℓQ}
    (T : QClock Q)
    {K K' : Kernel ℓKernelCon ℓKernelRel ℓCode}
    {BK : BudgetPort (Code K) (ScaleBoundary Q)}
    {BK' : BudgetPort (Code K') (ScaleBoundary Q)}
    {h : KernelHom K K'}
  → (Tb : QTimeBudgetTransport Q T BK BK' h)
  → SharpCut (ScaleBoundary Q)
      (λ observedGrade → QAdapter._≤s_ Q (transport-grade Tb) observedGrade)
transportTimeGradeSharpCutLe {Q = Q} T Tb =
  principalSharpCut (ScaleBoundary Q) (transport-grade Tb)

toGraded
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
    {Q : QAdapter ℓQ}
    (T : QClock Q)
    {K K' : Kernel ℓKernelCon ℓKernelRel ℓCode}
    {BK : BudgetPort (Code K) (ScaleBoundary Q)}
    {BK' : BudgetPort (Code K') (ScaleBoundary Q)}
    {h : KernelHom K K'}
  → QTimeBudgetTransport Q T BK BK' h
  → QBudgetTransport Q BK BK' h
toGraded {Q = Q} T Tb =
  transport Tb

idQTimeBudgetTransport
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
    (Q : QAdapter ℓQ)
    (T : QClock Q)
    {K : Kernel ℓKernelCon ℓKernelRel ℓCode}
  → (BK : BudgetPort (Code K) (ScaleBoundary Q))
  → QTimeBudgetTransport Q T BK BK (idKernelHom K)
idQTimeBudgetTransport Q T BK =
  record
    { time = QClock.zero T
    ; transport = idQBudgetTransport Q BK
    ; grade-is-time = sym (QClock.τ-zero T)
    }

assoc→
  : ∀ {ℓQ : Level} {Q : QAdapter ℓQ}
  → (a b c : QAdapter.Scale Q)
  → QAdapter._≤s_ Q
      (QAdapter._·_ Q (QAdapter._·_ Q a b) c)
      (QAdapter._·_ Q a (QAdapter._·_ Q b c))
assoc→ {Q = Q} a b c =
  fst (JoinPrequantale.·-assoc≈ (ScaleJoinPrequantale Q) a b c)

assoc←
  : ∀ {ℓQ : Level} {Q : QAdapter ℓQ}
  → (a b c : QAdapter.Scale Q)
  → QAdapter._≤s_ Q
      (QAdapter._·_ Q a (QAdapter._·_ Q b c))
      (QAdapter._·_ Q (QAdapter._·_ Q a b) c)
assoc← {Q = Q} a b c =
  snd (JoinPrequantale.·-assoc≈ (ScaleJoinPrequantale Q) a b c)

τ-+-≈
  : ∀ {ℓQ : Level} {Q : QAdapter ℓQ}
  → (T : QClock Q)
  → (t u : QClock.Time T)
  → _≈_ (ScaleBoundary Q)
      (QAdapter._·_ Q (QClock.τ T t) (QClock.τ T u))
      (QClock.τ T (QClock._+_ T t u))
τ-+-≈ {Q = Q} T t u =
  ≡→≈ {CP = ScaleBoundary Q} (sym (QClock.τ-+ T t u))

·-mono-left
  : ∀ {ℓQ : Level} {Q : QAdapter ℓQ}
    {a b c : QAdapter.Scale Q}
  → QAdapter._≤s_ Q a b
  → QAdapter._≤s_ Q
      (QAdapter._·_ Q a c)
      (QAdapter._·_ Q b c)
·-mono-left {Q = Q} {c = c} ab =
  QAdapter.·-mono Q ab (QAdapter.≤s-refl Q {a = c})

·-mono-right
  : ∀ {ℓQ : Level} {Q : QAdapter ℓQ}
    {a b c : QAdapter.Scale Q}
  → QAdapter._≤s_ Q b c
  → QAdapter._≤s_ Q
      (QAdapter._·_ Q a b)
      (QAdapter._·_ Q a c)
·-mono-right {Q = Q} {a = a} bc =
  QAdapter.·-mono Q (QAdapter.≤s-refl Q {a = a}) bc

time-grade-compose≤
  : ∀ {ℓQ : Level} {Q : QAdapter ℓQ}
  → (T : QClock Q)
  → (a : QAdapter.Scale Q)
  → (t u : QClock.Time T)
  → QAdapter._≤s_ Q
      (QAdapter._·_ Q (QAdapter._·_ Q a (QClock.τ T t)) (QClock.τ T u))
      (QAdapter._·_ Q a (QClock.τ T (QClock._+_ T t u)))
time-grade-compose≤ {Q = Q} T a t u =
  QAdapter.≤s-trans Q
    (assoc→ {Q = Q} a (QClock.τ T t) (QClock.τ T u))
    (·-mono-right {Q = Q} {a = a} (fst (τ-+-≈ T t u)))

composeQTimeBudgetTransport
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
    (Q : QAdapter ℓQ)
    (T : QClock Q)
    {K₁ K₂ K₃ : Kernel ℓKernelCon ℓKernelRel ℓCode}
    {f : KernelHom K₁ K₂}
    {g : KernelHom K₂ K₃}
    {BK₁ : BudgetPort (Code K₁) (ScaleBoundary Q)}
    {BK₂ : BudgetPort (Code K₂) (ScaleBoundary Q)}
    {BK₃ : BudgetPort (Code K₃) (ScaleBoundary Q)}
  → QTimeBudgetTransport Q T BK₁ BK₂ f
  → QTimeBudgetTransport Q T BK₂ BK₃ g
  → QTimeBudgetTransport Q T BK₁ BK₃ (g ∘ f)
composeQTimeBudgetTransport Q T tf tg =
  record
    { time = QClock._+_ T (time tf) (time tg)
    ; transport = composeQBudgetTransport Q (transport tf) (transport tg)
    ; grade-is-time = grade-is-time-comp
    }
  where
    open QAdapter Q
    open QClock T

    grade-is-time-comp
      : QBudgetTransport.grade (composeQBudgetTransport Q (transport tf) (transport tg))
          ≡ τ (QClock._+_ T (time tf) (time tg))
    grade-is-time-comp =
      trans
        (cong (λ u → _·_ u (transport-grade tg)) (grade-is-time tf))
        (trans
          (cong (λ u → _·_ (τ (time tf)) u) (grade-is-time tg))
          (sym (τ-+ (time tf) (time tg))))

-- --------------------------------------------------------------------------
-- Iteration bounds (endomaps).

-- n-fold time addition (prepend: first step happens first).
timeIter-prepend
  : ∀ {ℓQ : Level} {Q : QAdapter ℓQ}
  → (T : QClock Q)
  → QClock.Time T → Stageω → QClock.Time T
timeIter-prepend {Q = Q} T t zero = QClock.zero T
timeIter-prepend {Q = Q} T t (suc n) =
  QClock._+_ T t (timeIter-prepend {Q = Q} T t n)

timeIter
  : ∀ {ℓQ : Level} {Q : QAdapter ℓQ}
  → (T : QClock Q)
  → QClock.Time T → Stageω → QClock.Time T
timeIter = timeIter-prepend

pow-τ-timeIter
  : ∀ {ℓQ : Level} {Q : QAdapter ℓQ}
  → (T : QClock Q)
  → (t : QClock.Time T)
  → (n : Stageω)
  → pow (ScaleJoinPrequantale Q) (QClock.τ T t) n
    ≡ QClock.τ T (timeIter-prepend {Q = Q} T t n)
pow-τ-timeIter {Q = Q} T t zero =
  sym (QClock.τ-zero T)
pow-τ-timeIter {Q = Q} T t (suc n) =
  trans
    (cong (λ u → QAdapter._·_ Q (QClock.τ T t) u) (pow-τ-timeIter {Q = Q} T t n))
    (sym (QClock.τ-+ T t (timeIter-prepend {Q = Q} T t n)))

traceBudget≤
  : ∀ {ℓKernelCon ℓKernelRel ℓCode ℓQ : Level}
    {Q : QAdapter ℓQ}
    (T : QClock Q)
    {K : Kernel ℓKernelCon ℓKernelRel ℓCode}
    {BK : BudgetPort (Code K) (ScaleBoundary Q)}
    (f : KernelHom K K)
  → (Tf : QTimeBudgetTransport Q T BK BK f)
  → (n : Stageω)
  → (γ : Code K)
  → QAdapter._≤s_ Q
      (budgetμ {Q = Q} BK (traceCode f n γ))
      (QAdapter._·_ Q (budgetμ {Q = Q} BK γ) (QClock.τ T (timeIter-prepend {Q = Q} T (time Tf) n)))
traceBudget≤ {Q = Q} T {BK = BK} f Tf n γ =
  QAdapter.≤s-trans Q baseBound transport-step
  where
    Tb : QBudgetTransport Q BK BK f
    Tb = toGraded {Q = Q} T Tf

    baseBound
      : QAdapter._≤s_ Q
          (budgetμ {Q = Q} BK (traceCode f n γ))
          (QAdapter._·_ Q (budgetμ {Q = Q} BK γ) (pow (ScaleJoinPrequantale Q) (grade Tb) n))
    baseBound =
      iterBound
        (ScaleJoinPrequantale Q)
        {obs = budgetμ {Q = Q} BK}
        {f = mapCode f}
        (base Tb)
        n
        γ

    pow-grade-is-time
      : pow (ScaleJoinPrequantale Q) (grade Tb) n
          ≡ QClock.τ T (timeIter-prepend {Q = Q} T (time Tf) n)
    pow-grade-is-time =
      trans
        (cong (λ g → pow (ScaleJoinPrequantale Q) g n) (grade-is-time Tf))
        (pow-τ-timeIter {Q = Q} T (time Tf) n)

    transport-step
      : QAdapter._≤s_ Q
          (QAdapter._·_ Q (budgetμ {Q = Q} BK γ) (pow (ScaleJoinPrequantale Q) (grade Tb) n))
          (QAdapter._·_ Q (budgetμ {Q = Q} BK γ) (QClock.τ T (timeIter-prepend {Q = Q} T (time Tf) n)))
    transport-step =
      ·-mono-right {Q = Q} {a = budgetμ {Q = Q} BK γ}
        (fst (≡→≈ {CP = ScaleBoundary Q} pow-grade-is-time))
