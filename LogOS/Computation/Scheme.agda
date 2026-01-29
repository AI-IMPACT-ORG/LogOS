{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.Scheme where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro; to; from; ↔-refl; ↔-sym; ↔-trans)

open import LogOS.Computation.Core using (iterate; iterate-+; Computation)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; _≈CP_)
open import LogOS.Minimal.Closure public renaming (ClosureOp to Closure)
open import LogOS.Minimal.ScaleOps using (ScaleOps; BudgetOps)
open import LogOS.Prelude.Product using (_×_; _,_; fst; snd)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; z≤n; s≤s; total≤ℕ)

-- A “computation scheme” packages:
-- - a concrete representation (Code + compiler),
-- - a dynamics (Step),
-- - a closure operator (Close),
-- - an observation/meaning extractor (decode),
-- - and a quantale-valued step cost profile (QAdapter + stepCost).
--
-- This is designed so that different paradigms (Turing/Minsky, Church/λ, EVM,
-- quantum, …) become different *scheme choices* that can be compared:
-- same meaning via `run`, different resource profiles via `cost`.

record Scheme {ℓI ℓO ℓC ℓQ : Level}
              (Input  : Set ℓI)
              (Output : Set ℓO)
              : Set (lsuc (ℓI ⊔ ℓO ⊔ ℓC ⊔ ℓQ)) where
  field
    CP      : ConPreorder ℓC
    Step    : ConPreorder.Con CP → ConPreorder.Con CP
    Close    : Closure CP

    compile : Input → ConPreorder.Con CP
    fuel    : Input → ℕ
    decode  : ConPreorder.Con CP → Output

    Q       : QAdapter ℓQ
    stepCost : ConPreorder.Con CP → QAdapter.Scale Q

  open ConPreorder CP public using (Con; _⊑_; refl; trans)
  open Closure Close public renaming
    ( cl        to close
    ; mono      to close-mono
    ; infl      to close-infl
    ; idemp-lax to close-idemp-lax
    )
  open QAdapter Q public using (Scale; _≤s_; _⊔s_; ⊥s; _·_; e)

  Comp : Computation Con
  Comp = record { Step = Step ; Halts = λ _ → Topℓ }

  exec : ℕ → Input → Con
  exec n x = iterate Comp n (compile x)

  toClosedAt : ℕ → Input → Con
  toClosedAt n x = close (exec n x)

  run : Input → Output
  run x = decode (toClosedAt (fuel x) x)

  -- Grade-indexed execution: interpret a scale value as a step budget using `ScaleOps`.
  --
  -- This is the intended “machines are schemes” bridge: the scheme index is a
  -- grade in `Scale`, and `ScaleOps` turns it into an operational number of
  -- small-step iterations.
  run≤ : ScaleOps Q → Scale → Input → Output
  run≤ Ops b x =
    decode (close (exec (ScaleOps.steps Ops (ScaleOps.budget Ops b)) x))

  run≤ᵇ : BudgetOps Q → Scale → Input → Output
  run≤ᵇ Ops = run≤ (BudgetOps.Ops Ops)

  costExec : ℕ → Con → Scale
  costExec zero    c = e
  costExec (suc n) c = stepCost c · costExec n (Step c)

  costAt : ℕ → Input → Scale
  costAt n x = costExec n (compile x)

  cost : Input → Scale
  cost x = costAt (fuel x) x

  -- ==========================================================================
  -- Fuel-free semantics (Plan B upgrade)
  --
  -- The `run` function uses the scheme's chosen fuel bound. For universality,
  -- portability, and “many representations of the same computation”, it's often
  -- cleaner to define computation as:
  --
  --   “there exists some number of steps after which the state is stable, and
  --    the observed/decoded normal form is the answer”.
  --
  -- This keeps the notion of computation independent of any particular machine
  -- model; different paradigms are then just different `Scheme` choices.
  -- ==========================================================================

  -- Definitional halting: the stepper is literally stuck.
  --
  -- This is a strong notion (too strong for quotient-y state models).
  halts≡ : Con → Set ℓC
  halts≡ c = Step c ≡ c

  -- Observational halting (preorder-level): the next step is indistinguishable
  -- from the current state up to mutual refinement.
  --
  -- This is the right notion for quotient-y state models, where `Step c` may not
  -- be judgmentally equal to `c` but is still observationally stable.
  halts : Con → Set ℓC
  halts c = _≈CP_ CP (Step c) c

  halts≡→halts : ∀ {c} → halts≡ c → halts c
  halts≡→halts {c} eq rewrite eq = (ConPreorder.refl CP , ConPreorder.refl CP)

  NormalizesTo : Con → Con → Set ℓC
  NormalizesTo c c' = Σ ℕ (λ n → iterate Comp n c ≡ c' × halts≡ c')

  ComputesTo : Input → Output → Set (ℓC ⊔ ℓO)
  ComputesTo x y =
    Σ Con (λ c' → NormalizesTo (compile x) c' × decode (close c') ≡ y)

  -- Observational (preorder) variant: keep the same reachability witness, but
  -- weaken halting from judgmental equality to mutual refinement.

  NormalizesTo≈ : Con → Con → Set ℓC
  NormalizesTo≈ c c' = Σ ℕ (λ n → iterate Comp n c ≡ c' × halts c')

  NormalizesTo→NormalizesTo≈ : ∀ {c c'} → NormalizesTo c c' → NormalizesTo≈ c c'
  NormalizesTo→NormalizesTo≈ (n , (reach , halt)) =
    n , (reach , halts≡→halts halt)

  ComputesTo≈ : Input → Output → Set (ℓC ⊔ ℓO)
  ComputesTo≈ x y =
    Σ Con (λ c' → NormalizesTo≈ (compile x) c' × decode (close c') ≡ y)

  ComputesTo→ComputesTo≈ : ∀ {x y} → ComputesTo x y → ComputesTo≈ x y
  ComputesTo→ComputesTo≈ (c' , (norm , out≡)) =
    c' , (NormalizesTo→NormalizesTo≈ norm , out≡)

  -- Closure-stable semantics: a computation is witnessed by some number of
  -- steps after which the *closed* state is step-stable (up to ≈).
  --
  -- This is strictly weaker than `ComputesTo`/`ComputesTo≈` because it does not
  -- require the raw execution state to be stable.

  StabilizesTo : Input → Output → Set (ℓC ⊔ ℓO)
  StabilizesTo x y =
    Σ ℕ (λ n → decode (toClosedAt n x) ≡ y × halts (toClosedAt n x))

  StabilizesWithin : Input → Scale → Output → Set (ℓC ⊔ ℓO ⊔ ℓQ)
  StabilizesWithin x b y =
    Σ ℕ (λ n → decode (toClosedAt n x) ≡ y × halts (toClosedAt n x) × costAt n x ≤s b)

  -- Optional strengthening: connect `Close` and `Step`.
  --
  -- Minimal law: the closure produces step-stable states (up to ≈).

  record SchemeLaws : Set (lsuc ℓC) where
    field
      close-halts : ∀ c → halts (close c)

  toClosedAt-halts : SchemeLaws → ∀ n x → halts (toClosedAt n x)
  toClosedAt-halts laws n x = SchemeLaws.close-halts laws (exec n x)

  runIsStabilizesTo : SchemeLaws → ∀ x → StabilizesTo x (run x)
  runIsStabilizesTo laws x =
    fuel x , (LogOS.Prelude.refl , toClosedAt-halts laws (fuel x) x)

  runIsStabilizesWithinCost
    : SchemeLaws → ∀ x → StabilizesWithin x (cost x) (run x)
  runIsStabilizesWithinCost laws x =
    fuel x
    , (LogOS.Prelude.refl , (toClosedAt-halts laws (fuel x) x , QAdapter.≤s-refl Q))

  runIsStabilizesWithin
    : SchemeLaws → ∀ x b → cost x ≤s b → StabilizesWithin x b (run x)
  runIsStabilizesWithin laws x b cost≤ =
    fuel x , (LogOS.Prelude.refl , (toClosedAt-halts laws (fuel x) x , cost≤))

  -- Cost/budgeted variant: compute within a quantale budget.
  --
  -- For `QNat`, budgets are step/gas counts; for other adapters, budgets live in
  -- the adapter's `Scale`.

  NormalizesTo≤ : Scale → Con → Con → Set (ℓC ⊔ ℓQ)
  NormalizesTo≤ b c c' =
    Σ ℕ (λ n → iterate Comp n c ≡ c' × halts≡ c' × costExec n c ≤s b)

  ComputesWithin : Input → Scale → Output → Set (ℓC ⊔ ℓO ⊔ ℓQ)
  ComputesWithin x b y =
    Σ Con (λ c' → NormalizesTo≤ b (compile x) c' × decode (close c') ≡ y)

  -- Unbudgeted semantics is exactly “there exists some budget”.
  --
  -- This is the Join/colimit view of resource-indexed computation: finite
  -- executions produce a concrete cost witness, and budgeted executions can be
  -- forgotten.

  NormalizesTo≤→NormalizesTo
    : ∀ {b c c'} → NormalizesTo≤ b c c' → NormalizesTo c c'
  NormalizesTo≤→NormalizesTo (n , (reach , (halt , _))) = n , (reach , halt)

  NormalizesTo→∃NormalizesTo≤
    : ∀ {c c'} → NormalizesTo c c' → Σ Scale (λ b → NormalizesTo≤ b c c')
  NormalizesTo→∃NormalizesTo≤ {c = c} (n , (reach , halt)) =
    costExec n c , (n , (reach , (halt , QAdapter.≤s-refl Q)))

  NormalizesTo↔∃NormalizesTo≤
    : ∀ {c c'} → NormalizesTo c c' ↔ Σ Scale (λ b → NormalizesTo≤ b c c')
  NormalizesTo↔∃NormalizesTo≤ =
    record
      { to   = NormalizesTo→∃NormalizesTo≤
      ; from = λ ex → NormalizesTo≤→NormalizesTo (proj₂ ex)
      }

  ComputesWithin→ComputesTo
    : ∀ {x b y} → ComputesWithin x b y → ComputesTo x y
  ComputesWithin→ComputesTo (c' , (norm≤ , out≡)) =
    c' , (NormalizesTo≤→NormalizesTo norm≤ , out≡)

  ComputesTo→∃ComputesWithin
    : ∀ {x y} → ComputesTo x y → Σ Scale (λ b → ComputesWithin x b y)
  ComputesTo→∃ComputesWithin {x = x} (c' , (n , (reach , halt)) , out≡) =
    costExec n (compile x)
    , (c' , ((n , (reach , (halt , QAdapter.≤s-refl Q))) , out≡))

  ComputesTo↔∃ComputesWithin
    : ∀ {x y} → ComputesTo x y ↔ Σ Scale (λ b → ComputesWithin x b y)
  ComputesTo↔∃ComputesWithin =
    record
      { to   = ComputesTo→∃ComputesWithin
      ; from = λ ex → ComputesWithin→ComputesTo (proj₂ ex)
      }

  -- ==========================================================================
  -- Budget algebra (quantale-facing)
  --
  -- These lemmas make the finite-join structure operational for schemes:
  -- budgets can be weakened along `_≤s_` and combined via join (`_⊔s_`).
  -- ==========================================================================

  NormalizesTo≤-mono
    : ∀ {b b' c c'}
      → b ≤s b'
      → NormalizesTo≤ b c c'
      → NormalizesTo≤ b' c c'
  NormalizesTo≤-mono le (n , (reach , (halt , cost≤))) =
    n , (reach , (halt , QAdapter.≤s-trans Q cost≤ le))

  ComputesWithin-mono
    : ∀ {x b b' y}
      → b ≤s b'
      → ComputesWithin x b y
      → ComputesWithin x b' y
  ComputesWithin-mono le (c' , (norm≤ , out≡)) =
    c' , (NormalizesTo≤-mono le norm≤ , out≡)

  ComputesWithin-⊔s₁
    : ∀ {x b b' y}
      → ComputesWithin x b y
      → ComputesWithin x (b ⊔s b') y
  ComputesWithin-⊔s₁ {b = b} {b' = b'} =
    ComputesWithin-mono (QAdapter.⊔s-ub₁ Q b b')

  ComputesWithin-⊔s₂
    : ∀ {x b b' y}
      → ComputesWithin x b' y
      → ComputesWithin x (b ⊔s b') y
  ComputesWithin-⊔s₂ {b = b} {b' = b'} =
    ComputesWithin-mono (QAdapter.⊔s-ub₂ Q b b')

  ComputesWithin-⊔s
    : ∀ {x b b' y}
      → (ComputesWithin x b y) ⊎ (ComputesWithin x b' y)
      → ComputesWithin x (b ⊔s b') y
  ComputesWithin-⊔s (inj₁ p) = ComputesWithin-⊔s₁ p
  ComputesWithin-⊔s (inj₂ p) = ComputesWithin-⊔s₂ p

  -- ==========================================================================
  -- Cost decomposition (sequential composition)
  --
  -- This is a purely algebraic fact about `costExec` as a monoid fold.
  -- It does not assume any monotonicity of `_·_` w.r.t. `_≤s_`.
  -- ==========================================================================

  costExec-+
    : ∀ m n c
      → costExec (m + n) c
        ≡ (costExec m c · costExec n (iterate Comp m c))
  costExec-+ zero    n c =
    sym (QAdapter.·-idl Q (costExec n c))
  costExec-+ (suc m) n c =
    let
      a = stepCost c
      b = costExec m (Step c)
      d = costExec n (iterate Comp m (Step c))
    in
    LogOS.Prelude.trans
      (cong (λ z → a · z) (costExec-+ m n (Step c)))
      (sym (QAdapter.·-assoc Q a b d))

  -- ==========================================================================
  -- Quantale-graded execution (new: uses `·-mono`)
  --
  -- The key new capability after upgrading `QAdapter` with monotone
  -- multiplication: budgeted executions compose.
  -- ==========================================================================

  ExecWithin : ℕ → Con → Scale → Con → Set (ℓC ⊔ ℓQ)
  ExecWithin n c b c' = iterate Comp n c ≡ c' × costExec n c ≤s b

  ExecWithin-mono
    : ∀ {n c b b' c'}
      → b ≤s b'
      → ExecWithin n c b c'
      → ExecWithin n c b' c'
  ExecWithin-mono le (reach , cost≤) =
    reach , QAdapter.≤s-trans Q cost≤ le

  costExec-+≤
    : ∀ {m n c b d}
      → costExec m c ≤s b
      → costExec n (iterate Comp m c) ≤s d
      → costExec (m + n) c ≤s (b · d)
  costExec-+≤ {m = m} {n = n} {c = c} {b = b} {d = d} costm costn =
    subst (λ z → z ≤s (b · d)) (sym (costExec-+ m n c))
      (QAdapter.·-mono Q costm costn)

  ExecWithin-+
    : ∀ {m n c c₁ c₂ b d}
      → ExecWithin m c b c₁
      → ExecWithin n c₁ d c₂
      → ExecWithin (m + n) c (b · d) c₂
  ExecWithin-+ {m = m} {n = n} {c = c} {c₁ = c₁} {c₂ = c₂} {b = b} {d = d}
               (reach₁ , cost₁) (reach₂ , cost₂) =
    reach , costExec-+≤ {m = m} {n = n} {c = c} {b = b} {d = d} cost₁ cost₂'
    where
      reach : iterate Comp (m + n) c ≡ c₂
      reach =
        LogOS.Prelude.trans
          (iterate-+ Comp m n c)
          (LogOS.Prelude.trans (cong (iterate Comp n) reach₁) reach₂)

      cost₂' : costExec n (iterate Comp m c) ≤s d
      cost₂' =
        subst (λ z → costExec n z ≤s d) (sym reach₁) cost₂

  ReachesWithin : Con → Scale → Con → Set (ℓC ⊔ ℓQ)
  ReachesWithin c b c' = Σ ℕ (λ n → ExecWithin n c b c')

  ReachesWithin-refl : ∀ c → ReachesWithin c e c
  ReachesWithin-refl c = zero , (LogOS.Prelude.refl , QAdapter.≤s-refl Q)

  ReachesWithin-trans
    : ∀ {c c₁ c₂ b d}
      → ReachesWithin c b c₁
      → ReachesWithin c₁ d c₂
      → ReachesWithin c (b · d) c₂
  ReachesWithin-trans (m , ew₁) (n , ew₂) =
    (m + n) , ExecWithin-+ {m = m} {n = n} ew₁ ew₂

-- ==========================================================================
-- Observational equality (semantics is the set of possible outputs)
--
-- This is the standard “same computation” notion in a setting where
-- computation is defined relationally (big-step / normalization style).
-- It is intentionally independent of any particular evaluation schedule.
-- ==========================================================================

ObsEq
  : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
    {Input : Set ℓI} {Output : Set ℓO}
  → Scheme {ℓI} {ℓO} {ℓC₁} {ℓQ₁} Input Output
  → Scheme {ℓI} {ℓO} {ℓC₂} {ℓQ₂} Input Output
  → Set (ℓI ⊔ ℓO ⊔ ℓC₁ ⊔ ℓC₂)
ObsEq S T =
  ∀ x y →
    (Scheme.ComputesTo S x y → Scheme.ComputesTo T x y)
  × (Scheme.ComputesTo T x y → Scheme.ComputesTo S x y)

-- A more `LogOS.Syntax.Prop`-aligned presentation: observational equality as
-- pointwise logical equivalence (`↔`) of the computed-output relation.

ObsEq↔
  : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
    {Input : Set ℓI} {Output : Set ℓO}
  → Scheme {ℓI} {ℓO} {ℓC₁} {ℓQ₁} Input Output
  → Scheme {ℓI} {ℓO} {ℓC₂} {ℓQ₂} Input Output
  → Set (ℓI ⊔ ℓO ⊔ ℓC₁ ⊔ ℓC₂)
ObsEq↔ S T = ∀ x y → Scheme.ComputesTo S x y ↔ Scheme.ComputesTo T x y

abstract
  ObsEq↔-refl
    : ∀ {ℓI ℓO ℓC ℓQ}
      {Input : Set ℓI} {Output : Set ℓO}
      (S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output)
    → ObsEq↔ S S
  ObsEq↔-refl S x y = ↔-refl

  ObsEq↔-sym
    : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
      {Input : Set ℓI} {Output : Set ℓO}
      {S : Scheme {ℓI} {ℓO} {ℓC₁} {ℓQ₁} Input Output}
      {T : Scheme {ℓI} {ℓO} {ℓC₂} {ℓQ₂} Input Output}
    → ObsEq↔ S T → ObsEq↔ T S
  ObsEq↔-sym eq x y = ↔-sym (eq x y)

  ObsEq↔-trans
    : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂ ℓC₃ ℓQ₃}
      {Input : Set ℓI} {Output : Set ℓO}
      {S : Scheme {ℓI} {ℓO} {ℓC₁} {ℓQ₁} Input Output}
      {T : Scheme {ℓI} {ℓO} {ℓC₂} {ℓQ₂} Input Output}
      {U : Scheme {ℓI} {ℓO} {ℓC₃} {ℓQ₃} Input Output}
    → ObsEq↔ S T → ObsEq↔ T U → ObsEq↔ S U
  ObsEq↔-trans eST eTU x y = ↔-trans (eST x y) (eTU x y)

  ObsEq→ObsEq↔
    : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
      {Input : Set ℓI} {Output : Set ℓO}
      {S : Scheme {ℓI} {ℓO} {ℓC₁} {ℓQ₁} Input Output}
      {T : Scheme {ℓI} {ℓO} {ℓC₂} {ℓQ₂} Input Output}
    → ObsEq S T → ObsEq↔ S T
  ObsEq→ObsEq↔ eq x y = intro (fst (eq x y)) (snd (eq x y))

  ObsEq↔→ObsEq
    : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
      {Input : Set ℓI} {Output : Set ℓO}
      {S : Scheme {ℓI} {ℓO} {ℓC₁} {ℓQ₁} Input Output}
      {T : Scheme {ℓI} {ℓO} {ℓC₂} {ℓQ₂} Input Output}
    → ObsEq↔ S T → ObsEq S T
  ObsEq↔→ObsEq eq x y = to (eq x y) , from (eq x y)

  ObsEq-refl
    : ∀ {ℓI ℓO ℓC ℓQ}
      {Input : Set ℓI} {Output : Set ℓO}
      (S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output)
    → ObsEq S S
  ObsEq-refl S x y = (λ c → c) , (λ c → c)

  ObsEq-sym
    : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
      {Input : Set ℓI} {Output : Set ℓO}
      {S : Scheme {ℓI} {ℓO} {ℓC₁} {ℓQ₁} Input Output}
      {T : Scheme {ℓI} {ℓO} {ℓC₂} {ℓQ₂} Input Output}
    → ObsEq S T → ObsEq T S
  ObsEq-sym eq x y = snd (eq x y) , fst (eq x y)

  ObsEq-trans
    : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂ ℓC₃ ℓQ₃}
      {Input : Set ℓI} {Output : Set ℓO}
      {S : Scheme {ℓI} {ℓO} {ℓC₁} {ℓQ₁} Input Output}
      {T : Scheme {ℓI} {ℓO} {ℓC₂} {ℓQ₂} Input Output}
      {U : Scheme {ℓI} {ℓO} {ℓC₃} {ℓQ₃} Input Output}
    → ObsEq S T → ObsEq T U → ObsEq S U
  ObsEq-trans eST eTU x y =
    (λ c → fst (eTU x y) (fst (eST x y) c))
    , (λ c → snd (eST x y) (snd (eTU x y) c))

-- A tighter, executable observational equality:
-- two schemes are equivalent iff they compute the same observed output under
-- their chosen (possibly representation-specific) fuel schedule.
--
-- This matches the common “same function” notion used in mechanized compiler
-- correctness arguments and is the most convenient equivalence for
-- example-driven universality claims.

RunEq
  : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
    {Input : Set ℓI} {Output : Set ℓO}
  → Scheme {ℓI} {ℓO} {ℓC₁} {ℓQ₁} Input Output
  → Scheme {ℓI} {ℓO} {ℓC₂} {ℓQ₂} Input Output
  → Set (ℓI ⊔ ℓO)
RunEq S T = ∀ x → Scheme.run S x ≡ Scheme.run T x

RunEq-refl
  : ∀ {ℓI ℓO ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    (S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output)
  → RunEq S S
RunEq-refl _ _ = refl

RunEq-sym
  : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
    {Input : Set ℓI} {Output : Set ℓO}
    {S : Scheme {ℓI} {ℓO} {ℓC₁} {ℓQ₁} Input Output}
    {T : Scheme {ℓI} {ℓO} {ℓC₂} {ℓQ₂} Input Output}
  → RunEq S T → RunEq T S
RunEq-sym eq x = sym (eq x)

RunEq-trans
  : ∀ {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂ ℓC₃ ℓQ₃}
    {Input : Set ℓI} {Output : Set ℓO}
    {S : Scheme {ℓI} {ℓO} {ℓC₁} {ℓQ₁} Input Output}
    {T : Scheme {ℓI} {ℓO} {ℓC₂} {ℓQ₂} Input Output}
    {U : Scheme {ℓI} {ℓO} {ℓC₃} {ℓQ₃} Input Output}
  → RunEq S T → RunEq T U → RunEq S U
RunEq-trans eST eTU x = trans (eST x) (eTU x)

-- ==========================================================================
-- Bridging relational semantics ↔ chosen schedule semantics
--
-- A common source of confusion is mixing:
-- - fuel-free semantics: `ComputesTo` / `ComputesWithin` (existential runs), and
-- - schedule semantics: `run` (a chosen fuel/schedule for each input).
--
-- The pack below makes the relationship explicit:
-- if the chosen schedule reaches a fixed point (halts), then:
--   (1) `run` is sound w.r.t. `ComputesTo`, and
--   (2) `ComputesTo` collapses to the unique output `run` produces.
--
-- Under the same assumption on both sides, `RunEq` and `ObsEq` coincide.
-- ==========================================================================

FuelHalts
  : ∀ {ℓI ℓO ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
  → Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output
  → Set (ℓI ⊔ ℓC)
FuelHalts S = ∀ x → Scheme.halts≡ S (Scheme.exec S (Scheme.fuel S x) x)

module FuelSound {ℓI ℓO ℓC ℓQ}
                 {Input : Set ℓI} {Output : Set ℓO}
                 (S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output)
                 where
  open Scheme S hiding (refl; trans)

  stableFrom≤
    : ∀ {m n c}
      → m ≤ℕ n
      → halts≡ (iterate Comp m c)
      → iterate Comp n c ≡ iterate Comp m c
  stableFrom≤ {n = n} {c = c} z≤n halt0 = stable0 n c halt0
    where
      stable0 : ∀ n c → halts≡ c → iterate Comp n c ≡ c
      stable0 zero    _ _ = refl
      stable0 (suc n) c hc =
        trans
          (stable0 n (Step c) (cong Step hc))
          hc
  stableFrom≤ {c = c} (s≤s le) haltSm =
    stableFrom≤ {c = Step c} le haltSm

  fixedpoint-unique
    : ∀ m n c
      → halts≡ (iterate Comp m c)
      → halts≡ (iterate Comp n c)
      → iterate Comp m c ≡ iterate Comp n c
  fixedpoint-unique m n c hm hn with total≤ℕ m n
  ... | inj₁ m≤n = sym (stableFrom≤ m≤n hm)
  ... | inj₂ n≤m = stableFrom≤ n≤m hn

  runIsComputesTo : FuelHalts S → ∀ x → ComputesTo x (run x)
  runIsComputesTo fh x =
    c' , (n , (refl , halt')) , refl
    where
      n  = fuel x
      c' = exec n x
      halt' = fh x

  -- `run` is budget-sound for its own observed cost.
  --
  -- This is the “cost honesty produces an actual certificate” lemma:
  -- if the chosen fuel schedule halts, then the schedule output is also
  -- witnessed as a `ComputesWithin` computation at budget `cost x`.

  runIsComputesWithinCost
    : FuelHalts S → ∀ x → ComputesWithin x (cost x) (run x)
  runIsComputesWithinCost fh x =
    c' , ((n , (refl , (halt' , QAdapter.≤s-refl Q))) , refl)
    where
      n  = fuel x
      c' = exec n x
      halt' = fh x

  -- If you can bound the observed cost of the chosen schedule by some budget,
  -- you automatically get a `ComputesWithin` witness at that budget.

  runIsComputesWithin
    : FuelHalts S → ∀ x b → cost x ≤s b → ComputesWithin x b (run x)
  runIsComputesWithin fh x b cost≤ =
    ComputesWithin-mono cost≤ (runIsComputesWithinCost fh x)

  computesTo→run : FuelHalts S → ∀ x y → ComputesTo x y → y ≡ run x
  computesTo→run fh x y (c' , (n , (reach , haltC')) , outEq) =
    trans (sym outEq) (cong (λ c → decode (close c)) (sym eqFC))
    where
      c0 = compile x
      f  = fuel x

      haltN : halts≡ (iterate Comp n c0)
      haltN = subst halts≡ (sym reach) haltC'

      haltF : halts≡ (iterate Comp f c0)
      haltF = fh x

      eqFC : iterate Comp f c0 ≡ c'
      eqFC =
        trans
          (fixedpoint-unique f n c0 haltF haltN)
          reach

module Bridge
  {ℓI ℓO ℓC₁ ℓQ₁ ℓC₂ ℓQ₂}
  {Input : Set ℓI} {Output : Set ℓO}
  (S : Scheme {ℓI} {ℓO} {ℓC₁} {ℓQ₁} Input Output)
  (T : Scheme {ℓI} {ℓO} {ℓC₂} {ℓQ₂} Input Output)
  where
  open module S₀ = FuelSound S
  open module T₀ = FuelSound T

  RunEq→ObsEq
    : FuelHalts S → FuelHalts T → RunEq S T → ObsEq S T
  RunEq→ObsEq fhs fht eq x y =
    toDir , fromDir
    where
      toDir : Scheme.ComputesTo S x y → Scheme.ComputesTo T x y
      toDir cS =
        subst (λ y' → Scheme.ComputesTo T x y') (sym y≡runT) (T₀.runIsComputesTo fht x)
        where
          y≡runS : y ≡ Scheme.run S x
          y≡runS = S₀.computesTo→run fhs x y cS

          y≡runT : y ≡ Scheme.run T x
          y≡runT = trans y≡runS (eq x)

      fromDir : Scheme.ComputesTo T x y → Scheme.ComputesTo S x y
      fromDir cT =
        subst (λ y' → Scheme.ComputesTo S x y') (sym y≡runS) (S₀.runIsComputesTo fhs x)
        where
          y≡runT : y ≡ Scheme.run T x
          y≡runT = T₀.computesTo→run fht x y cT

          y≡runS : y ≡ Scheme.run S x
          y≡runS = trans y≡runT (sym (eq x))

  ObsEq→RunEq
    : FuelHalts S → FuelHalts T → ObsEq S T → RunEq S T
  ObsEq→RunEq fhs fht obs x =
    T₀.computesTo→run fht x (Scheme.run S x) tS
    where
      sS : Scheme.ComputesTo S x (Scheme.run S x)
      sS = S₀.runIsComputesTo fhs x

      tS : Scheme.ComputesTo T x (Scheme.run S x)
      tS = fst (obs x (Scheme.run S x)) sS

open Scheme public

-- ==========================================================================
-- Algorithms vs implementations
--
-- `Scheme` is an implementation surface (a particular representation + stepper
-- + observation + cost profile). An algorithm is *not* a scheme: it is a
-- machine-independent specification (problem graph) that can be realized by
-- many schemes.
--
-- This separation lets the library state “same algorithm, different
-- implementations” in a precise way and transport implementations along
-- simulations.
-- ==========================================================================

record Algorithm {ℓI ℓO ℓS : Level}
                 (Input  : Set ℓI)
                 (Output : Set ℓO)
                 : Set (lsuc (ℓI ⊔ ℓO ⊔ ℓS)) where
  field
    Spec : Input → Output → Set ℓS

open Algorithm public

-- Relational realization: any computed outcome must satisfy the spec.
record ImplementsRel {ℓI ℓO ℓS ℓC ℓQ : Level}
                     {Input : Set ℓI} {Output : Set ℓO}
                     (A : Algorithm {ℓI} {ℓO} {ℓS} Input Output)
                     (S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output)
                     : Set (lsuc (ℓI ⊔ ℓO ⊔ ℓS ⊔ ℓC ⊔ ℓQ)) where
  field
    sound : ∀ x y → Scheme.ComputesTo S x y → Algorithm.Spec A x y

-- Closure-stable relational realization: any stabilized outcome must satisfy the spec.
record ImplementsStableRel {ℓI ℓO ℓS ℓC ℓQ : Level}
                           {Input : Set ℓI} {Output : Set ℓO}
                           (A : Algorithm {ℓI} {ℓO} {ℓS} Input Output)
                           (S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output)
                           : Set (lsuc (ℓI ⊔ ℓO ⊔ ℓS ⊔ ℓC ⊔ ℓQ)) where
  field
    sound : ∀ x y → Scheme.StabilizesTo S x y → Algorithm.Spec A x y

-- Schedule realization: the chosen schedule’s output satisfies the spec.
record ImplementsRun {ℓI ℓO ℓS ℓC ℓQ : Level}
                     {Input : Set ℓI} {Output : Set ℓO}
                     (A : Algorithm {ℓI} {ℓO} {ℓS} Input Output)
                     (S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output)
                     : Set (lsuc (ℓI ⊔ ℓO ⊔ ℓS ⊔ ℓC ⊔ ℓQ)) where
  field
    correct : ∀ x → Algorithm.Spec A x (Scheme.run S x)

-- If closed states are step-stable (`SchemeLaws`), then closure-stable relational
-- correctness implies schedule correctness (no fuel fixed point needed).
stableRel→run
  : ∀ {ℓI ℓO ℓS ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    {A : Algorithm {ℓI} {ℓO} {ℓS} Input Output}
    {S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output}
  → Scheme.SchemeLaws S
  → ImplementsStableRel A S
  → ImplementsRun A S
stableRel→run {S = S} laws rel = record
  { correct = λ x →
      ImplementsStableRel.sound rel x (Scheme.run S x) (Scheme.runIsStabilizesTo S laws x)
  }

-- If the schedule truly reaches a fixed point (`FuelHalts`), then relational
-- correctness implies schedule correctness.
rel→run
  : ∀ {ℓI ℓO ℓS ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    {A : Algorithm {ℓI} {ℓO} {ℓS} Input Output}
    {S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output}
  → FuelHalts S
  → ImplementsRel A S
  → ImplementsRun A S
rel→run {S = S} fh rel = record
  { correct = λ x →
      ImplementsRel.sound rel x (Scheme.run S x) (FuelSound.runIsComputesTo S fh x)
  }

-- If the chosen schedule truly reaches a fixed point (`FuelHalts`), then
-- schedule correctness implies relational correctness (for any `ComputesTo` run).
run→rel
  : ∀ {ℓI ℓO ℓS ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    {A : Algorithm {ℓI} {ℓO} {ℓS} Input Output}
    {S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output}
  → FuelHalts S
  → ImplementsRun A S
  → ImplementsRel A S
run→rel {A = A} {S = S} fh run =
  record
    { sound = λ x y c →
        subst (Algorithm.Spec A x) (sym (FuelSound.computesTo→run S fh x y c))
          (ImplementsRun.correct run x)
    }

-- ==========================================================================
-- Bundles
-- ==========================================================================

-- A scheme together with the minimal law connecting its closure to dynamics.
--
-- This is the “honest default” bundle for downstream semantics: it makes
-- explicit whether the scheme can justify claims phrased in terms of
-- stabilisation after computation (rather than just fuel-based execution).
record LawfulScheme {ℓI ℓO ℓC ℓQ : Level}
                    (Input : Set ℓI)
                    (Output : Set ℓO)
                    : Set (lsuc (ℓI ⊔ ℓO ⊔ ℓC ⊔ ℓQ)) where
  field
    scheme : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output
    laws   : Scheme.SchemeLaws scheme

  open Scheme scheme public
