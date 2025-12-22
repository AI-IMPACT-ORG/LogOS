{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.Scheme where

open import LogOS.Prelude

open import LogOS.Computation.Core using (iterate; Computation)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPoset)
open import LogOS.Minimal.ScaleOps using (ScaleOps)
open import Data.Product using (_×_; _,_; fst; snd)
open import Data.NatOrder using (_≤ℕ_; z≤n; s≤s; total≤ℕ)

-- A minimal “renormaliser”/normaliser interface: a lax closure operator on a
-- preorder (monotone + inflationary + idempotent up to ⊑).
--
-- This is intentionally signature-independent; it matches the shape of
-- the `Flow`/monotonicity laws inside `LogOS.Minimal.Truth.GuardedCore.GuardedClosure`.

record Closure {ℓ : Level} (CP : ConPoset ℓ) : Set (lsuc ℓ) where
  open ConPoset CP
  field
    normalize    : Con → Con
    mono         : ∀ {c c'} → _⊑_ c c' → _⊑_ (normalize c) (normalize c')
    infl         : ∀ c → _⊑_ c (normalize c)
    idemp-lax    : ∀ c → _⊑_ (normalize (normalize c)) (normalize c)

-- A “computation scheme” packages:
-- - a concrete representation (Code + compiler),
-- - a dynamics (Step),
-- - a renormaliser/normaliser (Closure),
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
    CP      : ConPoset ℓC
    Step    : ConPoset.Con CP → ConPoset.Con CP
    Norm    : Closure CP

    compile : Input → ConPoset.Con CP
    fuel    : Input → ℕ
    decode  : ConPoset.Con CP → Output

    Q       : QAdapter ℓQ
    stepCost : ConPoset.Con CP → QAdapter.Scale Q

  open ConPoset CP public using (Con; _⊑_; refl; trans)
  open Closure Norm public renaming
    ( normalize  to normalize
    ; mono       to normalize-mono
    ; infl       to normalize-infl
    ; idemp-lax  to normalize-idemp-lax
    )
  open QAdapter Q public using (Scale; _≤s_; _·_; e)

  Comp : Computation Con
  Comp = record { Step = Step ; Halts = λ _ → Topℓ }

  exec : ℕ → Input → Con
  exec n x = iterate Comp n (compile x)

  toNormalAt : ℕ → Input → Con
  toNormalAt n x = normalize (exec n x)

  run : Input → Output
  run x = decode (toNormalAt (fuel x) x)

  -- Grade-indexed execution: interpret a scale value as a step budget using `ScaleOps`.
  --
  -- This is the intended “machines are schemes” bridge: the scheme index is a
  -- grade in `Scale`, and `ScaleOps` turns it into an operational number of
  -- small-step iterations.
  run≤ : ScaleOps Q → Scale → Input → Output
  run≤ Ops b x =
    decode (normalize (exec (ScaleOps.steps Ops (ScaleOps.budget Ops b)) x))

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

  halts : Con → Set ℓC
  halts c = Step c ≡ c

  NormalizesTo : Con → Con → Set ℓC
  NormalizesTo c c' = Σ ℕ (λ n → iterate Comp n c ≡ c' × halts c')

  ComputesTo : Input → Output → Set (ℓC ⊔ ℓO)
  ComputesTo x y =
    Σ Con (λ c' → NormalizesTo (compile x) c' × decode (normalize c') ≡ y)

  -- Cost/budgeted variant: compute within a quantale budget.
  --
  -- For `QNat`, budgets are step/gas counts; for other adapters, budgets live in
  -- the adapter's `Scale`.

  NormalizesTo≤ : Scale → Con → Con → Set (ℓC ⊔ ℓQ)
  NormalizesTo≤ b c c' =
    Σ ℕ (λ n → iterate Comp n c ≡ c' × halts c' × costExec n c ≤s b)

  ComputesWithin : Input → Scale → Output → Set (ℓC ⊔ ℓO ⊔ ℓQ)
  ComputesWithin x b y =
    Σ Con (λ c' → NormalizesTo≤ b (compile x) c' × decode (normalize c') ≡ y)

-- ==========================================================================
-- Observational equivalence (semantics is the set of possible outputs)
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

ObsEq-refl
  : ∀ {ℓI ℓO ℓC ℓQ}
    {Input : Set ℓI} {Output : Set ℓO}
    (S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output)
  → ObsEq S S
ObsEq-refl S _ _ = (λ p → p) , (λ p → p)

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
  (λ p → fst (eTU x y) (fst (eST x y) p)) ,
  (λ p → snd (eST x y) (snd (eTU x y) p))

-- A tighter, executable observational equivalence:
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
FuelHalts S = ∀ x → Scheme.halts S (Scheme.exec S (Scheme.fuel S x) x)

module FuelSound {ℓI ℓO ℓC ℓQ}
                 {Input : Set ℓI} {Output : Set ℓO}
                 (S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output)
                 where
  open Scheme S hiding (refl; trans)

  stableFrom≤
    : ∀ {m n c}
      → m ≤ℕ n
      → halts (iterate Comp m c)
      → iterate Comp n c ≡ iterate Comp m c
  stableFrom≤ {n = n} {c = c} z≤n halt0 = stable0 n c halt0
    where
      stable0 : ∀ n c → halts c → iterate Comp n c ≡ c
      stable0 zero    _ _ = refl
      stable0 (suc n) c hc =
        trans
          (stable0 n (Step c) (cong Step hc))
          hc
  stableFrom≤ {c = c} (s≤s le) haltSm =
    stableFrom≤ {c = Step c} le haltSm

  fixedpoint-unique
    : ∀ m n c
      → halts (iterate Comp m c)
      → halts (iterate Comp n c)
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

  computesTo→run : FuelHalts S → ∀ x y → ComputesTo x y → y ≡ run x
  computesTo→run fh x y (c' , (n , (reach , haltC')) , outEq) =
    trans (sym outEq) (cong (λ c → decode (normalize c)) (sym eqFC))
    where
      c0 = compile x
      f  = fuel x

      haltN : halts (iterate Comp n c0)
      haltN = subst halts (sym reach) haltC'

      haltF : halts (iterate Comp f c0)
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

-- Schedule realization: the chosen schedule’s output satisfies the spec.
record ImplementsRun {ℓI ℓO ℓS ℓC ℓQ : Level}
                     {Input : Set ℓI} {Output : Set ℓO}
                     (A : Algorithm {ℓI} {ℓO} {ℓS} Input Output)
                     (S : Scheme {ℓI} {ℓO} {ℓC} {ℓQ} Input Output)
                     : Set (lsuc (ℓI ⊔ ℓO ⊔ ℓS ⊔ ℓC ⊔ ℓQ)) where
  field
    correct : ∀ x → Algorithm.Spec A x (Scheme.run S x)

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
