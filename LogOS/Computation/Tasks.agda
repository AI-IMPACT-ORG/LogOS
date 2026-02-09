{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.Tasks where

-- Generic “arbitrary tasks” for the scheme/process layer:
-- a task is simply a starting state together with an explicit step budget.
--
-- This is useful when you want to talk about *raw code* (states) rather than a
-- particular high-level input language + compiler.

open import LogOS.Prelude

open import LogOS.Computation.Core using (iterate; Computation)
open import LogOS.Minimal.ScaleOps using (ScaleOps)
import LogOS.Minimal.Truth as Truth
import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat

-- A value of type `Fuelled A` is “an A together with a concrete step budget”.
record Fuelled {ℓ : Level} (A : Set ℓ) : Set ℓ where
  constructor mkFuelled
  field
    fuel    : ℕ
    payload : A

open Fuelled public

mapFuelled : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → (A → B) → Fuelled A → Fuelled B
mapFuelled f t = mkFuelled (fuel t) (f (payload t))

-- A value of type `Graded G A` is “an A together with a scheme grade/budget G”.
record Graded {ℓG ℓA : Level} (G : Set ℓG) (A : Set ℓA) : Set (ℓG ⊔ ℓA) where
  constructor mkGraded
  field
    grade   : G
    payload : A

open Graded public

mapGraded : ∀ {ℓG ℓA ℓB} {G : Set ℓG} {A : Set ℓA} {B : Set ℓB} → (A → B) → Graded G A → Graded G B
mapGraded f t = mkGraded (grade t) (f (payload t))

-- --------------------------------------------------------------------------
-- Process view: run a raw process state for `n` steps.

module ForProcess
  {ℓO ℓC ℓQ : Level}
  {Output : Set ℓO}
  (P : Cat.Process {ℓO} {ℓC} {ℓQ} Output)
  where

  open Cat.Process P

  CodeTask : Set ℓC
  CodeTask = Fuelled Con

  execFrom : ℕ → Con → Con
  execFrom n c = Cat.iterStep P n c

  nfFrom : ℕ → Con → Con
  nfFrom n c = close (execFrom n c)

  nfTask : CodeTask → Con
  nfTask t = nfFrom (fuel t) (payload t)

  runFrom : ℕ → Con → Output
  runFrom n c = decode (nfFrom n c)

  runTask : CodeTask → Output
  runTask t = runFrom (fuel t) (payload t)

  -- Grade-indexed task execution (scheme-style): execute for the number of
  -- steps induced by a scale grade, then decode the normal form.
  --
  -- This is the “machines are schemes” interface for raw code states.

  GradeTask : Set (ℓC ⊔ ℓQ)
  GradeTask = Graded Scale Con

  nf≤From : ScaleOps Q → Scale → Con → Con
  nf≤From Ops g c = close (Cat.run≤ P Ops g c)

  nf≤Task : ScaleOps Q → GradeTask → Con
  nf≤Task Ops t = nf≤From Ops (grade t) (payload t)

  run≤From : ScaleOps Q → Scale → Con → Output
  run≤From Ops g c = decode (nf≤From Ops g c)

  run≤Task : ScaleOps Q → GradeTask → Output
  run≤Task Ops t = run≤From Ops (grade t) (payload t)

  -- ------------------------------------------------------------------------
  -- Transport: process morphisms preserve meaning of finite/graded execution.

  module Transport
    {ℓC₂ : Level}
    {P₂ : Cat.Process {ℓO} {ℓC₂} {ℓQ} Output}
    (h : Cat.ProcessHom P P₂)
    where

    private
      Con₂ : Set ℓC₂
      Con₂ = Cat.Process.Con P₂

      maph : Con → Con₂
      maph = Cat.ProcessHom.map h

      execFrom₂ : ℕ → Con₂ → Con₂
      execFrom₂ n c = Cat.iterStep P₂ n c

      nfFrom₂ : ℕ → Con₂ → Con₂
      nfFrom₂ n c = Cat.Process.close P₂ (execFrom₂ n c)

      runFrom₂ : ℕ → Con₂ → Output
      runFrom₂ n c = Cat.Process.decode P₂ (nfFrom₂ n c)

      CodeTask₂ : Set ℓC₂
      CodeTask₂ = Fuelled Con₂

      runTask₂ : CodeTask₂ → Output
      runTask₂ t = runFrom₂ (Fuelled.fuel t) (Fuelled.payload t)

    execFrom-map : ∀ n c → maph (execFrom n c) ≡ execFrom₂ n (maph c)
    execFrom-map n c = Cat.iterStep-map h n c

    nfFrom-map : ∀ n c → maph (nfFrom n c) ≡ nfFrom₂ n (maph c)
    nfFrom-map n c =
      let
        r : Con
        r = execFrom n c
      in
      LogOS.Prelude.trans
        (Cat.ProcessHom.norm-comm h r)
        (cong (Cat.Process.close P₂) (execFrom-map n c))

    runFrom-map : ∀ n c → runFrom₂ n (maph c) ≡ runFrom n c
    runFrom-map n c =
      LogOS.Prelude.trans
        (cong (Cat.Process.decode P₂) (LogOS.Prelude.sym (nfFrom-map n c)))
        (Cat.ProcessHom.decode-comm h (nfFrom n c))

    runTask-map : ∀ t → runTask₂ (mapFuelled maph t) ≡ runTask t
    runTask-map t = runFrom-map (Fuelled.fuel t) (Fuelled.payload t)

  module TransportLax
    {ℓC₂ : Level}
    {P₂ : Cat.Process {ℓO} {ℓC₂} {ℓQ} Output}
    (h : Cat.ProcessHomLax P P₂)
    (stepMono₂ : Cat.StepMono P₂)
    where

    private
      Con₂ : Set ℓC₂
      Con₂ = Cat.Process.Con P₂

      _⊑₂_ : Con₂ → Con₂ → Set ℓC₂
      _⊑₂_ = Cat.Process._⊑_ P₂

      trans₂ : ∀ {x y z} → x ⊑₂ y → y ⊑₂ z → x ⊑₂ z
      trans₂ = Cat.Process.trans P₂

      maph : Con → Con₂
      maph = Cat.ProcessHomLax.map h

      execFrom₂ : ℕ → Con₂ → Con₂
      execFrom₂ n c = Cat.iterStep P₂ n c

      nfFrom₂ : ℕ → Con₂ → Con₂
      nfFrom₂ n c = Cat.Process.close P₂ (execFrom₂ n c)

      CodeTask₂ : Set ℓC₂
      CodeTask₂ = Fuelled Con₂

      nfTask₂ : CodeTask₂ → Con₂
      nfTask₂ t = nfFrom₂ (Fuelled.fuel t) (Fuelled.payload t)

    execFrom-map≤ : ∀ n c → maph (execFrom n c) ⊑₂ execFrom₂ n (maph c)
    execFrom-map≤ n c = Cat.iterStep-map≤ h stepMono₂ n c

    nfFrom-map≤ : ∀ n c → maph (nfFrom n c) ⊑₂ nfFrom₂ n (maph c)
    nfFrom-map≤ n c =
      let
        r : Con
        r = execFrom n c
      in
      trans₂
        (Cat.ProcessHomLax.norm-comm≤ h r)
        (Cat.Process.close-mono P₂ (execFrom-map≤ n c))

    nfTask-map≤ : ∀ t → maph (nfTask t) ⊑₂ nfTask₂ (mapFuelled maph t)
    nfTask-map≤ t = nfFrom-map≤ (Fuelled.fuel t) (Fuelled.payload t)

  module TransportCost
    {ℓC₂ : Level}
    {P₂ : Cat.Process {ℓO} {ℓC₂} {ℓQ} Output}
    (hc : Cat.ProcessHomCost P P₂)
    where

    module T = Transport (Cat.ProcessHomCost.hom hc)
    open T public using (execFrom-map; nfFrom-map; runFrom-map; runTask-map)

    private
      maph : Con → Cat.Process.Con P₂
      maph = Cat.ProcessHom.map (Cat.ProcessHomCost.hom hc)

    run≤From-map
      : ∀ (Ops₁ : ScaleOps Q) (Ops₂ : ScaleOps (Cat.Process.Q P₂)) g c
      → (stepsEq :
           ScaleOps.steps Ops₂
             (ScaleOps.budget Ops₂ (Truth.GuardedCore.GradeHom.map (Cat.ProcessHomCost.grade hc) g))
           ≡
           ScaleOps.steps Ops₁ (ScaleOps.budget Ops₁ g))
      → Cat.Process.decode P₂
          (Cat.Process.close P₂
            (Cat.run≤ P₂
              Ops₂
              (Truth.GuardedCore.GradeHom.map (Cat.ProcessHomCost.grade hc) g)
              (maph c)))
        ≡ run≤From Ops₁ g c
    run≤From-map Ops₁ Ops₂ g c stepsEq = Cat.run≤-meaning-comm hc Ops₁ Ops₂ g c stepsEq

    run≤Task-map
      : ∀ (Ops₁ : ScaleOps Q) (Ops₂ : ScaleOps (Cat.Process.Q P₂)) t
      → (stepsEq :
           ScaleOps.steps Ops₂
             (ScaleOps.budget Ops₂ (Truth.GuardedCore.GradeHom.map (Cat.ProcessHomCost.grade hc) (Graded.grade t)))
           ≡
           ScaleOps.steps Ops₁ (ScaleOps.budget Ops₁ (Graded.grade t)))
      → Cat.Process.decode P₂
          (Cat.Process.close P₂
            (Cat.run≤ P₂
              Ops₂
              (Truth.GuardedCore.GradeHom.map (Cat.ProcessHomCost.grade hc) (Graded.grade t))
              (maph (Graded.payload t))))
        ≡ run≤Task Ops₁ t
    run≤Task-map Ops₁ Ops₂ t stepsEq = run≤From-map Ops₁ Ops₂ (Graded.grade t) (Graded.payload t) stepsEq

-- --------------------------------------------------------------------------
-- Scheme view: run either a raw code state, or a compiled input, for an
-- explicit number of steps.

module ForScheme
  {ℓI ℓO ℓC ℓQ : Level}
  {Input : Set ℓI}
  {Output : Set ℓO}
  (S : Sch.Scheme {ℓI = ℓI} {ℓO = ℓO} {ℓC = ℓC} {ℓQ = ℓQ} Input Output)
  where

  open Sch.Scheme S

  CodeTask : Set ℓC
  CodeTask = Fuelled Con

  InputTask : Set ℓI
  InputTask = Fuelled Input

  execFrom : ℕ → Con → Con
  execFrom n c = iterate Comp n c

  runFrom : ℕ → Con → Output
  runFrom n c = decode (close (execFrom n c))

  runCodeTask : CodeTask → Output
  runCodeTask t = runFrom (fuel t) (payload t)

  runInputTask : InputTask → Output
  runInputTask t = decode (close (exec (fuel t) (payload t)))

  codeTaskOf : Input → CodeTask
  codeTaskOf x = mkFuelled (Sch.Scheme.fuel S x) (Sch.Scheme.compile S x)

  runCodeTaskOf≡run : ∀ x → runCodeTask (codeTaskOf x) ≡ run x
  runCodeTaskOf≡run _ = LogOS.Prelude.refl
