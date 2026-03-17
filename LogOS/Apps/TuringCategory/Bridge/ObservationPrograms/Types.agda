{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.Bridge.ObservationPrograms.Types where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; MonoMap)
open import LogOS.LT.Kernel using (Kernel; CodePreorder; bnd)
open import LogOS.LT.Hom using (KernelHom; idKernelHom)
open import LogOS.LT.View using (View; μ)

import LogOS.Apps.TuringCategory.PartialMaps as PM
open import LogOS.Apps.TuringCategory.Lift using (LiftCP)
import LogOS.Apps.TuringCategory.Bridge.KernelToPar as K2Par

-- --------------------------------------------------------------------------
-- Observation programs (typed lists of steps + gates)

ObsGate
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Kernel ℓ ℓRel ℓCode
  → Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
ObsGate K = K2Par.BoundaryObservationPort K (CodePreorder K)

mkObsGate
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → (V : View (Con (bnd K)) (LiftCP (CodePreorder K)))
  → (monoV : MonoMap (bnd K) (LiftCP (CodePreorder K)) (μ V))
  → ObsGate K
mkObsGate = K2Par.mkBoundaryObservationPort

gateView
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → ObsGate K
  → View (Con (bnd K)) (LiftCP (CodePreorder K))
gateView = K2Par.boundaryView

gateView-mono
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → (G : ObsGate K)
  → MonoMap (bnd K) (LiftCP (CodePreorder K)) (μ (gateView G))
gateView-mono = K2Par.boundaryView-mono

gateMap
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → ObsGate K
  → PM.PartialMap (CodePreorder K) (CodePreorder K)
gateMap {K = K} G = K2Par.observedPartialMap G (idKernelHom K)

data Atom {ℓ ℓRel ℓCode : Level}
  : Kernel ℓ ℓRel ℓCode
  → Kernel ℓ ℓRel ℓCode
  → Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode)) where

  run
    : ∀ {A B}
    → KernelHom A B
    → Atom A B

  observe
    : ∀ {A}
    → ObsGate A
    → Atom A A

infixr 5 _∷_
data Prog {ℓ ℓRel ℓCode : Level}
  : Kernel ℓ ℓRel ℓCode
  → Kernel ℓ ℓRel ℓCode
  → Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode)) where

  []  : ∀ {A} → Prog A A
  _∷_ : ∀ {A B C} → Atom A C → Prog C B → Prog A B

infixr 5 _++_
_++_
  : ∀ {ℓ ℓRel ℓCode : Level}
    {A B C : Kernel ℓ ℓRel ℓCode}
  → Prog A B
  → Prog B C
  → Prog A C
[] ++ q = q
(a ∷ p) ++ q = a ∷ (p ++ q)

semAtom
  : ∀ {ℓ ℓRel ℓCode : Level}
    {A B : Kernel ℓ ℓRel ℓCode}
  → Atom A B
  → PM.PartialMap (CodePreorder A) (CodePreorder B)
semAtom (run h) = K2Par.kernelHomToPartialMap h
semAtom {A = A} (observe G) = gateMap {K = A} G

semProg
  : ∀ {ℓ ℓRel ℓCode : Level}
    {A B : Kernel ℓ ℓRel ℓCode}
  → Prog A B
  → PM.PartialMap (CodePreorder A) (CodePreorder B)
semProg [] = PM.idp
semProg (a ∷ p) = semProg p PM.∘p semAtom a
