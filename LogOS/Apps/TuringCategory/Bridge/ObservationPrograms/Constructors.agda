{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.Bridge.ObservationPrograms.Constructors where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( Con
  ; _⊑_
  ; _≈_
  ; refl⊑
  ; ≈-refl
  ; MonoMap
  )
open import LogOS.LT.Kernel using (Kernel; CodePreorder; bnd)
open import LogOS.LT.Hom using (KernelHom; _∘_; ⇒∂→⇒)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat using (mkTotalObjR; mkTotalHomR)

import LogOS.Apps.TuringCategory.PartialMaps as PM
open import LogOS.Apps.TuringCategory.Lift using (LiftCP)
import LogOS.Apps.TuringCategory.Bridge.KernelToPar as K2Par

open import LogOS.Apps.TuringCategory.Bridge.ObservationPrograms.Types using
  ( ObsGate
  ; mkObsGate
  ; Atom
  ; run
  ; observe
  ; Prog
  ; _∷_
  ; []
  ; semProg
  )
open import LogOS.Apps.TuringCategory.Bridge.ObservationPrograms.ProgDisplayed using
  ( ProgOb
  ; ttProg
  ; ProgImplementation
  ; ParProg
  )

-- --------------------------------------------------------------------------
-- Constructors: embed total kernel steps and add observation gates.

-- Convenience: make a 1-step program from a kernel morphism.
runProg
  : ∀ {ℓ ℓRel ℓCode : Level}
    {A B : Kernel ℓ ℓRel ℓCode}
  → KernelHom A B
  → Prog A B
runProg h = run h ∷ []

-- Convenience: a 1-step observation program (endomap).
observeProg
  : ∀ {ℓ ℓRel ℓCode : Level}
    {A : Kernel ℓ ℓRel ℓCode}
  → ObsGate A
  → Prog A A
observeProg g = observe g ∷ []

-- Package a program into a decorated `ParProg` morphism by using its own semantics
-- as the base partial map (so the implementation proof is reflexive).
mkParProgHom
  : ∀ {ℓ ℓRel ℓCode : Level}
    {A B : Kernel ℓ ℓRel ℓCode}
  → Prog A B
  → Con
      (Thin2Cat.Hom
        (ParProg {ℓ} {ℓRel} {ℓCode})
        (mkTotalObjR A ttProg)
        (mkTotalObjR B ttProg))
mkParProgHom {A = A} {B = B} p =
  let
    f = semProg p

    implementation : ProgImplementation {A = A} {B = B} f
    implementation =
      record
        { proj₁ = p
        ; proj₂ = ≈-refl (PM.PartialMapPreorder (CodePreorder A) (CodePreorder B)) f
        }
  in
  mkTotalHomR f implementation

-- Embed a raw kernel morphism as a *total* partial map with a 1-step program witness.
embedLOG
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor
      (LOG {ℓ} {ℓRel} {ℓCode})
      (ParProg {ℓ} {ℓRel} {ℓCode})
embedLOG {ℓ} {ℓRel} {ℓCode} =
  let
    module S = Thin2Cat (LOG {ℓ} {ℓRel} {ℓCode})
    module T = Thin2Cat (ParProg {ℓ} {ℓRel} {ℓCode})
  in
  record
    { mapObj = λ K →
        mkTotalObjR K ttProg
    ; mapHom = λ {A} {B} h →
        let
          f = K2Par.kernelHomToPartialMap {K = A} {K' = B} h

          implementation : ProgImplementation {A = A} {B = B} f
          implementation =
            record
              { proj₁ = runProg h
              ; proj₂ = PM.Par-id-left {A = CodePreorder A} {B = CodePreorder B} f
              }
        in
        mkTotalHomR f implementation
    ; mapHom-mono = λ {A} {B} {x} {y} le γ → ⇒∂→⇒ {K = A} {K' = B} {f = x} {g = y} le γ
    ; id-pres = λ {A} →
        let
          idp = PM.idp {X = CodePreorder A}
        in
        ( (λ γ → refl⊑ (LiftCP (CodePreorder A)) {c = PM.map idp γ})
        , (λ γ → refl⊑ (LiftCP (CodePreorder A)) {c = PM.map idp γ})
        )
    ; comp-pres = λ {A} {B} {C₀} f g →
        let
          base = K2Par.kernelHomToPartialMap {K = A} {K' = C₀} (f S.∘ g)
        in
        ( (λ γ → refl⊑ (LiftCP (CodePreorder C₀)) {c = PM.map base γ})
        , (λ γ → refl⊑ (LiftCP (CodePreorder C₀)) {c = PM.map base γ})
        )
    }

-- One-step “run then observe on output boundary” via an explicit observation
-- port on the output kernel.
runThenObservePort
  : ∀ {ℓ ℓRel ℓCode : Level}
    {A B : Kernel ℓ ℓRel ℓCode}
  → KernelHom A B
  → K2Par.BoundaryObservationPort B (CodePreorder B)
  → Con
      (Thin2Cat.Hom
        (ParProg {ℓ} {ℓRel} {ℓCode})
        (mkTotalObjR A ttProg)
        (mkTotalObjR B ttProg))
runThenObservePort h Pₒ =
  mkParProgHom
    ( run h ∷ observe Pₒ ∷ [] )

-- One-step “run then observe on output boundary”: convenience wrapper that
-- builds the explicit observation port in place.
runThenObserve
  : ∀ {ℓ ℓRel ℓCode : Level}
    {A B : Kernel ℓ ℓRel ℓCode}
  → KernelHom A B
  → (V : View (Con (bnd B)) (LiftCP (CodePreorder B)))
  → (monoV : MonoMap (bnd B) (LiftCP (CodePreorder B)) (μ V))
  → Con
      (Thin2Cat.Hom
        (ParProg {ℓ} {ℓRel} {ℓCode})
        (mkTotalObjR A ttProg)
        (mkTotalObjR B ttProg))
runThenObserve h V monoV =
  runThenObservePort h (K2Par.mkBoundaryObservationPort V monoV)
