{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.HasseYonedaTransport where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Hom using (KernelHom)
open import LogOS.Kernel.Initial using (InitialKernel)

import LogOS.Theorems.CategoryTheory.Yoneda as Yoneda
import LogOS.Theorems.Meta.CommunicableTruth as Comm
import LogOS.Theorems.Meta.MathTruth as MT
import LogOS.Theorems.Meta.LimitPublicisation as LP

open import LogOS.Domain.Opacity.HasseObservableClass as HOC
import LogOS.Domain.Opacity.WeilCriterionLedger as WCL
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

-- Canonical “Hasse-style” regulator generators live in the initial kernel’s code.
-- They can then be interpreted in any kernel via the canonical fold map.

record HasseGenerator {ℓ : Level}
                      {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                      (IK : InitialKernel Sig Q)
                      : Set (lsuc (lsuc ℓ)) where
  field
    Reg     : Set ℓ
    mkTest₀ : Reg → Kernel.Code (InitialKernel.FreeK IK)

open HasseGenerator public

-- Interpret the regulator generator in any kernel via the canonical fold.

mkTest
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {IK : InitialKernel Sig Q}
    (K : Kernel Sig Q)
    (G : HasseGenerator IK)
  → Reg G → Kernel.Code K
mkTest {IK = IK} K G r =
  KernelHom.mapCode (InitialKernel.foldK IK K) (mkTest₀ G r)

-- Semantic equality on codes: decode-level equality in the target kernel.

infix 4 _≈decode_

_≈decode_
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Kernel.Code K → Kernel.Code K → Set ℓ
_≈decode_ K γ₁ γ₂ = Kernel.decode K γ₁ ≡ Kernel.decode K γ₂

-- Canonicality: interpreting regulators via the fold is independent (up to decode)
-- of the chosen morphism out of the initial kernel.

mkTest-canonical
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK : InitialKernel Sig Q)
    (K  : Kernel Sig Q)
    (G  : HasseGenerator IK)
    (h  : KernelHom (InitialKernel.FreeK IK) K)
  → ∀ r →
      _≈decode_ K (mkTest {IK = IK} K G r)
                 (KernelHom.mapCode h (mkTest₀ G r))
mkTest-canonical IK K G h r =
  let eq = Yoneda.yoneda-morphism-decode IK K h
  in eq (mkTest₀ G r)

-- Practical corollary: any decode-extensional property on `K` holds of the
-- canonical fold-interpretation iff it holds of the interpretation via any
-- chosen morphism out of the initial kernel.

mkTest-canonical-prop
  : ∀ {ℓ ℓP} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK : InitialKernel Sig Q)
    (K  : Kernel Sig Q)
    (G  : HasseGenerator IK)
    (h  : KernelHom (InitialKernel.FreeK IK) K)
    (P  : Kernel.Code K → Set ℓP)
  → Comm.DecodeExtensional′ K P
  → ∀ r → P (mkTest {IK = IK} K G r) ↔ P (KernelHom.mapCode h (mkTest₀ G r))
mkTest-canonical-prop IK K G h P extP r =
  record
    { to   = λ pr → extP (mkTest {IK = IK} K G r) (KernelHom.mapCode h (mkTest₀ G r))
                          (mkTest-canonical IK K G h r) pr
    ; from = λ pr → extP (KernelHom.mapCode h (mkTest₀ G r)) (mkTest {IK = IK} K G r)
                          (sym (mkTest-canonical IK K G h r)) pr
    }

-- Build a HasseObservableClass for the standard Pr-based observability semantics:
-- - tests are codes,
-- - observability is `Pr` for a chosen predicate W-pos,
-- - semantic equality is decode equality.

hasseObservableClass-fromPr
  : ∀ {ℓ ℓW ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K     : Kernel Sig Q)
    (W-pos : Kernel.Code K → Set ℓW)
    (Reg   : Set ℓ)
    (mkT   : Reg → Kernel.Code K)
    (mkT-observable : ∀ r → Comm.Pr {ℓC = ℓC} K W-pos (mkT r))
  → HOC.HasseObservableClass {ℓT = ℓ} {ℓW = ℓW} {ℓObs = (ℓ ⊔ ℓW ⊔ lsuc ℓC)} {ℓ≈ = ℓ}
      (MT.TruthPositivity-fromPr {ℓC = ℓC} K W-pos)
hasseObservableClass-fromPr {ℓC = ℓC} K W-pos Reg mkT mkT-observable = record
  { _≈_ = _≈decode_ K
  ; obs-resp = λ {t} {u} decEq obs →
      Comm.comm⋆-ext {ℓC = ℓC} K W-pos t u decEq obs
  ; Reg = Reg
  ; mkTest = mkT
  ; mkTest-observable = mkT-observable
  }

-- Convenience: if you proved a factorisation via some morphism out of the initial
-- kernel, Yoneda canonicality upgrades it to a factorisation via the fold map.

factorise-via-fold
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK : InitialKernel Sig Q)
    (K  : Kernel Sig Q)
    (G  : HasseGenerator IK)
    {S : Set ℓ}
    (probe : S → Kernel.Code K)
    (sel   : ∀ s → Reg G)
    (h     : KernelHom (InitialKernel.FreeK IK) K)
  → (∀ s → _≈decode_ K (KernelHom.mapCode h (mkTest₀ G (sel s))) (probe s))
  → ∀ s → _≈decode_ K (mkTest {IK = IK} K G (sel s)) (probe s)
factorise-via-fold IK K G probe sel h fact s =
  trans (mkTest-canonical IK K G h (sel s)) (fact s)

-- If observability is defined as `Pr W-pos`, then observability of transported
-- regulator tests is independent (up to decode) of the chosen morphism out of FreeK.

mkTest-observable-viaHom
  : ∀ {ℓ ℓW ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK : InitialKernel Sig Q)
    (K  : Kernel Sig Q)
    (W-pos : Kernel.Code K → Set ℓW)
    (G  : HasseGenerator IK)
    (h  : KernelHom (InitialKernel.FreeK IK) K)
  → (∀ r → Comm.Pr {ℓC = ℓC} K W-pos (KernelHom.mapCode h (mkTest₀ G r)))
  → (∀ r → Comm.Pr {ℓC = ℓC} K W-pos (mkTest {IK = IK} K G r))
mkTest-observable-viaHom {ℓC = ℓC} IK K W-pos G h obs r =
  Comm.comm⋆-ext {ℓC = ℓC} K W-pos
    (KernelHom.mapCode h (mkTest₀ G r))
    (mkTest {IK = IK} K G r)
    (sym (mkTest-canonical IK K G h r))
    (obs r)

-- One-shot GRH_Without_Vacuity_Guards lemma: weak Weil criterion + Pr-based observability + Hasse-generator
-- factorisation (up to decode equality) yields GRH.

GRH_Without_Vacuity_Guards-from-weak-criterion+HasseGenerator
  : ∀ {ℓ ℓW ℓC}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK : InitialKernel Sig Q)
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
    (W-pos : Kernel.Code K → Set ℓW)
    (WC : WCL.WeilCriterionWeak RS (MT.TruthPositivity-fromPr {ℓC = ℓC} K W-pos))
    (G  : HasseGenerator IK)
    (mkTest-observable : ∀ r → Comm.Pr {ℓC = ℓC} K W-pos (mkTest {IK = IK} K G r))
    (sel : ∀ s → RiemannSpectral.NontrivialZero RS s → Reg G)
    (mkTest∘sel≈probe
      : ∀ s (nz : RiemannSpectral.NontrivialZero RS s)
        → _≈decode_ K (mkTest {IK = IK} K G (sel s nz))
                     (WCL.WeilCriterionWeak.probe WC s))
  → GRH_Without_Vacuity_Guards RS
GRH_Without_Vacuity_Guards-from-weak-criterion+HasseGenerator {ℓ = ℓ} {ℓW = ℓW} {ℓC = ℓC} IK K RS W-pos WC G mkTest-observable sel mkTest∘sel≈probe =
  let
    TPo = MT.TruthPositivity-fromPr {ℓC = ℓC} K W-pos
    H : HOC.HasseObservableClass {ℓT = ℓ} {ℓW = ℓW} {ℓObs = (ℓ ⊔ ℓW ⊔ lsuc ℓC)} {ℓ≈ = ℓ}
          TPo
    H = hasseObservableClass-fromPr {ℓC = ℓC} K W-pos (Reg G) (mkTest {IK = IK} K G) mkTest-observable

    probe-in-class
      : ∀ s → RiemannSpectral.NontrivialZero RS s
          → HOC.HasseObservableClass.Class H (WCL.WeilCriterionWeak.probe WC s)
    probe-in-class =
      HOC.probe-in-class-fromFactor H WC sel mkTest∘sel≈probe
  in
  HOC.GRH_Without_Vacuity_Guards-from-weak-criterion+Hasse RS TPo WC H probe-in-class

-- Specialization: if W-pos is itself decode-extensional and Flow-stable,
-- then `mkTest-observable` can be replaced by plain truth on generated tests.
-- 
-- This packages the “stable truth is observable” step via `LP.TruthK→Pr`
-- (with communicability level chosen as ℓW).

GRH_Without_Vacuity_Guards-from-weak-criterion+HasseGenerator-stableTruth
  : ∀ {ℓ ℓW}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK : InitialKernel Sig Q)
    (K  : Kernel Sig Q)
    (RS : RiemannSpectral)
    (W-pos : Kernel.Code K → Set ℓW)
    (WC : WCL.WeilCriterionWeak RS (MT.TruthPositivity-fromPr {ℓC = ℓW} K W-pos))
    (G  : HasseGenerator IK)
    (W-ext : Comm.DecodeExtensional′ K W-pos)
    (W-stable : ∀ γ → W-pos γ ↔ W-pos (FlowCode K γ))
    (mkTest-true : ∀ r → W-pos (mkTest {IK = IK} K G r))
    (sel : ∀ s → RiemannSpectral.NontrivialZero RS s → Reg G)
    (mkTest∘sel≈probe
      : ∀ s (nz : RiemannSpectral.NontrivialZero RS s)
        → _≈decode_ K (mkTest {IK = IK} K G (sel s nz))
                     (WCL.WeilCriterionWeak.probe WC s))
  → GRH_Without_Vacuity_Guards RS
GRH_Without_Vacuity_Guards-from-weak-criterion+HasseGenerator-stableTruth {ℓW = ℓW} IK K RS W-pos WC G W-ext W-stable mkTest-true sel mkTest∘sel≈probe =
  GRH_Without_Vacuity_Guards-from-weak-criterion+HasseGenerator {ℓC = ℓW} IK K RS W-pos WC G mkTest-observable sel mkTest∘sel≈probe
  where
    mkTest-observable : ∀ r → Comm.Pr {ℓC = ℓW} K W-pos (mkTest {IK = IK} K G r)
    mkTest-observable r =
      LP.TruthK→Pr K W-pos W-ext W-stable (mkTest-true r)
