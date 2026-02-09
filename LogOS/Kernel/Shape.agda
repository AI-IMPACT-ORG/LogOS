{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Shape where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.View
open import LogOS.Syntax.Prop as Prop

-- Shared kernel “shape”: everything that is common to ungraded and graded kernels,
-- i.e. the S/H tiers + boundary constraint structure + reflective code interface.
--
-- The guarded (G) tier differs: ungraded kernels use a single closure `Flow : Con → Con`,
-- while graded kernels use a grade-indexed flow `Flow : Grade → Con → Con` and must make
-- the step-grade vs saturation-grade split explicit.

record KernelShape {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  module W = Worlds Sig
  open Truth.StrictTruth Sig

  field
    -- H-tier: world context + Q-weighted flow
    HWorld : W.WorldH Q

  private
    module HT = Truth.HomotypicalTruth Sig Q HWorld

  field
    -- Constraints and lax monoidal adjunction
    BB     : BulkBoundary ℓ
    MBulk  : MonoidalOps (BulkBoundary.bulk BB)
    MBnd   : MonoidalOps (BulkBoundary.bnd  BB)
    Holo   : LaxMonoidalAdjunction BB MBulk MBnd

    -- H-tier satisfaction and invariance (dependent on the chosen world)
    HTruth : HT.HLayer BB
    HInv   : HT.Invariance BB

    -- Boundary satisfaction + coherence (optional, internalized)
    Sat_H_bnd : ∂Cosp → (ConPreorder.Con (BulkBoundary.bnd BB)) → Set ℓ
    sat-coh   : ∀ (w : Cosp) (c : ConPreorder.Con (BulkBoundary.bnd BB)) →
                Prop._↔_ (HT.HLayer.Sat_H HTruth w c)
                         (Sat_H_bnd (to∂ w) c)

    -- S-tier: strict logic interface and translation into H-tier constraints
    Fml    : Set ℓ
    Strict : StrictLayer Fml
    TransH : Fml → (ConPreorder.Con (BulkBoundary.bnd BB))
    coh-LH : ∀ (w : Cosp) (φ : Fml) →
             Prop._↔_ (StrictLayer.Sat_S Strict w φ)
                      (HT.HLayer.Sat_H HTruth w (TransH φ))

    -- Code layer: guarded reflection and one-step computation core
    Code   : Set ℓ
    encode : (ConPreorder.Con (BulkBoundary.bnd BB)) → Code
    decode : Code → (ConPreorder.Con (BulkBoundary.bnd BB))

    Guard         : Code → Code
    Body          : Code → Code

    -- Guarded fixpoint witness at the code level.
    γ*            : Code

    -- Safe self-reflection (observational)
    reify         : Code → Code

    -- Boundary view of code body
    Body∂         : (ConPreorder.Con (BulkBoundary.bnd BB)) → (ConPreorder.Con (BulkBoundary.bnd BB))

open KernelShape public

-- Boundary satisfaction inherits H-tier monotonicity via `sat-coh`.

Sat_H_bnd-mono
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (S : KernelShape Sig Q)
  → ∀ {w c c'}
  → ConPreorder._⊑_ (BulkBoundary.bnd (KernelShape.BB S)) c c'
  → KernelShape.Sat_H_bnd S (LogOSSignature.to∂ Sig w) c
  → KernelShape.Sat_H_bnd S (LogOSSignature.to∂ Sig w) c'
Sat_H_bnd-mono {Sig = Sig} {Q = Q} S {w} {c} {c'} c≤c' sat =
  let
    module HT = Truth.HomotypicalTruth Sig Q (KernelShape.HWorld S)
    open HT
    open HLayer (KernelShape.HTruth S)
    coh  = KernelShape.sat-coh S w c
    coh' = KernelShape.sat-coh S w c'
  in
  Prop.to coh' (mono-Con c≤c' (Prop.from coh sat))

Sat_H_bnd-mono-ctx
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (S : KernelShape Sig Q)
  → ∀ {w w' c}
  → Worlds.WorldH._≤ctx_ (KernelShape.HWorld S) w w'
  → KernelShape.Sat_H_bnd S (LogOSSignature.to∂ Sig w) c
  → KernelShape.Sat_H_bnd S (LogOSSignature.to∂ Sig w') c
Sat_H_bnd-mono-ctx {Sig = Sig} {Q = Q} S {w} {w'} {c} w≤w' sat =
  let
    module HT = Truth.HomotypicalTruth Sig Q (KernelShape.HWorld S)
    open HT
    open HLayer (KernelShape.HTruth S)
    coh  = KernelShape.sat-coh S w c
    coh' = KernelShape.sat-coh S w' c
  in
  Prop.to coh' (mono-ctx w≤w' (Prop.from coh sat))

record KernelShapeLaws
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (S : KernelShape Sig Q)
  : Set (lsuc (lsuc ℓ)) where
  open KernelShape S renaming
    ( γ* to γ*ₛ
    ; decode to decodeₛ
    ; encode to encodeₛ
    ; Guard to Guardₛ
    ; Body to Bodyₛ
    ; reify to reifyₛ
    ; Body∂ to Body∂ₛ
    )
  private
    BBₛ = KernelShape.BB S
  open ConPreorder (BulkBoundary.bnd BBₛ)
  field
    decode∘encode : ∀ c → decodeₛ (encodeₛ c) ≡ c
    γ*-guard      : (_⊑_ (decodeₛ γ*ₛ) (decodeₛ (Guardₛ (Bodyₛ γ*ₛ))))
                  × (_⊑_ (decodeₛ (Guardₛ (Bodyₛ γ*ₛ))) (decodeₛ γ*ₛ))
    reify-decode  : ∀ γ → decodeₛ (reifyₛ γ) ≡ decodeₛ γ
    body-decode   : ∀ γ → decodeₛ (Bodyₛ γ) ≡ Body∂ₛ (decodeₛ γ)

  -- Canonical name: the guard law is mutual refinement at decode level.
  γ*-guard≈
    : _≈CP_ (BulkBoundary.bnd BBₛ) (decodeₛ γ*ₛ) (decodeₛ (Guardₛ (Bodyₛ γ*ₛ)))
  γ*-guard≈ = γ*-guard

  -- Directional projections (useful in proofs and rewriting).
  γ*-guard⇒ : _⊑_ (decodeₛ γ*ₛ) (decodeₛ (Guardₛ (Bodyₛ γ*ₛ)))
  γ*-guard⇒ = ≈CP⇒ {CP = BulkBoundary.bnd BBₛ} γ*-guard

  γ*-guard⇐ : _⊑_ (decodeₛ (Guardₛ (Bodyₛ γ*ₛ))) (decodeₛ γ*ₛ)
  γ*-guard⇐ = ≈CP⇐ {CP = BulkBoundary.bnd BBₛ} γ*-guard

record KernelLaws
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (S : KernelShape Sig Q)
  (G : Truth.GuardedCore.GuardedClosure (BulkBoundary.bnd (KernelShape.BB S)))
  : Set (lsuc (lsuc ℓ)) where
  open KernelShape S renaming
    ( γ* to γ*ₛ
    ; decode to decodeₛ
    ; encode to encodeₛ
    ; Guard to Guardₛ
    ; Body to Bodyₛ
    ; reify to reifyₛ
    ; Body∂ to Body∂ₛ
    )
  private
    BBₛ = KernelShape.BB S
  open ConPreorder (BulkBoundary.bnd BBₛ)
  field
    shapeLaws    : KernelShapeLaws S
    mono-Body∂    : ∀ {c d} → _⊑_ c d → _⊑_ (Body∂ₛ c) (Body∂ₛ d)
    mono-Flow     : ∀ {c d} → _⊑_ c d → _⊑_ (Truth.GuardedCore.GuardedClosure.Flow G c)
                                        (Truth.GuardedCore.GuardedClosure.Flow G d)
    guard-decode  : ∀ γ → decodeₛ (Guardₛ γ)
                  ≡ Truth.GuardedCore.GuardedClosure.Flow G (decodeₛ γ)
    decode-γ*     : decodeₛ γ*ₛ ≡ Truth.GuardedCore.GuardedClosure.Th* G

  open KernelShapeLaws shapeLaws public

FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (S : KernelShape Sig Q)
  → KernelShape.Code S → KernelShape.Code S
FlowCode S γ = KernelShape.Guard S (KernelShape.Body S γ)

-- Refinement on code via decode into boundary constraints.

Code≤
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → (S : KernelShape Sig Q)
  → KernelShape.Code S → KernelShape.Code S → Set ℓ
Code≤ S γ δ =
  let
    CP = BulkBoundary.bnd (KernelShape.BB S)
    decodeView : View (KernelShape.Code S) (ConPreorder→RelPreorder CP)
    decodeView = record { μ = KernelShape.decode S }
  in
  γ ⊑[ decodeView ] δ

CodePreorder
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → (S : KernelShape Sig Q)
  → ConPreorder ℓ
CodePreorder S =
  record
    { Con = KernelShape.Code S
    ; _⊑_ = Code≤ S
    ; refl = ConPreorder.refl (BulkBoundary.bnd (KernelShape.BB S))
    ; trans = ConPreorder.trans (BulkBoundary.bnd (KernelShape.BB S))
    }

Code≈
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → (S : KernelShape Sig Q)
  → KernelShape.Code S → KernelShape.Code S → Set ℓ
Code≈ S = _≈CP_ (CodePreorder S)

decode-mono
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → (S : KernelShape Sig Q)
  → MonoMap (CodePreorder S) (BulkBoundary.bnd (KernelShape.BB S)) (KernelShape.decode S)
decode-mono S le = le

decode-respects≈
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → (S : KernelShape Sig Q)
  → ∀ {γ δ}
  → Code≈ S γ δ
  → _≈CP_ (BulkBoundary.bnd (KernelShape.BB S))
      (KernelShape.decode S γ)
      (KernelShape.decode S δ)
decode-respects≈ S {γ} {δ} eq =
  monoMap-respects≈
    {CP₁ = CodePreorder S}
    {CP₂ = BulkBoundary.bnd (KernelShape.BB S)}
    {f = KernelShape.decode S}
    (decode-mono S)
    eq

record BodyMonotoneShape
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (S : KernelShape Sig Q) : Set (lsuc (lsuc ℓ)) where
  field
    mono-Body∂
      : ∀ {c d}
      → ConPreorder._⊑_ (BulkBoundary.bnd (KernelShape.BB S)) c d
      → ConPreorder._⊑_ (BulkBoundary.bnd (KernelShape.BB S))
          (KernelShape.Body∂ S c)
          (KernelShape.Body∂ S d)
