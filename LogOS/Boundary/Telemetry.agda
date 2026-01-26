{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Boundary.Telemetry where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port using (_≈∂[_]_)

-- Observational preorder on boundary programs (induced by Sat∂).

ObsLe∂Cosp
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → LogOSSignature.∂Cosp Sig
  → LogOSSignature.∂Cosp Sig
  → Set ℓ
ObsLe∂Cosp B p q =
  Prop.ObsLeOn (λ c p' → BoundaryIO.Sat∂ B p' c) p q

ObsCospPreorder
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → ConPreorder ℓ
ObsCospPreorder {Sig = Sig} B =
  let open LogOSSignature Sig in
  record
    { Con = ∂Cosp
    ; _⊑_ = ObsLe∂Cosp B
    ; refl = λ {p} c sat → sat
    ; trans = λ pq qr c sat → qr c (pq c sat)
    }

-- Boundary program observational equivalence induced by Sat∂.

infix 4 _≈∂Cosp[_]_
_≈∂Cosp[_]_
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → LogOSSignature.∂Cosp Sig
  → BoundaryIO Sig Q W BB H
  → LogOSSignature.∂Cosp Sig
  → Set ℓ
_≈∂Cosp[_]_ p B q =
  Prop.ObsEqOn (λ c p' → BoundaryIO.Sat∂ B p' c) p q

≈∂Cosp-refl
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → (p : LogOSSignature.∂Cosp Sig)
  → p ≈∂Cosp[ B ] p
≈∂Cosp-refl B p =
  Prop.ObsEqOn-refl (λ c p' → BoundaryIO.Sat∂ B p' c) p

≈∂Cosp-sym
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → {B : BoundaryIO Sig Q W BB H}
  → {p q : LogOSSignature.∂Cosp Sig}
  → p ≈∂Cosp[ B ] q
  → q ≈∂Cosp[ B ] p
≈∂Cosp-sym eq c = Prop.↔-sym (eq c)

≈∂Cosp-trans
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → {B : BoundaryIO Sig Q W BB H}
  → {p q r : LogOSSignature.∂Cosp Sig}
  → p ≈∂Cosp[ B ] q
  → q ≈∂Cosp[ B ] r
  → p ≈∂Cosp[ B ] r
≈∂Cosp-trans pq qr c = Prop.↔-trans (pq c) (qr c)

≈∂Cosp↔ObsLe
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → {p q : LogOSSignature.∂Cosp Sig}
  → Prop._↔_
      (p ≈∂Cosp[ B ] q)
      (Prop._∧_ (ObsLe∂Cosp B p q) (ObsLe∂Cosp B q p))
≈∂Cosp↔ObsLe B {p} {q} =
  Prop.ObsEqOn↔ObsLeOn {Sat = λ c p' → BoundaryIO.Sat∂ B p' c} {x = p} {y = q}

Respects≈∂Cosp[_]
  : ∀ {ℓ}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  → (B : BoundaryIO Sig Q W BB H)
  → (LogOSSignature.∂Cosp Sig → LogOSSignature.∂Cosp Sig)
  → Set ℓ
Respects≈∂Cosp[ B ] F =
  Prop.RespectsObsEqOn (λ c p → BoundaryIO.Sat∂ B p c) F

-- Telemetry trace preorder (full ConPreorder).

record TelemetryTrace (ℓT : Level) : Set (lsuc ℓT) where
  field
    trace : ConPreorder ℓT
  open ConPreorder trace public
    renaming (Con to Trace; _⊑_ to _⊑T_; refl to reflT; trans to transT)

Trace≈
  : ∀ {ℓT}
  → (T : TelemetryTrace ℓT)
  → TelemetryTrace.Trace T
  → TelemetryTrace.Trace T
  → Set ℓT
Trace≈ T x y =
  _≈CP_ (TelemetryTrace.trace T) x y

Trace≈-refl
  : ∀ {ℓT}
  → (T : TelemetryTrace ℓT)
  → (x : TelemetryTrace.Trace T)
  → Trace≈ T x x
Trace≈-refl T x = ≈CP-refl (TelemetryTrace.trace T) x

Trace≈-sym
  : ∀ {ℓT}
    {T : TelemetryTrace ℓT}
    {x y : TelemetryTrace.Trace T}
  → Trace≈ T x y
  → Trace≈ T y x
Trace≈-sym {T = T} = ≈CP-sym {CP = TelemetryTrace.trace T}

Trace≈-trans
  : ∀ {ℓT}
    {T : TelemetryTrace ℓT}
    {x y z : TelemetryTrace.Trace T}
  → Trace≈ T x y
  → Trace≈ T y z
  → Trace≈ T x z
Trace≈-trans {T = T} = ≈CP-trans {CP = TelemetryTrace.trace T}

-- Telemetry port for boundary constraints (Con_bnd).
--
-- Telemetry is observation-only: these ports never change kernel semantics.

record BoundaryTelemetryPort {ℓ ℓT}
                             (Sig : LogOSSignature ℓ)
                             (Q   : QAdapter ℓ)
                             (W   : Worlds.WorldH Sig Q)
                             (BB  : BulkBoundary ℓ)
                             (H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB)
                             (B   : BoundaryIO Sig Q W BB H)
                             (T   : TelemetryTrace ℓT)
                             : Set (lsuc (ℓ ⊔ ℓT)) where
  open BulkBoundary BB
  open TelemetryTrace T
  field
    observe-bnd : Con_bnd → Trace
    observe-bnd-mono
      : MonoMap bnd (TelemetryTrace.trace T) observe-bnd
    observe-bnd-respects
      : ∀ {c d}
      → c ≈∂[ B ] d
      → Trace≈ T (observe-bnd c) (observe-bnd d)

telemetry-respects-≈∂
  : ∀ {ℓ ℓT}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    {B : BoundaryIO Sig Q W BB H}
    {T : TelemetryTrace ℓT}
  → (P : BoundaryTelemetryPort Sig Q W BB H B T)
  → ∀ {c d}
  → c ≈∂[ B ] d
  → Trace≈ T (BoundaryTelemetryPort.observe-bnd P c)
               (BoundaryTelemetryPort.observe-bnd P d)
telemetry-respects-≈∂ P = BoundaryTelemetryPort.observe-bnd-respects P

-- Telemetry port for boundary programs (∂Cosp).

record ProgramTelemetryPort {ℓ ℓT}
                            (Sig : LogOSSignature ℓ)
                            (Q   : QAdapter ℓ)
                            (W   : Worlds.WorldH Sig Q)
                            (BB  : BulkBoundary ℓ)
                            (H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB)
                            (B   : BoundaryIO Sig Q W BB H)
                            (T   : TelemetryTrace ℓT)
                            : Set (lsuc (ℓ ⊔ ℓT)) where
  open LogOSSignature Sig
  open TelemetryTrace T
  field
    observe-∂ : ∂Cosp → Trace
    observe-∂-mono
      : MonoMap (ObsCospPreorder B) (TelemetryTrace.trace T) observe-∂
    observe-∂-respects
      : ∀ {p q}
      → p ≈∂Cosp[ B ] q
      → Trace≈ T (observe-∂ p) (observe-∂ q)

telemetry-respects-≈∂Cosp
  : ∀ {ℓ ℓT}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    {B : BoundaryIO Sig Q W BB H}
    {T : TelemetryTrace ℓT}
  → (P : ProgramTelemetryPort Sig Q W BB H B T)
  → ∀ {p q}
  → p ≈∂Cosp[ B ] q
  → Trace≈ T (ProgramTelemetryPort.observe-∂ P p)
               (ProgramTelemetryPort.observe-∂ P q)
telemetry-respects-≈∂Cosp P = ProgramTelemetryPort.observe-∂-respects P

observe-∂-respects-from-mono
  : ∀ {ℓ ℓT}
    {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {W : Worlds.WorldH Sig Q} {BB : BulkBoundary ℓ}
    {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
    {B : BoundaryIO Sig Q W BB H}
    {T : TelemetryTrace ℓT}
  → (obs : LogOSSignature.∂Cosp Sig → TelemetryTrace.Trace T)
  → MonoMap (ObsCospPreorder B) (TelemetryTrace.trace T) obs
  → {p q : LogOSSignature.∂Cosp Sig}
  → p ≈∂Cosp[ B ] q
  → Trace≈ T (obs p) (obs q)
observe-∂-respects-from-mono {B = B} {T = T} obs mono {p} {q} eq =
  let (pq , qp) = Prop._↔_.to (≈∂Cosp↔ObsLe B {p} {q}) eq in
  (mono pq , mono qp)

-- Combined telemetry port: shared trace carrier for both legs.

record TelemetryPort {ℓ ℓT}
                     (Sig : LogOSSignature ℓ)
                     (Q   : QAdapter ℓ)
                     (W   : Worlds.WorldH Sig Q)
                     (BB  : BulkBoundary ℓ)
                     (H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB)
                     (B   : BoundaryIO Sig Q W BB H)
                     : Set (lsuc (ℓ ⊔ ℓT)) where
  field
    TraceT : TelemetryTrace ℓT
    Bnd    : BoundaryTelemetryPort Sig Q W BB H B TraceT
    Prog   : ProgramTelemetryPort Sig Q W BB H B TraceT
