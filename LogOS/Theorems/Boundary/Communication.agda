{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Communication where

-- Communication-facing theorems: compose the kernel’s truth transport with an
-- external boundary semantics bridge, and expose “code → boundary → form”
-- as a single auditable pipeline.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop

open import LogOS.Kernel
open import LogOS.Boundary.FromKernel
open import LogOS.Boundary.IO
open import LogOS.Boundary.Semantics

module ForKernel
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {ℓForm : Level}
  (K : Kernel Sig Q)
  (S : BoundarySemantics {ℓForm = ℓForm}
        Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) (boundaryIO K))
  where

  open LogOSSignature Sig
  open Kernel K
  open BoundarySemantics S

  private
    B : _
    B = boundaryIO K

    Flow∂ : _
    Flow∂ = GTier.Flow G (GTier.step G)

  -- One-shot “operationalisation”: strict truth transports to an external
  -- boundary form through the kernel’s translation/coherence and the supplied
  -- boundary semantics equivalence.

  SatS↔Form
    : ∀ (w : Cosp) (φ : Fml)
    → Prop._↔_ (Truth.StrictTruth.StrictLayer.Sat_S Strict w φ)
               (SatF (BoundaryIO.to∂ B w) (Interp (TransH φ)))
  SatS↔Form w φ = record
    { to = λ satS →
        let
          lh  = coh-LH w φ
          h   = Prop._↔_.to lh satS
          hb  = Prop._↔_.to (BoundaryIO.sat-coh B w (TransH φ)) h
          ext = Prop._↔_.to (Sat∂≈F (BoundaryIO.to∂ B w) (TransH φ)) hb
        in ext
    ; from = λ satF →
        let
          hb  = Prop._↔_.from (Sat∂≈F (BoundaryIO.to∂ B w) (TransH φ)) satF
          h   = Prop._↔_.from (BoundaryIO.sat-coh B w (TransH φ)) hb
          satS = Prop._↔_.from (coh-LH w φ) h
        in satS
    }

  -- Externalised meaning of a code value (interpret its decoded boundary
  -- constraint as an external boundary form).

  Code→Form : Code → Form
  Code→Form γ = Interp (decode γ)

  -- Channel-commutation at the externalised level: external meaning after one
  -- code-step agrees with external meaning of the induced boundary step.

  Code→Form-FlowCode
    : ∀ (γ : Code)
    → Code→Form (FlowCode K γ)
      ≡ Interp (Flow∂ (Body∂ (decode γ)))
  Code→Form-FlowCode γ =
    -- The actual commutation is: Interp (decode (FlowCode γ)) ≡ Interp (Flow (Body∂ (decode γ))).
    -- We phrase it via `decode-FlowCode` and apply `cong Interp`.
    cong Interp (decode-FlowCode K γ)

  -- Semantic form (recommended): commutation as satisfaction equivalence.

  Code→Form-FlowCode-Sat
    : ∀ (p : ∂Cosp) (γ : Code)
    → Prop._↔_ (SatF p (Code→Form (FlowCode K γ)))
               (SatF p (Interp (Flow∂ (Body∂ (decode γ)))))
  Code→Form-FlowCode-Sat p γ =
    let e = Code→Form-FlowCode γ in
    record
      { to   = λ sat → subst (SatF p) e sat
      ; from = λ sat → subst (SatF p) (sym e) sat
      }

-- Convenient top-level wrappers (avoid opening the parameterised module).

SatS↔Form
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {ℓForm : Level}
    (K : Kernel Sig Q)
    (S : BoundarySemantics {ℓForm = ℓForm}
          Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) (boundaryIO K))
    (w : LogOSSignature.Cosp Sig)
    (φ : Kernel.Fml K)
  → Prop._↔_ (Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict K) w φ)
             (BoundarySemantics.SatF S (BoundaryIO.to∂ (boundaryIO K) w)
               (BoundarySemantics.Interp S (Kernel.TransH K φ)))
SatS↔Form K S w φ = ForKernel.SatS↔Form K S w φ

Code→Form
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {ℓForm : Level}
    (K : Kernel Sig Q)
    (S : BoundarySemantics {ℓForm = ℓForm}
          Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) (boundaryIO K))
  → Kernel.Code K → BoundarySemantics.Form S
Code→Form K S = ForKernel.Code→Form K S

Code→Form-FlowCode
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {ℓForm : Level}
    (K : Kernel Sig Q)
    (S : BoundarySemantics {ℓForm = ℓForm}
          Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) (boundaryIO K))
    (γ : Kernel.Code K)
  → Code→Form K S (FlowCode K γ)
    ≡ BoundarySemantics.Interp S
        (GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
          (Kernel.Body∂ K (Kernel.decode K γ)))
Code→Form-FlowCode K S γ = ForKernel.Code→Form-FlowCode K S γ

Code→Form-FlowCode-Sat
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {ℓForm : Level}
    (K : Kernel Sig Q)
    (S : BoundarySemantics {ℓForm = ℓForm}
          Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) (boundaryIO K))
    (p : LogOSSignature.∂Cosp Sig)
    (γ : Kernel.Code K)
  → Prop._↔_
      (BoundarySemantics.SatF S p (Code→Form K S (FlowCode K γ)))
      (BoundarySemantics.SatF S p
        (BoundarySemantics.Interp S
          (GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
            (Kernel.Body∂ K (Kernel.decode K γ)))))
Code→Form-FlowCode-Sat K S p γ = ForKernel.Code→Form-FlowCode-Sat K S p γ

-- ---------------------------------------------------------------------------
-- Communicative aliases (paper-friendly names).
-- ---------------------------------------------------------------------------

operationalise-strict
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {ℓForm : Level}
    (K : Kernel Sig Q)
    (S : BoundarySemantics {ℓForm = ℓForm}
          Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) (boundaryIO K))
    (w : LogOSSignature.Cosp Sig)
    (φ : Kernel.Fml K)
  → Prop._↔_ (Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict K) w φ)
             (BoundarySemantics.SatF S (BoundaryIO.to∂ (boundaryIO K) w)
               (BoundarySemantics.Interp S (Kernel.TransH K φ)))
operationalise-strict = SatS↔Form

code-channel-commutes
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {ℓForm : Level}
    (K : Kernel Sig Q)
    (S : BoundarySemantics {ℓForm = ℓForm}
          Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K) (boundaryIO K))
    (γ : Kernel.Code K)
  → Code→Form K S (FlowCode K γ)
    ≡ BoundarySemantics.Interp S
        (GTier.Flow (Kernel.G K) (GTier.step (Kernel.G K))
          (Kernel.Body∂ K (Kernel.decode K γ)))
code-channel-commutes = Code→Form-FlowCode

code-channel-commutes-Sat = Code→Form-FlowCode-Sat
