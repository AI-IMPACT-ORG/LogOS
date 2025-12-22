{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.KernelUniversalProcess where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con using (ConPoset; BulkBoundary)
import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel
open import LogOS.Kernel.Graded

import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat

-- Kernel-as-process: expose the kernel’s canonical computation in two layers:
--
-- 1) Code process: state = `Kernel.Code`, step = `Guard ∘ Body`,
--    observation = `decode`.
-- 2) Boundary process: state = boundary constraints, step = `Flow ∘ Body∂`,
--    observation = identity.
--
-- The key link is definitional/explicit: `decode` transports the code step into
-- the boundary step via `guard-decode` + `body-decode`.

module ForKernel {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : Kernel Sig Q) where

  open Kernel K

  private
    CP∂ : ConPoset ℓ
    CP∂ = BulkBoundary.bnd BB

    module CP∂ = ConPoset CP∂

    Flow∂ : CP∂.Con → CP∂.Con
    Flow∂ = GT.GuardedClosure.Flow GTruth

    step∂ : CP∂.Con → CP∂.Con
    step∂ c = Flow∂ (Body∂ c)

    idClosure∂ : Sch.Closure CP∂
    idClosure∂ =
      record
        { normalize = λ c → c
        ; mono      = λ p → p
        ; infl      = λ c → CP∂.refl
        ; idemp-lax = λ c → CP∂.refl
        }

    -- Code carrier with the equality preorder (enough to talk about “a process”).
    CPCode : ConPoset ℓ
    CPCode =
      record
        { Con  = Code
        ; _⊑_  = _≡_
        ; refl = refl
        ; trans = trans
        }

    idClosureCode : Sch.Closure CPCode
    idClosureCode =
      record
        { normalize = λ c → c
        ; mono      = λ p → p
        ; infl      = λ _ → refl
        ; idemp-lax = λ _ → refl
        }

  BoundaryProcess : Cat.Process CP∂.Con
  BoundaryProcess =
    record
      { CP       = CP∂
      ; Step     = step∂
      ; Norm     = idClosure∂
      ; decode   = λ c → c
      ; Q        = Q
      ; stepCost = λ _ → QAdapter.e Q
      }

  CodeProcess : Cat.Process CP∂.Con
  CodeProcess =
    record
      { CP       = CPCode
      ; Step     = λ γ → Guard (Body γ)
      ; Norm     = idClosureCode
      ; decode   = decode
      ; Q        = Q
      ; stepCost = λ _ → QAdapter.e Q
      }

  decodeHom : Cat.ProcessHom CodeProcess BoundaryProcess
  decodeHom =
    record
      { map = decode
      ; mono = λ {x} {y} eq →
          subst (λ d → CP∂._⊑_ (decode x) d) (cong decode eq) CP∂.refl
      ; step-comm = λ γ →
          let
            step₁ : decode (Guard (Body γ)) ≡ Flow∂ (decode (Body γ))
            step₁ = guard-decode (Body γ)
            step₂ : decode (Body γ) ≡ Body∂ (decode γ)
            step₂ = body-decode γ
          in
          trans step₁ (cong Flow∂ step₂)
      ; norm-comm = λ _ → refl
      ; decode-comm = λ _ → refl
      }

-- Graded kernel-as-process: same story as `ForKernel`, but boundary evolution is
-- driven by the graded flow at the kernel’s chosen step grade (not necessarily
-- saturation). This makes “budgeted/graded computation” explicit at the process
-- level.

module ForGradedKernel {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (K : GradedKernel Sig Q) where

  open GradedKernel K

  private
    CP∂ : ConPoset ℓ
    CP∂ = BulkBoundary.bnd BB

    module CP∂ = ConPoset CP∂

    Flow∂At : QAdapter.Scale Q → CP∂.Con → CP∂.Con
    Flow∂At g = Truth.GuardedCore.GradedClosure.Flow GTruth g

    step∂ : CP∂.Con → CP∂.Con
    step∂ c = Flow∂At step-grade (Body∂ c)

    idClosure∂ : Sch.Closure CP∂
    idClosure∂ =
      record
        { normalize = λ c → c
        ; mono      = λ p → p
        ; infl      = λ _ → CP∂.refl
        ; idemp-lax = λ _ → CP∂.refl
        }

    CPCode : ConPoset ℓ
    CPCode =
      record
        { Con  = Code
        ; _⊑_  = _≡_
        ; refl = refl
        ; trans = trans
        }

    idClosureCode : Sch.Closure CPCode
    idClosureCode =
      record
        { normalize = λ c → c
        ; mono      = λ p → p
        ; infl      = λ _ → refl
        ; idemp-lax = λ _ → refl
        }

  BoundaryProcess : Cat.Process CP∂.Con
  BoundaryProcess =
    record
      { CP       = CP∂
      ; Step     = step∂
      ; Norm     = idClosure∂
      ; decode   = λ c → c
      ; Q        = Q
      ; stepCost = λ _ → step-grade
      }

  CodeProcess : Cat.Process CP∂.Con
  CodeProcess =
    record
      { CP       = CPCode
      ; Step     = λ γ → Guard (Body γ)
      ; Norm     = idClosureCode
      ; decode   = decode
      ; Q        = Q
      ; stepCost = λ _ → step-grade
      }

  decodeHom : Cat.ProcessHom CodeProcess BoundaryProcess
  decodeHom =
    record
      { map = decode
      ; mono = λ {x} {y} eq →
          subst (λ d → CP∂._⊑_ (decode x) d) (cong decode eq) CP∂.refl
      ; step-comm = λ γ →
          let
            step₁ : decode (Guard (Body γ)) ≡ Flow∂At step-grade (decode (Body γ))
            step₁ = guard-decode (Body γ)
            step₂ : decode (Body γ) ≡ Body∂ (decode γ)
            step₂ = body-decode γ
          in
          trans step₁ (cong (Flow∂At step-grade) step₂)
      ; norm-comm = λ _ → refl
      ; decode-comm = λ _ → refl
      }
