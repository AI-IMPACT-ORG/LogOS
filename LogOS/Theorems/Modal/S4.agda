{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Modal.S4 where

-- A very small, very general “S4 modality” package for LogOS:
-- a monotone, inflationary, idempotent-lax endomap on a preorder.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; PartialOrder)
open import LogOS.Minimal.Closure using (ClosureOp)
import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel using (Kernel; BoxClosure)
open import LogOS.Kernel.Core as KCore hiding (FlowCode)
open import LogOS.Kernel.Graded using (GradedKernel) renaming (BoxClosure to BoxClosureG)
open import LogOS.Kernel.LogicKernel using (LogicKernel) renaming (BoxClosure to BoxClosureLK)

open import LogOS.Theorems.Reflection.Projector using (Projector; ProjectorMono; projectorMonoOfClosureOp)

record S4Modality {ℓ : Level} (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
  open ConPreorder CP
  field
    □        : Con → Con
    mono     : ∀ {c c'} → _⊑_ c c' → _⊑_ (□ c) (□ c')
    infl     : ∀ c → _⊑_ c (□ c)          -- T axiom
    idemp-lax : ∀ c → _⊑_ (□ (□ c)) (□ c) -- 4 axiom (lax)

open S4Modality public

-- Idempotence “both ways” is derivable once monotonicity + inflation are present.

idemp-infl
  : ∀ {ℓ} {CP : ConPreorder ℓ} (M : S4Modality CP)
    (c : ConPreorder.Con CP)
  → ConPreorder._⊑_ CP (□ M c) (□ M (□ M c))
idemp-infl {CP = CP} M c =
  let open ConPreorder CP
  in mono M (infl M c)

-- A grade-indexed closure yields an S4 modality at the saturation grade `sat`.

fromGradedSat
  : ∀ {ℓ} {Q : QAdapter ℓ} {CP : ConPreorder ℓ}
    (G : Truth.GuardedCore.GradedClosure Q CP)
  → S4Modality CP
fromGradedSat {CP = CP} G =
  let open ConPreorder CP
      open Truth.GuardedCore.GradedClosure G renaming (mono to monoFlow)
  in record
    { □        = Flow sat
    ; mono     = monoFlow
    ; infl     = infl-sat
    ; idemp-lax = idemp-sat
    }

-- Any grade can be promoted to saturation (general grade-shift lemma).

promoteToSat
  : ∀ {ℓ} {Q : QAdapter ℓ} {CP : ConPreorder ℓ}
    (G : Truth.GuardedCore.GradedClosure Q CP)
  → ∀ g c
  → ConPreorder._⊑_ CP
      (Truth.GuardedCore.GradedClosure.Flow G g c)
      (Truth.GuardedCore.GradedClosure.Flow G (Truth.GuardedCore.GradedClosure.sat G) c)
promoteToSat {CP = CP} G g c =
  let open ConPreorder CP
      open Truth.GuardedCore.GradedClosure G
  in mono-grade (sat-top g) c

-- Any (unguarded) closure step yields an S4 modality on the same constraint preorder.

fromGuardedClosure
  : ∀ {ℓ} {CP : ConPreorder ℓ}
    (G : Truth.GuardedCore.GuardedClosure CP)
  → S4Modality CP
fromGuardedClosure {CP = CP} G =
  let open ConPreorder CP
      open Truth.GuardedCore.GuardedClosure G renaming (mono to monoFlow; infl to inflFlow; idemp-lax to idempFlow)
  in record
    { □        = Flow
    ; mono     = monoFlow
    ; infl     = inflFlow
    ; idemp-lax = idempFlow
    }

-- The distinguished fixed point witness is a modal fixed point (up to mutual refinement).

Th*-fixed-s4
  : ∀ {ℓ} {CP : ConPreorder ℓ}
    (G : Truth.GuardedCore.GuardedClosure CP)
  → let M = fromGuardedClosure G in
    ConPreorder._⊑_ CP (Truth.GuardedCore.GuardedClosure.Th* G) (□ M (Truth.GuardedCore.GuardedClosure.Th* G))
    ×
    ConPreorder._⊑_ CP (□ M (Truth.GuardedCore.GuardedClosure.Th* G)) (Truth.GuardedCore.GuardedClosure.Th* G)
Th*-fixed-s4 {CP = CP} G =
  let open Truth.GuardedCore.GuardedClosure G
  in Th*-fixed

-- Forgetful view: any S4 modality yields a (lax) projector by dropping monotonicity.

toProjector : ∀ {ℓ} {CP : ConPreorder ℓ} → S4Modality CP → Projector CP
toProjector M = record
  { P = □ M
  ; infl = infl M
  ; idemp-lax = idemp-lax M
  }

-- Conversions / connective tissue ------------------------------------------------

fromClosureOp : ∀ {ℓ} {CP : ConPreorder ℓ} → ClosureOp CP → S4Modality CP
fromClosureOp C =
  record
    { □ = ClosureOp.cl C
    ; mono = ClosureOp.mono C
    ; infl = ClosureOp.infl C
    ; idemp-lax = ClosureOp.idemp-lax C
    }

toClosureOp : ∀ {ℓ} {CP : ConPreorder ℓ} → S4Modality CP → ClosureOp CP
toClosureOp M =
  record
    { cl = □ M
    ; mono = mono M
    ; infl = infl M
    ; idemp-lax = idemp-lax M
    }

toProjectorMono : ∀ {ℓ} {CP : ConPreorder ℓ} → S4Modality CP → ProjectorMono CP
toProjectorMono M =
  record
    { core = toProjector M
    ; mono-P = mono M
    }

fromProjectorMono : ∀ {ℓ} {CP : ConPreorder ℓ} → ProjectorMono CP → S4Modality CP
fromProjectorMono PM =
  record
    { □ = Projector.P (ProjectorMono.core PM)
    ; mono = ProjectorMono.mono-P PM
    ; infl = Projector.infl (ProjectorMono.core PM)
    ; idemp-lax = Projector.idemp-lax (ProjectorMono.core PM)
    }

toProjectorMono-fromClosureOp
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → ClosureOp CP → ProjectorMono CP
toProjectorMono-fromClosureOp = projectorMonoOfClosureOp

-- Kernel-facing constructors ---------------------------------------------------
--
-- These are cheap “capitalisation” helpers: once the kernel exposes Box as a
-- closure modality on code, we can immediately reuse the generic S4 toolkit.

fromKernelBox
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → S4Modality (KCore.CodePreorder (Kernel.shape K))
fromKernelBox K = fromClosureOp (BoxClosure K)

fromGradedKernelBox
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → S4Modality (KCore.CodePreorder (GradedKernel.shape K))
fromGradedKernelBox K = fromClosureOp (BoxClosureG K)

fromLogicKernelBox
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → S4Modality (KCore.CodePreorder (LogicKernel.shape K))
fromLogicKernelBox K = fromClosureOp (BoxClosureLK K)

-- Round-trip simp lemmas ------------------------------------------------------

toClosureOp∘fromClosureOp
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → (C : ClosureOp CP)
  → toClosureOp (fromClosureOp C) ≡ C
toClosureOp∘fromClosureOp _ = refl

fromClosureOp∘toClosureOp
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → (M : S4Modality CP)
  → fromClosureOp (toClosureOp M) ≡ M
fromClosureOp∘toClosureOp _ = refl

toProjectorMono∘fromProjectorMono
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → (PM : ProjectorMono CP)
  → toProjectorMono (fromProjectorMono PM) ≡ PM
toProjectorMono∘fromProjectorMono _ = refl

fromProjectorMono∘toProjectorMono
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → (M : S4Modality CP)
  → fromProjectorMono (toProjectorMono M) ≡ M
fromProjectorMono∘toProjectorMono _ = refl

-- Antisymmetry upgrade --------------------------------------------------------

idemp≡
  : ∀ {ℓ} {CP : ConPreorder ℓ}
  → PartialOrder CP
  → (M : S4Modality CP)
  → (c : ConPreorder.Con CP)
  → □ M (□ M c) ≡ □ M c
idemp≡ {CP = CP} po M c =
  PartialOrder.antisym po (idemp-lax M c) (idemp-infl M c)
