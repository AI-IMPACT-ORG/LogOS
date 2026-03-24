{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.PortReindexing.Strictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Equality-based pullback/reindexing helpers along `toLOG`.

open import LogOS.Prelude
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.Thin2Functor.Strictification using (StrictThin2Functor)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; DecoratedThin2Cat
  )
open import LogOS.LT.DisplayedThin2Cat.Strictification using
  ( reindexDisplayedStrictF
  ; weakenReindexDisplayedStrictF
  )

open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.LOG.Implementation2Cat.Core using (LOGᴳʳ; toLOG)

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.PortSigStrictification as PortSigStrictification
import LogOS.LT.Ports.PortStack.Raw as PortStackShadowing
import LogOS.LT.Ports.Template.Singleton2Cat as Template

private
  toLOGStrict
    : ∀ {ℓ ℓRel ℓCode : Level}
    → StrictThin2Functor
        (LOGᴳʳ {ℓ} {ℓRel} {ℓCode})
        (LOG {ℓ} {ℓRel} {ℓCode})
  toLOGStrict {ℓ} {ℓRel} {ℓCode} =
    record
      { F = toLOG {ℓ} {ℓRel} {ℓCode}
      ; id-pres≡ = λ {A} → refl
      ; comp-pres≡ = λ {A} {B} {C} _ _ → refl
      }

pullbackPortSigAlongToLOG
  : ∀ {ℓ ℓRel ℓCode : Level}
    {ℓTag : Level} {Tag : Set ℓTag}
  → PortSig.PortSig (LOG {ℓ} {ℓRel} {ℓCode}) Tag
  → PortSig.PortSig (LOGᴳʳ {ℓ} {ℓRel} {ℓCode}) Tag
pullbackPortSigAlongToLOG {ℓ} {ℓRel} {ℓCode} =
  PortSigStrictification.pullbackPortSig (toLOGStrict {ℓ} {ℓRel} {ℓCode})

pullbackPortEntryAlongToLOG
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortSig.PortEntry (LOG {ℓ} {ℓRel} {ℓCode})
  → PortSig.PortEntry (LOGᴳʳ {ℓ} {ℓRel} {ℓCode})
pullbackPortEntryAlongToLOG {ℓ} {ℓRel} {ℓCode} =
  PortSigStrictification.pullbackPortEntry (toLOGStrict {ℓ} {ℓRel} {ℓCode})

pullbackPortStackAlongToLOG
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortStackShadowing.PortStack (LOG {ℓ} {ℓRel} {ℓCode})
  → PortStackShadowing.PortStack (LOGᴳʳ {ℓ} {ℓRel} {ℓCode})
pullbackPortStackAlongToLOG {ℓ} {ℓRel} {ℓCode} =
  PortStackShadowing.pullbackPortStack (toLOGStrict {ℓ} {ℓRel} {ℓCode})

module PullbackSingletonExportsAlongToLOG
  {ℓ ℓRel ℓCode : Level}
  {ℓTag : Level} {Tag : Set ℓTag}
  (sig : PortSig.PortSig (LOG {ℓ} {ℓRel} {ℓCode}) Tag)
  =
  Template.SingletonExports
    (pullbackPortSigAlongToLOG sig)

weakenDecoratedAlongToLOG
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom}
  → (D : DisplayedThin2Cat (LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom)
  → Thin2Functor
      (DecoratedThin2Cat (reindexDisplayedStrictF (toLOGStrict {ℓ} {ℓRel} {ℓCode}) D))
      (DecoratedThin2Cat D)
weakenDecoratedAlongToLOG {ℓ} {ℓRel} {ℓCode} =
  weakenReindexDisplayedStrictF (toLOGStrict {ℓ} {ℓRel} {ℓCode})
