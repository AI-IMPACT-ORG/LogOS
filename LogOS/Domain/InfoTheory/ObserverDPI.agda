{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.InfoTheory.ObserverDPI where

-- DPI as monotonicity along observer channels.

open import LogOS.Prelude

open import LogOS.Minimal.Con using (ConPoset)
import LogOS.Domain.Complexity.DataProcessingInequality as DPI

record ObserverChannel
  {ℓObs ℓI : Level}
  (Obs : Set ℓObs)
  (IP  : ConPoset ℓI)
  (info : Obs → ConPoset.Con IP)
  : Set (lsuc (ℓObs ⊔ ℓI)) where
  open ConPoset IP
  field
    run : Obs → Obs
    nonincreasing : ∀ o → _⊑_ (info (run o)) (info o)

module AsDPI
  {ℓObs ℓI : Level}
  {Obs : Set ℓObs}
  (IP : ConPoset ℓI)
  (info : Obs → ConPoset.Con IP)
  where

  open ConPoset IP

  channels : DPI.ChannelFamily Obs
  channels =
    record
      { Ch  = ObserverChannel Obs IP info
      ; run = ObserverChannel.run
      }

  dpi : DPI.DPIOn Obs channels IP
  dpi =
    record
      { info = info
      ; dpi  = λ C o → ObserverChannel.nonincreasing C o
      }
