{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.InfoTheory.ObserverDPI where

-- DPI as monotonicity along observer channels.

open import LogOS.Prelude

open import LogOS.Minimal.Con using (ConPreorder)
import LogOS.Complexity.DataProcessingInequality as DPI

record ObserverChannel
  {ℓObs ℓI : Level}
  (Obs : Set ℓObs)
  (IP  : ConPreorder ℓI)
  (info : Obs → ConPreorder.Con IP)
  : Set (lsuc (ℓObs ⊔ ℓI)) where
  open ConPreorder IP
  field
    run : Obs → Obs
    nonincreasing : ∀ o → _⊑_ (info (run o)) (info o)

module AsDPI
  {ℓObs ℓI : Level}
  {Obs : Set ℓObs}
  (IP : ConPreorder ℓI)
  (info : Obs → ConPreorder.Con IP)
  where

  open ConPreorder IP

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
