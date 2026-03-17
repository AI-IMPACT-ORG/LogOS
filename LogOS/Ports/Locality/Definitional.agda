{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Locality.Definitional where

open import LogOS.Prelude
import LogOS.Ports.Locality.Lifts as Lifts

pointwise≡→≈LocalBoundary = Lifts.pointwise≡→≈LocalBoundary
