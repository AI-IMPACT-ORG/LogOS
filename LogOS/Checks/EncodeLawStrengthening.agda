{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.EncodeLawStrengthening where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)
open import LogOS.LT.Kernel using (Kernel; BoundaryKernel; EncodePort)
open import LogOS.LT.Hom.Core using (idKernelHom)

import LogOS.LT.LOG.EncodePort2Cat as EncodeLaw
import LogOS.LT.LOG.EncodePort2Cat.Coherence as EncodeCoherence

K : Kernel lzero lzero lzero
K = BoundaryKernel UnitPreorder₀

EK : EncodePort K
EK = record { encode = λ c → c }

_ : EncodeLaw.EncodeLaw (idKernelHom K) EK EK
_ = EncodeCoherence.coherence→law (EncodeCoherence.idEncodeCoherence EK)
