{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.QuoteLawStrengthening where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)
open import LogOS.LT.Flow using (idClosure)
open import LogOS.LT.Hom.Core using (idKernelHom)

import LogOS.LT.LOG.QuotePort2Cat.Port as QuotePort
import LogOS.LT.LOG.QuotePort2Cat.Displayed as QuoteLaw
import LogOS.LT.LOG.QuotePort2Cat.Coherence as QuoteCoherence

GC = idClosure UnitPreorder₀

K = QuotePort.quoteKernel GC

QP = QuotePort.quotePort GC

_ : QuoteLaw.QuoteLaw (idKernelHom K) QP QP
_ = QuoteCoherence.coherence→law (QuoteCoherence.idQuoteCoherence QP)
