{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Quantum.Scalars.Free where

open import LogOS.Prelude hiding (_+_; _*_)

open import LogOS.UniversalIR.Core.QuantumCircuitAmp using (QScalars)

-- A purely syntactic scalar carrier (free algebra).
--
-- This is used to instantiate amplitude-level semantics without committing to a
-- specific numeric model.

infixl 6 _+F_
infixl 7 _*F_
infix  8 -F_

data FormalScalar : Set where
  0F 1F     : FormalScalar
  _+F_ _*F_ : FormalScalar → FormalScalar → FormalScalar
  -F_       : FormalScalar → FormalScalar
  conjF     : FormalScalar → FormalScalar
  invSqrt2F : FormalScalar
  invSqrtF  : FormalScalar → FormalScalar

formalScalars : QScalars {lzero}
formalScalars =
  record
    { Carrier  = FormalScalar
    ; 0#       = 0F
    ; 1#       = 1F
    ; _+_      = _+F_
    ; _*_      = _*F_
    ; -_       = -F_
    ; conj     = conjF
    ; invSqrt2 = invSqrt2F
    ; invSqrt  = invSqrtF
    }

