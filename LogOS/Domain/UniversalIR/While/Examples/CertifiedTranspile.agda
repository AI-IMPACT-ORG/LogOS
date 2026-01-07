{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.While.Examples.CertifiedTranspile where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Core using (MinskyCode; EVMCode)
open import LogOS.Domain.UniversalIR.While.Compile
open import LogOS.Domain.UniversalIR.While.Decompile
open import LogOS.Domain.UniversalIR.While.Examples.Factorial using (n₅; outM₅; outE₅; outM₅≡outE₅; outM₅≡120; outE₅≡120)

open import Data.Maybe using (Maybe; just; nothing)

-- EXAMPLE (argument): compilation/transpilation diagram checks between multiple backends.

-- Compile a factorial task to Minsky, decompile it (with a certificate),
-- and recompile to Ethereum.

task : FactTask
task = mkFact n₅

mCode : MinskyCode
mCode = compileMinsky task

decompileM-ok : decompileMinsky mCode ≡ just (task , refl)
decompileM-ok = refl

eMaybe : Maybe EVMCode
eMaybe = transpileMinsky→Ethereum mCode

eCode : EVMCode
eCode = compileEthereum task

eMaybe-ok : eMaybe ≡ just eCode
eMaybe-ok rewrite decompileM-ok = refl

-- Round-trip back (EVM → Minsky) on the compiler image.

mMaybe : Maybe MinskyCode
mMaybe = transpileEthereum→Minsky eCode

mMaybe-ok : mMaybe ≡ just mCode
mMaybe-ok = refl

-- Decompile again: the transpiled EVM code yields the same source task.

decompileE-ok : decompileEthereum eCode ≡ just (task , refl)
decompileE-ok = refl

-- “Decompile twice”: decompilation is idempotent on the compiler image.

decompileM-twice : decompileMinsky (compileMinsky task) ≡ just (task , refl)
decompileM-twice = refl

decompileE-twice : decompileEthereum (compileEthereum task) ≡ just (task , refl)
decompileE-twice = refl

-- Non-trivial runtime agreement (factorial 5 = 120), via the shared runner.

outM≡outE : outM₅ ≡ outE₅
outM≡outE = outM₅≡outE₅

outM≡120 : outM₅ ≡ 120
outM≡120 = outM₅≡120

outE≡120 : outE₅ ≡ 120
outE≡120 = outE₅≡120
