{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.While.Decompile where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Core
open import LogOS.Domain.UniversalIR.Std using (==ℕ-true→≡)
open import LogOS.Domain.UniversalIR.While.Compile

open import LogOS.Prelude.Bool using (Bool; true; false)
open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.Prelude.Maybe using (Maybe; just; nothing)

-- Decompilation “by construction”: return a source task together with a proof
-- that recompiling it yields (a chosen normal form of) the target code.

DecompilesTo : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → (A → B) → (B → B) → B → Set (ℓA ⊔ ℓB)
DecompilesTo {A = A} compile norm b = Σ A (λ a → compile a ≡ norm b)

id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

inspect : ∀ {ℓ} {A : Set ℓ} → (x : A) → Σ A (λ y → x ≡ y)
inspect x = x , refl

-- 1) Minsky: exact decompilation for the factorial compiler image ------------

decompileMinsky : (c : MinskyCode) → Maybe (DecompilesTo compileMinsky id c)
decompileMinsky
  (mkM 7 0 0 n 0
    (DECJZ R1 1 6 ∷
     DECJZ R2 2 4 ∷
     INC R0 3 ∷
     INC R3 1 ∷
     DECJZ R3 5 0 ∷
     INC R2 4 ∷
     DECJZ R3 11 11 ∷
     INC R1 8 ∷
     DECJZ R2 9 14 ∷
     INC R2 10 ∷
     DECJZ R3 0 0 ∷
     DECJZ R0 12 13 ∷
     INC R1 11 ∷
     DECJZ R2 8 8 ∷
     DECJZ R1 15 16 ∷
     INC R0 14 ∷
     HALT ∷ [])) =
  just (mkFact n , refl)
{-# CATCHALL #-}
decompileMinsky _ = nothing

-- 2) Ethereum: close away the memory function ---------------------------
--
-- Memory is a function in this minimal EVM model. For factorial, the program
-- initializes the memory cells it uses (0 and 1), so the initial memory is
-- irrelevant; decompilation can therefore return a normal form that fixes it.

stripMem : EVMCode → EVMCode
stripMem (mkE pc stk _ code) = mkE pc stk mem0 code

decompileEthereum : (c : EVMCode) → Maybe (DecompilesTo compileEthereum stripMem c)
decompileEthereum
  (mkE 0 [] m
    (PUSH 1 ∷ PUSH 0 ∷ MSTORE ∷
     PUSH n ∷ PUSH 1 ∷ MSTORE ∷
     PUSH 1 ∷ MLOAD ∷ PUSH body ∷ JUMPI ∷
     PUSH end ∷ JUMP ∷
     PUSH 1 ∷ MLOAD ∷ PUSH 0 ∷ MLOAD ∷ MUL ∷ PUSH 0 ∷ MSTORE ∷
     PUSH 1 ∷ MLOAD ∷ PUSH 1 ∷ SUB ∷ PUSH 1 ∷ MSTORE ∷
     PUSH loop ∷ JUMP ∷
     PUSH 0 ∷ MLOAD ∷ STOP ∷ []))
  with inspect (body ==ℕ 12) | inspect (end ==ℕ 27) | inspect (loop ==ℕ 6)
... | true  , body≡true | true , end≡true | true , loop≡true
  rewrite ==ℕ-true→≡ body 12 body≡true
        | ==ℕ-true→≡ end 27 end≡true
        | ==ℕ-true→≡ loop 6 loop≡true
        = just (mkFact n , refl)
{-# CATCHALL #-}
... | _ | _ | _ = nothing
{-# CATCHALL #-}
decompileEthereum _ = nothing

-- Derived transpilers between paradigms for this fragment -------------------

transpileMinsky→Ethereum : MinskyCode → Maybe EVMCode
transpileMinsky→Ethereum c with decompileMinsky c
... | just (t , _) = just (compileEthereum t)
... | nothing      = nothing

transpileEthereum→Minsky : EVMCode → Maybe MinskyCode
transpileEthereum→Minsky c with decompileEthereum c
... | just (t , _) = just (compileMinsky t)
... | nothing      = nothing
