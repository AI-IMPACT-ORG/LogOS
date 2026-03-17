{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.SetMM.Parse.Wff where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  ; _>>=_
  ; Unit
  ; Cmp
  ; cmpNat
  ; _++_
  ; contains
  ; lookupAt
  ; lookupIx
  ; len
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Sig using
  ( Sig
  ; tc⊢
  ; tcWff
  ; tcSet
  ; tokLParen
  ; tokRParen
  ; tokImp
  ; tokAnd
  ; tokOr
  ; tokIff
  ; tokNot
  ; tokAll
  ; tokEx
  ; tokBot
  ; tokIn
  ; tokEq
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Vars using (Vars; wffVars; setVars)
open import LogOS.Apps.ZFC.Metamath.SetMM.Syntax using
  ( PFormula
  ; metaF
  ; botF
  ; notPF
  ; _∈PF_
  ; _≈PF_
  ; _⇒PF_
  ; _∧PF_
  ; _∨PF_
  ; _↔PF_
  ; ∀PF
  ; ∃PF
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Parse.Support using
  ( Split
  ; BinOp
  ; mkImp
  ; mkAnd
  ; mkOr
  ; mkIff
  ; classifyBinOp
  ; splitAtom
  ; splitTop
  ; stripOuterParens
  ; ParseRun
  ; mkParseRun
  ; exactParse
  ; Head
  ; hNot
  ; hAll
  ; hEx
  ; hOther
  ; headCase
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Parse.Term using (parseTermFuel)
open import LogOS.Apps.ZFC.Proof.Syntax as ZF using (Term)

-- Parsing implementation: bounded recursion on a fuel (token-length) parameter.
--
-- Keep this concrete `ℕ`-fueling here: it is a parser-depth budget tightly
-- coupled to token-splitting/parenthesis recursion and uses Agda-safe structural
-- recursion for termination.
-- A generic `FuelProfile` abstraction would obscure that coupling without any
-- additional portability benefit for this module.

parseNotFuel : Sig → Vars → List ℕ → ℕ → List ℕ → Maybe (ParseRun PFormula)

parseQuantFuel
  : Sig → Vars → List ℕ → ℕ → List ℕ → (ℕ → PFormula → PFormula) → Maybe (ParseRun PFormula)

parseAllFuel : Sig → Vars → List ℕ → ℕ → List ℕ → Maybe (ParseRun PFormula)

parseExFuel : Sig → Vars → List ℕ → ℕ → List ℕ → Maybe (ParseRun PFormula)

parseAtomicFuel : Sig → Vars → List ℕ → List ℕ → Maybe (ParseRun PFormula)

parseAtomicFuelLen1 : Sig → Vars → List ℕ → List ℕ → Maybe (ParseRun PFormula)

parseAtomicFuelLen2 : Sig → Vars → List ℕ → List ℕ → Maybe (ParseRun PFormula)

parseAtomicBinaryFuel : Sig → Vars → List ℕ → Maybe Term → Maybe Term → ℕ → Maybe (ParseRun PFormula)

parseOtherFuel : Sig → Vars → List ℕ → ℕ → List ℕ → Maybe (ParseRun PFormula)

parseParenFuel : Sig → Vars → List ℕ → ℕ → List ℕ → Maybe (ParseRun PFormula)

parseWffFuel
  : Sig
  → Vars
  → (env : List ℕ)   -- (bound vars ++ free vars), newest binder at head
  → (fuel : ℕ)
  → List ℕ
  → Maybe (ParseRun PFormula)
parseWffFuel S V env zero _ = nothing
parseWffFuel S V env (suc k) [] = nothing
parseWffFuel S V env (suc k) toks@(t ∷ ts) with headCase S t
... | hNot   = parseNotFuel S V env k ts
... | hAll   = parseAllFuel S V env k ts
... | hEx    = parseExFuel S V env k ts
... | hOther = parseOtherFuel S V env k toks

parseNotFuel S V env k xs with parseWffFuel S V env k xs
... | just φ = just (mkParseRun (notPF (ParseRun.value φ)) (ParseRun.rest φ))
... | nothing = nothing

parseQuantFuel S V env k toks q with toks
... | [] = nothing
... | x ∷ rest with contains x (setVars V)
... | nothing = nothing
... | just _ =
  parseWffFuel S V (x ∷ env) k rest >>= λ φ →
  just (mkParseRun (q x (ParseRun.value φ)) (ParseRun.rest φ))

parseAllFuel S V env k toks = parseQuantFuel S V env k toks ∀PF

parseExFuel S V env k toks = parseQuantFuel S V env k toks ∃PF

parseAtomicFuel S V env xs with len xs
... | zero = nothing
... | suc zero = parseAtomicFuelLen1 S V env xs
... | suc (suc n) = parseAtomicFuelLen2 S V env xs

parseAtomicFuelLen1 _ _ _ [] = nothing
parseAtomicFuelLen1 S V _ (x ∷ []) = stepBot (cmpNat x (tokBot S))
  where
    stepBot : Cmp → Maybe (ParseRun PFormula)
    stepMeta : Maybe Core.Unit → Maybe (ParseRun PFormula)

    stepBot Core.equal = just (mkParseRun botF [])
    stepBot Core.less = stepMeta (contains x (wffVars V))
    stepBot Core.greater = stepMeta (contains x (wffVars V))

    stepMeta (just _) = just (mkParseRun (metaF x) [])
    stepMeta nothing = nothing
parseAtomicFuelLen1 _ _ _ (_ ∷ _ ∷ _) = nothing

parseAtomicFuelLen2 S V env xs with splitAtom S xs
... | nothing = nothing
... | just sp =
  parseAtomicBinaryFuel
    S V env
    (exactParse (parseTermFuel S V env (len (Split.lhs sp)) (Split.lhs sp)))
    (exactParse (parseTermFuel S V env (len (Split.rhs sp)) (Split.rhs sp)))
    (Split.op sp)

parseAtomicBinaryFuel S _ _ (just tx) (just ty) op = stepIn (cmpNat op (tokIn S))
  where
    stepIn : Cmp → Maybe (ParseRun PFormula)
    stepEq : Cmp → Maybe (ParseRun PFormula)

    stepIn Core.equal = just (mkParseRun (tx ∈PF ty) [])
    stepIn Core.less = stepEq (cmpNat op (tokEq S))
    stepIn Core.greater = stepEq (cmpNat op (tokEq S))

    stepEq Core.equal = just (mkParseRun (tx ≈PF ty) [])
    stepEq Core.less = nothing
    stepEq Core.greater = nothing
parseAtomicBinaryFuel _ _ _ nothing (just _) _ = nothing
parseAtomicBinaryFuel _ _ _ (just _) nothing _ = nothing
parseAtomicBinaryFuel _ _ _ nothing nothing _ = nothing

parseOtherFuel S V env k xs with stripOuterParens S xs
... | just inner = parseParenFuel S V env k inner
... | nothing = parseAtomicFuel S V env xs

parseParenFuel S V env k inner with splitTop S inner
... | nothing = parseWffFuel S V env k inner
... | just sp = go (exactParse (parseWffFuel S V env k (Split.lhs sp))) (exactParse (parseWffFuel S V env k (Split.rhs sp)))
  where
    mkBin : BinOp → PFormula → PFormula → Maybe (ParseRun PFormula)
    mkBin mkImp φ ψ = just (mkParseRun (φ ⇒PF ψ) [])
    mkBin mkAnd φ ψ = just (mkParseRun (φ ∧PF ψ) [])
    mkBin mkOr φ ψ = just (mkParseRun (φ ∨PF ψ) [])
    mkBin mkIff φ ψ = just (mkParseRun (φ ↔PF ψ) [])

    go : Maybe PFormula → Maybe PFormula → Maybe (ParseRun PFormula)
    go (just φ) (just ψ) with classifyBinOp S (Split.op sp)
    ... | just op = mkBin op φ ψ
    ... | nothing = nothing
    go (just _) nothing = nothing
    go nothing (just _) = nothing
    go nothing nothing = nothing

parseWffBulk
  : Sig
  → Vars
  → (env : List ℕ)
  → List ℕ
  → Maybe (ParseRun PFormula)
parseWffBulk S V env xs = parseWffFuel S V env (len xs) xs

parseWff
  : Sig
  → Vars
  → (env : List ℕ)
  → List ℕ
  → Maybe PFormula
parseWff S V env xs = exactParse (parseWffBulk S V env xs)

-- Parse a full Metamath provable formula with residual tokens preserved.
parse⊢Bulk : Sig → Vars → (free : List ℕ) → List ℕ → Maybe (ParseRun PFormula)
parse⊢Bulk S V free [] = nothing
parse⊢Bulk S V free (tc ∷ ts) with cmpNat tc (tc⊢ S)
... | Core.equal = parseWffBulk S V free ts
... | Core.less = nothing
... | Core.greater = nothing

parse⊢ : Sig → Vars → (free : List ℕ) → List ℕ → Maybe PFormula
parse⊢ S V free ts = exactParse (parse⊢Bulk S V free ts)
