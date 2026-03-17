{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.SetMM.Parse.Support where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; nothing
  ; just
  ; Snoc
  ; unsnoc
  ; Cmp
  ; cmpNat
  ; predNat
  ; len
  ; reverse
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Sig using
  ( Sig
  ; tokLParen
  ; tokRParen
  ; tokImp
  ; tokAnd
  ; tokOr
  ; tokIff
  ; tokIn
  ; tokEq
  ; tokUnion
  ; tokPower
  ; tokSucc
  ; tokPair
  ; tokNot
  ; tokAll
  ; tokEx
  )

-- Split a token stream of the form `(<lhs> op <rhs>)` at the first top-level op.
record Split : Set where
  constructor split
  field
    lhs : List ℕ
    op  : ℕ
    rhs : List ℕ

data BinOp : Set where
  mkImp mkAnd mkOr mkIff : BinOp

classifyBinOp : Sig → ℕ → Maybe BinOp
classifyBinOp S t = goImp (cmpNat t (tokImp S))
  where
    goImp : Cmp → Maybe BinOp
    goAnd : Cmp → Maybe BinOp
    goOr : Cmp → Maybe BinOp
    goIff : Cmp → Maybe BinOp

    goImp Core.equal = just mkImp
    goImp Core.less = goAnd (cmpNat t (tokAnd S))
    goImp Core.greater = goAnd (cmpNat t (tokAnd S))

    goAnd Core.equal = just mkAnd
    goAnd Core.less = goOr (cmpNat t (tokOr S))
    goAnd Core.greater = goOr (cmpNat t (tokOr S))

    goOr Core.equal = just mkOr
    goOr Core.less = goIff (cmpNat t (tokIff S))
    goOr Core.greater = goIff (cmpNat t (tokIff S))

    goIff Core.equal = just mkIff
    goIff Core.less = nothing
    goIff Core.greater = nothing

data AtomRel : Set where
  mkIn mkEq : AtomRel

classifyAtomRel : Sig → ℕ → Maybe AtomRel
classifyAtomRel S t = goIn (cmpNat t (tokIn S))
  where
    goIn : Cmp → Maybe AtomRel
    goEq : Cmp → Maybe AtomRel

    goIn Core.equal = just mkIn
    goIn Core.less = goEq (cmpNat t (tokEq S))
    goIn Core.greater = goEq (cmpNat t (tokEq S))

    goEq Core.equal = just mkEq
    goEq Core.less = nothing
    goEq Core.greater = nothing

data TermOp : Set where
  mkUnion mkPower mkSucc mkPair : TermOp

classifyTermOp : Sig → ℕ → Maybe TermOp
classifyTermOp S t = goUnion (cmpNat t (tokUnion S))
  where
    goUnion : Cmp → Maybe TermOp
    goPower : Cmp → Maybe TermOp
    goSucc : Cmp → Maybe TermOp
    goPair : Cmp → Maybe TermOp

    goUnion Core.equal = just mkUnion
    goUnion Core.less = goPower (cmpNat t (tokPower S))
    goUnion Core.greater = goPower (cmpNat t (tokPower S))

    goPower Core.equal = just mkPower
    goPower Core.less = goSucc (cmpNat t (tokSucc S))
    goPower Core.greater = goSucc (cmpNat t (tokSucc S))

    goSucc Core.equal = just mkSucc
    goSucc Core.less = goPair (cmpNat t (tokPair S))
    goSucc Core.greater = goPair (cmpNat t (tokPair S))

    goPair Core.equal = just mkPair
    goPair Core.less = nothing
    goPair Core.greater = nothing

splitAtom
  : Sig
  → List ℕ
  → Maybe Split
splitAtom S xs = go zero [] xs
  where
    go : ℕ → List ℕ → List ℕ → Maybe Split
    go _ _ [] = nothing
    go d acc (t ∷ ts) = stepLParen (cmpNat t (tokLParen S))
      where
        stepLParen : Cmp → Maybe Split
        stepRParen : Cmp → Maybe Split
        stepDepth : Cmp → Maybe Split
        stepOp : Maybe AtomRel → Maybe Split

        stepLParen Core.equal = go (suc d) (t ∷ acc) ts
        stepLParen Core.less = stepRParen (cmpNat t (tokRParen S))
        stepLParen Core.greater = stepRParen (cmpNat t (tokRParen S))

        stepRParen Core.equal = go (predNat d) (t ∷ acc) ts
        stepRParen Core.less = stepDepth (cmpNat d zero)
        stepRParen Core.greater = stepDepth (cmpNat d zero)

        stepDepth Core.equal = stepOp (classifyAtomRel S t)
        stepDepth Core.less = go d (t ∷ acc) ts
        stepDepth Core.greater = go d (t ∷ acc) ts

        stepOp (just _) = just (split (reverse acc) t ts)
        stepOp nothing = go d (t ∷ acc) ts

splitTop
  : Sig
  → List ℕ
  → Maybe Split
splitTop S xs = go zero [] xs
  where
    go : ℕ → List ℕ → List ℕ → Maybe Split
    go _ _ [] = nothing
    go d acc (t ∷ ts) = stepLParen (cmpNat t (tokLParen S))
      where
        stepLParen : Cmp → Maybe Split
        stepRParen : Cmp → Maybe Split
        stepDepth : Cmp → Maybe Split
        stepOp : Maybe BinOp → Maybe Split

        stepLParen Core.equal = go (suc d) (t ∷ acc) ts
        stepLParen Core.less = stepRParen (cmpNat t (tokRParen S))
        stepLParen Core.greater = stepRParen (cmpNat t (tokRParen S))

        stepRParen Core.equal = go (predNat d) (t ∷ acc) ts
        stepRParen Core.less = stepDepth (cmpNat d zero)
        stepRParen Core.greater = stepDepth (cmpNat d zero)

        stepDepth Core.equal = stepOp (classifyBinOp S t)
        stepDepth Core.less = go d (t ∷ acc) ts
        stepDepth Core.greater = go d (t ∷ acc) ts

        stepOp (just _) = just (split (reverse acc) t ts)
        stepOp nothing = go d (t ∷ acc) ts

stripOuterParens : Sig → List ℕ → Maybe (List ℕ)
stripOuterParens S [] = nothing
stripOuterParens S (t ∷ ts) with cmpNat t (tokLParen S)
... | Core.equal = go (unsnoc ts)
  where
    go : Maybe (Snoc ℕ) → Maybe (List ℕ)
    go nothing = nothing
    go (just s) with cmpNat (Snoc.last s) (tokRParen S)
    ... | Core.equal = just (Snoc.init s)
    ... | Core.less = nothing
    ... | Core.greater = nothing
... | Core.less = nothing
... | Core.greater = nothing

-- A residual parse result: parsed value plus unconsumed suffix.
record ParseRun (A : Set) : Set where
  constructor mkParseRun
  field
    value : A
    rest  : List ℕ

-- Demand full consumption of the token stream.
exactParse : ∀ {A : Set} → Maybe (ParseRun A) → Maybe A
exactParse nothing = nothing
exactParse (just (mkParseRun x [])) = just x
exactParse (just (mkParseRun _ (_ ∷ _))) = nothing

-- Classify the head token so `parseWffFuel` can be written as a single top-level `with`.
data Head : Set where
  hNot hAll hEx hOther : Head

headCase : Sig → ℕ → Head
headCase S t with cmpNat t (tokNot S) | cmpNat t (tokAll S) | cmpNat t (tokEx S)
... | Core.equal | _ | _ = hNot
... | Core.less | Core.equal | _ = hAll
... | Core.greater | Core.equal | _ = hAll
... | Core.less | Core.less | Core.equal = hEx
... | Core.less | Core.greater | Core.equal = hEx
... | Core.greater | Core.less | Core.equal = hEx
... | Core.greater | Core.greater | Core.equal = hEx
... | Core.less | Core.less | Core.less = hOther
... | Core.less | Core.less | Core.greater = hOther
... | Core.less | Core.greater | Core.less = hOther
... | Core.less | Core.greater | Core.greater = hOther
... | Core.greater | Core.less | Core.less = hOther
... | Core.greater | Core.less | Core.greater = hOther
... | Core.greater | Core.greater | Core.less = hOther
... | Core.greater | Core.greater | Core.greater = hOther

