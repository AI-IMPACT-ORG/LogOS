{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.SetMM.Parse.Term where

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
  ; contains
  ; lookupIx
  ; len
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Sig using (Sig; tokEmpty; tokOmega)
open import LogOS.Apps.ZFC.Metamath.SetMM.Vars using (Vars; setVars)
open import LogOS.Apps.ZFC.Metamath.SetMM.Parse.Support using
  ( ParseRun
  ; mkParseRun
  ; exactParse
  ; TermOp
  ; mkUnion
  ; mkPower
  ; mkSucc
  ; mkPair
  ; classifyTermOp
  )

open import LogOS.Apps.ZFC.Proof.Syntax as ZF using
  ( Term
  ; var
  ; emptyT
  ; omegaT
  ; unionT
  ; powerT
  ; succT
  ; pairT
  )

mutual
  parseTerm : Sig → Vars → List ℕ → List ℕ → Maybe Term
  parseTerm S V env ts = exactParse (parseTermFuel S V env (len ts) ts)

  parseTermFuel
    : Sig → Vars → List ℕ → ℕ → List ℕ → Maybe (ParseRun Term)
  parseTermFuel _ _ _ zero _ = nothing
  parseTermFuel S V env (suc k) [] = nothing
  parseTermFuel S V env (suc k) (x ∷ []) = stepEmpty (cmpNat x (tokEmpty S))
    where
      stepEmpty : Cmp → Maybe (ParseRun Term)
      stepOmega : Cmp → Maybe (ParseRun Term)
      stepVar : Maybe Core.Unit → Maybe (ParseRun Term)
      stepLookup : Maybe ℕ → Maybe (ParseRun Term)

      stepEmpty Core.equal = just (mkParseRun ZF.emptyT [])
      stepEmpty Core.less = stepOmega (cmpNat x (tokOmega S))
      stepEmpty Core.greater = stepOmega (cmpNat x (tokOmega S))

      stepOmega Core.equal = just (mkParseRun ZF.omegaT [])
      stepOmega Core.less = stepVar (contains x (setVars V))
      stepOmega Core.greater = stepVar (contains x (setVars V))

      stepVar nothing = nothing
      stepVar (just _) = stepLookup (lookupIx x env)

      stepLookup nothing = nothing
      stepLookup (just i) = just (mkParseRun (ZF.var i) [])
  parseTermFuel S V env (suc k) (op ∷ x ∷ ts) with classifyTermOp S op
  ... | just mkUnion =
    parseTermFuel S V env k (x ∷ ts) >>= λ t →
    just (mkParseRun (ZF.unionT (ParseRun.value t)) (ParseRun.rest t))
  ... | just mkPower =
    parseTermFuel S V env k (x ∷ ts) >>= λ t →
    just (mkParseRun (ZF.powerT (ParseRun.value t)) (ParseRun.rest t))
  ... | just mkSucc =
    parseTermFuel S V env k (x ∷ ts) >>= λ t →
    just (mkParseRun (ZF.succT (ParseRun.value t)) (ParseRun.rest t))
  ... | just mkPair = parsePair (x ∷ ts)
    where
      parsePair : List ℕ → Maybe (ParseRun Term)
      parsePair (x ∷ y ∷ []) =
        exactParse (parseTermFuel S V env k (x ∷ [])) >>= λ t →
        exactParse (parseTermFuel S V env k (y ∷ [])) >>= λ u →
        just (mkParseRun (ZF.pairT t u) [])
      parsePair [] = nothing
      parsePair (_ ∷ []) = nothing
      parsePair (_ ∷ _ ∷ _ ∷ _) = nothing
  ... | nothing = nothing
