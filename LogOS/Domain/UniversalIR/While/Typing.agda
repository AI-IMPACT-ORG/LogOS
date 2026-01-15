{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.While.Typing where

open import LogOS.Prelude

open import Data.Product using (_×_; _,_)

open import LogOS.Domain.UniversalIR.While.Language

-- Minimal effect typing: track which variables may be read and written.

data VarEff : Set where
  eff0  : VarEff
  effA  : VarEff
  effB  : VarEff
  effAB : VarEff

infix 4 _≤var_

effVar : Var → VarEff
effVar A = effA
effVar B = effB

varJoin : VarEff → VarEff → VarEff
varJoin eff0  eff0  = eff0
varJoin eff0  effA  = effA
varJoin eff0  effB  = effB
varJoin eff0  effAB = effAB
varJoin effA  eff0  = effA
varJoin effA  effA  = effA
varJoin effA  effB  = effAB
varJoin effA  effAB = effAB
varJoin effB  eff0  = effB
varJoin effB  effA  = effAB
varJoin effB  effB  = effB
varJoin effB  effAB = effAB
varJoin effAB eff0  = effAB
varJoin effAB effA  = effAB
varJoin effAB effB  = effAB
varJoin effAB effAB = effAB

varJoin-none-left : ∀ e → varJoin eff0 e ≡ e
varJoin-none-left eff0  = refl
varJoin-none-left effA  = refl
varJoin-none-left effB  = refl
varJoin-none-left effAB = refl

varJoin-none-right : ∀ e → varJoin e eff0 ≡ e
varJoin-none-right eff0  = refl
varJoin-none-right effA  = refl
varJoin-none-right effB  = refl
varJoin-none-right effAB = refl

varJoin-idem : ∀ e → varJoin e e ≡ e
varJoin-idem eff0  = refl
varJoin-idem effA  = refl
varJoin-idem effB  = refl
varJoin-idem effAB = refl

data _≤var_ : VarEff → VarEff → Set where
  le0   : ∀ {e} → eff0 ≤var e
  leA   : effA ≤var effA
  leAAB : effA ≤var effAB
  leB   : effB ≤var effB
  leBAB : effB ≤var effAB
  leAB  : effAB ≤var effAB

varLe-refl : ∀ e → e ≤var e
varLe-refl eff0  = le0
varLe-refl effA  = leA
varLe-refl effB  = leB
varLe-refl effAB = leAB

varJoin-upper-right : ∀ e₁ e₂ → e₂ ≤var varJoin e₁ e₂
varJoin-upper-right eff0  eff0  = le0
varJoin-upper-right eff0  effA  = leA
varJoin-upper-right eff0  effB  = leB
varJoin-upper-right eff0  effAB = leAB
varJoin-upper-right effA  eff0  = le0
varJoin-upper-right effA  effA  = leA
varJoin-upper-right effA  effB  = leBAB
varJoin-upper-right effA  effAB = leAB
varJoin-upper-right effB  eff0  = le0
varJoin-upper-right effB  effA  = leAAB
varJoin-upper-right effB  effB  = leB
varJoin-upper-right effB  effAB = leAB
varJoin-upper-right effAB eff0  = le0
varJoin-upper-right effAB effA  = leAAB
varJoin-upper-right effAB effB  = leBAB
varJoin-upper-right effAB effAB = leAB

varJoin-mono-left : ∀ {e₁ e₁' e₂} → e₁ ≤var e₁' → varJoin e₁ e₂ ≤var varJoin e₁' e₂
varJoin-mono-left {e₁' = e₁'} {e₂ = e₂} le0 =
  subst (λ x → x ≤var varJoin e₁' e₂) (sym (varJoin-none-left e₂)) (varJoin-upper-right e₁' e₂)
varJoin-mono-left {e₂ = e₂} leA = varLe-refl (varJoin effA e₂)
varJoin-mono-left {e₂ = eff0} leAAB = leAAB
varJoin-mono-left {e₂ = effA} leAAB = leAAB
varJoin-mono-left {e₂ = effB} leAAB = leAB
varJoin-mono-left {e₂ = effAB} leAAB = leAB
varJoin-mono-left {e₂ = e₂} leB = varLe-refl (varJoin effB e₂)
varJoin-mono-left {e₂ = eff0} leBAB = leBAB
varJoin-mono-left {e₂ = effA} leBAB = leAB
varJoin-mono-left {e₂ = effB} leBAB = leBAB
varJoin-mono-left {e₂ = effAB} leBAB = leAB
varJoin-mono-left {e₂ = e₂} leAB = varLe-refl (varJoin effAB e₂)

varJoin-absorb-left : ∀ e g → varJoin e (varJoin g e) ≡ varJoin g e
varJoin-absorb-left eff0 eff0 = refl
varJoin-absorb-left eff0 effA = refl
varJoin-absorb-left eff0 effB = refl
varJoin-absorb-left eff0 effAB = refl
varJoin-absorb-left effA eff0 = refl
varJoin-absorb-left effA effA = refl
varJoin-absorb-left effA effB = refl
varJoin-absorb-left effA effAB = refl
varJoin-absorb-left effB eff0 = refl
varJoin-absorb-left effB effA = refl
varJoin-absorb-left effB effB = refl
varJoin-absorb-left effB effAB = refl
varJoin-absorb-left effAB eff0 = refl
varJoin-absorb-left effAB effA = refl
varJoin-absorb-left effAB effB = refl
varJoin-absorb-left effAB effAB = refl

record Eff : Set where
  constructor mkEff
  field
    read  : VarEff
    write : VarEff

open Eff public

infix 4 _≤eff_

effNone : Eff
effNone = mkEff eff0 eff0

effGuard : Var → Eff
effGuard v = mkEff (effVar v) eff0

effJoin : Eff → Eff → Eff
effJoin e₁ e₂ = mkEff (varJoin (read e₁) (read e₂)) (varJoin (write e₁) (write e₂))

effJoin-none-left : ∀ e → effJoin effNone e ≡ e
effJoin-none-left (mkEff r w) =
  cong₂ mkEff (varJoin-none-left r) (varJoin-none-left w)

effJoin-none-right : ∀ e → effJoin e effNone ≡ e
effJoin-none-right (mkEff r w) =
  cong₂ mkEff (varJoin-none-right r) (varJoin-none-right w)

effJoin-idem : ∀ e → effJoin e e ≡ e
effJoin-idem (mkEff r w) =
  cong₂ mkEff (varJoin-idem r) (varJoin-idem w)

effJoin-absorb-left : ∀ e g → effJoin e (effJoin g e) ≡ effJoin g e
effJoin-absorb-left (mkEff r w) (mkEff gr gw) =
  cong₂ mkEff (varJoin-absorb-left r gr) (varJoin-absorb-left w gw)

_≤eff_ : Eff → Eff → Set
e₁ ≤eff e₂ = (read e₁ ≤var read e₂) × (write e₁ ≤var write e₂)

effLe-refl : ∀ e → e ≤eff e
effLe-refl e = (varLe-refl (read e) , varLe-refl (write e))

effLe-bottom : ∀ e → effNone ≤eff e
effLe-bottom e = (le0 , le0)

effJoin-upper-right : ∀ e₁ e₂ → e₂ ≤eff effJoin e₁ e₂
effJoin-upper-right e₁ e₂ =
  ( varJoin-upper-right (read e₁) (read e₂)
  , varJoin-upper-right (write e₁) (write e₂)
  )

effJoin-mono-left : ∀ {e₁ e₁' e₂} → e₁ ≤eff e₁' → effJoin e₁ e₂ ≤eff effJoin e₁' e₂
effJoin-mono-left {e₂ = e₂} (leR , leW) =
  ( varJoin-mono-left leR
  , varJoin-mono-left leW
  )

data StmtEff : Stmt → Eff → Set where
  eff-skip  : StmtEff skip effNone
  eff-inc   : ∀ {v} → StmtEff (inc v) (mkEff (effVar v) (effVar v))
  eff-dec   : ∀ {v} → StmtEff (dec v) (mkEff (effVar v) (effVar v))
  eff-mulAB : StmtEff mulAB (mkEff effAB effA)
  eff-seq   : ∀ {s t e₁ e₂} → StmtEff s e₁ → StmtEff t e₂ → StmtEff (s >> t) (effJoin e₁ e₂)
  eff-while : ∀ {v body e} → StmtEff body e → StmtEff (whileNZ v body) (effJoin (effGuard v) e)

inferEff : Stmt → Eff
inferEff skip            = effNone
inferEff (inc v)         = mkEff (effVar v) (effVar v)
inferEff (dec v)         = mkEff (effVar v) (effVar v)
inferEff mulAB           = mkEff effAB effA
inferEff (s >> t)        = effJoin (inferEff s) (inferEff t)
inferEff (whileNZ v body) = effJoin (effGuard v) (inferEff body)

stmtEff-infer : ∀ {s} → StmtEff s (inferEff s)
stmtEff-infer {s = skip} = eff-skip
stmtEff-infer {s = inc v} = eff-inc
stmtEff-infer {s = dec v} = eff-dec
stmtEff-infer {s = mulAB} = eff-mulAB
stmtEff-infer {s = s >> t} = eff-seq stmtEff-infer stmtEff-infer
stmtEff-infer {s = whileNZ v body} = eff-while stmtEff-infer

stmtEff-sound : ∀ {s e} → StmtEff s e → inferEff s ≡ e
stmtEff-sound eff-skip = refl
stmtEff-sound eff-inc = refl
stmtEff-sound eff-dec = refl
stmtEff-sound eff-mulAB = refl
stmtEff-sound (eff-seq s t) = cong₂ effJoin (stmtEff-sound s) (stmtEff-sound t)
stmtEff-sound (eff-while {v = v} s) =
  cong (effJoin (effGuard v)) (stmtEff-sound s)

stmtEff-unique : ∀ {s e₁ e₂} → StmtEff s e₁ → StmtEff s e₂ → e₁ ≡ e₂
stmtEff-unique s₁ s₂ = trans (sym (stmtEff-sound s₁)) (stmtEff-sound s₂)

StmtOk : Stmt → Set
StmtOk s = StmtEff s (inferEff s)

stmtOk : ∀ {s} → StmtOk s
stmtOk = stmtEff-infer
