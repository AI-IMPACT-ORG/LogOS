{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Core.QuantumCircuit where

open import LogOS.Prelude
open import LogOS.UniversalIR.Core.Utils

open import LogOS.Prelude.Bool using (Bool; true; false)
open import LogOS.Prelude.List using (List; []; _∷_; _++_; map)
open import LogOS.Prelude.Maybe using (Maybe; just; nothing)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl)
open import LogOS.Prelude.Empty using (⊥; ⊥-elim)
open import LogOS.UniversalIR.Encoding using (length)

infix 4 _≢_
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

private
  inspect : ∀ {A : Set} → (x : A) → Σ A (λ y → x ≡ y)
  inspect x = x , refl

-- 5) Basis-state quantum circuits (explicit gates, deterministic measurement) -

not : Bool → Bool
not true  = false
not false = true

updateAt : ∀ {A : Set} → ℕ → (A → A) → List A → List A
updateAt _       _ []       = []
updateAt zero    f (x ∷ xs) = f x ∷ xs
updateAt (suc i) f (x ∷ xs) = x ∷ updateAt i f xs

Wires : Set
Wires = List Bool

mapMaybe : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
mapMaybe _ nothing  = nothing
mapMaybe f (just x) = just (f x)

lookupAt : ℕ → Wires → Maybe Bool
lookupAt _ []       = nothing
lookupAt zero (b ∷ _) = just b
lookupAt (suc i) (_ ∷ ws) = lookupAt i ws

length-updateAt : ∀ {A : Set} i f (xs : List A) → length (updateAt i f xs) ≡ length xs
length-updateAt _ _ [] = refl
length-updateAt zero _ (_ ∷ _) = refl
length-updateAt (suc i) f (_ ∷ xs) = cong suc (length-updateAt i f xs)

data QCInstr : Set where
  QCHALT   : QCInstr
  QNOP     : QCInstr
  QX       : ℕ → QCInstr
  QCNOT    : ℕ → ℕ → QCInstr
  QTOFF    : ℕ → ℕ → ℕ → QCInstr
  QMEASURE : ℕ → ℕ → ℕ → QCInstr    -- measure wire i; jump to j/k (basis states)

QNOP≢QCHALT : QNOP ≢ QCHALT
QNOP≢QCHALT ()

QX≢QCHALT : ∀ i → QX i ≢ QCHALT
QX≢QCHALT _ ()

QCNOT≢QCHALT : ∀ c t → QCNOT c t ≢ QCHALT
QCNOT≢QCHALT _ _ ()

QTOFF≢QCHALT : ∀ a b t → QTOFF a b t ≢ QCHALT
QTOFF≢QCHALT _ _ _ ()

flipAt : ℕ → Wires → Wires
flipAt i = updateAt i not

applyCNOTAt : ℕ → Wires → Maybe Bool → Wires
applyCNOTAt tgt ws (just true) = flipAt tgt ws
applyCNOTAt _   ws (just false) = ws
applyCNOTAt _   ws nothing      = ws

applyCNOT : ℕ → ℕ → Wires → Wires
applyCNOT ctrl tgt ws = applyCNOTAt tgt ws (lookupAt ctrl ws)

applyTOFFAt : ℕ → Wires → Maybe Bool → Maybe Bool → Wires
applyTOFFAt tgt ws (just true) (just true) = flipAt tgt ws
applyTOFFAt _   ws (just true) (just false) = ws
applyTOFFAt _   ws (just true) nothing      = ws
applyTOFFAt _   ws (just false) _           = ws
applyTOFFAt _   ws nothing      _           = ws

applyTOFFAt-left-false : ∀ tgt ws b → applyTOFFAt tgt ws (just false) b ≡ ws
applyTOFFAt-left-false _ _ _ = refl

applyTOFFAt-left-nothing : ∀ tgt ws b → applyTOFFAt tgt ws nothing b ≡ ws
applyTOFFAt-left-nothing _ _ _ = refl

applyTOFFAt-right-false : ∀ tgt ws a → applyTOFFAt tgt ws a (just false) ≡ ws
applyTOFFAt-right-false _ _ (just true) = refl
applyTOFFAt-right-false _ _ (just false) = refl
applyTOFFAt-right-false _ _ nothing = refl

applyTOFFAt-right-nothing : ∀ tgt ws a → applyTOFFAt tgt ws a nothing ≡ ws
applyTOFFAt-right-nothing _ _ (just true) = refl
applyTOFFAt-right-nothing _ _ (just false) = refl
applyTOFFAt-right-nothing _ _ nothing = refl

applyTOFF : ℕ → ℕ → ℕ → Wires → Wires
applyTOFF c₁ c₂ tgt ws = applyTOFFAt tgt ws (lookupAt c₁ ws) (lookupAt c₂ ws)

length-flipAt : ∀ i ws → length (flipAt i ws) ≡ length ws
length-flipAt i ws = length-updateAt i not ws

length-applyCNOT : ∀ c t ws → length (applyCNOT c t ws) ≡ length ws
length-applyCNOT c t ws with lookupAt c ws
... | just true  = length-flipAt t ws
... | just false = refl
... | nothing    = refl

length-applyTOFF : ∀ c₁ c₂ t ws → length (applyTOFF c₁ c₂ t ws) ≡ length ws
length-applyTOFF c₁ c₂ t ws with lookupAt c₁ ws | lookupAt c₂ ws
... | just true  | just true  = length-flipAt t ws
... | just true  | just false = refl
... | just true  | nothing    = refl
... | just false | just true  = refl
... | just false | just false = refl
... | just false | nothing    = refl
... | nothing    | just true  = refl
... | nothing    | just false = refl
... | nothing    | nothing    = refl

-- Gate-only fragment (no control flow): used by the CQM relational view.
-- This is a wire-level action; measurement is treated as a no-op on wires.

data Gate : Set where
  GNOP  : Gate
  GX    : ℕ → Gate
  GCNOT : ℕ → ℕ → Gate
  GTOFF : ℕ → ℕ → ℕ → Gate

record GateProg : Set where
  constructor mkGateProg
  field
    gates : List Gate

open GateProg public

gateToInstr : Gate → QCInstr
gateToInstr GNOP = QNOP
gateToInstr (GX i) = QX i
gateToInstr (GCNOT c t) = QCNOT c t
gateToInstr (GTOFF a b t) = QTOFF a b t

applyQCInstr : QCInstr → Wires → Wires
applyQCInstr QCHALT ws = ws
applyQCInstr QNOP ws = ws
applyQCInstr (QX i) ws = flipAt i ws
applyQCInstr (QCNOT c t) ws = applyCNOT c t ws
applyQCInstr (QTOFF a b t) ws = applyTOFF a b t ws
applyQCInstr (QMEASURE _ _ _) ws = ws

length-applyQCInstr : ∀ instr ws → length (applyQCInstr instr ws) ≡ length ws
length-applyQCInstr QCHALT _ = refl
length-applyQCInstr QNOP _ = refl
length-applyQCInstr (QX i) ws = length-flipAt i ws
length-applyQCInstr (QCNOT c t) ws = length-applyCNOT c t ws
length-applyQCInstr (QTOFF a b t) ws = length-applyTOFF a b t ws
length-applyQCInstr (QMEASURE _ _ _) _ = refl

runInstrs : List QCInstr → Wires → Wires
runInstrs []       ws = ws
runInstrs (i ∷ is) ws = runInstrs is (applyQCInstr i ws)

runInstrs-++ : ∀ is₁ is₂ ws → runInstrs (is₁ ++ is₂) ws ≡ runInstrs is₂ (runInstrs is₁ ws)
runInstrs-++ []       is₂ ws = refl
runInstrs-++ (i ∷ is) is₂ ws = runInstrs-++ is is₂ (applyQCInstr i ws)

applyGate : Gate → Wires → Wires
applyGate g = applyQCInstr (gateToInstr g)

length-applyGate : ∀ g ws → length (applyGate g ws) ≡ length ws
length-applyGate g ws = length-applyQCInstr (gateToInstr g) ws

agreeAt : ℕ → Wires → Wires → Set
agreeAt i ws ws' = lookupAt i ws ≡ lookupAt i ws'

agreeOn : List ℕ → Wires → Wires → Set
agreeOn [] _ _ = ⊤
agreeOn (i ∷ is) ws ws' = agreeAt i ws ws' × agreeOn is ws ws'

touchedGate : Gate → List ℕ
touchedGate GNOP = []
touchedGate (GX i) = i ∷ []
touchedGate (GCNOT c t) = c ∷ t ∷ []
touchedGate (GTOFF a b t) = a ∷ b ∷ t ∷ []

lookupAt-flipAt : ∀ i ws → lookupAt i (flipAt i ws) ≡ mapMaybe not (lookupAt i ws)
lookupAt-flipAt _ [] = refl
lookupAt-flipAt zero (b ∷ _) = refl
lookupAt-flipAt (suc i) (_ ∷ ws) = lookupAt-flipAt i ws

lookupAt-nothing-updateAt
  : ∀ i j f ws
  → lookupAt i ws ≡ nothing
  → lookupAt i (updateAt j f ws) ≡ nothing
lookupAt-nothing-updateAt _ _ _ [] _ = refl
lookupAt-nothing-updateAt zero zero _ (_ ∷ _) ()
lookupAt-nothing-updateAt zero (suc _) _ (_ ∷ _) ()
lookupAt-nothing-updateAt (suc i) zero _ (_ ∷ ws) eq = eq
lookupAt-nothing-updateAt (suc i) (suc j) f (_ ∷ ws) eq =
  lookupAt-nothing-updateAt i j f ws eq

agreeAt-updateAt
  : ∀ i j f ws ws'
  → agreeAt i ws ws'
  → agreeAt i (updateAt j f ws) (updateAt j f ws')
agreeAt-updateAt zero zero f [] [] _ = refl
agreeAt-updateAt zero zero f [] (_ ∷ _) ()
agreeAt-updateAt zero zero f (_ ∷ _) [] ()
agreeAt-updateAt zero zero f (x ∷ xs) (y ∷ ys) eq = cong (mapMaybe f) eq
agreeAt-updateAt zero (suc j) f [] [] _ = refl
agreeAt-updateAt zero (suc j) f [] (_ ∷ _) ()
agreeAt-updateAt zero (suc j) f (_ ∷ _) [] ()
agreeAt-updateAt zero (suc j) f (x ∷ xs) (y ∷ ys) eq = eq
agreeAt-updateAt (suc i) zero f [] [] _ = refl
agreeAt-updateAt (suc i) zero f [] (_ ∷ ys) eq = eq
agreeAt-updateAt (suc i) zero f (_ ∷ xs) [] eq = eq
agreeAt-updateAt (suc i) zero f (_ ∷ xs) (_ ∷ ys) eq = eq
agreeAt-updateAt (suc i) (suc j) f [] [] _ = refl
agreeAt-updateAt (suc i) (suc j) f [] (_ ∷ ys) eq =
  sym (lookupAt-nothing-updateAt i j f ys (sym eq))
agreeAt-updateAt (suc i) (suc j) f (_ ∷ xs) [] eq =
  lookupAt-nothing-updateAt i j f xs eq
agreeAt-updateAt (suc i) (suc j) f (_ ∷ xs) (_ ∷ ys) eq =
  agreeAt-updateAt i j f xs ys eq

agreeAt-flipAt-any : ∀ i j ws ws' → agreeAt i ws ws' → agreeAt i (flipAt j ws) (flipAt j ws')
agreeAt-flipAt-any i j ws ws' eq = agreeAt-updateAt i j not ws ws' eq

agreeAt-flipAt : ∀ i ws ws' → agreeAt i ws ws' → agreeAt i (flipAt i ws) (flipAt i ws')
agreeAt-flipAt i ws ws' eq
  rewrite lookupAt-flipAt i ws
        | lookupAt-flipAt i ws'
  = cong (mapMaybe not) eq

agreeAt-applyCNOT-target
  : ∀ c t ws ws'
  → agreeAt c ws ws' → agreeAt t ws ws'
  → agreeAt t (applyCNOT c t ws) (applyCNOT c t ws')
agreeAt-applyCNOT-target c t ws ws' eqC eqT
  with lookupAt c ws | lookupAt c ws' | eqC
... | just true  | .(just true)  | refl = agreeAt-flipAt t ws ws' eqT
... | just false | .(just false) | refl = eqT
... | nothing    | .nothing      | refl = eqT

agreeAt-applyCNOT-control
  : ∀ c t ws ws'
  → agreeAt c ws ws'
  → agreeAt c (applyCNOT c t ws) (applyCNOT c t ws')
agreeAt-applyCNOT-control c t ws ws' eqC
  with lookupAt c ws | lookupAt c ws' | eqC
... | just true  | .(just true)  | refl = agreeAt-flipAt-any c t ws ws' eqC
... | just false | .(just false) | refl = eqC
... | nothing    | .nothing      | refl = eqC

agreeAt-applyTOFF-target
  : ∀ a b t ws ws'
  → agreeAt a ws ws' → agreeAt b ws ws' → agreeAt t ws ws'
  → agreeAt t (applyTOFF a b t ws) (applyTOFF a b t ws')
agreeAt-applyTOFF-target a b t ws ws' eqA eqB eqT
  with lookupAt a ws | lookupAt b ws | lookupAt a ws' | lookupAt b ws' | eqA | eqB
... | just true  | just true  | .(just true)  | .(just true)  | refl | refl =
  agreeAt-flipAt t ws ws' eqT
... | just true  | just false | .(just true)  | .(just false) | refl | refl
  rewrite applyTOFFAt-right-false t ws (just true)
        | applyTOFFAt-right-false t ws' (just true)
  = eqT
... | just true  | nothing    | .(just true)  | .nothing      | refl | refl
  rewrite applyTOFFAt-right-nothing t ws (just true)
        | applyTOFFAt-right-nothing t ws' (just true)
  = eqT
... | just false | b₁         | .(just false) | b₂            | refl | _
  rewrite applyTOFFAt-left-false t ws b₁
        | applyTOFFAt-left-false t ws' b₂
  = eqT
... | nothing    | b₁         | .nothing      | b₂            | refl | _
  rewrite applyTOFFAt-left-nothing t ws b₁
        | applyTOFFAt-left-nothing t ws' b₂
  = eqT

agreeAt-applyTOFF-control₁
  : ∀ a b t ws ws'
  → agreeAt a ws ws' → agreeAt b ws ws'
  → agreeAt a (applyTOFF a b t ws) (applyTOFF a b t ws')
agreeAt-applyTOFF-control₁ a b t ws ws' eqA eqB
  with lookupAt a ws | lookupAt b ws | lookupAt a ws' | lookupAt b ws' | eqA | eqB
... | just true  | just true  | .(just true)  | .(just true)  | refl | refl =
  agreeAt-flipAt-any a t ws ws' eqA
... | just true  | just false | .(just true)  | .(just false) | refl | refl
  rewrite applyTOFFAt-right-false t ws (just true)
        | applyTOFFAt-right-false t ws' (just true)
  = eqA
... | just true  | nothing    | .(just true)  | .nothing      | refl | refl
  rewrite applyTOFFAt-right-nothing t ws (just true)
        | applyTOFFAt-right-nothing t ws' (just true)
  = eqA
... | just false | b₁         | .(just false) | b₂            | refl | _
  rewrite applyTOFFAt-left-false t ws b₁
        | applyTOFFAt-left-false t ws' b₂
  = eqA
... | nothing    | b₁         | .nothing      | b₂            | refl | _
  rewrite applyTOFFAt-left-nothing t ws b₁
        | applyTOFFAt-left-nothing t ws' b₂
  = eqA

agreeAt-applyTOFF-control₂
  : ∀ a b t ws ws'
  → agreeAt a ws ws' → agreeAt b ws ws'
  → agreeAt b (applyTOFF a b t ws) (applyTOFF a b t ws')
agreeAt-applyTOFF-control₂ a b t ws ws' eqA eqB
  with lookupAt a ws | lookupAt b ws | lookupAt a ws' | lookupAt b ws' | eqA | eqB
... | just true  | just true  | .(just true)  | .(just true)  | refl | refl =
  agreeAt-flipAt-any b t ws ws' eqB
... | just false | just true  | .(just false) | .(just true)  | refl | refl
  rewrite applyTOFFAt-left-false t ws (just true)
        | applyTOFFAt-left-false t ws' (just true)
  = eqB
... | nothing    | just true  | .nothing      | .(just true)  | refl | refl
  rewrite applyTOFFAt-left-nothing t ws (just true)
        | applyTOFFAt-left-nothing t ws' (just true)
  = eqB
... | just true  | just false | .(just true)  | .(just false) | refl | refl
  rewrite applyTOFFAt-right-false t ws (just true)
        | applyTOFFAt-right-false t ws' (just true)
  = eqB
... | just false | just false | .(just false) | .(just false) | refl | refl
  rewrite applyTOFFAt-right-false t ws (just false)
        | applyTOFFAt-right-false t ws' (just false)
  = eqB
... | nothing    | just false | .nothing      | .(just false) | refl | refl
  rewrite applyTOFFAt-right-false t ws nothing
        | applyTOFFAt-right-false t ws' nothing
  = eqB
... | just true  | nothing    | .(just true)  | .nothing      | refl | refl
  rewrite applyTOFFAt-right-nothing t ws (just true)
        | applyTOFFAt-right-nothing t ws' (just true)
  = eqB
... | just false | nothing    | .(just false) | .nothing      | refl | refl
  rewrite applyTOFFAt-right-nothing t ws (just false)
        | applyTOFFAt-right-nothing t ws' (just false)
  = eqB
... | nothing    | nothing    | .nothing      | .nothing      | refl | refl
  rewrite applyTOFFAt-right-nothing t ws nothing
        | applyTOFFAt-right-nothing t ws' nothing
  = eqB

gateLocal
  : ∀ g ws ws'
  → agreeOn (touchedGate g) ws ws'
  → agreeOn (touchedGate g) (applyGate g ws) (applyGate g ws')
gateLocal GNOP _ _ _ = tt
gateLocal (GX i) ws ws' (eq , _) = agreeAt-flipAt i ws ws' eq , tt
gateLocal (GCNOT c t) ws ws' (eqC , (eqT , _)) =
  (agreeAt-applyCNOT-control c t ws ws' eqC ,
   (agreeAt-applyCNOT-target c t ws ws' eqC eqT , tt))
gateLocal (GTOFF a b t) ws ws' (eqA , (eqB , (eqT , _))) =
  (agreeAt-applyTOFF-control₁ a b t ws ws' eqA eqB ,
   (agreeAt-applyTOFF-control₂ a b t ws ws' eqA eqB ,
    (agreeAt-applyTOFF-target a b t ws ws' eqA eqB eqT , tt)))

runGates : List Gate → Wires → Wires
runGates []       ws = ws
runGates (g ∷ gs) ws = runGates gs (applyGate g ws)

runGates-++ : ∀ gs₁ gs₂ ws → runGates (gs₁ ++ gs₂) ws ≡ runGates gs₂ (runGates gs₁ ws)
runGates-++ []       gs₂ ws = refl
runGates-++ (g ∷ gs) gs₂ ws = runGates-++ gs gs₂ (applyGate g ws)

infixr 5 _++g_
_++g_ : GateProg → GateProg → GateProg
mkGateProg gs₁ ++g mkGateProg gs₂ = mkGateProg (gs₁ ++ gs₂)

gateProg : List Gate → List QCInstr
gateProg = map gateToInstr

gateProgOf : GateProg → List QCInstr
gateProgOf gp = gateProg (gates gp)

runGateProg : GateProg → Wires → Wires
runGateProg gp = runGates (gates gp)

runGateProg-++
  : ∀ g₁ g₂ ws → runGateProg (g₁ ++g g₂) ws ≡ runGateProg g₂ (runGateProg g₁ ws)
runGateProg-++ (mkGateProg gs₁) (mkGateProg gs₂) ws =
  runGates-++ gs₁ gs₂ ws

runGates-runInstrs : ∀ gs ws → runGates gs ws ≡ runInstrs (gateProg gs) ws
runGates-runInstrs [] ws = refl
runGates-runInstrs (g ∷ gs) ws = runGates-runInstrs gs (applyGate g ws)


-- Program/state split:
-- - program = output arity + instruction list
-- - state   = pc + wires

record QuantumCircuitProg : Set where
  constructor mkProg
  field
    outLen : ℕ
    prog   : List QCInstr

record QuantumCircuitState : Set where
  constructor mkState
  field
    pc    : ℕ
    wires : Wires

record QuantumCircuitCode : Set where
  constructor mkCode
  field
    State : QuantumCircuitState
    Prog  : QuantumCircuitProg

  open QuantumCircuitState State public using (pc; wires)
  open QuantumCircuitProg Prog public using (outLen; prog)

pattern mkQC pc outLen wires prog = mkCode (mkState pc wires) (mkProg outLen prog)

open QuantumCircuitCode public using (pc; outLen; wires; prog)

setPCQC : ℕ → QuantumCircuitCode → QuantumCircuitCode
setPCQC n q = mkQC n (outLen q) (wires q) (prog q)

setWiresQC : Wires → QuantumCircuitCode → QuantumCircuitCode
setWiresQC ws q = mkQC (pc q) (outLen q) ws (prog q)

stepQCInstr : QCInstr → QuantumCircuitCode → QuantumCircuitCode
stepQCInstr QCHALT q = q
stepQCInstr (QMEASURE i j k) q with lookupDefault false (wires q) i
... | true  = setPCQC k q
... | false = setPCQC j q
stepQCInstr QNOP q =
  setPCQC (suc (pc q)) (setWiresQC (applyQCInstr QNOP (wires q)) q)
stepQCInstr (QX i) q =
  setPCQC (suc (pc q)) (setWiresQC (applyQCInstr (QX i) (wires q)) q)
stepQCInstr (QCNOT c t) q =
  setPCQC (suc (pc q)) (setWiresQC (applyQCInstr (QCNOT c t) (wires q)) q)
stepQCInstr (QTOFF a b t) q =
  setPCQC (suc (pc q)) (setWiresQC (applyQCInstr (QTOFF a b t) (wires q)) q)

stepQC : QuantumCircuitCode → QuantumCircuitCode
stepQC q = stepQCInstr (lookupDefault QCHALT (prog q) (pc q)) q


WiresOk : QuantumCircuitCode → Set
WiresOk q = length (wires q) ≡ outLen q

WiresOk-stepQCInstr : ∀ instr q → WiresOk q → WiresOk (stepQCInstr instr q)
WiresOk-stepQCInstr QCHALT _ ok = ok
WiresOk-stepQCInstr (QMEASURE i _ _) q ok with lookupDefault false (wires q) i
... | true = ok
... | false = ok
WiresOk-stepQCInstr QNOP q ok =
  trans (length-applyQCInstr QNOP (wires q)) ok
WiresOk-stepQCInstr (QX i) q ok =
  trans (length-applyQCInstr (QX i) (wires q)) ok
WiresOk-stepQCInstr (QCNOT c t) q ok =
  trans (length-applyQCInstr (QCNOT c t) (wires q)) ok
WiresOk-stepQCInstr (QTOFF a b t) q ok =
  trans (length-applyQCInstr (QTOFF a b t) (wires q)) ok

WiresOk-stepQC : ∀ q → WiresOk q → WiresOk (stepQC q)
WiresOk-stepQC q ok =
  WiresOk-stepQCInstr (lookupDefault QCHALT (prog q) (pc q)) q ok

prog-stepQCInstr : ∀ instr q → prog (stepQCInstr instr q) ≡ prog q
prog-stepQCInstr QCHALT _ = refl
prog-stepQCInstr (QMEASURE i _ _) q with lookupDefault false (wires q) i
... | true = refl
... | false = refl
prog-stepQCInstr QNOP _ = refl
prog-stepQCInstr (QX _) _ = refl
prog-stepQCInstr (QCNOT _ _) _ = refl
prog-stepQCInstr (QTOFF _ _ _) _ = refl

prog-stepQC : ∀ q → prog (stepQC q) ≡ prog q
prog-stepQC q =
  prog-stepQCInstr (lookupDefault QCHALT (prog q) (pc q)) q

outLen-stepQCInstr : ∀ instr q → outLen (stepQCInstr instr q) ≡ outLen q
outLen-stepQCInstr QCHALT _ = refl
outLen-stepQCInstr (QMEASURE i _ _) q with lookupDefault false (wires q) i
... | true = refl
... | false = refl
outLen-stepQCInstr QNOP _ = refl
outLen-stepQCInstr (QX _) _ = refl
outLen-stepQCInstr (QCNOT _ _) _ = refl
outLen-stepQCInstr (QTOFF _ _ _) _ = refl

outLen-stepQC : ∀ q → outLen (stepQC q) ≡ outLen q
outLen-stepQC q =
  outLen-stepQCInstr (lookupDefault QCHALT (prog q) (pc q)) q

iterQC : ℕ → QuantumCircuitCode → QuantumCircuitCode
iterQC zero q = q
iterQC (suc n) q = iterQC n (stepQC q)

stepQC-gateProg
  : ∀ g gs ws
  → stepQC (mkQC 0 (length ws) ws (gateProg (g ∷ gs)))
    ≡ mkQC 1 (length ws) (applyGate g ws) (gateProg (g ∷ gs))
stepQC-gateProg GNOP _ _ = refl
stepQC-gateProg (GX _) _ _ = refl
stepQC-gateProg (GCNOT _ _) _ _ = refl
stepQC-gateProg (GTOFF _ _ _) _ _ = refl

NoMeasure : QCInstr → Set
NoMeasure QCHALT = ⊤
NoMeasure QNOP = ⊤
NoMeasure (QX _) = ⊤
NoMeasure (QCNOT _ _) = ⊤
NoMeasure (QTOFF _ _ _) = ⊤
NoMeasure (QMEASURE _ _ _) = ⊥

AllNoMeasure : List QCInstr → Set
AllNoMeasure = AllPred NoMeasure

lookupNoMeasure
  : ∀ (xs : List QCInstr) (n : ℕ)
  → AllNoMeasure xs
  → NoMeasure (lookupDefault QCHALT xs n)
lookupNoMeasure xs n nm = lookupAllPred NoMeasure QCHALT xs n tt nm

noMeasure-gateProg : ∀ gs → AllNoMeasure (gateProg gs)
noMeasure-gateProg [] = tt
noMeasure-gateProg (GNOP ∷ gs) = tt , noMeasure-gateProg gs
noMeasure-gateProg (GX _ ∷ gs) = tt , noMeasure-gateProg gs
noMeasure-gateProg (GCNOT _ _ ∷ gs) = tt , noMeasure-gateProg gs
noMeasure-gateProg (GTOFF _ _ _ ∷ gs) = tt , noMeasure-gateProg gs

iterQC-ignore-head
  : ∀ n pc i is ws outLen
  → AllNoMeasure (i ∷ is)
  → wires (iterQC n (mkQC (suc pc) outLen ws (i ∷ is)))
      ≡ wires (iterQC n (mkQC pc outLen ws is))
iterQC-ignore-head zero _ _ _ _ _ _ = refl
iterQC-ignore-head (suc n) pc i is ws outLen nm
  with lookupDefault QCHALT is pc | lookupNoMeasure is pc (snd nm)
... | QCHALT | _ =
  iterQC-ignore-head n pc i is ws outLen nm
... | QMEASURE _ _ _ | ()
... | QNOP | _ =
  iterQC-ignore-head n (suc pc) i is (applyQCInstr QNOP ws) outLen nm
... | QX j | _ =
  iterQC-ignore-head n (suc pc) i is (applyQCInstr (QX j) ws) outLen nm
... | QCNOT c t | _ =
  iterQC-ignore-head n (suc pc) i is (applyQCInstr (QCNOT c t) ws) outLen nm
... | QTOFF a b t | _ =
  iterQC-ignore-head n (suc pc) i is (applyQCInstr (QTOFF a b t) ws) outLen nm

iterQC-gateProg
  : ∀ gs ws
  → wires (iterQC (length gs) (mkQC 0 (length ws) ws (gateProg gs)))
    ≡ runGates gs ws
iterQC-gateProg [] ws = refl
iterQC-gateProg (g ∷ gs) ws =
  trans
    (cong (λ q → wires (iterQC (length gs) q)) (stepQC-gateProg g gs ws))
    (trans
      (iterQC-ignore-head (length gs) 0 (gateToInstr g) (gateProg gs)
        (applyGate g ws) (length ws) (noMeasure-gateProg (g ∷ gs)))
      (subst
        (λ len → wires (iterQC (length gs) (mkQC 0 len (applyGate g ws) (gateProg gs)))
          ≡ runGates gs (applyGate g ws))
        (length-applyGate g ws)
        (iterQC-gateProg gs (applyGate g ws))))

iterQC-gateProg-runInstrs
  : ∀ gs ws
  → wires (iterQC (length gs) (mkQC 0 (length ws) ws (gateProg gs)))
    ≡ runInstrs (gateProg gs) ws
iterQC-gateProg-runInstrs gs ws =
  trans (iterQC-gateProg gs ws) (runGates-runInstrs gs ws)

JumpBound : ℕ → QCInstr → Set
JumpBound _ QCHALT = ⊤
JumpBound _ QNOP = ⊤
JumpBound _ (QX _) = ⊤
JumpBound _ (QCNOT _ _) = ⊤
JumpBound _ (QTOFF _ _ _) = ⊤
JumpBound n (QMEASURE _ j k) = (j ≤ℕ n) × (k ≤ℕ n)

AllJumpBound : ℕ → List QCInstr → Set
AllJumpBound n = AllPred (JumpBound n)

lookupJumpBound
  : ∀ (n : ℕ) (xs : List QCInstr) (i : ℕ)
  → AllJumpBound n xs
  → JumpBound n (lookupDefault QCHALT xs i)
lookupJumpBound n xs i jb = lookupAllPred (JumpBound n) QCHALT xs i tt jb

noMeasure→jumpBound : ∀ {n instr} → NoMeasure instr → JumpBound n instr
noMeasure→jumpBound {instr = QMEASURE _ _ _} ()
noMeasure→jumpBound {instr = QCHALT} _ = tt
noMeasure→jumpBound {instr = QNOP} _ = tt
noMeasure→jumpBound {instr = QX _} _ = tt
noMeasure→jumpBound {instr = QCNOT _ _} _ = tt
noMeasure→jumpBound {instr = QTOFF _ _ _} _ = tt

allNoMeasure→allJumpBound
  : ∀ {n xs} → AllNoMeasure xs → AllJumpBound n xs
allNoMeasure→allJumpBound {xs = []} _ = tt
allNoMeasure→allJumpBound {n} {x ∷ xs} (nmX , nmXs) =
  noMeasure→jumpBound {n} {x} nmX , allNoMeasure→allJumpBound {n} {xs} nmXs

IdxBound : ℕ → ℕ → Set
IdxBound n i = suc i ≤ℕ n

WireBound : ℕ → QCInstr → Set
WireBound _ QCHALT = ⊤
WireBound _ QNOP = ⊤
WireBound n (QX i) = IdxBound n i
WireBound n (QCNOT c t) = IdxBound n c × IdxBound n t
WireBound n (QTOFF a b t) = IdxBound n a × IdxBound n b × IdxBound n t
WireBound n (QMEASURE i _ _) = IdxBound n i

AllWireBound : ℕ → List QCInstr → Set
AllWireBound n = AllPred (WireBound n)

GateBound : ℕ → Gate → Set
GateBound _ GNOP = ⊤
GateBound n (GX i) = IdxBound n i
GateBound n (GCNOT c t) = IdxBound n c × IdxBound n t
GateBound n (GTOFF a b t) = IdxBound n a × IdxBound n b × IdxBound n t

AllGateBound : ℕ → List Gate → Set
AllGateBound n = AllPred (GateBound n)

gateBound→wireBound : ∀ n g → GateBound n g → WireBound n (gateToInstr g)
gateBound→wireBound _ GNOP _ = tt
gateBound→wireBound _ (GX _) b = b
gateBound→wireBound _ (GCNOT _ _) b = b
gateBound→wireBound _ (GTOFF _ _ _) b = b

gateProg-wireBound : ∀ n gs → AllGateBound n gs → AllWireBound n (gateProg gs)
gateProg-wireBound _ [] _ = tt
gateProg-wireBound n (g ∷ gs) (b , bs) =
  gateBound→wireBound n g b , gateProg-wireBound n gs bs

wireBound-stepQC
  : ∀ q
  → AllWireBound (outLen q) (prog q)
  → AllWireBound (outLen q) (prog (stepQC q))
wireBound-stepQC q wb rewrite prog-stepQC q = wb

lookupDefault-notDefault-inRange
  : ∀ {A : Set} (d : A) (xs : List A) (i : ℕ)
  → lookupDefault d xs i ≢ d
  → suc i ≤ℕ length xs
lookupDefault-notDefault-inRange _ [] _ neq = ⊥-elim (neq refl)
lookupDefault-notDefault-inRange d (_ ∷ xs) zero _ = s≤s z≤n
lookupDefault-notDefault-inRange d (_ ∷ xs) (suc i) neq =
  s≤s (lookupDefault-notDefault-inRange d xs i neq)

pcInRange-nonDefault
  : ∀ q
  → pc q ≤ℕ length (prog q)
  → lookupDefault QCHALT (prog q) (pc q) ≢ QCHALT
  → suc (pc q) ≤ℕ length (prog q)
pcInRange-nonDefault q _ neq =
  lookupDefault-notDefault-inRange QCHALT (prog q) (pc q) neq

record WFCircuit (q : QuantumCircuitCode) : Set where
  field
    wiresOk   : WiresOk q
    pcBound   : pc q ≤ℕ length (prog q)
    jumpBound : AllJumpBound (length (prog q)) (prog q)
    wireBound : AllWireBound (outLen q) (prog q)

pcBound-stepQC
  : ∀ q
  → pc q ≤ℕ length (prog q)
  → AllJumpBound (length (prog q)) (prog q)
  → pc (stepQC q) ≤ℕ length (prog q)
pcBound-stepQC q pc≤ jb with inspect (lookupDefault QCHALT (prog q) (pc q))
... | instr , eq =
  subst
    (λ i → pc (stepQCInstr i q) ≤ℕ length (prog q))
    (sym eq)
    (handle instr eq
      (subst
        (λ i → JumpBound (length (prog q)) i)
        eq
        (lookupJumpBound (length (prog q)) (prog q) (pc q) jb)))
  where
    neqFrom
      : ∀ {instr}
      → instr ≢ QCHALT
      → lookupDefault QCHALT (prog q) (pc q) ≡ instr
      → lookupDefault QCHALT (prog q) (pc q) ≢ QCHALT
    neqFrom instr≢ eq eq' = instr≢ (trans (sym eq) eq')

    handle
      : (instr : QCInstr)
      → lookupDefault QCHALT (prog q) (pc q) ≡ instr
      → JumpBound (length (prog q)) instr
      → pc (stepQCInstr instr q) ≤ℕ length (prog q)
    handle QCHALT _ _ = pc≤
    handle (QMEASURE i j k) _ (j≤ , k≤) with lookupDefault false (wires q) i
    ... | true = k≤
    ... | false = j≤
    handle QNOP eq _ =
      lookupDefault-notDefault-inRange QCHALT (prog q) (pc q)
        (neqFrom QNOP≢QCHALT eq)
    handle (QX i) eq _ =
      lookupDefault-notDefault-inRange QCHALT (prog q) (pc q)
        (neqFrom (QX≢QCHALT i) eq)
    handle (QCNOT c t) eq _ =
      lookupDefault-notDefault-inRange QCHALT (prog q) (pc q)
        (neqFrom (QCNOT≢QCHALT c t) eq)
    handle (QTOFF a b t) eq _ =
      lookupDefault-notDefault-inRange QCHALT (prog q) (pc q)
        (neqFrom (QTOFF≢QCHALT a b t) eq)

jumpBound-stepQC
  : ∀ q
  → AllJumpBound (length (prog q)) (prog q)
  → AllJumpBound (length (prog q)) (prog (stepQC q))
jumpBound-stepQC q jb rewrite prog-stepQC q = jb

WFCircuit-stepQC : ∀ q → WFCircuit q → WFCircuit (stepQC q)
WFCircuit-stepQC q wf =
  record
    { wiresOk = WiresOk-stepQC q (WFCircuit.wiresOk wf)
    ; pcBound = subst
        (λ xs → pc (stepQC q) ≤ℕ length xs)
        (sym (prog-stepQC q))
        (pcBound-stepQC q (WFCircuit.pcBound wf) (WFCircuit.jumpBound wf))
    ; jumpBound = subst
        (λ len → AllJumpBound len (prog (stepQC q)))
        (sym (cong length (prog-stepQC q)))
        (jumpBound-stepQC q (WFCircuit.jumpBound wf))
    ; wireBound = subst
        (λ n → AllWireBound n (prog (stepQC q)))
        (sym (outLen-stepQC q))
        (wireBound-stepQC q (WFCircuit.wireBound wf))
    }

WFCircuit-noMeasure
  : ∀ q
  → WiresOk q
  → pc q ≤ℕ length (prog q)
  → AllNoMeasure (prog q)
  → AllWireBound (outLen q) (prog q)
  → WFCircuit q
WFCircuit-noMeasure q ok pc≤ nm wb =
  record
    { wiresOk = ok
    ; pcBound = pc≤
    ; jumpBound = allNoMeasure→allJumpBound nm
    ; wireBound = wb
    }

pcBound-stepQC-noMeasure
  : ∀ q
  → pc q ≤ℕ length (prog q)
  → AllNoMeasure (prog q)
  → pc (stepQC q) ≤ℕ length (prog q)
pcBound-stepQC-noMeasure q pc≤ nm =
  pcBound-stepQC q pc≤ (allNoMeasure→allJumpBound nm)

WFCircuit-stepQC-noMeasure
  : ∀ q
  → WiresOk q
  → pc q ≤ℕ length (prog q)
  → AllNoMeasure (prog q)
  → AllWireBound (outLen q) (prog q)
  → WFCircuit (stepQC q)
WFCircuit-stepQC-noMeasure q ok pc≤ nm wb =
  WFCircuit-stepQC q (WFCircuit-noMeasure q ok pc≤ nm wb)

WFCircuit-gateProg
  : ∀ n gs ws
  → length ws ≡ n
  → AllGateBound n gs
  → WFCircuit (mkQC 0 n ws (gateProg gs))
WFCircuit-gateProg n gs ws lenEq gb =
  record
    { wiresOk = lenEq
    ; pcBound = z≤n
    ; jumpBound = allNoMeasure→allJumpBound (noMeasure-gateProg gs)
    ; wireBound = gateProg-wireBound n gs gb
    }

-- --------------------------------------------------------------------------
-- Observer-facing interface (deterministic “Born without probabilities”)
--
-- This circuit model is basis-state only: measurement is deterministic and
-- returns the bit already present on a wire. That still supports the CQM shape:
-- “states + effects + measurement”, just without amplitudes.

boundaryWires : BoundaryObs Wires
boundaryWires = record { Obs = Wires ; observe = λ w → w }

Effect : Set₁
Effect = EffectAt boundaryWires

infix 4 _⊨_
_⊨_ : QuantumCircuitCode → Effect → Set
q ⊨ E = (wires q ⊨ᵇ boundaryWires) E

measureWire : ℕ → QuantumCircuitCode → Bool
measureWire i q = lookupDefault false (wires q) i
