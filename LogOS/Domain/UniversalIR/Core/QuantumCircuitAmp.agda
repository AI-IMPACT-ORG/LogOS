{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Core.QuantumCircuitAmp where

open import LogOS.Prelude hiding (_+_; _*_)

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; fzero; fsuc)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Product using (_×_; _,_)
open import LogOS.Domain.UniversalIR.Core.Utils using (lookupDefault)

-- Abstract scalar interface for amplitude-level semantics.
-- The laws (unitarity, norm preservation) are intentionally left abstract.

record QScalars {ℓ : Level} : Set (lsuc ℓ) where
  infixl 6 _+_
  infixl 7 _*_
  infix  8 -_
  field
    Carrier  : Set ℓ
    0# 1#    : Carrier
    _+_ _*_  : Carrier → Carrier → Carrier
    -_       : Carrier → Carrier
    conj     : Carrier → Carrier
    invSqrt2 : Carrier
    invSqrt  : Carrier → Carrier

module For {ℓ} (S : QScalars {ℓ}) where
  open QScalars S
    renaming
      ( Carrier to Scalar
      ; _+_ to _+S_
      ; _*_ to _*S_
      ; -_ to negS
      ; conj to conjS
      ; invSqrt2 to invSqrt2S
      ; invSqrt to invSqrtS
      )

  -- Length-indexed wires (basis states).
  infixr 5 _∷_
  data Wires : ℕ → Set where
    []  : Wires zero
    _∷_ : ∀ {n} → Bool → Wires n → Wires (suc n)

  not : Bool → Bool
  not true  = false
  not false = true

  lookupAt : ∀ {n} → Fin n → Wires n → Bool
  lookupAt fzero (b ∷ _) = b
  lookupAt (fsuc i) (_ ∷ ws) = lookupAt i ws

  updateAt : ∀ {n} → Fin n → (Bool → Bool) → Wires n → Wires n
  updateAt fzero f (b ∷ ws) = f b ∷ ws
  updateAt (fsuc i) f (b ∷ ws) = b ∷ updateAt i f ws

  setAt : ∀ {n} → Fin n → Bool → Wires n → Wires n
  setAt i v = updateAt i (λ _ → v)

  flipAt : ∀ {n} → Fin n → Wires n → Wires n
  flipAt i = updateAt i not

  applyCNOT : ∀ {n} → Fin n → Fin n → Wires n → Wires n
  applyCNOT ctrl tgt ws with lookupAt ctrl ws
  ... | true  = flipAt tgt ws
  ... | false = ws

  applyTOFF : ∀ {n} → Fin n → Fin n → Fin n → Wires n → Wires n
  applyTOFF c1 c2 tgt ws with lookupAt c1 ws | lookupAt c2 ws
  ... | true  | true  = flipAt tgt ws
  ... | true  | false = ws
  ... | false | true  = ws
  ... | false | false = ws

  -- Finite sum over all basis states.
  sumWires : ∀ {n} → (Wires n → Scalar) → Scalar
  sumWires {zero} f = f []
  sumWires {suc n} f =
    sumWires (λ ws → f (false ∷ ws)) +S sumWires (λ ws → f (true ∷ ws))

  State : ℕ → Set ℓ
  State n = Wires n → Scalar

  abs2 : Scalar → Scalar
  abs2 x = conjS x *S x

  record QState (n : ℕ) : Set (lsuc ℓ) where
    field
      amp     : State n
      norm≡1  : sumWires (λ w → abs2 (amp w)) ≡ 1#

  record RawDist (n : ℕ) : Set (lsuc ℓ) where
    field
      p : Wires n → Scalar

  record Dist (n : ℕ) : Set (lsuc ℓ) where
    field
      p      : Wires n → Scalar
      sum≡1  : sumWires p ≡ 1#

  measure : ∀ {n} → QState n → Dist n
  measure ψ = record
    { p     = λ w → abs2 (QState.amp ψ w)
    ; sum≡1 = QState.norm≡1 ψ
    }

  measureRaw : ∀ {n} → State n → RawDist n
  measureRaw ψ = record { p = λ w → abs2 (ψ w) }

  -- Weighted finite distributions (support list, no normalization proof).
  record DistList {ℓA : Level} (A : Set ℓA) : Set (lsuc (ℓ ⊔ ℓA)) where
    field
      support : List (Scalar × A)

  pureDist : ∀ {ℓA} {A : Set ℓA} → A → DistList A
  pureDist a = record { support = (1# , a) ∷ [] }

  scaleSupport : ∀ {ℓA} {A : Set ℓA} → Scalar → List (Scalar × A) → List (Scalar × A)
  scaleSupport _ [] = []
  scaleSupport w ((v , a) ∷ xs) = (w *S v , a) ∷ scaleSupport w xs

  scaleDist : ∀ {ℓA} {A : Set ℓA} → Scalar → DistList A → DistList A
  scaleDist w d = record { support = scaleSupport w (DistList.support d) }

  bindDist : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → DistList A → (A → DistList B) → DistList B
  bindDist {A = A} {B = B} d f = record { support = bind (DistList.support d) }
    where
    bind : List (Scalar × A) → List (Scalar × B)
    bind [] = []
    bind ((w , a) ∷ xs) =
      scaleSupport w (DistList.support (f a)) ++ bind xs

  -- Enumerate all wires (basis states) of length n.
  allWires : ∀ n → List (Wires n)
  allWires zero = [] ∷ []
  allWires (suc n) =
    map (λ ws → false ∷ ws) (allWires n) ++ map (λ ws → true ∷ ws) (allWires n)

  distFromState : ∀ {n} → State n → DistList (Wires n)
  distFromState {n} ψ =
    record
      { support = map (λ w → (abs2 (ψ w) , w)) (allWires n)
      }

  -- Amplitude-level gates (unitary fragment).
  data QCInstrA (n : ℕ) : Set where
    QCHALT : QCInstrA n
    QX     : Fin n → QCInstrA n
    QH     : Fin n → QCInstrA n
    QCNOT  : Fin n → Fin n → QCInstrA n
    QTOFF  : Fin n → Fin n → Fin n → QCInstrA n

  -- Linear action on amplitudes.
  --
  -- For involutive classical gates (X/CNOT/TOFF), the unitary action is a
  -- permutation of basis states, hence precomposition.

  applyH : ∀ {n} → Fin n → State n → State n
  applyH i ψ w with lookupAt i w
  ... | false =
    invSqrt2S *S (ψ (setAt i false w) +S ψ (setAt i true w))
  ... | true =
    invSqrt2S *S (ψ (setAt i false w) +S negS (ψ (setAt i true w)))

  applyInstr : ∀ {n} → QCInstrA n → State n → State n
  applyInstr QCHALT ψ = ψ
  applyInstr (QX i) ψ = λ w → ψ (flipAt i w)
  applyInstr (QH i) ψ = applyH i ψ
  applyInstr (QCNOT c t) ψ = λ w → ψ (applyCNOT c t w)
  applyInstr (QTOFF a b t) ψ = λ w → ψ (applyTOFF a b t w)

  record QuantumCircuitAmpCode : Set (lsuc ℓ) where
    constructor mkQCA
    field
      pc     : ℕ
      outLen : ℕ
      state  : State outLen
      prog   : List (QCInstrA outLen)

  open QuantumCircuitAmpCode public

  setPCQCA : ℕ → QuantumCircuitAmpCode → QuantumCircuitAmpCode
  setPCQCA n q = mkQCA n (outLen q) (state q) (prog q)

  setStateQCA : (q : QuantumCircuitAmpCode) → State (outLen q) → QuantumCircuitAmpCode
  setStateQCA q s = mkQCA (pc q) (outLen q) s (prog q)

  stepQCAInstr : (q : QuantumCircuitAmpCode) → QCInstrA (outLen q) → QuantumCircuitAmpCode
  stepQCAInstr q QCHALT = q
  stepQCAInstr q (QX i) =
    setPCQCA (suc (pc q)) (setStateQCA q (applyInstr (QX i) (state q)))
  stepQCAInstr q (QH i) =
    setPCQCA (suc (pc q)) (setStateQCA q (applyInstr (QH i) (state q)))
  stepQCAInstr q (QCNOT c t) =
    setPCQCA (suc (pc q)) (setStateQCA q (applyInstr (QCNOT c t) (state q)))
  stepQCAInstr q (QTOFF a b t) =
    setPCQCA (suc (pc q)) (setStateQCA q (applyInstr (QTOFF a b t) (state q)))

  stepQCA : QuantumCircuitAmpCode → QuantumCircuitAmpCode
  stepQCA q = stepQCAInstr q (lookupDefault QCHALT (prog q) (pc q))

  -- Measurement-extended instruction set and probabilistic stepping.
  data QCInstrP (n : ℕ) : Set where
    QCHALT   : QCInstrP n
    QX       : Fin n → QCInstrP n
    QH       : Fin n → QCInstrP n
    QCNOT    : Fin n → Fin n → QCInstrP n
    QTOFF    : Fin n → Fin n → Fin n → QCInstrP n
    QMEASURE : Fin n → ℕ → ℕ → QCInstrP n   -- measure wire i; jump to j/k

  record QuantumCircuitAmpPCode (n : ℕ) : Set (lsuc ℓ) where
    constructor mkQCAP
    field
      pc    : ℕ
      state : State n
      prog  : List (QCInstrP n)

  open QuantumCircuitAmpPCode public

  setPCQCAP : ∀ {n} → ℕ → QuantumCircuitAmpPCode n → QuantumCircuitAmpPCode n
  setPCQCAP n q = mkQCAP n (state q) (prog q)

  setStateQCAP : ∀ {n} → State n → QuantumCircuitAmpPCode n → QuantumCircuitAmpPCode n
  setStateQCAP s q = mkQCAP (pc q) s (prog q)

  applyInstrP : ∀ {n} → QCInstrP n → State n → State n
  applyInstrP QCHALT ψ = ψ
  applyInstrP (QX i) ψ = applyInstr (QX i) ψ
  applyInstrP (QH i) ψ = applyInstr (QH i) ψ
  applyInstrP (QCNOT c t) ψ = applyInstr (QCNOT c t) ψ
  applyInstrP (QTOFF a b t) ψ = applyInstr (QTOFF a b t) ψ
  applyInstrP (QMEASURE _ _ _) ψ = ψ

  scaleState : ∀ {n} → Scalar → State n → State n
  scaleState c ψ = λ w → c *S ψ w

  projFalse : ∀ {n} → Fin n → State n → State n
  projFalse i ψ w with lookupAt i w
  ... | false = ψ w
  ... | true  = 0#

  projTrue : ∀ {n} → Fin n → State n → State n
  projTrue i ψ w with lookupAt i w
  ... | true  = ψ w
  ... | false = 0#

  probFalse : ∀ {n} → Fin n → State n → Scalar
  probFalse i ψ = sumWires (λ w → abs2 (projFalse i ψ w))

  probTrue : ∀ {n} → Fin n → State n → Scalar
  probTrue i ψ = sumWires (λ w → abs2 (projTrue i ψ w))

  collapseFalse : ∀ {n} → Fin n → State n → State n
  collapseFalse i ψ = scaleState (invSqrtS (probFalse i ψ)) (projFalse i ψ)

  collapseTrue : ∀ {n} → Fin n → State n → State n
  collapseTrue i ψ = scaleState (invSqrtS (probTrue i ψ)) (projTrue i ψ)

  stepQCAProb : ∀ {n} → QuantumCircuitAmpPCode n → DistList (QuantumCircuitAmpPCode n)
  stepQCAProb q with lookupDefault QCHALT (prog q) (pc q)
  ... | QCHALT = pureDist q
  ... | QX i =
    pureDist (setPCQCAP (suc (pc q)) (setStateQCAP (applyInstrP (QX i) (state q)) q))
  ... | QH i =
    pureDist (setPCQCAP (suc (pc q)) (setStateQCAP (applyInstrP (QH i) (state q)) q))
  ... | QCNOT c t =
    pureDist (setPCQCAP (suc (pc q)) (setStateQCAP (applyInstrP (QCNOT c t) (state q)) q))
  ... | QTOFF a b t =
    pureDist (setPCQCAP (suc (pc q)) (setStateQCAP (applyInstrP (QTOFF a b t) (state q)) q))
  ... | QMEASURE i j k =
    record
      { support =
          (probFalse i (state q) , setPCQCAP j (setStateQCAP (collapseFalse i (state q)) q))
          ∷ (probTrue i (state q) , setPCQCAP k (setStateQCAP (collapseTrue i (state q)) q))
          ∷ []
      }

  stepDistQCA : ∀ {n} → DistList (QuantumCircuitAmpPCode n) → DistList (QuantumCircuitAmpPCode n)
  stepDistQCA d = bindDist d stepQCAProb

  observeDist : ∀ {n} → QuantumCircuitAmpPCode n → DistList (Wires n)
  observeDist q = distFromState (state q)

  observeDistList : ∀ {n} → DistList (QuantumCircuitAmpPCode n) → DistList (Wires n)
  observeDistList d = bindDist d observeDist
