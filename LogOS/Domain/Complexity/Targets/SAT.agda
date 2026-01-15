{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Targets.SAT where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)

open import LogOS.Base.Signature using (LogOSSignature)

open import LogOS.Domain.Complexity.LanguageWitnessW as LWW

-- A minimal, safe SAT (CNF) development:
-- - variables are ℕ
-- - a literal is (var, polarity)
-- - a clause is a list of literals (disjunction)
-- - a CNF is a list of clauses (conjunction)
--
-- We keep it simple and purely semantic; the “old-school TM” part is handled
-- elsewhere (encodings/backends). This module’s purpose is to provide a crisp
-- LogOS-native target language with a polynomial-size witness.

Lit : Set
Lit = ℕ × Bool

Clause : Set
Clause = List Lit

CNF : Set
CNF = List Clause

Assignment : Set
Assignment = ℕ → Bool

not : Bool → Bool
not true  = false
not false = true

infixr 6 _∧b_
infixr 5 _∨b_

_∧b_ : Bool → Bool → Bool
true  ∧b b = b
false ∧b _ = false

_∨b_ : Bool → Bool → Bool
true  ∨b _ = true
false ∨b b = b

evalLit : Assignment → Lit → Bool
evalLit ρ (v , pol) with pol
... | true  = ρ v
... | false = not (ρ v)

evalClause : Assignment → Clause → Bool
evalClause ρ [] = false
evalClause ρ (l ∷ ls) = evalLit ρ l ∨b evalClause ρ ls

evalCNF : Assignment → CNF → Bool
evalCNF ρ [] = true
evalCNF ρ (c ∷ cs) = evalClause ρ c ∧b evalCNF ρ cs

-- Formula size: count literals (a simple proxy).

clauseSize : Clause → ℕ
clauseSize [] = zero
clauseSize (_ ∷ ls) = suc (clauseSize ls)

cnfSize : CNF → ℕ
cnfSize [] = zero
cnfSize (c ∷ cs) = clauseSize c + cnfSize cs

-- We model witnesses as assignments plus a “witness size” measure.
-- To keep it clean and polynomial, we take witness size to be the input size itself.
-- (Domains can refine this to “#variables” once they fix a variable-bound extraction.)

wsize : CNF → Assignment → ℕ
wsize φ _ = cnfSize φ

SAT : CNF → Set
SAT φ = Σ Assignment (λ ρ → evalCNF ρ φ ≡ true)

-- A decidable checker for a candidate witness (just compute evalCNF and compare to true).

Check : CNF → Assignment → Set
Check φ ρ = evalCNF ρ φ ≡ true

decCheck : ∀ φ ρ → Check φ ρ ⊎ ¬ Check φ ρ
decCheck φ ρ with evalCNF ρ φ
... | true  = inj₁ refl
... | false = inj₂ (λ ())

-- SAT has a witness system with polynomial witness size (trivially, bound = identity).

WS-SAT : LWW.WitnessSystemW CNF SAT
WS-SAT =
  record
    { W = λ _ → Assignment
    ; wsize = λ {φ} ρ → wsize φ ρ
    ; size = cnfSize
    ; polyBound = λ n → n
    ; Check = Check
    ; decCheck = decCheck
    ; sound = λ φ ρ pr → ρ , pr
    ; complete = λ φ sat →
        let ρ = proj₁ sat
            pr = proj₂ sat
        in ρ , (LWW.≤ℕ-refl , pr)
    }

-- -------------------------------------------------------------------------
-- Cost-guard graded separation (previously in SATPhysicalSeparationCostGuardsGraded).
-- -------------------------------------------------------------------------

module CostGuardsGraded where
  open import LogOS.Minimal.Adapter using (QAdapter)
  open import LogOS.Kernel.Graded
  open import LogOS.Domain.Complexity.Poly using (PolyPred)
  import LogOS.Domain.Complexity.PhysicsClassesWCostGuardsGraded as PCWCG
  import LogOS.Domain.Complexity.PhysProofBridgeWCostGuardsGraded as PBWCG
  import LogOS.Domain.Complexity.PhysSeparationPipelineWCostGuardsGraded as Pipe

  module For {ℓQ : Level}
             (Pℕ : PolyPred)
             (Q  : QAdapter ℓQ)
             (gradeBound : ℕ → QAdapter.Scale Q)
             (monoGradeBound : ∀ {m n} → m ≤ℕ n → QAdapter._≤s_ Q (gradeBound m) (gradeBound n))
             where

    module C = PCWCG.For {ℓI = lzero} {ℓW = lzero} {ℓ = lzero} {ℓQ = ℓQ} CNF cnfSize Pℕ Q gradeBound
    module B = PBWCG.For {ℓI = lzero} {ℓW = lzero} {ℓ = lzero} {ℓQ = ℓQ} CNF cnfSize Pℕ Q gradeBound
    module P = Pipe.For {ℓI = lzero} {ℓW = lzero} {ℓ = lzero} {ℓQ = ℓQ} CNF cnfSize Pℕ Q gradeBound

    SATL : C.Language
    SATL = SAT

    inPhysNPwCostGuards-SAT : C.PhysNPwCostGuards SATL
    inPhysNPwCostGuards-SAT =
      ( record
          { PW =
              record
                { WS        = WS-SAT
                ; checkCost = λ φ _ → gradeBound (cnfSize φ)
                ; checkBound = λ n → n
                ; polyCheck = PolyPred.id-isPoly Pℕ
                ; checkCost≤ = λ _ _ → monoGradeBound ≤ℕ-refl
                }
          ; wsize≤checkCost = λ _ _ → monoGradeBound ≤ℕ-refl
          }
      , tt
      )

    separationFromProof
      : (MM : B.MergeMeasure SATL)
      → B.ProofLowerBound SATL MM
      → P.Claim SATL
    separationFromProof MM PLB =
      P.Pack.claim
        (P.mkPack (record { inNPwCostGuards = inPhysNPwCostGuards-SAT ; MM = MM ; PLB = PLB }))

  module Kernel
    {ℓ ℓP ℓA : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
    (DetRun : CNF → GradedKernel.Code K)
    (VerRun : CNF → GradedKernel.Code K)
    (VerRunWith : CNF → GradedKernel.Code K → GradedKernel.Code K)
    (IsPoly : (ℕ → ℕ) → Set ℓP)
    (gradeBound : ℕ → QAdapter.Scale Q)
    (WSize : GradedKernel.Code K → ℕ)
    where

    module C = PCWCG.Kernel K CNF cnfSize DetRun VerRun VerRunWith IsPoly gradeBound WSize
    module B = PBWCG.Kernel K CNF cnfSize DetRun VerRun VerRunWith IsPoly gradeBound WSize
    module P = Pipe.Kernel K CNF cnfSize DetRun VerRun VerRunWith IsPoly gradeBound WSize

    separationFromProof
      : {Acc : C.Con → Set ℓA}
        → C.PhysNPwCostGuards Acc
        → (MM : B.MergeMeasure Acc)
        → B.ProofLowerBound Acc MM
        → P.Claim Acc
    separationFromProof inNPwCostGuards MM PLB =
      P.Pack.claim
        (P.mkPack (record { inNPwCostGuards = inNPwCostGuards ; MM = MM ; PLB = PLB }))
