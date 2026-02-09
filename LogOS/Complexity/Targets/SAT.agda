{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.Targets.SAT where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)
open import LogOS.Prelude using (Setω)

open import LogOS.Prelude using (ℕ; zero; suc; _+_)
open import LogOS.Prelude using (Σ; _,_; _×_; proj₁; proj₂)
open import LogOS.Prelude using (_⊎_; inj₁; inj₂)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; ≤ℕ-refl)

open import LogOS.Prelude.Bool using (Bool; true; false)
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Base.Signature using (LogOSSignature)

open import LogOS.Complexity.Poly using (PolyPred)
import LogOS.Complexity.PvsNPLedger as CP
open import LogOS.Complexity.LanguageWitnessW as LWW
import LogOS.Theorems.Meta.ApplicationKit as AppKit

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

-- Classical alignment: SAT ∈ NP (literature-aligned interface).

module Classical (Pℕ : PolyPred) where
  module C = CP.For {ℓI = lzero} {ℓW = lzero} {ℓ = lzero} CNF cnfSize Pℕ

  SATInNP : C.InNP SAT
  SATInNP =
    ( record
        { WS        = WS-SAT
        ; checkCost = λ φ _ → cnfSize φ
        ; checkBound = λ n → n
        ; polyCheck = PolyPred.id-isPoly Pℕ
        ; checkCost≤ = λ _ _ → ≤ℕ-refl
        }
    , tt
    )

-- ETH-aligned assumption pack (classical surface).

module ClassicalETH (Pℕ : PolyPred) where
  module C = CP.For {ℓI = lzero} {ℓW = lzero} {ℓ = lzero} CNF cnfSize Pℕ

  HardWitness : C.PolyTimeDecider SAT → Set
  HardWitness PD =
    Σ CNF (λ φ → ¬ (C.PolyTimeDecider.cost PD φ ≤ℕ
                    C.PolyTimeDecider.bound PD (cnfSize φ)))

  record Assumptions : Set (lsuc (lsuc lzero)) where
    field
      hard : ∀ (PD : C.PolyTimeDecider SAT) → HardWitness PD

  record Claim : Set (lsuc (lsuc lzero)) where
    field
      inNP : C.InNP SAT
      notP : ¬ C.InP SAT

  separationW : Assumptions → C.SeparationW SAT
  separationW A =
    record
      { inNPw = Classical.SATInNP Pℕ
      ; detSuperPoly = Assumptions.hard A
      }

  p≠np : Assumptions → C.P≠NP
  p≠np A = C.sep→P≠NP (separationW A)

  derive : Assumptions → Claim
  derive A =
    record
      { inNP = Classical.SATInNP Pℕ
      ; notP = C.notInP (Assumptions.hard A)
      }

  module Q = AppKit.MakeConstPack Assumptions Claim derive
  open Q public using (Pack; mkPack; assumptionsOf; claimOf)

-- NP-completeness axiom pack (classical surface).

module ClassicalNPComplete (Pℕ : PolyPred) where
  open import LogOS.Complexity.Reduction as Red

  module SATC = CP.For {ℓI = lzero} {ℓW = lzero} {ℓ = lzero} CNF cnfSize Pℕ

  record Assumptions : Setω where
    field
      reduce
        : ∀ {ℓI}
          {Input : Set ℓI}
          (size : Input → ℕ)
          (L : Input → Set lzero)
        → (let module C = CP.For {ℓI = ℓI} {ℓW = lzero} {ℓ = lzero} Input size Pℕ in C.InNP L)
        → Red.PolyReduction Input CNF L SAT size cnfSize Pℕ

  npInPFromSAT
    : (A : Assumptions)
      → (inSATP : SATC.InP SAT)
      → (boundMono : ∀ {m n} → m ≤ℕ n →
           SATC.PolyTimeDecider.bound (proj₁ inSATP) m ≤ℕ
           SATC.PolyTimeDecider.bound (proj₁ inSATP) n)
      → (polyComp : ∀ {ℓI}
           {Input : Set ℓI}
           (size : Input → ℕ)
           (L : Input → Set lzero)
           (inNP : (let module C = CP.For {ℓI = ℓI} {ℓW = lzero} {ℓ = lzero} Input size Pℕ in C.InNP L))
           → PolyPred.isPoly Pℕ
               (λ n →
                 SATC.PolyTimeDecider.bound (proj₁ inSATP)
                   (Red.PolyReduction.bound (Assumptions.reduce A size L inNP) n)))
      → ∀ {ℓI}
          {Input : Set ℓI}
          (size : Input → ℕ)
          (L : Input → Set lzero)
          (inNP : (let module C = CP.For {ℓI = ℓI} {ℓW = lzero} {ℓ = lzero} Input size Pℕ in C.InNP L))
          → (let module C = CP.For {ℓI = ℓI} {ℓW = lzero} {ℓ = lzero} Input size Pℕ in C.InP L)
  npInPFromSAT A inSATP boundMono polyComp {ℓI} {Input = Input} size L inNP =
    let module C = CP.For {ℓI = ℓI} {ℓW = lzero} {ℓ = lzero} Input size Pℕ
        module R = Red.Classical {ℓI₁ = ℓI} {ℓI₂ = lzero} {ℓ = lzero}
                          Input CNF size cnfSize Pℕ
        red = Assumptions.reduce A size L inNP
    in
    R.inPFromPolyReduction red inSATP boundMono (polyComp size L inNP)

-- -------------------------------------------------------------------------
-- Cost-guard graded separation (previously in SATPhysicalSeparationCostGuardsGraded).
-- -------------------------------------------------------------------------

module CostGuardsGraded where
  open import LogOS.Minimal.Adapter using (QAdapter)
  open import LogOS.API.Kernel.Graded
  open import LogOS.Complexity.Poly using (PolyPred)
  import LogOS.Complexity.PhysicsClassesWCostGuardsGraded as PCWCG
  import LogOS.Complexity.PhysProofBridgeWCostGuardsGraded as PBWCG
  import LogOS.Complexity.PhysSeparationPipelineWCostGuardsGraded as Pipe

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
        (P.mkPack
          (record
            { inNPwCostGuards = inPhysNPwCostGuards-SAT
            ; MM = MM
            ; PLB = PLB
            }))

    module SATFromProof where
      record Assumptions : Set (lsuc (lsuc (ℓQ ⊔ lzero))) where
        field
          MM  : B.MergeMeasure SATL
          PLB : B.ProofLowerBound SATL MM

      Claim : Set (lsuc (lsuc (ℓQ ⊔ lzero)))
      Claim = P.Claim SATL

      mkPack : Assumptions → P.Pack {L = SATL}
      mkPack A =
        P.mkPack
          (record
            { inNPwCostGuards = inPhysNPwCostGuards-SAT
            ; MM             = Assumptions.MM A
            ; PLB            = Assumptions.PLB A
            })

      pack : Assumptions → P.Pack {L = SATL}
      pack = mkPack

      claim : Assumptions → Claim
      claim A = P.Pack.claim (mkPack A)

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
        → C.PhysTotalNPwCostGuards Acc
        → (MM : B.MergeMeasure Acc)
        → B.ProofLowerBound Acc MM
        → P.Claim Acc
    separationFromProof inTotalNPwCostGuards MM PLB =
      P.Pack.claim
        (P.mkPack
          (record
            { inTotalNPwCostGuards = inTotalNPwCostGuards
            ; MM = MM
            ; PLB = PLB
            }))
