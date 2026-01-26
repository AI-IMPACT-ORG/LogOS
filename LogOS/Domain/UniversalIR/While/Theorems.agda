{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.While.Theorems where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Std
open import LogOS.Domain.UniversalIR.Core
open import LogOS.Domain.UniversalIR.IR using (lowerToIR; decode; observe)

open import LogOS.Domain.UniversalIR.While.Language
open import LogOS.Domain.UniversalIR.While.Semantics
open import LogOS.Domain.UniversalIR.While.Compile

open import LogOS.Domain.UniversalIR.Languages.Minsky as Minsky using (fuelMul; fuelInnerMul; fuelRestoreMul; perIterMul)

open import LogOS.Prelude.List using (List; []; _∷_)

-- --------------------------------------------------------------------------
-- Source meaning: factorial as a terminating big-step execution.

fact : ℕ → ℕ
fact zero    = suc zero
fact (suc n) = (suc n) * fact n

loopBody : Stmt
loopBody = mulAB >> dec B

whileMulDec-spec :
  ∀ acc n →
  Exec (whileNZ B loopBody) ⟨ acc , n ⟩ ⟨ acc * fact n , 0 ⟩
whileMulDec-spec acc zero
  rewrite *-oneʳ acc
  = exec-while-zero refl
whileMulDec-spec acc (suc n) =
  exec-while-step refl
    (exec-seq exec-mulAB exec-dec)
    (subst (Exec (whileNZ B loopBody) ⟨ acc * suc n , n ⟩)
           (cong (λ x → ⟨ x , 0 ⟩) (*-assoc acc (suc n) (fact n)))
           (whileMulDec-spec (acc * suc n) n))

factorial-spec : ∀ n → Exec factorial ⟨ 0 , n ⟩ ⟨ fact n , 0 ⟩
factorial-spec n =
  exec-seq
    -- set1 A : clears A (already 0) then increments to 1
    (exec-seq (exec-while-zero refl) exec-inc)
    (subst (Exec (whileNZ B loopBody) ⟨ 1 , n ⟩)
           (cong (λ x → ⟨ x , 0 ⟩) (*-oneˡ (fact n)))
           (whileMulDec-spec 1 n))

-- --------------------------------------------------------------------------
-- Minsky backend: end-to-end correctness for the compiled factorial code.

-- Transfer loop at pc = 11..12: move R0 into R1, clearing R0.

transferR0→R1 :
  ∀ r0 r1 r2 →
  simulate (fuelAddR1 r0) (UM (mkM 11 r0 r1 r2 0 progFactM))
    ≡ UM (mkM 13 0 (r1 + r0) r2 0 progFactM)
transferR0→R1 zero r1 r2 =
  cong (λ x → UM (mkM 13 0 x r2 0 progFactM)) (sym (+-zeroʳ r1))
transferR0→R1 (suc r0) r1 r2 =
  trans
    (transferR0→R1 r0 (suc r1) r2)
    (cong (λ x → UM (mkM 13 0 x r2 0 progFactM))
          (trans refl (sym (+-sucʳ r1 r0))))

-- Output loop at pc = 14..15: move R1 into R0, clearing R1.

transferR1→R0 :
  ∀ r0 r1 r2 →
  simulate (fuelAddR1 r1) (UM (mkM 14 r0 r1 r2 0 progFactM))
    ≡ UM (mkM 16 (r0 + r1) 0 r2 0 progFactM)
transferR1→R0 r0 zero r2 =
  cong (λ x → UM (mkM 16 x 0 r2 0 progFactM)) (sym (+-zeroʳ r0))
transferR1→R0 r0 (suc r1) r2 =
  trans
    (transferR1→R0 (suc r0) r1 r2)
    (cong (λ x → UM (mkM 16 x 0 r2 0 progFactM))
          (trans refl (sym (+-sucʳ r0 r1))))

-- Non-trivial: correctness of the inlined multiplication macro (pcs 0..5).

mulInner :
  ∀ r0 r1 r2 r3 →
  simulate (fuelInnerMul r2) (UM (mkM 1 r0 r1 r2 r3 progFactM))
    ≡ UM (mkM 4 (r0 + r2) r1 0 (r3 + r2) progFactM)
mulInner r0 r1 zero    r3
  rewrite +-zeroʳ r0 | +-zeroʳ r3
  = refl
mulInner r0 r1 (suc r2) r3 =
  trans
    (mulInner (suc r0) r1 r2 (suc r3))
    (cong₂ (λ x y → UM (mkM 4 x r1 0 y progFactM))
           (swapSuc r0 r2)
           (swapSuc r3 r2))

mulRestore :
  ∀ r0 r1 r2 r3 →
  simulate (fuelRestoreMul r3) (UM (mkM 4 r0 r1 r2 r3 progFactM))
    ≡ UM (mkM 0 r0 r1 (r2 + r3) 0 progFactM)
mulRestore r0 r1 r2 zero
  rewrite +-zeroʳ r2
  = refl
mulRestore r0 r1 r2 (suc r3) =
  trans
    (mulRestore r0 r1 (suc r2) r3)
    (cong (λ x → UM (mkM 0 r0 r1 x 0 progFactM))
          (swapSuc r2 r3))

mulIter :
  ∀ r0 a b →
  simulate (perIterMul b) (UM (mkM 0 r0 (suc a) b 0 progFactM))
    ≡ UM (mkM 0 (r0 + b) a b 0 progFactM)
mulIter r0 a b =
  trans
    (simulate-+ (fuelInnerMul b) (fuelRestoreMul b)
      (UM (mkM 1 r0 a b 0 progFactM)))
    (trans
      (cong (λ u → simulate (fuelRestoreMul b) u) (mulInner r0 a b 0))
      (mulRestore (r0 + b) a 0 b))

mulSim :
  ∀ acc a b →
  simulate (fuelMul a b) (UM (mkM 0 acc a b 0 progFactM))
    ≡ UM (mkM 6 (acc + (a * b)) 0 b 0 progFactM)
mulSim acc zero    b
  rewrite +-zeroʳ acc
  = refl
mulSim acc (suc a) b =
  trans
    (simulate-+ (perIterMul b) (fuelMul a b)
      (UM (mkM 0 acc (suc a) b 0 progFactM)))
    (trans
      (cong (λ u → simulate (fuelMul a b) u) (mulIter acc a b))
      (trans
        (mulSim (acc + b) a b)
        (cong (λ x → UM (mkM 6 x 0 b 0 progFactM))
              (+-assoc acc b (a * b)))))

-- One full loop iteration (B = suc n) from pc = 8 back to pc = 8.

iterFuelM : ℕ → ℕ → ℕ
iterFuelM acc (suc n) = 3 + (fuelMul acc (suc n) + (1 + fuelAddR1 (acc * suc n) + 1))
iterFuelM _   zero    = 0

iterStepM :
  ∀ acc n →
  simulate (iterFuelM acc (suc n)) (UM (mkM 8 0 acc (suc n) 0 progFactM))
    ≡ UM (mkM 8 0 (acc * suc n) n 0 progFactM)
iterStepM acc n =
  let
    b : ℕ
    b = suc n

    rest : ℕ
    rest = fuelMul acc b + (1 + fuelAddR1 (acc * b) + 1)

    S0 : UCode
    S0 = UM (mkM 8 0 acc b 0 progFactM)

    S1 : UCode
    S1 = UM (mkM 0 0 acc b 0 progFactM)

    S2 : UCode
    S2 = UM (mkM 6 (acc * b) 0 b 0 progFactM)

    S3 : UCode
    S3 = UM (mkM 11 (acc * b) 0 b 0 progFactM)

    S4 : UCode
    S4 = UM (mkM 13 0 (acc * b) b 0 progFactM)

    toCall : simulate 3 S0 ≡ S1
    toCall = refl

    mulDone : simulate (fuelMul acc b) S1 ≡ S2
    mulDone =
      trans
        (mulSim 0 acc b)
        refl

    retJump : simulate 1 S2 ≡ S3
    retJump = refl

    moved : simulate (fuelAddR1 (acc * b)) S3 ≡ S4
    moved = transferR0→R1 (acc * b) 0 b

    decB : simulate 1 S4 ≡ UM (mkM 8 0 (acc * b) n 0 progFactM)
    decB = refl
  in
  trans
    (simulate-+ 3 rest S0)
    (trans
      (cong (λ u → simulate rest u) toCall)
      (trans
        (simulate-+ (fuelMul acc b) (1 + fuelAddR1 (acc * b) + 1) S1)
        (trans
          (cong (λ u → simulate (1 + fuelAddR1 (acc * b) + 1) u) mulDone)
          (trans
            (simulate-+ 1 (fuelAddR1 (acc * b) + 1) S2)
            (trans
              (cong (λ u → simulate (fuelAddR1 (acc * b) + 1) u) retJump)
              (trans
                (simulate-+ (fuelAddR1 (acc * b)) 1 S3)
                (trans
                  (cong (λ u → simulate 1 u) moved)
                  decB)))))))

-- Total loop fuel from pc = 8 until we exit to pc = 14.

fuelLoopM : ℕ → ℕ → ℕ
fuelLoopM acc zero    = suc zero                       -- DECJZ at pc=8 takes the exit
fuelLoopM acc (suc n) = iterFuelM acc (suc n) + fuelLoopM (acc * suc n) n

loopSimM :
  ∀ acc n →
  simulate (fuelLoopM acc n) (UM (mkM 8 0 acc n 0 progFactM))
    ≡ UM (mkM 14 0 (acc * fact n) 0 0 progFactM)
loopSimM acc zero
  rewrite *-oneʳ acc
  = refl
loopSimM acc (suc n) =
  trans
    (simulate-+ (iterFuelM acc (suc n)) (fuelLoopM (acc * suc n) n)
      (UM (mkM 8 0 acc (suc n) 0 progFactM)))
    (trans
      (cong (λ u → simulate (fuelLoopM (acc * suc n) n) u) (iterStepM acc n))
      (trans
        (loopSimM (acc * suc n) n)
        (cong (λ x → UM (mkM 14 0 x 0 0 progFactM))
              (*-assoc acc (suc n) (fact n)))))

-- Full factorial run, ending at HALT (pc = 16) with the answer in R0.

fuelFactM : ℕ → ℕ
fuelFactM n = suc (fuelLoopM 1 n + fuelAddR1 (fact n))

factSimM :
  ∀ n →
  simulate (fuelFactM n) (UM (compileMinsky (mkFact n)))
    ≡ UM (mkM 16 (fact n) 0 0 0 progFactM)
factSimM n =
  trans
    (simulate-+ 1 (fuelLoopM 1 n + fuelAddR1 (fact n))
      (UM (compileMinsky (mkFact n))))
    (trans
      refl
      (trans
        (simulate-+ (fuelLoopM 1 n) (fuelAddR1 (fact n))
          (UM (mkM 8 0 1 n 0 progFactM)))
        (trans
          (cong (λ u → simulate (fuelAddR1 (fact n)) u) (loopSimM 1 n))
          (trans
            (cong (λ u → simulate (fuelAddR1 (fact n)) u)
                  (cong (λ x → UM (mkM 14 0 x 0 0 progFactM)) (*-oneˡ (fact n))))
            (trans
              (transferR1→R0 0 (fact n) 0)
              refl)))))

minsky-factorial-correct :
  ∀ n →
  observe (simulate (fuelFactM n) (UM (compileMinsky (mkFact n)))) ≡ fact n
minsky-factorial-correct n =
  trans
    (cong (λ u → decode (lowerToIR u)) (factSimM n))
    (decodeChurch-church (fact n))
