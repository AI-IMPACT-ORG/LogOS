{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.WFGraph.FormulaKernel where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Syntax.Prop using (_↔_; intro)

open import Data.Product using (Σ; _,_; _×_)
open import Data.Fin using (Fin)

open import LogOS.ObjectLogic.FOL.Semantics as FOLSem

open import LogOS.Domain.ZFC.SetU.WFGraphCore as Core using (WFGraph)
open import LogOS.Domain.ZFC.SetU.GraphTreeBridge using (SupStructure)
open import LogOS.Domain.ZFC.WFGraph.Model as WF
  using (PowersetStructure; ExtensionalityStructure; FoundationStructure)

open import LogOS.Domain.ZFC.WFGraph.FormulaCode as FC

-- A WFGraph kernel variant where `Code` includes actual first-order formulas
-- (with explicit parameters), and `decode` maps formulas to their extensions.
--
-- This closes the “code-as-formula” gap for the WFGraph route while keeping the
-- kernel computational structure trivial (as in `WFGraph.Model`).

module _ {ℓ : Level}
         (G   : WFGraph ℓ)
         (S   : SupStructure G)
         (Ext : ExtensionalityStructure G)
         (P   : PowersetStructure G S)
         (Fnd : FoundationStructure G)
         where

  open Core.WFGraph G renaming (Node to N; Edge to E)
  open SupStructure S renaming (supN to supNₛ)

  -- Reuse the same (trivial) S/H/G-tier structure as the base WFGraph kernel.

  Sig : LogOSSignature ℓ
  Sig = WF.Sig G S Ext P Fnd

  Q : QAdapter ℓ
  Q = WF.Q G S Ext P Fnd

  -- ------------------------------------------------------------------------
  -- Set-theory formula semantics on the WFGraph carrier.
  -- ------------------------------------------------------------------------

  RelI : FC.STRel₂ {ℓ} → N → N → Set ℓ
  RelI FC.mem x y = E y x
  RelI FC.eq  x y = x ≡ y

  module Sem = FOLSem.For {Σ₀ = FC.ΣST {ℓ}} N (λ ()) RelI

  PredCodeST : Set ℓ
  PredCodeST = FC.PredCode N

  RelCodeST : Set ℓ
  RelCodeST = FC.RelCode N

  SatPred : PredCodeST → N → Set ℓ
  SatPred (k , (ps , φ)) z =
    Sem.Sat (Sem.extend z ps) φ

  SatRel : RelCodeST → N → N → Set ℓ
  SatRel (k , (ps , ψ)) u z =
    Sem.Sat (Sem.extend z (Sem.extend u ps)) ψ

  -- ------------------------------------------------------------------------
  -- Code layer: sets + predicate-formulas + relation-formulas.
  -- `decode` maps formulas to their extension sets/graphs.
  -- ------------------------------------------------------------------------

  data Code : Set ℓ where
    setCode  : N → Code
    predCode : PredCodeST → Code
    relCode  : RelCodeST → Code

  encode : N → Code
  encode = setCode

  extensionPred : PredCodeST → N
  extensionPred φ =
    supNₛ (Σ N (λ z → SatPred φ z))
      (λ { (z , _) → z })

  extensionRel : RelCodeST → N
  extensionRel ψ =
    let
      opair : N → N → N
      opair = WF.opair G S Ext P Fnd
    in
    supNₛ (Σ N (λ u → Σ N (λ z → SatRel ψ u z)))
      (λ { (u , (z , _)) → opair u z })

  decode : Code → N
  decode (setCode x)  = x
  decode (predCode φ) = extensionPred φ
  decode (relCode ψ)  = extensionRel ψ

  decode∘encode : ∀ c → decode (encode c) ≡ c
  decode∘encode _ = refl

  -- ------------------------------------------------------------------------
  -- Trivial computation / reflection (matches `WFGraph.Model`).
  -- ------------------------------------------------------------------------

  emptyN : N
  emptyN = WF.emptyN G S Ext P Fnd

  Guard : Code → Code
  Guard γ = γ

  Body : Code → Code
  Body _ = setCode emptyN

  γ* : Code
  γ* = setCode emptyN

  γ*-guard
    : (ConPoset._⊑_ (BulkBoundary.bnd (WF.BB G S Ext P Fnd))
        (decode γ*)
        (decode (Guard (Body γ*))))
    × (ConPoset._⊑_ (BulkBoundary.bnd (WF.BB G S Ext P Fnd))
        (decode (Guard (Body γ*)))
        (decode γ*))
  γ*-guard =
    ConPoset.refl (BulkBoundary.bnd (WF.BB G S Ext P Fnd))
    , ConPoset.refl (BulkBoundary.bnd (WF.BB G S Ext P Fnd))

  reify : Code → Code
  reify γ = γ

  reify-decode : ∀ γ → decode (reify γ) ≡ decode γ
  reify-decode _ = refl

  Body∂ : N → N
  Body∂ _ = emptyN

  body-decode : ∀ γ → decode (Body γ) ≡ Body∂ (decode γ)
  body-decode _ = refl

  -- ------------------------------------------------------------------------
  -- The kernel record.
  -- ------------------------------------------------------------------------

  K : Kernel Sig Q
  K = record
    { shape = record
        { HWorld = WF.HWorld G S Ext P Fnd
        ; BB     = WF.BB G S Ext P Fnd
        ; MBulk  = WF.mon G S Ext P Fnd
        ; MBnd   = WF.mon G S Ext P Fnd
        ; Holo   = WF.Holo G S Ext P Fnd
        ; HTruth = WF.HTruth G S Ext P Fnd
        ; HInv   = WF.HInv G S Ext P Fnd
        ; Sat_H_bnd = WF.Sat_H_bnd G S Ext P Fnd
        ; sat-coh   = WF.sat-coh G S Ext P Fnd
        ; Fml    = Topℓ {ℓ}
        ; Strict = WF.Strict G S Ext P Fnd
        ; TransH = λ _ → emptyN
        ; coh-LH = λ _ _ → intro (λ x → x) (λ x → x)
        ; Code   = Code
        ; encode = encode
        ; decode = decode
        ; Guard = Guard
        ; Body  = Body
        ; γ*    = γ*
        ; reify = reify
        ; Body∂ = Body∂
        }
    ; GTruth       = WF.GTruth G S Ext P Fnd
    ; laws = record
        { shapeLaws = record
            { decode∘encode = decode∘encode
            ; γ*-guard      = γ*-guard
            ; reify-decode  = reify-decode
            ; body-decode   = body-decode
            }
        ; mono-Body∂    = λ {c} {d} _ → WF.refl⊑N G S Ext P Fnd emptyN
        ; mono-Flow     = λ {c} {d} le → le
        ; guard-decode  = λ _ → refl
        ; decode-γ*     = refl
        }
    }
