{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.Syntax.Prop as Prop

-- (no alias; reference Truth.HomotypicalTruth directly in field types)

-- Single, integrated kernel: S/H/G + Code, without duplicative layers.
-- All pieces are primitive records from the Minimal core.
-- Optional graded extension (grade-indexed guarded flow): see `LogOS/Kernel/Graded.agda`.

record Kernel {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) : Set (lsuc (lsuc ℓ)) where
  open LogOSSignature Sig
  module W  = Worlds Sig
  module GT = Truth.GuardedTruth Sig Q
  open Truth.StrictTruth Sig
  field
    -- H-tier: world context + Q-weighted flow
    HWorld : W.WorldH Q

  private
    module HT = Truth.HomotypicalTruth Sig Q HWorld

  field
    -- Constraints and lax monoidal adjunction
    BB     : BulkBoundary ℓ
    MBulk  : MonoidalPoset (BulkBoundary.bulk BB)
    MBnd   : MonoidalPoset (BulkBoundary.bnd  BB)
    Holo   : LaxMonoidalAdjunction BB MBulk MBnd

    -- H-tier satisfaction and invariance (dependent on the chosen world)
    HTruth : HT.HLayer BB
    HInv   : HT.Invariance BB

    -- Boundary satisfaction + coherence (optional, internalized)
    Sat_H_bnd : ∂Cosp → (ConPoset.Con (BulkBoundary.bnd BB)) → Set ℓ
    sat-coh   : ∀ (w : Cosp) (c : ConPoset.Con (BulkBoundary.bnd BB)) →
                Prop._↔_ (HT.HLayer.Sat_H HTruth w c)
                         (Sat_H_bnd (bnd w) c)

    -- S-tier: strict logic interface and translation into H-tier constraints
    Fml    : Set ℓ
    Strict : StrictLayer Fml
    TransH : Fml → (ConPoset.Con (BulkBoundary.bnd BB))
    coh-LH : ∀ (w : Cosp) (φ : Fml) →
             Prop._↔_ (StrictLayer.Sat_S Strict w φ)
                      (HT.HLayer.Sat_H HTruth w (TransH φ))

    -- G-tier: guarded truth closure on boundary constraints
    GTruth : (GT.GuardedClosure) (BulkBoundary.bnd BB)

    -- Code layer: guarded reflection
    Code   : Set ℓ
    encode : (ConPoset.Con (BulkBoundary.bnd BB)) → Code
    decode : Code → (ConPoset.Con (BulkBoundary.bnd BB))
    decode∘encode : ∀ c → decode (encode c) ≡ c
    -- Code-level step is derived as `FlowCode = Guard ∘ Body`.
    -- At the boundary, this corresponds to `Flow ∘ Body∂` (see `decode-FlowCode`).
    Guard         : Code → Code
    Body          : Code → Code
    guard-decode  : ∀ γ → decode (Guard γ) ≡ (GT.GuardedClosure.Flow GTruth) (decode γ)
    -- Guarded fixpoint
    γ*            : Code
    -- `γ*` is a code-level witness for the guarded fixed point, but we only
    -- require *closure-level* strength: stability under one `FlowCode` step is
    -- expressed as boundary preorder inequalities, not as a definitional code
    -- equality.
    γ*-guard      : (ConPoset._⊑_ (BulkBoundary.bnd BB)
                      (decode γ*)
                      (decode (Guard (Body γ*))))
                    × (ConPoset._⊑_ (BulkBoundary.bnd BB)
                        (decode (Guard (Body γ*)))
                        (decode γ*))
    decode-γ*     : decode γ* ≡ (GT.GuardedClosure.Th* GTruth)

    -- Safe self-reflection (observational)
    -- Reify code through boundary semantics
    reify         : Code → Code
    reify-decode  : ∀ γ → decode (reify γ) ≡ decode γ
    -- Boundary view of code body (one-step computation core)
    Body∂         : (ConPoset.Con (BulkBoundary.bnd BB)) → (ConPoset.Con (BulkBoundary.bnd BB))
    body-decode   : ∀ γ → decode (Body γ) ≡ Body∂ (decode γ)

  -- No local ↔; use Prop._↔_

-- Derived code-level Flow (Guard ∘ body)

FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) → Kernel.Code K → Kernel.Code K
FlowCode K γ = Kernel.Guard K (Kernel.Body K γ)

decode-FlowCode
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (γ : Kernel.Code K)
  → Kernel.decode K (FlowCode K γ)
    ≡ (let module GT = Truth.GuardedTruth Sig Q in GT.GuardedClosure.Flow (Kernel.GTruth K))
      (Kernel.Body∂ K (Kernel.decode K γ))
decode-FlowCode {Sig = Sig} {Q = Q} K γ =
  trans (Kernel.guard-decode K (Kernel.Body K γ))
        (cong (let module GT = Truth.GuardedTruth Sig Q in GT.GuardedClosure.Flow (Kernel.GTruth K))
              (Kernel.body-decode K γ))

record BodyMonotone
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q) : Set (lsuc (lsuc ℓ)) where
  field
    mono-Body∂
      : ∀ {c d}
      → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) c d
      → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Kernel.Body∂ K c) (Kernel.Body∂ K d)

-- Optional graded extension (kept under a separate namespace to avoid clashes).
import LogOS.Kernel.Graded as Gradedₜ
module Graded = Gradedₜ
