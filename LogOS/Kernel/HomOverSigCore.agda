{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.HomOverSigCore where

-- ============================================================================
-- SHARED CORE: HETEROGENEOUS MORPHISMS OVER SIGNATURE MAPS
--
-- This module factors out the bookkeeping shared by:
-- - `LogOS.Kernel.HomOverSig`
-- - `LogOS.Kernel.LogicKernel.HomOverSig`
--
-- It is intentionally lightweight: it does not assume anything about the
-- internal structure of objects or morphisms, only that:
-- - objects are indexed by a signature,
-- - there is a pullback/reindex operation along `SigHom` (contravariant), and
-- - morphisms compose within each fixed-signature fibre.
-- ============================================================================

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom

record Ops {ℓ : Level} : Set (lsuc (lsuc (lsuc ℓ))) where
  field
    Obj : LogOSSignature ℓ → Set (lsuc (lsuc ℓ))

    Hom : ∀ {Sig : LogOSSignature ℓ} → Obj Sig → Obj Sig → Set (lsuc (lsuc ℓ))
    idHom : ∀ {Sig : LogOSSignature ℓ} (K : Obj Sig) → Hom K K
    composeHom
      : ∀ {Sig : LogOSSignature ℓ} {K₁ K₂ K₃ : Obj Sig}
      → Hom K₁ K₂ → Hom K₂ K₃ → Hom K₁ K₃

    reindexObj
      : ∀ {Sig₁ Sig₂ : LogOSSignature ℓ}
      → SigHom Sig₁ Sig₂ → Obj Sig₂ → Obj Sig₁

    reindexHom
      : ∀ {Sig₁ Sig₂ : LogOSSignature ℓ}
        (σ : SigHom Sig₁ Sig₂)
        {K K' : Obj Sig₂}
      → Hom K K' → Hom (reindexObj σ K) (reindexObj σ K')

    reindex-composeHom
      : ∀ {Sig₁ Sig₂ Sig₃ : LogOSSignature ℓ}
        (σ : SigHom Sig₁ Sig₂)
        (τ : SigHom Sig₂ Sig₃)
        (K : Obj Sig₃)
      → Hom (reindexObj σ (reindexObj τ K))
            (reindexObj (composeSigHom σ τ) K)

    -- Identity coherence: a canonical hom into the pullback along `idSigHom`.
    --
    -- This is intentionally a *morphism*, not propositional equality, so we do not
    -- require any record extensionality or definitional reduction at the object level.
    reindex-idHom
      : ∀ {Sig : LogOSSignature ℓ} (K : Obj Sig)
      → Hom K (reindexObj (idSigHom Sig) K)

module WithOps {ℓ : Level} (ops : Ops {ℓ}) where
  open Ops ops

  record HomOver {Sig₁ Sig₂ : LogOSSignature ℓ}
                 (K₁ : Obj Sig₁)
                 (K₂ : Obj Sig₂)
                 : Set (lsuc (lsuc ℓ)) where
    field
      σ   : SigHom Sig₁ Sig₂
      hom : Hom K₁ (reindexObj σ K₂)

  open HomOver public

  idHomOver
    : ∀ {Sig : LogOSSignature ℓ} (K : Obj Sig)
    → HomOver K K
  idHomOver {Sig = Sig} K =
    record
      { σ   = idSigHom Sig
      ; hom = reindex-idHom K
      }

  composeHomOver
    : ∀ {Sig₁ Sig₂ Sig₃ : LogOSSignature ℓ}
      {K₁ : Obj Sig₁} {K₂ : Obj Sig₂} {K₃ : Obj Sig₃}
    → HomOver K₁ K₂ → HomOver K₂ K₃ → HomOver K₁ K₃
  composeHomOver {K₂ = K₂} {K₃ = K₃} h₁₂ h₂₃ =
    record
      { σ   = composeSigHom σ₁₂ σ₂₃
      ; hom = composeHom hom₁₂ (composeHom hom₂₃' bridge)
      }
    where
      open HomOver h₁₂ renaming (σ to σ₁₂; hom to hom₁₂)
      open HomOver h₂₃ renaming (σ to σ₂₃; hom to hom₂₃)

      hom₂₃' : Hom (reindexObj σ₁₂ K₂) (reindexObj σ₁₂ (reindexObj σ₂₃ K₃))
      hom₂₃' = reindexHom σ₁₂ hom₂₃

      bridge : Hom (reindexObj σ₁₂ (reindexObj σ₂₃ K₃))
                   (reindexObj (composeSigHom σ₁₂ σ₂₃) K₃)
      bridge = reindex-composeHom σ₁₂ σ₂₃ K₃
