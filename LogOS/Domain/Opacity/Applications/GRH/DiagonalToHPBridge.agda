{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH.DiagonalToHPBridge where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel

open import LogOS.Domain.Opacity.NumberTheory.HP.Interface as HPi
open import LogOS.Domain.Opacity.NumberTheory.HP.Flow as HP

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann
open import LogOS.Domain.Opacity.NumberTheory.LFunction.DiagonalTX
open import LogOS.Domain.Opacity.Applications.GRH.ZetaBridge

-- Given a diagonal truncated operator specification TX (det-zero bridge and
-- local1⇒OnLine), and a Hilbert–Pólya instance HP together with a selector that
-- connects fixed points at embed ∘ c to local1 witnesses, build the finite
-- ZetaOpBridge needed by GRH_Without_Vacuity_Guards_from_finite automatically.

record DiagHPSelector {ℓ} {ℓTX : Level}
                       {Sig : LogOSSignature ℓ}
                       {Q   : QAdapter ℓ}
                       (K   : Kernel Sig Q)
                       (HP  : HPi.HPInterface K)
                       (RS  : RiemannSpectral)
                       (TX  : DiagonalTX {ℓTX} RS)
                       : Set (lsuc (ℓ ⊔ ℓTX)) where
  open Kernel K
  open RiemannSpectral RS
  open DiagonalTX TX
  open HPi.HPInterface HP
  field
    -- Boundary selection for each spectral point
    c : Spectral → ConPreorder.Con (BulkBoundary.bnd BB)

    -- Diagonal operator alignment (two directions):
    -- 1) If Op @ embed (c s) is fixed, then there is a local1 witness.
    fixed→∃local1 : ∀ s → Op (embed (c s)) ≡ embed (c s) → Σ P (λ p → a₁ p s)

    -- 2) If there exists a local1 witness, then Op @ embed (c s) is fixed.
    ∃local1→fixed : ∀ s → Σ P (λ p → a₁ p s) → Op (embed (c s)) ≡ embed (c s)

    -- Link between RS.NontrivialZero and the truncated determinant zero
    nz→ΛXZero : ∀ s → NontrivialZero s → ΛXZero s

fromDiagonal
  : ∀ {ℓ ℓTX} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K   : Kernel Sig Q)
    (HP  : HPi.HPInterface K)
    (RS  : RiemannSpectral)
    (TX  : DiagonalTX {ℓTX} RS)
    (Sel : DiagHPSelector {ℓ} {ℓTX} K HP RS TX)
  → ZetaOpBridgeFinite Sig Q K HP RS
fromDiagonal K HP RS TX Sel =
  let open RiemannSpectral RS
      open DiagonalTX TX
      open DiagHPSelector Sel
      open HPi.HPInterface HP
  in
  record
    { c = c
    ; zero-ref =
        record
          { sat-→ = λ _ s nz →
              ∃local1→fixed s (det-zero→∃local1 s (nz→ΛXZero s nz))
          }
    ; opFixed-ref =
        record
          { sat-→ = λ _ s opfx →
              local1→OnLine s (fixed→∃local1 s opfx)
          }
    }
