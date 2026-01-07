{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.LobCore where

open import LogOS.Prelude

-- A kernel-independent core: Löb from HBL + diagonalisation.
--
-- This module isolates the textbook proof-theoretic ingredients from any
-- particular LogOS kernel. Kernel-level theorems should prefer the more
-- structural LogOS-native constructors (e.g. internal-hom/reflective packs)
-- and treat this as a reusable lemma.

record ProvabilityOpsC {ℓCode : Level} (Code : Set ℓCode) : Set (lsuc ℓCode) where
  field
    Imp : Code → Code → Code
    Box : Code → Code

record ImpRulesC {ℓCode ℓPr : Level}
                 {Code : Set ℓCode}
                 (⊢    : Code → Set ℓPr)
                 (Op   : ProvabilityOpsC Code)
                 : Set (lsuc (ℓCode ⊔ ℓPr)) where
  open ProvabilityOpsC Op
  field
    mp   : ∀ {φ ψ} → ⊢ (Imp φ ψ) → ⊢ φ → ⊢ ψ
    impI : ∀ {φ ψ} → (⊢ φ → ⊢ ψ) → ⊢ (Imp φ ψ)

record HBLClassicC {ℓCode ℓPr : Level}
                   {Code : Set ℓCode}
                   (⊢    : Code → Set ℓPr)
                   (Op   : ProvabilityOpsC Code)
                   : Set (lsuc (ℓCode ⊔ ℓPr)) where
  open ProvabilityOpsC Op
  field
    Necessitation : ∀ φ → ⊢ φ → ⊢ (Box φ)
    Kdist         : ∀ φ ψ → ⊢ (Box (Imp φ ψ)) → (⊢ (Box φ) → ⊢ (Box ψ))
    Four          : ∀ φ → ⊢ (Box φ) → ⊢ (Box (Box φ))

record DiagonalizationC {ℓCode ℓPr : Level}
                        {Code : Set ℓCode}
                        (⊢    : Code → Set ℓPr)
                        (Op   : ProvabilityOpsC Code)
                        : Set (lsuc (ℓCode ⊔ ℓPr)) where
  open ProvabilityOpsC Op
  field
    diag : (Code → Code) → Code
    diag→ : ∀ f → ⊢ (Imp (diag f) (f (diag f)))
    →diag : ∀ f → ⊢ (Imp (f (diag f)) (diag f))

record LoebAxiomC {ℓCode ℓPr : Level}
                  {Code : Set ℓCode}
                  (⊢    : Code → Set ℓPr)
                  (Op   : ProvabilityOpsC Code)
                  : Set (lsuc (ℓCode ⊔ ℓPr)) where
  open ProvabilityOpsC Op
  field
    loeb
      : (φ : Code)
      → ⊢ (Imp (Box φ) φ)
      → ⊢ φ

loebAxiom-from-HBL
  : ∀ {ℓCode ℓPr : Level}
    {Code : Set ℓCode}
    (⊢  : Code → Set ℓPr)
    (Op : ProvabilityOpsC Code)
    (Ir : ImpRulesC ⊢ Op)
    (Hb : HBLClassicC ⊢ Op)
    (Dl : DiagonalizationC ⊢ Op)
  → LoebAxiomC ⊢ Op
loebAxiom-from-HBL {Code = Code} ⊢ Op Ir Hb Dl = record { loeb = loeb }
  where
    open ProvabilityOpsC Op
    open ImpRulesC Ir
    open HBLClassicC Hb
    open DiagonalizationC Dl

    loeb
      : (φ : Code)
      → ⊢ (Imp (Box φ) φ)
      → ⊢ φ
    loeb φ prf =
      let
        f : Code → Code
        f x = Imp (Box x) φ

        ψ : Code
        ψ = diag f

        diag→ψ : ⊢ (Imp ψ (Imp (Box ψ) φ))
        diag→ψ = diag→ f

        ψ→diag : ⊢ (Imp (Imp (Box ψ) φ) ψ)
        ψ→diag = →diag f

        step : ⊢ (Box ψ) → ⊢ φ
        step pBoxψ =
          let
            pBoxBoxψ : ⊢ (Box (Box ψ))
            pBoxBoxψ = Four ψ pBoxψ

            pBox-diag→ : ⊢ (Box (Imp ψ (Imp (Box ψ) φ)))
            pBox-diag→ = Necessitation (Imp ψ (Imp (Box ψ) φ)) diag→ψ

            pBox-ImpBoxψφ : ⊢ (Box (Imp (Box ψ) φ))
            pBox-ImpBoxψφ =
              Kdist ψ (Imp (Box ψ) φ) pBox-diag→ pBoxψ

            pBoxφ : ⊢ (Box φ)
            pBoxφ = Kdist (Box ψ) φ pBox-ImpBoxψφ pBoxBoxψ
          in
          mp prf pBoxφ

        pImpBoxψφ : ⊢ (Imp (Box ψ) φ)
        pImpBoxψφ = impI step

        pψ : ⊢ ψ
        pψ = mp ψ→diag pImpBoxψφ

        pBoxψ : ⊢ (Box ψ)
        pBoxψ = Necessitation ψ pψ
      in
      step pBoxψ
