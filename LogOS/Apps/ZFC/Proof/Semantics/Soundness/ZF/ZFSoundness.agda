{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Semantics.Soundness.ZF.ZFSoundness where

open import LogOS.Prelude using
  ( Level
  ; _×_
  ; _⊎_
  ; Σ
  ; _,_
  ; fst
  ; snd
  ; proj₁
  ; proj₂
  ; inj₁
  ; inj₂
  ; refl
  ; sym
  ; trans
  ; cong
  ; cong₂
  ; subst
  ; ⊥-elim
  ; _≡_
  )
open import LogOS.Host.Nat using (ℕ; zero; suc)

open import LogOS.Syntax.Prop using (_↔_; intro; to; from)
open import LogOS.LT.View using (μ)

import LogOS.Apps.ZFC.Proof.Syntax as Syntax
open Syntax
import LogOS.Apps.ZFC.Proof.Axioms as Ax
open Ax

import LogOS.Apps.ZFC.Proof.Semantics.Core as Core
import LogOS.Apps.ZFC.Proof.Semantics.Soundness.Logic as Logic

module ForModel {ℓ : Level} (M : Core.Model {ℓ}) where
  open Core.Model M
  private
    module MC = Core.ModelCore M

  open MC using
    ( ↔-trans
    ; ValEq
    ; valEqByCases01
    ; renameVal
    ; renameVal-liftRen-extend
    ; insert1-separation-cong
    ; insert2-replacement-cong
    ; evalTerm-cong
    ; evalFormula-cong
    ; evalTerm-rename
    ; evalFormula-rename
    ; insertAt
    ; insertAt-suc-extend
    ; insertAt-zero-extend
    ; evalTerm-lift
    ; evalFormula-lift
    ; evalFormula-substAt
    ; emptySet-empty
    ; zeroSet-empty
    ; zero≈empty
    )

  open Logic.ForModel M using (extensionality≈)

  zfSound : ∀ {ρ φ} → ZFAxiom φ → evalFormula φ ρ
  zfSound {ρ} axExtensionality x y h =
    extensionality≈ x y h
  zfSound {ρ} axEmpty z z∈e =
    ⊥-elim (emptySet-empty z z∈e)
  zfSound {ρ} axPairing x y z =
    pairing-spec x y z
  zfSound {ρ} axUnion x z =
    union-spec x z
  zfSound {ρ} axPowerset x z =
    powerset-spec x z
  zfSound {ρ} axSucc x z =
    succ-spec x z
  zfSound {ρ} axInfinity z =
    intro to∞ from∞
    where
      ω-law
        : ∀ z
        → (z ∈ omegaSet)
            ↔ ((z ≈ zeroSet) ⊎ (Σ SetU (λ y → y ∈ omegaSet × (z ≈ succSet y))))
      ω-law = infinity-spec

      to∞ : z ∈ omegaSet → (z ≈ emptySet) ⊎ (Σ SetU (λ y → y ∈ omegaSet × (z ≈ succSet y)))
      to∞ z∈ω with to (ω-law z) z∈ω
      ... | inj₁ z≈0 = inj₁ (trans≈ z≈0 zero≈empty)
      ... | inj₂ w = inj₂ w

      from∞ : (z ≈ emptySet) ⊎ (Σ SetU (λ y → y ∈ omegaSet × (z ≈ succSet y))) → z ∈ omegaSet
      from∞ (inj₁ z≈e) =
        from (ω-law z) (inj₁ (trans≈ z≈e (sym≈ zero≈empty)))
      from∞ (inj₂ w) = from (ω-law z) (inj₂ w)
  zfSound {ρ} axFoundation x nonempty =
    let
      base = foundation x nonempty
      y = proj₁ base
      y∈x = fst (proj₂ base)
      wf = snd (proj₂ base)
      wf-form : evalFormula
        (∀F (v0 ∈F v2 ⇒ ((v0 ∈F v1) ⇒ ⊥F)))
        (extend y (extend x ρ))
      wf-form = λ z →
        λ z∈x →
          λ z∈y → ⊥-elim (wf z z∈x z∈y)
    in
    y , (y∈x , wf-form)
  zfSound {ρ} (axSeparationSchema P) x =
    let
      y : SetU
      y = μ (SeparationFV P ρ) x

      sep-law : ∀ z → (z ∈ y) ↔ ((z ∈ x) × evalFormula P (extend z (extend x ρ)))
      sep-law z = separationF-spec P ρ x z
    in
    y
      , (λ z →
          let
            embed-law
              : evalFormula (liftAfter0Formula P) (extend z (extend y (extend x ρ)))
                  ↔ evalFormula P (extend z (extend x ρ))
            embed-law =
              ↔-trans
                (evalFormula-rename insert1Ren P (extend z (extend y (extend x ρ))))
                (evalFormula-cong (insert1-separation-cong ρ x y z) P)
          in
          intro
            (λ z∈y →
              let p = to (sep-law z) z∈y in
              fst p , from embed-law (snd p))
            (λ p →
              from (sep-law z) (fst p , to embed-law (snd p))))
  zfSound {ρ} (axReplacementSchema R) x funPrem =
    let
      -- Convert the functional premise from the axiom formula to the
      -- `FunctionalOnX` shape expected by the stack-level FO replacement view.
      functionalOnX
        : FunctionalOnX R ρ x
      functionalOnX u u∈x =
        let
          ex∧uniq = funPrem u u∈x
          ex = fst ex∧uniq
          uniq = snd ex∧uniq

          -- Context under `∃ z` (inside `∀ u`):
          --   `z` at 0, `u` at 1, `x` at 2.
          R-exists : Formula
          R-exists = Ax.R-exists R

          -- Context under `∀ z1 . ∀ z2` (inside `∀ u`):
          --   `z2` at 0, `z1` at 1, `u` at 2, `x` at 3.
          R-u-z1Ren : Renaming
          R-u-z1Ren = Ax.R-u-z1Ren

          R-u-z2Ren : Renaming
          R-u-z2Ren = Ax.R-u-z2Ren

          R-u-z1 : Formula
          R-u-z1 = Ax.R-u-z1 R

          R-u-z2 : Formula
          R-u-z2 = Ax.R-u-z2 R

          swap01-insertAfter1-cong
            : ∀ (ρ : Valuation) (x u z : SetU)
            → ValEq
                (renameVal swap01Ren (renameVal insertAfter1Ren (extend z (extend u (extend x ρ)))))
                (extend u (extend z ρ))
          swap01-insertAfter1-cong ρ x u z =
            valEqByCases01 refl refl (λ n → refl)

          R-u-z1-cong
            : ∀ (ρ : Valuation) (x u z₁ z₂ : SetU)
            → ValEq
                (renameVal R-u-z1Ren (extend z₂ (extend z₁ (extend u (extend x ρ)))))
                (extend u (extend z₁ ρ))
          R-u-z1-cong ρ x u z₁ z₂ =
            valEqByCases01 refl refl (λ n → refl)

          R-u-z2-cong
            : ∀ (ρ : Valuation) (x u z₁ z₂ : SetU)
            → ValEq
                (renameVal R-u-z2Ren (extend z₂ (extend z₁ (extend u (extend x ρ)))))
                (extend u (extend z₂ ρ))
          R-u-z2-cong ρ x u z₁ z₂ =
            valEqByCases01 refl refl (λ n → refl)

          R-exists-law
            : ∀ (ρ : Valuation) (x u z : SetU)
            → evalFormula R-exists (extend z (extend u (extend x ρ)))
                ↔ evalFormula R (extend u (extend z ρ))
          R-exists-law ρ x u z =
            ↔-trans
              (evalFormula-rename insertAfter1Ren (renameFormula swap01Ren R) (extend z (extend u (extend x ρ))))
              (↔-trans
                (evalFormula-rename swap01Ren R (renameVal insertAfter1Ren (extend z (extend u (extend x ρ)))))
                (evalFormula-cong (swap01-insertAfter1-cong ρ x u z) R))

          R-u-z1-law
            : ∀ (ρ : Valuation) (x u z₁ z₂ : SetU)
            → evalFormula R-u-z1 (extend z₂ (extend z₁ (extend u (extend x ρ))))
                ↔ evalFormula R (extend u (extend z₁ ρ))
          R-u-z1-law ρ x u z₁ z₂ =
            ↔-trans
              (evalFormula-rename R-u-z1Ren R (extend z₂ (extend z₁ (extend u (extend x ρ)))))
              (evalFormula-cong (R-u-z1-cong ρ x u z₁ z₂) R)

          R-u-z2-law
            : ∀ (ρ : Valuation) (x u z₁ z₂ : SetU)
            → evalFormula R-u-z2 (extend z₂ (extend z₁ (extend u (extend x ρ))))
                ↔ evalFormula R (extend u (extend z₂ ρ))
          R-u-z2-law ρ x u z₁ z₂ =
            ↔-trans
              (evalFormula-rename R-u-z2Ren R (extend z₂ (extend z₁ (extend u (extend x ρ)))))
              (evalFormula-cong (R-u-z2-cong ρ x u z₁ z₂) R)

          z : SetU
          z = proj₁ ex

          ruz-exists : evalFormula R-exists (extend z (extend u (extend x ρ)))
          ruz-exists = proj₂ ex

          ruz : evalFormula R (extend u (extend z ρ))
          ruz = to (R-exists-law ρ x u z) ruz-exists
        in
        z
          , ( ruz
            , (λ z′ ruz′ →
                let
                  uniq′ = uniq z z′

                  ruz1 : evalFormula R-u-z1 (extend z′ (extend z (extend u (extend x ρ))))
                  ruz1 = from (R-u-z1-law ρ x u z z′) ruz

                  ruz2 : evalFormula R-u-z2 (extend z′ (extend z (extend u (extend x ρ))))
                  ruz2 = from (R-u-z2-law ρ x u z z′) ruz′

                  zz′ : z ≈ z′
                  zz′ = uniq′ (ruz1 , ruz2)
                in
                sym≈ zz′
              )
            )

      y : SetU
      y = μ (ReplacementFV R ρ) (x , functionalOnX)

      rep-law : ∀ z → (z ∈ y) ↔ (Σ SetU (λ u → u ∈ x × evalFormula R (extend u (extend z ρ))))
      rep-law z = replacementF-spec R ρ x functionalOnX z

      -- In the axiom formula, `R` is embedded under two extra binders (y , x)
      -- after the first two variables (u , z). This renaming drops those.
      insertAfter1By2-replacement-cong
        : ∀ (x y z u : SetU)
        → ValEq
            (renameVal insertAfter1By2Ren (extend u (extend z (extend y (extend x ρ)))))
            (extend u (extend z ρ))
      insertAfter1By2-replacement-cong x y z u =
        valEqByCases01 refl refl (λ n → refl)
    in
    y
      , (λ z →
          let
            embed-law
              : ∀ u
              → evalFormula (renameFormula insertAfter1By2Ren R) (extend u (extend z (extend y (extend x ρ))))
                  ↔ evalFormula R (extend u (extend z ρ))
            embed-law u =
              ↔-trans
                (evalFormula-rename insertAfter1By2Ren R (extend u (extend z (extend y (extend x ρ)))))
                (evalFormula-cong (insertAfter1By2-replacement-cong x y z u) R)
          in
          intro
            (λ z∈y →
              let
                (u , (u∈x , ru)) = to (rep-law z) z∈y
              in
              u , (u∈x , from (embed-law u) ru))
            (λ (u , (u∈x , rUz)) →
              from (rep-law z)
                (u , (u∈x , to (embed-law u) rUz))))
