{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.WFGraph.FormulaPack where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro; ¬_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; fst; snd)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Domain.ZFC.SetTheory.FormulaPack using (ZFAxiomsᶠ)
open import LogOS.Domain.ZFC.SetU.IterativeSetTree using (Natℓ; zero; sucℓ)
open import LogOS.Domain.ZFC.SetU.WFGraphCore using (WFGraph)
open import LogOS.Domain.ZFC.SetU.GraphTreeBridge using (SupStructure)
open import LogOS.Domain.ZFC.WFGraph.Model as WF
  using (PowersetStructure; ExtensionalityStructure; FoundationStructure)
import LogOS.Domain.ZFC.WFGraph.FormulaKernel as FK

-- WFGraph ZF model (coded/schematic interface) where codes are genuine
-- first-order formulas and `decode` maps them to their extensions.

module ForZFC {ℓ : Level}
              (G   : WFGraph ℓ)
              (S   : SupStructure G)
              (Ext : ExtensionalityStructure G)
              (P   : PowersetStructure G S)
              (Fnd : FoundationStructure G)
              where

  open WFGraph G renaming (Node to N; Edge to E)
  open SupStructure S renaming (supN to supNₛ; mem-sup↔ to mem-sup↔ₛ)

  -- The formula-coded WFGraph kernel.
  Sig : LogOSSignature ℓ
  Sig = FK.Sig G S Ext P Fnd

  Q : QAdapter ℓ
  Q = FK.Q G S Ext P Fnd

  K : Kernel Sig Q
  K = FK.K G S Ext P Fnd

  open Kernel K

  -- Reuse the concrete set constructors from the base WFGraph model.
  emptyN : N
  emptyN = WF.emptyN G S Ext P Fnd

  opair : N → N → N
  opair = WF.opair G S Ext P Fnd

  unionN : N → N
  unionN = WF.unionN G S Ext P Fnd

  succN : N → N
  succN = WF.succN G S Ext P Fnd

  mem-succN↔ : ∀ x z → E (succN x) z ↔ ((E x z) ⊎ (z ≡ x))
  mem-succN↔ = WF.mem-succN↔ G S Ext P Fnd

  empty-axiomN : Σ N (λ e → ∀ z → ¬ (E e z))
  empty-axiomN = WF.empty-axiomN G S Ext P Fnd

  pairing-axiomN : ∀ x y → Σ N (λ p → ∀ z → E p z ↔ ((z ≡ x) ⊎ (z ≡ y)))
  pairing-axiomN = WF.pairing-axiomN G S Ext P Fnd

  -- ------------------------------------------------------------------------
  -- Infinity: ω as a concrete `supN` of iterated successors of ∅.
  -- ------------------------------------------------------------------------

  vnN : Natℓ {ℓ} → N
  vnN zero     = emptyN
  vnN (sucℓ n) = succN (vnN n)

  ωN : N
  ωN = supNₛ (Natℓ {ℓ}) vnN

  mem-ωN↔ : ∀ z → E ωN z ↔ Σ (Natℓ {ℓ}) (λ n → vnN n ≡ z)
  mem-ωN↔ z = mem-sup↔ₛ {I = Natℓ {ℓ}} {f = vnN} {y = z}

  infinity-ωN
    : ∀ z →
      (E ωN z)
        ↔ ((z ≡ emptyN) ⊎ (Σ N (λ y → (E ωN y) × (z ≡ succN y))))
  infinity-ωN z =
    intro (to z) (from z)
    where
      to
        : ∀ z
        → E ωN z
        → (z ≡ emptyN) ⊎ (Σ N (λ y → (E ωN y) × (z ≡ succN y)))
      to z ez with _↔_.to (mem-ωN↔ z) ez
      ... | (zero , pr) =
        inj₁ (sym pr)
      ... | (sucℓ n , pr) =
        inj₂
          ( vnN n
          , ( _↔_.from (mem-ωN↔ (vnN n)) (n , refl)
            , sym pr
            )
          )

      from
        : ∀ z
        → (z ≡ emptyN) ⊎ (Σ N (λ y → (E ωN y) × (z ≡ succN y)))
        → E ωN z
      from z (inj₁ z≡0) =
        subst (λ t → E ωN t) (sym z≡0)
          (_↔_.from (mem-ωN↔ emptyN) (zero , refl))
      from z (inj₂ (y , (y∈ω , z≡sy))) with _↔_.to (mem-ωN↔ y) y∈ω
      ... | (n , pr) =
        let
          sy≡z : succN y ≡ z
          sy≡z = sym z≡sy

          sn≡z : vnN (sucℓ n) ≡ z
          sn≡z = trans (cong succN pr) sy≡z
        in
        _↔_.from (mem-ωN↔ z) (sucℓ n , sn≡z)

  -- ------------------------------------------------------------------------
  -- Formula-pack ZF interface.
  -- ------------------------------------------------------------------------

  zfᶠ : ZFAxiomsᶠ K
  zfᶠ = record
    { SetU   = N
    ; _∈_    = λ z x → E x z
    ; _≈_    = _≡_
    ; refl≈  = λ _ → refl
    ; sym≈   = λ e → sym e
    ; trans≈ = λ e₁ e₂ → trans e₁ e₂
    ; ⟦_⟧     = decode
    ; by-decode≈ = λ eq → eq
    ; extensionality = ExtensionalityStructure.ext≡ Ext
    ; mem-ext = λ {x} {y} eq z →
        intro
          (λ exz → subst (λ t → E t z) eq exz)
          (λ eyz → subst (λ t → E t z) (sym eq) eyz)
    ; mem-congL = λ {x} {y} eq z →
        intro
          (λ exz → subst (λ t → E z t) eq exz)
          (λ eyz → subst (λ t → E z t) (sym eq) eyz)
    ; empty = empty-axiomN
    ; pairing = pairing-axiomN
    ; union = λ x →
        unionN x ,
          (λ z →
            intro
              (λ ez →
                let m =
                      _↔_.to
                        (mem-sup↔ₛ
                          {I = WF.UnionI G S Ext P Fnd x}
                          {f = WF.unionMap G S Ext P Fnd x}
                          {y = z})
                        ez
                in
                let i  = proj₁ m
                    pr = proj₂ m
                    y0 = proj₁ i
                    xy = fst (proj₂ i)
                    z0 = proj₁ (snd (proj₂ i))
                    yz = proj₂ (snd (proj₂ i))
                in subst (λ t → Σ N (λ y' → E x y' × E y' t)) pr (y0 , (xy , yz)))
              (λ { (y0 , (xy , yz)) →
                _↔_.from
                  (mem-sup↔ₛ
                    {I = WF.UnionI G S Ext P Fnd x}
                    {f = WF.unionMap G S Ext P Fnd x}
                    {y = z})
                  ((y0 , (xy , (z , yz))) , refl) }))
    ; powerset =
        λ x →
          PowersetStructure.Pow P x
          , (λ z → PowersetStructure.Pow-mem↔ P {x = x} {z = z})
    ; zeroS = emptyN
    ; zeroS-empty = proj₂ empty-axiomN
    ; succ  = succN
    ; mem-succ↔ = λ x z → mem-succN↔ x z
    ; infinity = ωN , infinity-ωN
    ; Pred = λ φ z → E (decode φ) z
    ; Rel  = λ ψ u z → E (decode ψ) (opair u z)
    ; separationᶠ = λ φ x → WF.separationᵈN G S Ext P Fnd (decode φ) x
    ; replacementᶠ = λ ψ fun x → WF.replacementᵈN G S Ext P Fnd (decode ψ) fun x
    ; foundation = FoundationStructure.foundation Fnd emptyN
    }
