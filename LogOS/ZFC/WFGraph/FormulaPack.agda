{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.WFGraph.FormulaPack where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro; ¬_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.API.Kernel

open import LogOS.Prelude using (Σ; _,_; proj₁; proj₂; _×_; fst; snd)
open import LogOS.Prelude using (_⊎_; inj₁; inj₂)

open import LogOS.ZFC.SetTheory.FormulaPack using (ZFAxiomsᶠ)
open import LogOS.ZFC.SetU.IterativeSetTree using (Natℓ; zero; sucℓ)
open import LogOS.ZFC.SetU.WFGraphCore using (WFGraph)
open import LogOS.ZFC.SetU.GraphTreeBridge using (SupStructure)
open import LogOS.ZFC.WFGraph.Model as WF
  using (PowersetStructure; ExtensionalityStructure; FoundationStructure)
import LogOS.ZFC.WFGraph.FormulaKernel as FK

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

  open Kernel K hiding (G)

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

  -- Extensional preorder on nodes: inclusion by membership implication.
  infix 4 _⊑N_
  _⊑N_ : N → N → Set ℓ
  x ⊑N y = ∀ z → E x z → E y z

  conPreorder : ConPreorder ℓ
  conPreorder =
    record
      { Con = N
      ; _⊑_ = _⊑N_
      ; refl = λ {c} z ez → ez
      ; trans = λ xy yz z ez → yz z (xy z ez)
      }

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
    ; ⟦_⟧     = decode
    ; by-decode≈ = λ eq → ≡→≈CP {CP = conPreorder} eq
    ; mem-congL = λ {x} {y} xy≈yx z →
        let
          x≡y : x ≡ y
          x≡y =
            ExtensionalityStructure.ext≡ Ext x y
              (λ u →
                intro
                  (≈CP⇒ {CP = conPreorder} xy≈yx u)
                  (≈CP⇐ {CP = conPreorder} xy≈yx u))
        in
        intro
          (λ exz → subst (λ t → E z t) x≡y exz)
          (λ eyz → subst (λ t → E z t) (sym x≡y) eyz)
    ; empty = empty-axiomN
    ; pairing = λ x y →
        let
          p = pairing-axiomN x y
          pSet = proj₁ p
          pProp = proj₂ p

          to≈
            : ∀ {z}
            → (z ≡ x ⊎ z ≡ y)
            → (_≈CP_ conPreorder z x ⊎ _≈CP_ conPreorder z y)
          to≈ {z} =
            λ
              { (inj₁ z≡x) → inj₁ (≡→≈CP {CP = conPreorder} z≡x)
              ; (inj₂ z≡y) → inj₂ (≡→≈CP {CP = conPreorder} z≡y)
              }

          from≈
            : ∀ {z}
            → (_≈CP_ conPreorder z x ⊎ _≈CP_ conPreorder z y)
            → (z ≡ x ⊎ z ≡ y)
          from≈ {z} =
            λ
              { (inj₁ z≈x) →
                  inj₁
                    (ExtensionalityStructure.ext≡ Ext z x
                      (λ u →
                        intro
                          (≈CP⇒ {CP = conPreorder} z≈x u)
                          (≈CP⇐ {CP = conPreorder} z≈x u)))
              ; (inj₂ z≈y) →
                  inj₂
                    (ExtensionalityStructure.ext≡ Ext z y
                      (λ u →
                        intro
                          (≈CP⇒ {CP = conPreorder} z≈y u)
                          (≈CP⇐ {CP = conPreorder} z≈y u)))
              }
        in
        pSet ,
          (λ z →
            intro
              (λ ez → to≈ (_↔_.to (pProp z) ez))
              (λ disj → _↔_.from (pProp z) (from≈ disj)))
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
    ; mem-succ↔ = λ x z →
        let
          m = mem-succN↔ x z
          to≈ : (E x z ⊎ z ≡ x) → (E x z ⊎ _≈CP_ conPreorder z x)
          to≈ =
            λ
              { (inj₁ xz)   → inj₁ xz
              ; (inj₂ z≡x)  → inj₂ (≡→≈CP {CP = conPreorder} z≡x)
              }

          from≈ : (E x z ⊎ _≈CP_ conPreorder z x) → (E x z ⊎ z ≡ x)
          from≈ =
            λ
              { (inj₁ xz) → inj₁ xz
              ; (inj₂ z≈x) →
                  inj₂
                    (ExtensionalityStructure.ext≡ Ext z x
                      (λ u →
                        intro
                          (≈CP⇒ {CP = conPreorder} z≈x u)
                          (≈CP⇐ {CP = conPreorder} z≈x u)))
              }
        in
        intro
          (λ ez → to≈ (_↔_.to m ez))
          (λ disj → _↔_.from m (from≈ disj))
    ; infinity =
        ωN ,
          (λ z →
            let
              m = infinity-ωN z

              to≈
                : ((z ≡ emptyN) ⊎ (Σ N (λ y → (E ωN y) × (z ≡ succN y))))
                → (_≈CP_ conPreorder z emptyN
                  ⊎ Σ N (λ y → (E ωN y) × _≈CP_ conPreorder z (succN y)))
              to≈ =
                λ
                  { (inj₁ z≡0) → inj₁ (≡→≈CP {CP = conPreorder} z≡0)
                  ; (inj₂ (y , (y∈ω , z≡sy))) →
                      inj₂ (y , (y∈ω , ≡→≈CP {CP = conPreorder} z≡sy))
                  }

              from≈
                : (_≈CP_ conPreorder z emptyN
                  ⊎ Σ N (λ y → (E ωN y) × _≈CP_ conPreorder z (succN y)))
                → ((z ≡ emptyN) ⊎ (Σ N (λ y → (E ωN y) × (z ≡ succN y))))
              from≈ =
                λ
                  { (inj₁ z≈0) →
                      inj₁
                        (ExtensionalityStructure.ext≡ Ext z emptyN
                          (λ u →
                            intro
                              (≈CP⇒ {CP = conPreorder} z≈0 u)
                              (≈CP⇐ {CP = conPreorder} z≈0 u)))
                  ; (inj₂ (y , (y∈ω , z≈sy))) →
                      inj₂
                        ( y
                        , ( y∈ω
                          , ExtensionalityStructure.ext≡ Ext z (succN y)
                              (λ u →
                                intro
                                  (≈CP⇒ {CP = conPreorder} z≈sy u)
                                  (≈CP⇐ {CP = conPreorder} z≈sy u))
                          )
                        )
                  }
            in
            intro
              (λ ez → to≈ (_↔_.to m ez))
              (λ disj → _↔_.from m (from≈ disj)))
    ; Pred = λ φ z → E (decode φ) z
    ; Rel  = λ ψ u z → E (decode ψ) (opair u z)
    ; separationᶠ = λ φ x → WF.separationᵈN G S Ext P Fnd (decode φ) x
    ; replacementᶠ = λ ψ fun x → WF.replacementᵈN G S Ext P Fnd (decode ψ) fun x
    ; foundation =
        λ x →
          foundation' x
    }
    where
      foundation'
        : ∀ x
        → (_≈CP_ conPreorder x emptyN)
          ⊎ (Σ N (λ y → E x y × (∀ z → E x z → ¬ (E y z))))
      foundation' x with FoundationStructure.foundation Fnd emptyN x
      ... | inj₁ eq = inj₁ (≡→≈CP {CP = conPreorder} eq)
      ... | inj₂ rest = inj₂ rest
