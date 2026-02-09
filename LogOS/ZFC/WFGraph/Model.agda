{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.WFGraph.Model where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro; ¬_; ⊥; ⊥-elim)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.Truth as Truth
open import LogOS.API.Kernel

open import LogOS.Prelude using (Σ; _,_; proj₁; proj₂; _×_)
open import LogOS.Prelude using (_⊎_; inj₁; inj₂)

open import LogOS.ZFC.SetU.WFGraphCore as Core using (WFGraph)
open import LogOS.ZFC.SetU.GraphTreeBridge as Bridge using (SupStructure)
open import LogOS.ZFC.SetTheory.DefinablePackNoInfinity using (ZFAxiomsᵈ-NoInf)

-- An explicit, presentations-first ZF model over a well-founded membership graph.
--
-- This is the “most interesting” route in the sense that:
-- - sets are *nodes* of a global well-founded graph,
-- - membership is the edge relation,
-- - definable relations are sets of Kuratowski pairs (also nodes),
-- - Union/Pairing/Separationᵈ/Replacementᵈ are implemented by concrete `supN`,
-- - Powerset is left as an explicit *extra* structure on the graph carrier.
--
-- This module does not attempt to solve the full LogOS⇾ZFC story by itself
-- (Infinity/limit closure, stability, observational upgrades). It provides a
-- concrete ZF-like universe that can be plugged into those pipelines.

record PowersetStructure {ℓ : Level} (G : WFGraph ℓ) (S : SupStructure G) : Set (lsuc ℓ) where
  open WFGraph G renaming (Node to N; Edge to E)
  field
    Pow : N → N
    Pow-mem↔ : ∀ {x z} → E (Pow x) z ↔ (∀ w → E z w → E x w)

open PowersetStructure public

record ExtensionalityStructure {ℓ : Level} (G : WFGraph ℓ) : Set (lsuc ℓ) where
  open WFGraph G renaming (Node to N; Edge to E)
  field
    ext≡ : ∀ x y → (∀ z → E x z ↔ E y z) → x ≡ y

open ExtensionalityStructure public

record FoundationStructure {ℓ : Level} (G : WFGraph ℓ) : Set (lsuc ℓ) where
  open WFGraph G renaming (Node to N; Edge to E)
  field
    foundation
      : (emptyN : N)
      → ∀ x → (x ≡ emptyN) ⊎ (Σ N (λ y → E x y × (∀ z → E x z → ¬ (E y z))))

open FoundationStructure public

module _ {ℓ : Level}
         (G : WFGraph ℓ)
         (S : SupStructure G)
         (Ext : ExtensionalityStructure G)
         (P : PowersetStructure G S)
         (F : FoundationStructure G)
         where
  open WFGraph G renaming (Node to N; Edge to E; wf to wfG)
  open SupStructure S renaming (supN to supNₛ; mem-sup↔ to mem-sup↔ₛ)

  -- Basic set constructors on the graph carrier.

  emptyN : N
  emptyN = supNₛ (⊥ {ℓ}) (λ ())

  singleton : N → N
  singleton x = supNₛ (Topℓ {ℓ}) (λ _ → x)

  Two : Set ℓ
  Two = Topℓ {ℓ} ⊎ Topℓ {ℓ}

  pairMap : N → N → Two → N
  pairMap x y (inj₁ _) = x
  pairMap x y (inj₂ _) = y

  pairN : N → N → N
  pairN x y = supNₛ Two (pairMap x y)

  -- Kuratowski ordered pair ⟨x,y⟩ = {{x},{x,y}}
  opair : N → N → N
  opair x y = supNₛ (Topℓ {ℓ} ⊎ Topℓ {ℓ}) (λ { (inj₁ _) → singleton x ; (inj₂ _) → pairN x y })

  -- Union: ⋃x has members of members of x.
  UnionI : N → Set ℓ
  UnionI x = Σ N (λ y → E x y × Σ N (λ z → E y z))

  unionMap : ∀ x → UnionI x → N
  unionMap _ (y , (_ , (z , _))) = z

  unionN : N → N
  unionN x =
    supNₛ (UnionI x) (unionMap x)

  -- Successor: succ x = x ∪ {x}
  SuccI : N → Set ℓ
  SuccI x = Topℓ {ℓ} ⊎ Σ N (λ y → E x y)

  succMap : ∀ x → SuccI x → N
  succMap x (inj₁ _) = x
  succMap _ (inj₂ (y , _)) = y

  succN : N → N
  succN x =
    supNₛ (SuccI x) (succMap x)

  mem-succN↔ : ∀ x z → E (succN x) z ↔ ((E x z) ⊎ (z ≡ x))
  mem-succN↔ x z =
    intro (to z) (from z)
    where
      to : ∀ z → E (succN x) z → (E x z) ⊎ (z ≡ x)
      to z ez
        with _↔_.to (mem-sup↔ₛ {I = SuccI x} {f = succMap x} {y = z}) ez
      ... | (inj₁ _ , pr) = inj₂ (sym pr)
      ... | (inj₂ (y , xy) , pr) = inj₁ (subst (E x) pr xy)

      from : ∀ z → (E x z ⊎ z ≡ x) → E (succN x) z
      from z (inj₂ z≡x) =
        subst (λ t → E (succN x) t) (sym z≡x)
          (_↔_.from (mem-sup↔ₛ {I = SuccI x} {f = succMap x} {y = x}) ((inj₁ tt) , refl))
      from z (inj₁ xz) =
        _↔_.from (mem-sup↔ₛ {I = SuccI x} {f = succMap x} {y = z})
          ((inj₂ (z , xz)) , refl)

  -- Boundary/kernel carrier: nodes ordered by inclusion of immediate members.
  infix 4 _⊑N_
  _⊑N_ : N → N → Set ℓ
  x ⊑N y = ∀ z → E x z → E y z

  refl⊑N : ∀ x → x ⊑N x
  refl⊑N _ _ e = e

  trans⊑N : ∀ {x y z} → x ⊑N y → y ⊑N z → x ⊑N z
  trans⊑N xy yz u e = yz u (xy u e)

  -- Empty axiom from `mem-sup↔ₛ`.
  empty-axiomN : Σ N (λ e → ∀ z → ¬ (E e z))
  empty-axiomN =
    emptyN , (λ z ez →
      let m = _↔_.to (mem-sup↔ₛ {I = ⊥ {ℓ}} {f = λ ()} {y = z}) ez
      in ⊥-elim (proj₁ m))

  pairing-axiomN : ∀ x y → Σ N (λ p → ∀ z → E p z ↔ ((z ≡ x) ⊎ (z ≡ y)))
  pairing-axiomN x y =
    pairN x y ,
      (λ z →
        intro (to z) (from z))
    where
      to : ∀ z → E (pairN x y) z → (z ≡ x) ⊎ (z ≡ y)
      to z ez
        with _↔_.to
               (mem-sup↔ₛ
                 {I = Two}
                 {f = pairMap x y}
                 {y = z})
               ez
      ... | (inj₁ _ , pr) = inj₁ (sym pr)
      ... | (inj₂ _ , pr) = inj₂ (sym pr)

      from : ∀ z → (z ≡ x ⊎ z ≡ y) → E (pairN x y) z
      from z (inj₁ z≡x) =
        _↔_.from
          (mem-sup↔ₛ
            {I = Two}
            {f = pairMap x y}
            {y = z})
          (inj₁ ttℓ , sym z≡x)
      from z (inj₂ z≡y) =
        _↔_.from
          (mem-sup↔ₛ
            {I = Two}
            {f = pairMap x y}
            {y = z})
          (inj₂ ttℓ , sym z≡y)

  -- NOTE: The rest of the ZF constructors are provided as explicit structure
  -- below (and do not attempt to optimise proof size here).

  -- A tiny LogOS kernel whose boundary constraints are these nodes (ordered by ⊑N).
  -- All world/adjunction layers are trivial; the point is to supply a kernel K so
  -- we can package the definable-ZF interface `ZFAxiomsᵈ-NoInf K`.

  Sig : LogOSSignature ℓ
  Sig = record
    { sorts = record { Iface = Topℓ {ℓ} ; Cosp = Topℓ {ℓ} ; ∂Cosp = Topℓ {ℓ} }
    ; cospanOps = record
        { src = λ _ → ttℓ
        ; tgt = λ _ → ttℓ
        ; idC = λ _ → ttℓ
        ; _∘C_ = λ _ _ → ttℓ
        ; _⊕C_ = λ _ _ → ttℓ
        ; _⊗C_ = λ _ _ → ttℓ
        }
    ; boundaryOps = record
        { src∂ = λ _ → ttℓ
        ; tgt∂ = λ _ → ttℓ
        ; id∂  = λ _ → ttℓ
        ; _∘∂_ = λ _ _ → ttℓ
        ; _⊕∂_ = λ _ _ → ttℓ
        ; _⊗∂_ = λ _ _ → ttℓ
        ; from∂ = λ _ → ttℓ
        ; to∂   = λ _ → ttℓ
        }
    }

  Q : QAdapter ℓ
  Q = trivialQAdapter

  module W = Worlds Sig

  HWorld : W.WorldH Q
  HWorld = record
    { _≤ctx_ = λ _ _ → Topℓ {ℓ}
    ; WFlow   = λ _ _ → ttℓ
    ; wflow-refl = λ _ → ttℓ
    ; wflow-trans = λ _ _ _ → ttℓ
    }

  conPreorder : ConPreorder ℓ
  conPreorder = record
    { Con  = N
    ; _⊑_ = _⊑N_
    ; refl = refl⊑N _
    ; trans = trans⊑N
    }

  BB : BulkBoundary ℓ
  BB = record { bulk = conPreorder ; bnd = conPreorder }

  mon : MonoidalOps conPreorder
  mon = record
    { _⊗_ = λ x _ → x
    ; I   = emptyN
    ; mono⊗ = λ p _ → p
    }

  module HT = Truth.HomotypicalTruth Sig Q HWorld
  module ST = Truth.StrictTruth Sig

  Holo : LaxMonoidalAdjunction BB mon mon
  Holo = record
    { core = record
        { ext = λ x → x
        ; bnd = λ x → x
        ; unit-lax = λ x → refl⊑N x
        ; counit-lax = λ x → refl⊑N x
        }
    ; ext-⊗-lax = λ x y → refl⊑N x
    ; ext-I-lax = refl⊑N emptyN
    ; bnd-⊗-lax = λ x y → refl⊑N x
    ; bnd-I-lax = refl⊑N emptyN
    }

  HTruth : HT.HLayer BB
  HTruth = record
    { Sat_H = λ _ _ → Topℓ {ℓ}
    ; mono-Con = λ _ _ → ttℓ
    ; mono-ctx = λ _ _ → ttℓ
    }

  -- Explicit degeneracy witness: H-tier truth is vacuous (always satisfied).
  vacuousHTruth : HT.VacuousHLayer HTruth
  vacuousHTruth = record { satAll = λ _ _ → ttℓ }

  HInv : HT.Invariance BB
  HInv = record
    { Inv_H = λ c → c
    ; infl = λ x → refl⊑N x
    ; idemp-lax = λ x → refl⊑N x
    }

  Sat_H_bnd : Topℓ {ℓ} → N → Set ℓ
  Sat_H_bnd _ _ = Topℓ {ℓ}

  sat-coh : ∀ (w : Topℓ {ℓ}) (c : N) → (HT.HLayer.Sat_H HTruth w c) ↔ (Sat_H_bnd ttℓ c)
  sat-coh _ _ = intro (λ x → x) (λ x → x)

  Strict : ST.StrictLayer (Topℓ {ℓ})
  Strict = record { Sat_S = λ _ _ → Topℓ {ℓ} }

  -- Guarded tier: ungraded, identity flow (closed, idempotent-lax).
  GTierWF : GTier Q conPreorder
  GTierWF = record
    { Step      = ⊤
    ; step      = tt
    ; sat       = tt
    ; Flow      = λ _ c → c
    ; mono      = λ {c} {c'} le → le
    ; infl-sat  = λ c → refl⊑N c
    ; idemp-sat = λ c → refl⊑N c
    ; Th*       = emptyN
    ; Th*-fixed = refl⊑N emptyN , refl⊑N emptyN
    }

  K : Kernel Sig Q
  K = record
    { shape = record
        { HWorld = HWorld
        ; BB     = BB
        ; MBulk  = mon
        ; MBnd   = mon
        ; Holo   = Holo
        ; HTruth = HTruth
        ; HInv   = HInv
        ; Sat_H_bnd = Sat_H_bnd
        ; sat-coh   = sat-coh
        ; Fml = Topℓ {ℓ}
        ; Strict = Strict
        ; TransH = λ _ → emptyN
        ; coh-LH = λ _ _ → intro (λ x → x) (λ x → x)
        ; Code = N
        ; encode = λ c → c
        ; decode = λ γ → γ
        ; Guard = λ γ → γ
        ; Body = λ _ → emptyN
        ; γ* = emptyN
        ; reify = λ γ → γ
        ; Body∂ = λ _ → emptyN
        }
    ; shapeLaws = record
        { decode∘encode = λ _ → refl
        ; γ*-guard      = refl⊑N emptyN , refl⊑N emptyN
        ; reify-decode  = λ _ → refl
        ; body-decode   = λ _ → refl
        }
    ; G           = GTierWF
    ; guard-decode = λ _ → refl
    ; decode-γ*    = refl
    }

  -- Definable ZF interface over this kernel.
  --
  -- NOTE: this is “definable” only in the sense that relations/functions are
  -- encoded as *sets of ordered pairs* (nodes) and consumed through `Graph`.

  GraphN : N → N → N → Set ℓ
  GraphN γ u z = E γ (opair u z)

  SepI : N → N → Set ℓ
  SepI γ x = Σ N (λ z → (E x z) × (E γ z))

  sepMap : ∀ γ x → SepI γ x → N
  sepMap _ _ (z , _) = z

  separationᵈN : (γ : N) → (x : N) → Σ N (λ y → ∀ z → E y z ↔ ((E x z) × (E γ z)))
  separationᵈN γ x =
    supNₛ (SepI γ x) (sepMap γ x) ,
    (λ z →
      intro
        (λ eyz →
          let m = _↔_.to (mem-sup↔ₛ {I = SepI γ x} {f = sepMap γ x} {y = z}) eyz
          in
          let i = proj₁ m
              pr = proj₂ m
              zx = fst (proj₂ i)
              zg = snd (proj₂ i)
          in subst (λ t → (E x t) × (E γ t)) pr (zx , zg))
        (λ { (exz , egz) →
          _↔_.from (mem-sup↔ₛ {I = SepI γ x} {f = sepMap γ x} {y = z})
                   ((z , (exz , egz)) , refl) }))

  RepI : N → N → Set ℓ
  RepI γ x = Σ N (λ u → (E x u) × Σ N (λ z → GraphN γ u z))

  repMap : ∀ γ x → RepI γ x → N
  repMap _ _ (u , (_ , (z , _))) = z

  replacementᵈN
    : (γ : N)
    → (∀ u z₁ z₂ → GraphN γ u z₁ → GraphN γ u z₂ → _≈CP_ conPreorder z₁ z₂)
    → (x : N)
    → Σ N (λ y → ∀ z → E y z ↔ (Σ N (λ u → (E x u) × GraphN γ u z)))
  replacementᵈN γ _ x =
    supNₛ (RepI γ x) (repMap γ x) ,
    (λ z →
      intro
        (λ eyz →
          let m = _↔_.to (mem-sup↔ₛ {I = RepI γ x} {f = repMap γ x} {y = z}) eyz
          in
          let i = proj₁ m
              pr = proj₂ m
              u  = proj₁ i
              xu = fst (proj₂ i)
              z' = proj₁ (snd (proj₂ i))
              gz = proj₂ (snd (proj₂ i))
          in subst (λ t → Σ N (λ u0 → (E x u0) × GraphN γ u0 t)) pr (u , (xu , gz)))
        (λ { (u , (xu , gu)) →
          _↔_.from (mem-sup↔ₛ {I = RepI γ x} {f = repMap γ x} {y = z})
                   ((u , (xu , (z , gu))) , refl) }))

  zfᵈNoInf : ZFAxiomsᵈ-NoInf K
  zfᵈNoInf = record
    { SetU   = N
    ; _∈_    = λ z x → E x z
    ; ⟦_⟧     = λ γ → γ
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
                          {I = UnionI x}
                          {f = unionMap x}
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
                    {I = UnionI x}
                    {f = unionMap x}
                    {y = z})
                  ((y0 , (xy , (z , yz))) , refl) }))
    ; powerset = λ x → Pow P x , (λ z → Pow-mem↔ P {x = x} {z = z})
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
    ; separationᵈ = separationᵈN
    ; Graph = GraphN
    ; replacementᵈ = replacementᵈN
    ; foundation =
        λ x →
          let
            to≈ : (x ≡ emptyN) → _≈CP_ conPreorder x emptyN
            to≈ eq = ≡→≈CP {CP = conPreorder} eq
          in
          foundation' x to≈
    }
    where
      foundation'
        : ∀ x
        → (x ≡ emptyN → _≈CP_ conPreorder x emptyN)
        → (_≈CP_ conPreorder x emptyN)
          ⊎ (Σ N (λ y → E x y × (∀ z → E x z → ¬ (E y z))))
      foundation' x to≈ with FoundationStructure.foundation F emptyN x
      ... | inj₁ eq = inj₁ (to≈ eq)
      ... | inj₂ rest = inj₂ rest
