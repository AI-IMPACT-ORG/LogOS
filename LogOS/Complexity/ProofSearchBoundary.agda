{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.ProofSearchBoundary where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; ⊥; _↔_)

open import LogOS.Prelude using (ℕ; zero; suc; _+_)
open import LogOS.Prelude using (_⊎_; inj₁; inj₂)
open import LogOS.Prelude using (Σ; _,_; proj₁; proj₂; _×_; fst; snd)
open import LogOS.Prelude as Eq using (_≡_; refl; subst; cong; sym)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl; trans≤ℕ)

import LogOS.Complexity.CookReckhow as CR
open import LogOS.Complexity.CookReckhow using (Finℓ; fzero; fsuc; toNat)
import LogOS.Syntax.ProofSystem as PSCore
import LogOS.Computation.SemiDecider as SD
import LogOS.Theorems.Meta.LimitPublicisation as LP
open import LogOS.Theorems.Meta.LocalGlobalBoundary as LGB

-- Sharp boundary: proof verification vs proof search.
--
-- Given a decidable checker `Check : ℕ → Input → Set`, “verification” is the
-- per-candidate decision `Check n x ⊎ ¬ Check n x`.
--
-- “Proof search” is existential:
-- - bounded search (`∃ n ≤ b`) is decidable by finite search;
-- - unbounded search (`∃ n`) is only semi-decidable in general.
--
-- The “limit of infinite resources” is precisely the colimit of the bounded
-- approximants, i.e. the Σℕ form.

module For {ℓI ℓ : Level}
           (Input : Set ℓI)
           (P : Input → Set ℓ)
           where

  NatPreorder : LP.Preorder ℕ
  NatPreorder =
    record
      { CP =
          record
            { Con   = ℕ
            ; _⊑_   = _≤ℕ_
            ; refl  = ≤ℕ-refl
            ; trans = trans≤ℕ
            }
      ; Con≡ = refl
      }

  -- A proof system presented as a decidable checker on natural proof codes.
  record ProofSystem : Set (lsuc (lsuc (ℓ ⊔ ℓI))) where
    field
      Check    : ℕ → Input → Set ℓ
      decCheck : ∀ n x → Check n x ⊎ ¬ Check n x
      sound    : ∀ n x → Check n x → P x

  toCore : ProofSystem → PSCore.ProofSystem Input P
  toCore PS =
    record
      { Proof    = λ _ → ℕ
      ; Check    = λ x n → ProofSystem.Check PS n x
      ; decCheck = λ x n → ProofSystem.decCheck PS n x
      ; sound    = λ x n pr → ProofSystem.sound PS n x pr
      }

  -- Completeness turns the unbounded search predicate into P itself.
  Complete : ProofSystem → Set (lsuc (lsuc (ℓ ⊔ ℓI)))
  Complete PS = PSCore.Complete (toCore PS)

  -- Unbounded proof search = “there exists some proof code”.
  Prov∞ : ProofSystem → Input → Set ℓ
  Prov∞ PS x = PSCore.Prov (toCore PS) x

  -- Bounded proof search = “there exists a proof code ≤ b”.
  Prov≤ : ProofSystem → ℕ → Input → Set ℓ
  Prov≤ PS b x =
    Σ (Finℓ {ℓ} (suc b)) (λ i → ProofSystem.Check PS (toNat i) x)

  -- Monotonicity of bounded search in the resource bound b.
  --
  -- (This is the basic “increasing approximants” structure used to talk about limits.)
  embedFin : ∀ {n} → Finℓ {ℓ} n → Finℓ {ℓ} (suc n)
  embedFin fzero = fzero
  embedFin (fsuc i) = fsuc (embedFin i)

  toNat-embedFin : ∀ {n} (i : Finℓ {ℓ} n) → toNat (embedFin i) ≡ toNat i
  toNat-embedFin fzero = refl
  toNat-embedFin (fsuc i) = cong suc (toNat-embedFin i)

  monoProv≤ : ∀ {PS b} → ∀ x → Prov≤ PS b x → Prov≤ PS (suc b) x
  monoProv≤ {PS = PS} x (i , pr) =
    embedFin i
    , subst (λ n → ProofSystem.Check PS n x) (sym (toNat-embedFin i)) pr

  -- General monotonicity along any ≤ℕ witness (useful for cofinal/colimit transport).
  --
  -- This is a small but high-leverage “kernel guarantee”: once you have a bounded
  -- witness, it can be whiskered/extended to any larger budget.

  +-identityʳ : ∀ n → n + zero ≡ n
  +-identityʳ zero = refl
  +-identityʳ (suc n) = cong suc (+-identityʳ n)

  +-sucʳ : ∀ n k → n + suc k ≡ suc (n + k)
  +-sucʳ zero k = refl
  +-sucʳ (suc n) k = cong suc (+-sucʳ n k)

  raiseBy : ∀ {PS b x} (k : ℕ) → Prov≤ PS b x → Prov≤ PS (b + k) x
  raiseBy {PS} {b} {x} zero pr =
    subst (λ t → Prov≤ PS t x) (sym (+-identityʳ b)) pr
  raiseBy {PS} {b} {x} (suc k) pr =
    subst (λ t → Prov≤ PS t x) (sym (+-sucʳ b k))
      (monoProv≤ {PS = PS} {b = b + k} x (raiseBy {PS = PS} {b = b} {x = x} k pr))

  leToAdd : ∀ {b b'} → b ≤ℕ b' → Σ ℕ (λ k → b + k ≡ b')
  leToAdd {b = zero} {b'} z≤n = b' , refl
  leToAdd {b = suc b} {b' = suc b'} (s≤s p) =
    let ex = leToAdd {b = b} {b' = b'} p in
    proj₁ ex , cong suc (proj₂ ex)

  monoProv≤≤ : ∀ {PS b b'} → ∀ x → b ≤ℕ b' → Prov≤ PS b x → Prov≤ PS b' x
  monoProv≤≤ {PS} {b} {b'} x b≤b' pr =
    let ex = leToAdd {b = b} {b' = b'} b≤b' in
    subst (λ t → Prov≤ PS t x) (proj₂ ex) (raiseBy {PS = PS} {b = b} {x = x} (proj₁ ex) pr)

  -- The “limit”: Prov∞ is equivalent to the Σ of bounded approximants,
  -- and each bounded approximant is decidable by finite search.

  bounded→unbounded : ∀ {PS b x} → Prov≤ PS b x → Prov∞ PS x
  bounded→unbounded {PS} {b} {x} (i , pr) = toNat i , pr

  unbounded→someBound : ∀ {PS x} → Prov∞ PS x → Σ ℕ (λ b → Prov≤ PS b x)
  unbounded→someBound {PS} {x} (n , pr) =
    n , (searchIndex n , subst (λ k → ProofSystem.Check PS k x) (sym (toNat-searchIndex n)) pr)
    where
      searchIndex : ∀ n → Finℓ {ℓ} (suc n)
      searchIndex zero = fzero
      searchIndex (suc n) = fsuc (searchIndex n)

      toNat-searchIndex : ∀ n → toNat (searchIndex n) ≡ n
      toNat-searchIndex zero = refl
      toNat-searchIndex (suc n) = cong suc (toNat-searchIndex n)

  -- Convert a ≤ℕ witness into a bounded Fin index.
  --
  -- This is the bridge that lets you talk about “proof size ≤ budget”
  -- while still using the finite-search representation `Finℓ (suc b)`.
  finOfNat≤ : ∀ {b} (n : ℕ) → n ≤ℕ b → Finℓ {ℓ} (suc b)
  finOfNat≤ zero    z≤n = fzero
  finOfNat≤ (suc n) (s≤s nb) = fsuc (finOfNat≤ n nb)

  toNat-finOfNat≤ : ∀ {b} (n : ℕ) (p : n ≤ℕ b) → toNat (finOfNat≤ n p) ≡ n
  toNat-finOfNat≤ zero z≤n = refl
  toNat-finOfNat≤ (suc n) (s≤s p) = cong suc (toNat-finOfNat≤ n p)

  -- Cofinal schedules formalize “infinite resources”: a schedule eventually exceeds any bound.
  Cofinal : (ℕ → ℕ) → Set
  Cofinal sched = LGB.Cofinalℕ NatPreorder sched

-- If sched is cofinal, then Prov∞ is the colimit of the bounded approximants Prov≤ (sched n).
--
  -- Informally: unbounded proof search is the limit of bounded proof search.
  Prov∞→colim
    : ∀ {PS} (sched : ℕ → ℕ)
      → Cofinal sched
      → ∀ x → Prov∞ PS x → Σ ℕ (λ n → Prov≤ PS (sched n) x)
  Prov∞→colim {PS} sched cof x (k , pr) =
    let ex = cof k in
    let n  = proj₁ ex in
    let k≤ = proj₂ ex in
    let i  = finOfNat≤ k k≤ in
    n , (i , subst (λ t → ProofSystem.Check PS t x) (sym (toNat-finOfNat≤ k k≤)) pr)

  -- Decidability of bounded proof search.
  decProv≤ : ∀ (PS : ProofSystem) (b : ℕ) (x : Input) → Prov≤ PS b x ⊎ ¬ Prov≤ PS b x
  decProv≤ PS b x =
    CR.Search.searchFin (suc b)
      (λ i → ProofSystem.Check PS (toNat i) x)
      (λ i → ProofSystem.decCheck PS (toNat i) x)

  -- Unbounded proof search is semi-decidable via its bounded approximants.
  --
  -- This packages the “bounded search approximants” structure into a reusable
  -- interface (`SemiDecider`), making the intended reading explicit.

  semiProv∞ : (PS : ProofSystem) → SD.SemiDecider Input (Prov∞ PS)
  semiProv∞ PS =
    SD.mapSemiDecider (joinProv≤↔Prov∞ {PS = PS})
      (LGB.semiDeciderJoin NatPreorder (λ n → n) cofId (Prov≤ PS) monoProv≤-pre (decProv≤ PS))
    where
      joinProv≤↔Prov∞ : ∀ {PS} x → LGB.Join (Prov≤ PS) x ↔ Prov∞ PS x
      joinProv≤↔Prov∞ {PS} x =
        record
          { to   = λ ex → bounded→unbounded {PS = PS} {b = proj₁ ex} {x = x} (proj₂ ex)
          ; from = unbounded→someBound {PS = PS} {x = x}
          }

      cofId : LGB.Cofinalℕ NatPreorder (λ n → n)
      cofId b = b , ≤ℕ-refl

      monoProv≤-pre : ∀ {i j} → LP.Preorder._≤_ NatPreorder i j → ∀ {x} → Prov≤ PS i x → Prov≤ PS j x
      monoProv≤-pre {i = i} {j = j} i≤j {x} pr = monoProv≤≤ {PS = PS} x i≤j pr

  -- Verification is “local”: any *given* candidate can be checked.
  verify : ∀ (PS : ProofSystem) (n : ℕ) (x : Input) → ProofSystem.Check PS n x ⊎ ¬ ProofSystem.Check PS n x
  verify PS n x = ProofSystem.decCheck PS n x

  -- If PS is complete for P, then P is exactly unbounded proof search.
  P→Prov∞ : ∀ {PS} → Complete PS → ∀ x → P x → Prov∞ PS x
  P→Prov∞ {PS} C x px = PSCore.Complete.complete C x px

  Prov∞→P : (PSys : ProofSystem) → ∀ x → Prov∞ PSys x → P x
  Prov∞→P PSys x ex = ProofSystem.sound PSys (proj₁ ex) x (proj₂ ex)
