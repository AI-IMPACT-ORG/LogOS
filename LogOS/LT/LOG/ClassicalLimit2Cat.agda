{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.ClassicalLimit2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Kernels equipped with an explicit *classical-limit* assumption:
-- antisymmetry of the boundary preorder.
-- (“Classical limit” here means extensional/posetal collapse, not classical logic/LEM.)
--
-- Engineering reading:
-- this is the opt-in object layer that allows collapsing `≈`-coherence to strict
-- equalities (`≡`) as an explicit robustness check.

open import LogOS.Prelude
open import LogOS.LT.Kernel using (bnd)
import LogOS.LT.Hom.Core as Hom
open Hom using (KernelHom)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; ProductDisplayed
  ; DecoratedThin2Cat
  ; mapDecorated
  )

open import LogOS.LT.ConPreorder.Antisymmetry using (Antisymmetry)
import LogOS.LT.LOG.StrictDecode2Cat as StrictDecode

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.Template.Singleton2Cat as Template

ClassicalLimitDisplayed
  : ∀ {ℓ ℓRel ℓCode : Level}
  → DisplayedThin2Cat (LOG {ℓ} {ℓRel} {ℓCode}) (lsuc (ℓ ⊔ ℓRel)) lzero
ClassicalLimitDisplayed {ℓ} {ℓRel} {ℓCode} =
  record
    { Ob = λ K → Antisymmetry (bnd K)
    ; HomD = λ {K} {K'} (_ : KernelHom K K') (_ : Antisymmetry (bnd K)) (_ : Antisymmetry (bnd K')) → ⊤
    ; idD = λ _ → tt
    ; compD = λ _ _ → tt
    }

-- --------------------------------------------------------------------------
-- PortStack packaging: tag + signature + singleton stack.

data ClassicalLimitTag : Set where
  classicalLimitTag : ClassicalLimitTag

module Port {ℓ ℓRel ℓCode : Level} =
  Template.SingletonLayer
    {Tag = ClassicalLimitTag}
    (ClassicalLimitDisplayed {ℓ} {ℓRel} {ℓCode})

classicalLimitSig
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortSig.PortSig (LOG {ℓ} {ℓRel} {ℓCode}) ClassicalLimitTag
classicalLimitSig {ℓ} {ℓRel} {ℓCode} =
  Port.portSig {ℓ} {ℓRel} {ℓCode}

open Port public using (port2Cat; singleton; stack; port; Displayed; WithPort; forget)

-- --------------------------------------------------------------------------
-- Strictify: build a strict decode-law layer from antisymmetry.
--
-- This is the internal antisymmetry-based strictification step: given an explicit antisymmetry port on
-- the target boundary, any `≈`-coherent kernel morphism upgrades to a strict
-- decode law (`≡`), without changing its observable behaviour.

strictifyStrictDecode
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor
      (WithPort {ℓ} {ℓRel} {ℓCode})
      (StrictDecode.WithPort {ℓ} {ℓRel} {ℓCode})
strictifyStrictDecode {ℓ} {ℓRel} {ℓCode} =
  mapDecorated
    (ClassicalLimitDisplayed {ℓ} {ℓRel} {ℓCode})
    (StrictDecode.Displayed {ℓ} {ℓRel} {ℓCode})
    (λ {A} _ → StrictDecode.strictDecodeUnit)
    (λ {A} {B} {f} {x} {y} _ → λ γ → Antisymmetry.≈→≡ y (Hom.decode-mapCode f γ))

-- --------------------------------------------------------------------------
-- Generic strictification: thread the classical-limit assumption through an
-- *arbitrary* displayed port layer over `LOG`.
--
-- If a port is formulated as a displayed layer `D` over `LOG`, then:
-- - `ProductDisplayed ClassicalLimitDisplayed D` equips objects with the
--   antisymmetry port and keeps the original port data.
-- - `ProductDisplayed StrictDecodeDisplayed D` keeps the original port data and
--   equips morphisms with the strict decode law.
--
-- The strictifier below is the canonical bridge between these: it derives the
-- strict decode law from antisymmetry of the *target* boundary, without
-- changing the underlying adapter (`KernelHom`) or the port law witness.

strictifyDisplayed
  : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
    {D : DisplayedThin2Cat (LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
  → Thin2Functor
      (DecoratedThin2Cat (ProductDisplayed (ClassicalLimitDisplayed {ℓ} {ℓRel} {ℓCode}) D))
      (DecoratedThin2Cat (ProductDisplayed (StrictDecode.Displayed {ℓ} {ℓRel} {ℓCode}) D))
strictifyDisplayed {ℓ} {ℓRel} {ℓCode} {D = D} =
  mapDecorated
    (ProductDisplayed (ClassicalLimitDisplayed {ℓ} {ℓRel} {ℓCode}) D)
    (ProductDisplayed (StrictDecode.Displayed {ℓ} {ℓRel} {ℓCode}) D)
    (λ {A} (_ , portA) → (StrictDecode.strictDecodeUnit , portA))
    (λ {A} {B} {f} {x} {y} (_ , compat) →
      ( (λ γ → Antisymmetry.≈→≡ (fst y) (Hom.decode-mapCode f γ))
      , compat
      ))
