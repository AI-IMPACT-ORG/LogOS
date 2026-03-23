{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractDeutsch2Cat.Causality where

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ)
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.HomFlow using (KernelHomFlow; idKernelHomFlow; composeKernelHomFlow)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)

import LogOS.Ports.AbstractDeutsch2Cat.Locality as Locality
import LogOS.Ports.LawSlice2Cat as LawSlice

module Deutsch2CatLocal {ℓI ℓOCon ℓORel ℓCode : Level} (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}) where
  open DependentLocalSemantics PS
  module Local = Locality.Deutsch2CatLocal {ℓCode = ℓCode} PS

  data CausalTag : Set where
    causalTag : CausalTag

  causalTagId : ℕ
  causalTagId = 11

  -- Explicit unit payload (avoids `⊤`/`tt` footguns in composed stacks).
  record CausalOb : Set where
    constructor ttCausal

  module Port =
    LawSlice.Exports
      {C = Local.WithPort}
      {Tag = CausalTag}
      causalTagId
      CausalOb
      (λ {A} {B} (h : Con (Thin2Cat.Hom Local.WithPort A B))
        → KernelHomFlow GC GC (Local.physicalToKernelHom h))
      (idKernelHomFlow GC)
      (λ ff gg → composeKernelHomFlow ff gg)

  port2Cat : LawSlice.Singleton2Cat Local.WithPort causalTagId CausalTag
  port2Cat = Port.port2Cat

  open Port public using (singleton; stack; port; Displayed; WithPort; forget)
