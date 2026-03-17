{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.InstitutionRefinement where

open import LogOS.Prelude

open import LogOS.LT.InstitutionFragment using
  ( InstitutionFragment
  ; KernelInstitutionFragment
  ; KernelInstitutionCodeLaws
  ; KernelInstitutionFragmentCodeLaws
  ; KernelInstitutionFragmentData
  )
import LogOS.API.Strictification as StrictAPI

_ : InstitutionFragment
      (lsuc (lzero ⊔ lzero ⊔ lzero))
      (lsuc lzero ⊔ lsuc lzero ⊔ lzero)
      lzero
      lzero
      lzero
      lzero
_ = KernelInstitutionFragment

_ : KernelInstitutionCodeLaws {lzero} {lzero} {lzero}
_ = KernelInstitutionFragmentCodeLaws

kernelStrictLaws
  : StrictAPI.Institution.InstitutionFragmentStrictLaws
      (KernelInstitutionFragmentData {lzero} {lzero} {lzero})
kernelStrictLaws =
  record
    { mapSen-id = λ _ → refl
    ; mapSen-comp = λ _ _ _ → refl
    ; mapMod-id = λ _ → refl
    ; mapMod-comp = λ _ _ _ → refl
    }

_ : StrictAPI.Institution.InstitutionFragmentStrictLaws
      (KernelInstitutionFragmentData {lzero} {lzero} {lzero})
_ = kernelStrictLaws
