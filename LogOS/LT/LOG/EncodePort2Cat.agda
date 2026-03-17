{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.EncodePort2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _⊑_; refl⊑)
open import LogOS.LT.Kernel using (Kernel; EncodePort; encode; CodePreorder)
open import LogOS.LT.Hom.Core using (KernelHom; map∂; mapCode; idKernelHom; _∘_)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)

import LogOS.LT.Presentation.ExtensionalMinimality as ExtMin
import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.Template.Singleton2Cat as Template

data EncodeTag : Set where
  encodeTag : EncodeTag

encodeTagId : ℕ
encodeTagId = 20

record EncodeLaw {ℓ ℓRel ℓCode : Level} {K K' : Kernel ℓ ℓRel ℓCode}
  (h : KernelHom K K')
  (EK  : EncodePort K)
  (EK' : EncodePort K')
  : Set (ℓ ⊔ ℓRel ⊔ ℓCode) where
  field
    mapCode-encode⊑
      : ∀ c
      → _⊑_ (CodePreorder K')
          (mapCode h (encode EK c))
          (encode EK' (map∂ h c))

open EncodeLaw public

idEncodeLaw
  : ∀ {ℓ ℓRel ℓCode : Level} {K : Kernel ℓ ℓRel ℓCode}
  → (EK : EncodePort K)
  → EncodeLaw (idKernelHom K) EK EK
idEncodeLaw {K = K} _ =
  record { mapCode-encode⊑ = λ _ → refl⊑ (CodePreorder K) }

composeEncodeLaw
  : ∀ {ℓ ℓRel ℓCode : Level} {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
    {f : KernelHom K₁ K₂}
    {g : KernelHom K₂ K₃}
    {EK₁ : EncodePort K₁}
    {EK₂ : EncodePort K₂}
    {EK₃ : EncodePort K₃}
  → EncodeLaw f EK₁ EK₂
  → EncodeLaw g EK₂ EK₃
  → EncodeLaw (g ∘ f) EK₁ EK₃
composeEncodeLaw {K₂ = K₂} {K₃ = K₃} {f = f} {g = g} {EK₁ = EK₁} {EK₂ = EK₂} {EK₃ = EK₃} cf cg =
  record
    { mapCode-encode⊑ =
        λ c →
          let
            monoMapCodeG = ExtMin.mapCode-mono g
            module R = LogOS.Prelude.RefinementKit.Reasoning (CodePreorder K₃)
            open R using (begin⊑_; _⊑⟨_⟩_; _∎⊑)
          in
          begin⊑
            mapCode (g ∘ f) (encode EK₁ c)
              ⊑⟨ monoMapCodeG (mapCode-encode⊑ cf c) ⟩
            mapCode g (encode EK₂ (map∂ f c))
              ⊑⟨ mapCode-encode⊑ cg (map∂ f c) ⟩
            encode EK₃ (map∂ (g ∘ f) c)
            ∎⊑
    }

EncodeDisplayed
  : ∀ {ℓ ℓRel ℓCode : Level}
  → DisplayedThin2Cat (LOG {ℓ} {ℓRel} {ℓCode})
      (lsuc (ℓ ⊔ ℓCode))
      (ℓ ⊔ ℓRel ⊔ ℓCode)
EncodeDisplayed =
  record
    { Ob = EncodePort
    ; HomD = λ {K} {K'} (h : KernelHom K K') EK EK' → EncodeLaw h EK EK'
    ; idD = idEncodeLaw
    ; compD = λ cf cg → composeEncodeLaw cf cg
    }

module Port {ℓ ℓRel ℓCode : Level} =
  Template.SingletonLayer
    encodeTagId
    {Tag = EncodeTag}
    (EncodeDisplayed {ℓ} {ℓRel} {ℓCode})

encodeSig
  : ∀ {ℓ ℓRel ℓCode : Level}
  → PortSig.PortSig (LOG {ℓ} {ℓRel} {ℓCode}) encodeTagId EncodeTag
encodeSig {ℓ} {ℓRel} {ℓCode} =
  Port.portSig {ℓ} {ℓRel} {ℓCode}

open Port public using (port2Cat; singleton; stack; port; Displayed; WithPort; forget)
