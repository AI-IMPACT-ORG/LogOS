{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Irreversibility.BitReset where

-- Minimal total irreversible map:
-- a bit reset collapses `zero` and `one` at the boundary without using
-- partiality. The obstruction is purely order-theoretic.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _≈_)
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom using (KernelHom; mkKernelHomParts; map∂)
open import LogOS.LT.ConPreorder.Isomorphism using (OrderIso; collapse-obstructs-orderIso) renaming (f to iso-f)

infix 4 _⊑Bit_

data Bit : Set where
  zero : Bit
  one  : Bit

_⊑Bit_ : Bit → Bit → Set
_⊑Bit_ = _≡_

BitPreorder : ConPreorder lzero lzero
BitPreorder =
  record
    { Con = Bit
    ; _⊑_ = _⊑Bit_
    ; refl = refl
    ; trans = trans
    }

BitKernel : Kernel lzero lzero lzero
BitKernel =
  record
    { bnd = BitPreorder
    ; Code = Bit
    ; decode = λ b → b
    }

resetBoundary : Bit → Bit
resetBoundary _ = zero

reset0 : KernelHom BitKernel BitKernel
reset0 =
  mkKernelHomParts
    (record
      { map∂ = resetBoundary
      ; map∂-mono = λ { refl → refl }
      })
    (record
      { mapCode = resetBoundary
      ; decode-mapCode = λ _ → (refl , refl)
      })

reset0-collapses-zero-one
  : _≈_ BitPreorder (map∂ reset0 zero) (map∂ reset0 one)
reset0-collapses-zero-one = (refl , refl)

zero≉one : ¬ _≈_ BitPreorder zero one
zero≉one (() , _)

reset0-boundary-notOrderIso
  : ¬ Σ (OrderIso BitPreorder) (λ i → ∀ x → iso-f i x ≡ map∂ reset0 x)
reset0-boundary-notOrderIso (i , f≡reset) =
  collapse-obstructs-orderIso i zero one zero≉one fi-collapses
  where
    fi-zero≡fi-one : iso-f i zero ≡ iso-f i one
    fi-zero≡fi-one = trans (f≡reset zero) (sym (f≡reset one))

    fi-collapses : _≈_ BitPreorder (iso-f i zero) (iso-f i one)
    fi-collapses = (fi-zero≡fi-one , sym fi-zero≡fi-one)
