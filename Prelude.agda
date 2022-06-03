{-# OPTIONS --without-K #-}
module Prelude where

open import Data.Product
open import Level using (Level)

private
  variable
    Ix : Set
    ℓ  : Level
    X  : Set ℓ
    Y  : Set ℓ
    Z  : Set ℓ

-- functions
id : X → X
id x = x

_∘_ : (Y → Z) → (X → Y) → (X → Z)
g ∘ f = λ x → g (f x)

-- top
data ⊤ : Set where
  tt : ⊤


-- direct-sum

⨆ : {Ix} → ((i : Ix) → Set) → Set
⨆ {Ix} fᵢ = Σ Ix fᵢ

-- point

data Pt (a : Set) : Set where
  ⋆  : Pt a
  ↑_ : a → Pt a
