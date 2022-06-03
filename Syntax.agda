{-# OPTIONS --cubical #-}

module Syntax where

open import Cubical.Core.Everything hiding (Sub)
open import Cubical.Foundations.Prelude using (refl;_∎;_≡⟨_⟩_;_≡⟨_⟩≡⟨_⟩_; cong; isSet; isProp)
open import Level renaming (suc to ℓsuc)

data Ty : Set where
  ι : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : (Γ : Con) → (A : Ty) → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {Γ}{B} → A ∈ Γ → A ∈ (Γ , B)

data Weak : Con → Con → Set where
  ∙     : Weak ∙ ∙
  keepₖ : ∀ {Δ Γ} {A} → Weak Γ Δ → Weak (Γ , A) (Δ , A)
  dropₖ : ∀ {Δ Γ} {A} → Weak Γ Δ → Weak (Γ , A) Δ

data Tm (Γ : Con) : Ty → Set
data Sub : Con → Con → Set


data Sub where
  ∙    : ∀ {Γ} → Sub Γ ∙
  _,_  : ∀ {Γ} {Δ} {A} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ , A)
  idₛ  : ∀ {Γ} → Sub Γ Γ
  _∘ₛ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
  wkₛ  : ∀ {Γ Δ}{A} → Sub Γ (Δ , A) → Sub Γ Δ
  idₗ   : ∀ {Γ Δ} {δ : Sub Γ Δ} → idₛ ∘ₛ δ ≡ δ
  idᵣ   : ∀ {Γ Δ} {δ : Sub Γ Δ} → δ ∘ₛ idₛ ≡ δ
  assoc :  ∀ {Γ₁ Γ₂ Γ₃ Γ₄} {s₃ : Sub Γ₃ Γ₄} {s₂ : Sub Γ₂ Γ₃} {s₁ : Sub Γ₁ Γ₂} →
    (s₃ ∘ₛ s₂) ∘ₛ s₁ ≡ s₃ ∘ₛ (s₂ ∘ₛ s₁)
  η∙   : ∀ {Γ} {σ : Sub Γ ∙} → σ ≡ ∙

weakₛ : ∀ {Γ}{A} → Sub (Γ , A) Γ
weakₛ = wkₛ idₛ


data Tm Γ where
  var  : ∀ {A} → A ∈ Γ → Tm Γ A
  varₛ :  ∀ {A} → (s : Sub Γ (Γ , A)) → Tm Γ A
  lam : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  _[_] : ∀ {Δ} {A} → Tm Δ A → Sub Γ Δ → Tm Γ A
  [id] : ∀ {A}{t : Tm Γ A} → t [ idₛ ] ≡ t
  [∘ₛ] : ∀ {Δ Σ}{A}{s₁ : Sub Δ Σ} {s₂ : Sub Γ Δ  }{t : Tm Σ A} → t [ s₁ ] [ s₂ ] ≡ t [ s₁ ∘ₛ s₂ ]
  η   : ∀ {A B} → (f : Tm Γ (A ⇒ B)) → (lam (app (f [ weakₛ ]) (var vz))) ≡ f
  β   : ∀ {A B} {Δ} → (s : Sub Γ Δ)
    → (f : Tm (Δ , A) B) (t : Tm Γ A) → app ((lam f) [ s ]) t ≡ f [ (s , t) ]


module Elim {ℓ} {ℓ'} where
  record Motives : Set (ℓ-suc (ℓ ⊔ ℓ')) where
    field
      Subᴹ : ∀ (Γ Δ : Con) → Sub Γ Δ → Set ℓ
      Tmᴹ  : (Γ : Con) (A : Ty) → Tm Γ A → Set ℓ'
      
  record Methods (M : Motives) : Set (ℓ ⊔ ℓ') where
    open Motives M
    field
      ∙ᴹ    : ∀ {Γ} → Subᴹ Γ ∙ ∙
      _,ᴹ_  : ∀ {Γ} {Δ} {A} {s : Sub Γ Δ} {t : Tm Γ A} → 
        Subᴹ Γ Δ s → Tmᴹ Γ A t → Subᴹ Γ (Δ , A) (s , t)
      idₛᴹ  : ∀ {Γ} → Subᴹ Γ Γ idₛ
      _∘ₛᴹ_ : ∀ {Γ Δ Σ} {s₁ : Sub Δ Σ}{s₂ : Sub Γ Δ} →
        (Subᴹ Δ Σ s₁) → (Subᴹ Γ Δ s₂) → Subᴹ Γ Σ (s₁ ∘ₛ s₂)
      wkₛᴹ  : ∀ {Γ Δ}{A} {s : Sub Γ (Δ , A)} → Subᴹ Γ (Δ , A) s → Subᴹ Γ Δ (wkₛ s)
      idₗᴹ   : ∀ {Γ Δ} {δ : Sub Γ Δ} → PathP (λ i → Subᴹ Γ Δ (idₗ i)) → Subᴹ Γ Δ (idₛ ∘ₛ δ ) 
--  idₛ ∘ₛ δ ≡ δ
{-

      _∘ₛᴹ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ


      idᵣᴹ   : ∀ {Γ Δ} {δ : Sub Γ Δ} → δ ∘ₛ idₛ ≡ δ
      assocᴹ :  ∀ {Γ₁ Γ₂ Γ₃ Γ₄} {s₃ : Sub Γ₃ Γ₄} {s₂ : Sub Γ₂ Γ₃} {s₁ : Sub Γ₁ Γ₂} →
        (s₃ ∘ₛ s₂) ∘ₛ s₁ ≡ s₃ ∘ₛ (s₂ ∘ₛ s₁)
      η∙ᴹ   : ∀ {Γ} {σ : Sub Γ ∙} → σ ≡ ∙
-}
{-
      varᴹ  : ∀ {A} → A ∈ Γ → Tm Γ A
      varₛᴹ :  ∀ {A} → (s : Sub Γ (Γ , A)) → Tm Γ A
      lamᴹ : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
      appᴹ : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
      _[_]ᴹ : ∀ {Δ} {A} → Tm Δ A → Sub Γ Δ → Tm Γ A
      [id]ᴹ : ∀ {A}{t : Tm Γ A} → t [ idₛ ] ≡ t
      [∘ₛ]ᴹ : ∀ {Δ Σ}{A}{s₁ : Sub Δ Σ} {s₂ : Sub Γ Δ  }{t : Tm Σ A} → t [ s₁ ] [ s₂ ] ≡ t [ s₁ ∘ₛ s₂ ]
      ηᴹ   : ∀ {A B} → (f : Tm Γ (A ⇒ B)) → (lam (app (f [ weakₛ ]) (var vz))) ≡ f
      βᴹ   : ∀ {A B} {Δ} → (s : Sub Γ Δ)
        → (f : Tm (Δ , A) B) (t : Tm Γ A) → app ((lam f) [ s ]) t ≡ f [ (s , t) ]
-}

{-
module Init {ℓ'} (I : Type ℓ) where
  open RecFreeTy {ℓ' = ℓ'} I

  initial : (M : M.MonoidObj {ℓ'}) → Free I → fst M
  initial = {!!}
-}
