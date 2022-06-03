{-# OPTIONS --cubical #-}
module Contextual where

-- open import Data.Nat
import Prelude as P
open import Categories.Category.Core
open import Categories.Category
open import Level renaming (suc to ℓsuc)
import Categories.Object.Terminal as Terminal
import Categories.Object.Product as Product
import Categories.Object.Exponential as Exponential
open import Cubical.Core.Everything

private
  variable
    o ℓ e : Level

record ContextualCCC (𝒞 : Category o ℓ e) : Set (ℓsuc (o ⊔ ℓ ⊔ e)) where
  open Category 𝒞
  open Terminal 𝒞
  open Product 𝒞
  open Exponential 𝒞
  private
    module Prod = Product.Product
    module Exp = Exponential.Exponential
    module Fin = Terminal.Terminal
  field
    ⊤  : Terminal
    Ty  : Set o
    ∣_∣  : (t : Ty) → Obj
    _×_  : (Γ : Obj) → (A : Ty) → Product Γ ∣ A ∣
    _⇛_ : (A B : Ty) → Exponential ∣ A ∣ ∣ B ∣
    _×≈_ : (A B : Ty) → Exp.B^A (A ⇛ B) × A ≡ (Exp.product (A ⇛ B))
  
  -- underlying object of product
  _|>_ : (Γ : Obj) → (A : Ty) → Obj
  Γ |> A = Prod.A×B (Γ × A)

  -- underlying object of exponential
  _∣⇛∣_ : (A B : Ty) → Obj
  A ∣⇛∣ B = Exp.B^A (A ⇛ B)

  ⟨_,_⟩ : ∀ {Δ Γ : Obj} {A : Ty} → 𝒞 [ Δ , Γ ] → 𝒞 [ Δ , ∣ A ∣ ] → 𝒞 [ Δ , Γ |> A ]
  ⟨_,_⟩ {Γ = Γ} {A = A} = Prod.⟨_,_⟩ (Γ × A)

  Z : ∀ {Γ : Obj} {A : Ty} → 𝒞 [ Γ |> A , ∣ A ∣  ]
  Z {Γ = Γ} {A = A} = Prod.π₂ (Γ × A)

  π : ∀ {Γ : Obj} {A : Ty} → 𝒞 [ Γ |> A , Γ  ]
  π {Γ = Γ} {A = A} = Prod.π₁ (Γ × A)

  Λ : ∀ {Γ : Obj} {A B : Ty} → 𝒞 [ Γ |> A , ∣ B ∣ ] → 𝒞 [ Γ , (A ∣⇛∣ B) ]
  Λ {Γ = Γ} {A = A} {B = B} = Exp.λg (A ⇛ B) (Γ × A)

  APP : ∀ {Γ : Obj} {A B : Ty} → 𝒞 [ Γ , (A ∣⇛∣ B) ] → 𝒞 [ Γ , ∣ A ∣ ] → 𝒞 [ Γ , ∣ B ∣ ]
  APP {A = A} {B = B} f g = {!!} -- (Exp.eval (A ⇛ B)) ∘ ⟨ f , g ⟩
    where
      coe : 𝒞 [ ∣ A ∣ |> B ,  Exp.B^A×A (A ⇛ B)]
      coe = {!!}
      eval : 𝒞 [ Exp.B^A×A (A ⇛ B) , ∣ B ∣ ] 
      eval = Exp.eval (A ⇛ B)
