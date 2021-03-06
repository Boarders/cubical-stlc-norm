{-# OPTIONS --cubical #-}
module Contextual where

-- open import Data.Nat
import Prelude as P
open import Categories.Category.Core
open import Categories.Category
open import Level renaming (suc to âsuc)
import Categories.Object.Terminal as Terminal
import Categories.Object.Product as Product
import Categories.Object.Exponential as Exponential
open import Cubical.Core.Everything

private
  variable
    o â e : Level

record ContextualCCC (ð : Category o â e) : Set (âsuc (o â â â e)) where
  open Category ð
  open Terminal ð
  open Product ð
  open Exponential ð
  private
    module Prod = Product.Product
    module Exp = Exponential.Exponential
    module Fin = Terminal.Terminal
  field
    â¤  : Terminal
    Ty  : Set o
    â£_â£  : (t : Ty) â Obj
    _Ã_  : (Î : Obj) â (A : Ty) â Product Î â£ A â£
    _â_ : (A B : Ty) â Exponential â£ A â£ â£ B â£
    _Ãâ_ : (A B : Ty) â Exp.B^A (A â B) Ã A â¡ (Exp.product (A â B))
  
  -- underlying object of product
  _|>_ : (Î : Obj) â (A : Ty) â Obj
  Î |> A = Prod.AÃB (Î Ã A)

  -- underlying object of exponential
  _â£ââ£_ : (A B : Ty) â Obj
  A â£ââ£ B = Exp.B^A (A â B)

  â¨_,_â© : â {Î Î : Obj} {A : Ty} â ð [ Î , Î ] â ð [ Î , â£ A â£ ] â ð [ Î , Î |> A ]
  â¨_,_â© {Î = Î} {A = A} = Prod.â¨_,_â© (Î Ã A)

  Z : â {Î : Obj} {A : Ty} â ð [ Î |> A , â£ A â£  ]
  Z {Î = Î} {A = A} = Prod.Ïâ (Î Ã A)

  Ï : â {Î : Obj} {A : Ty} â ð [ Î |> A , Î  ]
  Ï {Î = Î} {A = A} = Prod.Ïâ (Î Ã A)

  Î : â {Î : Obj} {A B : Ty} â ð [ Î |> A , â£ B â£ ] â ð [ Î , (A â£ââ£ B) ]
  Î {Î = Î} {A = A} {B = B} = Exp.Î»g (A â B) (Î Ã A)

  APP : â {Î : Obj} {A B : Ty} â ð [ Î , (A â£ââ£ B) ] â ð [ Î , â£ A â£ ] â ð [ Î , â£ B â£ ]
  APP {A = A} {B = B} f g = {!!} -- (Exp.eval (A â B)) â â¨ f , g â©
    where
      coe : ð [ â£ A â£ |> B ,  Exp.B^AÃA (A â B)]
      coe = {!!}
      eval : ð [ Exp.B^AÃA (A â B) , â£ B â£ ] 
      eval = Exp.eval (A â B)
