{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base

module category.instances.product where

module _ {ℓCo ℓCm ℓDo ℓDm : Level} (C : PreCategory ℓCo ℓCm) (D : PreCategory ℓDo ℓDm) where
  private
    module C = PreCategory C
    module D = PreCategory D
    ℓo = ℓ-max ℓCo ℓDo
    ℓm = ℓ-max ℓCm ℓDm

  ProductCat : PreCategory ℓo ℓm
  ProductCat = record
    { Obj = ProductObj
    ; Mor = ProductMor
    ; id = C.id , D.id
    ; _⋆_ = \ (cf , df)  (cg , dg) -> cf ⋆⟨ C ⟩ cg , df ⋆⟨ D ⟩ dg
    ; ⋆-left-id = \ (f , g) i -> C.⋆-left-id f i , D.⋆-left-id g i
    ; ⋆-right-id = \ (f , g) i -> C.⋆-right-id f i , D.⋆-right-id g i
    ; ⋆-assoc = \ (cf , df) (cg , dg) (ch , dh) i -> C.⋆-assoc cf cg ch i , D.⋆-assoc df dg dh i
    }
    where
    ProductObj : Type ℓo
    ProductObj = C.Obj × D.Obj

    ProductMor : (s t : ProductObj) -> Type ℓm
    ProductMor (s-c , s-d) (t-c , t-d) = C [ s-c , t-c ] × D [ s-d , t-d ]

module _ {ℓC1o ℓC1m ℓD1o ℓD1m ℓC2o ℓC2m ℓD2o ℓD2m : Level}
         {C1 : PreCategory ℓC1o ℓC1m} {D1 : PreCategory ℓD1o ℓD1m}
         {C2 : PreCategory ℓC2o ℓC2m} {D2 : PreCategory ℓD2o ℓD2m}
         (F : Functor C1 D1) (G : Functor C2 D2) where
  private
    module F = Functor F
    module G = Functor G

  product-functor : Functor (ProductCat C1 C2) (ProductCat D1 D2)
  product-functor .F-obj (c1 , c2) = (F.obj c1 , G.obj c2)
  product-functor .F-mor (f1 , f2) = (F.mor f1 , G.mor f2)
  product-functor .F-id (c1 , c2) i =  F.id c1 i , G.id c2 i
  product-functor .F-⋆ (f1 , f2) (g1 , g2) i =  F.⋆ f1 g1 i , G.⋆ f2 g2 i
