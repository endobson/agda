{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module category.zipper where

open import base
open import equality hiding (begin_ ; _end)
open import category.base
open import relation


module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) where
  data CPathˡ (a : Obj C) : Obj C -> Type (ℓ-max ℓO ℓM) where
    [] : CPathˡ a a
    _::_ : {b c : Obj C} -> CPathˡ a b -> C [ b , c ] -> CPathˡ a c

  data CPathʳ' (a : Obj C) : Obj C -> Type (ℓ-max ℓO ℓM) where
    [] : CPathʳ' a a
    _::_ : {b c : Obj C} -> C [ b , c ] -> CPathʳ' a c -> CPathʳ' a b

  CPathʳ : Rel (Obj C) (ℓ-max ℓO ℓM)
  CPathʳ a b = CPathʳ' b a

  record Zipper (a b : Obj C) : Type (ℓ-max ℓO ℓM) where
    constructor zipper
    field
      { a' } : Obj C
      { b' } : Obj C
      left : CPathˡ a a'
      center : C [ a' , b' ]
      right : CPathʳ b' b

module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} where
  private
    module C = PreCategory C
  open PreCategory C using (_⋆_)

  data ZipperRule {a b : Obj C} : Zipper C a b -> Zipper C a b -> Type (ℓ-max ℓO ℓM) where
    left⇒ : {a' c b' : Obj C} 
            {l : CPathˡ C a a'} {m1 : C [ a' , c ]} {m2 : C [ c , b' ]} {r : CPathʳ C b' b} -> 
            ZipperRule (zipper (l :: m1) m2 r) (zipper l (m1 ⋆ m2) r)
    left⇐ : {a' c b' : Obj C} 
            {l : CPathˡ C a a'} {m1 : C [ a' , c ]} {m2 : C [ c , b' ]} {r : CPathʳ C b' b} -> 
            ZipperRule (zipper l (m1 ⋆ m2) r) (zipper (l :: m1) m2 r) 
    right⇒ : {a' c b' : Obj C} 
             {l : CPathˡ C a a'} {m1 : C [ a' , c ]} {m2 : C [ c , b' ]} {r : CPathʳ C b' b} -> 
             ZipperRule (zipper l (m1 ⋆ m2) r) (zipper l m1 (m2 :: r))
    right⇐ : {a' c b' : Obj C} 
             {l : CPathˡ C a a'} {m1 : C [ a' , c ]} {m2 : C [ c , b' ]} {r : CPathʳ C b' b} -> 
             ZipperRule (zipper l m1 (m2 :: r)) (zipper l (m1 ⋆ m2) r) 
    _>z>_ : {z1 z2 z3 : Zipper C a b} -> ZipperRule z1 z2 -> ZipperRule z2 z3 ->
            ZipperRule z1 z3
    z-cong : {a' b' : Obj C} 
             {l : CPathˡ C a a'} {m1 : C [ a' , b' ]} {m2 : C [ a' , b' ]} {r : CPathʳ C b' b} -> 
             m1 == m2 ->
             ZipperRule (zipper l m1 r) (zipper l m2 r)

  shift⇐ : {a a' c1 c2 b' b : Obj C} 
           {l : CPathˡ C a a'} {m1 : C [ a' , c1 ]} {m2 : C [ c1 , c2 ]} {m3 : C [ c2 , b' ]} 
           {r : CPathʳ C b' b} -> 
           ZipperRule (zipper l (m1 ⋆ m2) (m3 :: r)) (zipper (l :: m1) (m2 ⋆ m3) r)
  shift⇐ = left⇐ >z> right⇐

  shift⇒ : {a a' c1 c2 b' b : Obj C} 
           {l : CPathˡ C a a'} {m1 : C [ a' , c1 ]} {m2 : C [ c1 , c2 ]} {m3 : C [ c2 , b' ]} 
           {r : CPathʳ C b' b} -> 
           ZipperRule  (zipper (l :: m1) (m2 ⋆ m3) r) (zipper l (m1 ⋆ m2) (m3 :: r))
  shift⇒ = right⇒ >z> left⇒



  infixl 20 _>z>_

  cpathˡ->mor : {a b : Obj C} -> CPathˡ C a b -> C [ a , b ]
  cpathˡ->mor [] = id C
  cpathˡ->mor (p :: f) = cpathˡ->mor p ⋆ f

  cpathʳ->mor : {a b : Obj C} -> CPathʳ C a b -> C [ a , b ]
  cpathʳ->mor [] = id C
  cpathʳ->mor (f :: p) = f ⋆ cpathʳ->mor p

  zipper->mor : {a b : Obj C} -> Zipper C a b -> C [ a , b ]
  zipper->mor (zipper l m r) = cpathˡ->mor l ⋆ m ⋆ cpathʳ->mor r

  zrule->path : {a b : Obj C} (z1 z2 : Zipper C a b) -> 
                ZipperRule z1 z2 -> zipper->mor z1 == zipper->mor z2
  zrule->path (zipper l m1 r) (zipper l m2 r) (z-cong p) = 
    (\i -> cpathˡ->mor l ⋆ p i ⋆ cpathʳ->mor r)
  zrule->path (zipper l1 m1 r1) (zipper l2 m2 r2) (p1 >z> p2) =
    zrule->path _ _ p1 >=> zrule->path _ _ p2
  zrule->path (zipper (l1 :: m1) m2 r1) (zipper l2 m3 r2) left⇒ =
    C.⋆-left C.⋆-assocⁱ
  zrule->path (zipper l1 m1 r1) (zipper l2 m2 r2) left⇐ =
    C.⋆-left (sym C.⋆-assocⁱ)
  zrule->path (zipper l1 m1 r1) (zipper l2 m2 r2) right⇐ =
    C.⋆-assocⁱ >=> C.⋆-right (sym C.⋆-assocⁱ) >=> sym C.⋆-assocⁱ
  zrule->path (zipper l1 m1 r1) (zipper l2 m2 r2) right⇒ =
    C.⋆-assocⁱ >=> C.⋆-right C.⋆-assocⁱ >=> sym C.⋆-assocⁱ

module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) where
  private
    module C = PreCategory C

  zrule : {a b : Obj C} -> {m1 m2 : C [ a , b ]} ->
          ZipperRule {C = C} (zipper [] m1 []) (zipper [] m2 []) -> m1 == m2
  zrule r = 
    sym (C.⋆-left-id _) >=> sym (C.⋆-right-id _) >=> 
    zrule->path _ _ r >=> 
    C.⋆-right-id _ >=> C.⋆-left-id _


module ZReasoning {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) where

  infix  1 begin_
  infixr 2 [_,_,_]=<_>_
  infix  3 [_,_,_]end

  begin_ : {a b : Obj C} -> {m1 m2 : C [ a , b ]} ->
           ZipperRule {C = C} (zipper [] m1 []) (zipper [] m2 []) -> m1 == m2
  begin_ = zrule C

  [_,_,_]=<_>_ : {a a' b' b : Obj C} (l : CPathˡ C a a') (m : C [ a' , b' ]) (r : CPathʳ C b' b) ->
                 {z2 z3 : Zipper C a b} -> ZipperRule (zipper l m r) z2 -> ZipperRule z2 z3 ->
                 ZipperRule (zipper l m r) z3
  [ l , m , r ]=< p > p2 = p >z> p2


  [_,_,_]end : {a a' b' b : Obj C} (l : CPathˡ C a a') (m : C [ a' , b' ]) (r : CPathʳ C b' b) ->
               ZipperRule (zipper l m r) (zipper l m r)
  [ _ , _ , _ ]end = z-cong refl













