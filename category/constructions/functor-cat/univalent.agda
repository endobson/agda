{-# OPTIONS --cubical --safe --exact-split #-}

module category.constructions.functor-cat.univalent where

open import base
open import equality-path
open import category.base
open import category.functor
open import category.constructions.functor-cat
open import category.natural-transformation
open import category.univalent
open import equality.identity-system

module _
  {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
  {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD} where
  private
    FC = FunctorC C D

  open isIdentitySystem
  open CategoryHelpers D

  opaque
    isUnivalent-FunctorC : isUnivalent' D -> isUnivalent' (FunctorC C D)
    isUnivalent-FunctorC univ =
      record { to-path = base-path ; to-path-over = over-path }
      where
      module _ {f1 : Functor C D} {f2 : Functor C D}
               (ni : CatIso FC f1 f2) where

        obj-iso : (c : Obj C) -> CatIso D (F-obj f1 c) (F-obj f2 c)
        obj-iso c = record
          { mor = NT-obj (CatIso.mor ni) c
          ; inv = NT-obj (CatIso.inv ni) c
          ; sec = \i -> NT-obj (CatIso.sec ni i) c
          ; ret = \i -> NT-obj (CatIso.ret ni i) c
          }

        op : (c : Obj C) -> (F-obj f1 c) == (F-obj f2 c)
        op c = to-path univ (obj-iso c)

        mp : {c1 c2 : Obj C} (m : C [ c1 , c2 ]) ->
                    PathP (\i -> D [ op c1 i , op c2 i ]) (F-mor f1 m) (F-mor f2 m)
        mp {c1} {c2} m = transP-mid (sym reduce-left) inner-path reduce-right
          where
          p1 : PathP (\i -> CatIso D (F-obj f1 c1) (op c1 i)) (idCatIso D (F-obj f1 c1)) (obj-iso c1)
          p1 = to-path-over univ (obj-iso c1)
          p2 : PathP (\i -> CatIso D (F-obj f1 c2) (op c2 i)) (idCatIso D (F-obj f1 c2)) (obj-iso c2)
          p2 = to-path-over univ (obj-iso c2)

          p3 : PathP (\i -> D [ (op c1 i) , (F-obj f1 c1) ])
                     (NT-obj (id-NT f1) c1) (CatIso.inv (obj-iso c1))
          p3 i = CatIso.inv (p1 i)
          p4 : PathP (\i -> D [ (F-obj f1 c2) , (op c2 i) ])
                     (NT-obj (id-NT f1) c2) (CatIso.mor (obj-iso c2))
          p4 i = CatIso.mor (p2 i)

          inner-path :
            PathP (\i -> D [ op c1 i , op c2 i ])
              (id D ⋆ F-mor f1 m ⋆ id D)
              (CatIso.inv (obj-iso c1) ⋆ F-mor f1 m ⋆ CatIso.mor (obj-iso c2))
          inner-path i = p3 i ⋆ F-mor f1 m ⋆ p4 i
          reduce-right : (CatIso.inv (obj-iso c1) ⋆ F-mor f1 m ⋆ CatIso.mor (obj-iso c2)) == F-mor f2 m
          reduce-right =
            ⋆-left (NT-mor (CatIso.inv ni) m) >=>
            ⋆-assoc >=>
            ⋆-right (\i -> NT-obj (CatIso.sec ni i) c2) >=>
            ⋆-right-id
          reduce-left : (id D ⋆ F-mor f1 m ⋆ id D) == F-mor f1 m
          reduce-left = ⋆-right-id >=> ⋆-left-id

        base-path : f1 == f2
        base-path = functor-path op mp

        over-path : PathP (\i -> CatIso FC f1 (base-path i)) (idCatIso FC f1) ni
        over-path = cat-iso-pathp refl base-path (natural-transformation-pathp inner-path)
          where
          inner-path : (c : Obj C) ->
            PathP (\ i -> D [ F-obj f1 c , F-obj (base-path i) c ])
              (id D) (CatIso.mor (obj-iso c))
          inner-path c i = CatIso.mor (univ .to-path-over (obj-iso c) i)
