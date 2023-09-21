{-# OPTIONS --cubical --safe --exact-split #-}

module category.constructions.full where

open import base
open import category.base
open import category.displayed
open import category.univalent
open import equality.identity-system
open import hlevel
open import relation
open import sigma.base

module _ {ℓO ℓM ℓP : Level} (C : PreCategory ℓO ℓM) (P : Obj C -> Type ℓP) where

  FullCᴰ : PreCategoryᴰ C ℓP ℓ-zero
  FullCᴰ = record
    { Objᴰ = P
    ; Morᴰ = \_ _ _ -> Top
    ; idᴰ = tt
    ; _⋆ᴰ_ = \_ _ -> tt
    ; ⋆ᴰ-left-id = \_ -> refl
    ; ⋆ᴰ-right-id = \_ -> refl
    ; ⋆ᴰ-assoc = \_ _ _ -> refl
    ; isSet-Morᴰ = isProp->isSet isPropTop
    }

  FullC : PreCategory (ℓ-max ℓO ℓP) ℓM
  FullC = record
    { Obj = Σ (Obj C) P
    ; Mor = \(c1 , _) (c2 , _) -> C [ c1 , c2 ]
    ; id = C.id
    ; _⋆_ = C._⋆_
    ; ⋆-left-id = C.⋆-left-id
    ; ⋆-right-id = C.⋆-right-id
    ; ⋆-assoc = C.⋆-assoc
    ; isSet-Mor = C.isSet-Mor
    }
    where
    module C = PreCategory C

  FullC-functor : Functor FullC C
  FullC-functor = record
    { obj = \(c , p) -> c
    ; mor = \m -> m
    ; id = \m -> refl
    ; ⋆ = \_ _ -> refl
    }

module _ {ℓO ℓM ℓP : Level} {C : PreCategory ℓO ℓM} {P : Obj C -> Type ℓP}
         (univ : isUnivalent' C) (isProp-P : isPropValuedPred P) where

  private
    module univ = isIdentitySystem univ
    lowerIso : ∀ {x y} -> CatIso (FullC C P) x y -> CatIso C (fst x) (fst y)
    lowerIso (cat-iso f g sec ret) = (cat-iso f g sec ret)

    raiseIso : ∀ {x y} -> CatIso C (fst x) (fst y) -> CatIso (FullC C P) x y
    raiseIso (cat-iso f g sec ret) = (cat-iso f g sec ret)

  isUnivalent'-FullC : isUnivalent' (FullC C P)
  isUnivalent'-FullC = record
    { to-path = \i -> ΣProp-path (isProp-P _) (univ.to-path (lowerIso i))
    ; to-path-over = \i j -> raiseIso (univ.to-path-over (lowerIso i) j)
    }
