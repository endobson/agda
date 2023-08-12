{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel.retract where

open import base
open import hlevel.base
open import equality-path
open import cubical

private
  variable
    ℓ : Level
    A₁ A₂ : Type ℓ

abstract
  isContr-Retract : (f : A₁ -> A₂) (g : A₂ -> A₁) (h : ∀ a -> g (f a) == a) -> isContr A₂ -> isContr A₁
  isContr-Retract f g h (a2 , p) = (g a2 , \a1 -> cong g (p (f a1)) >=> h a1)

  isProp-Retract : (f : A₁ -> A₂) (g : A₂ -> A₁) (h : ∀ a -> g (f a) == a) -> isProp A₂ -> isProp A₁
  isProp-Retract f g h hl a1 a2 i =
    hcomp (\j -> \{ (i = i0) -> h a1 j
                  ; (i = i1) -> h a2 j
                  })
      (g (hl (f a1) (f a2) i))

  isSet-Retract : (f : A₁ -> A₂) (g : A₂ -> A₁) (h : ∀ a -> g (f a) == a) -> isSet A₂ -> isSet A₁
  isSet-Retract f g h hl x y p1 p2 i j =
    hcomp (\k -> \{ (i = i0) -> h (p1 j) k
                  ; (i = i1) -> h (p2 j) k
                  ; (j = i0) -> h x k
                  ; (j = i1) -> h y k
                  })
      (g (hl (f x) (f y) (cong f p1) (cong f p2) i j))

  isOfHLevel-Retract : (n : Nat)
    (f : A₁ -> A₂) (g : A₂ -> A₁)
    (h : (x : A₁) -> g (f x) ≡ x) ->
    isOfHLevel n A₂ -> isOfHLevel n A₁
  isOfHLevel-Retract 0 = isContr-Retract
  isOfHLevel-Retract 1 = isProp-Retract
  isOfHLevel-Retract (suc (suc n)) f g h hl x y =
    isOfHLevel-Retract (suc n) (cong f) g' h' (hl (f x) (f y))
    where
    g' : (f x == f y) -> x == y
    g' fp i =
      hcomp (\j -> \{ (i = i0) -> h x j
                    ; (i = i1) -> h y j
                    })
        (g (fp i))

    h' : (p : x == y) -> g' (cong f p) == p
    h' p i j =
      hcomp (\k -> \{ (i = i1) -> p j
                    ; (j = i0) -> h x (i ∨ k)
                    ; (j = i1) -> h y (i ∨ k)
                    })
        (h (p j) i)
