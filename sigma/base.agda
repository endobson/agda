{-# OPTIONS --cubical --safe --exact-split #-}

module sigma.base where

open import base
open import hlevel.base
open import equality

private
  variable
    ℓ : Level
    A : Type ℓ
    B : A -> Type ℓ

module _ where
  private
    module a where
      abstract
        snd-path : (x y : Σ A B)
                   -> ({a : A} -> isProp (B a))
                   -> (p : (x .fst) == (y .fst))
                   -> PathP (\i -> B (p i)) (x .snd) (y .snd)
        snd-path x y h p = isProp->PathP (\i -> h {(p i)})

        snd-path-refl : {ℓA ℓB : Level} {A : Type ℓA} {B : A -> Type ℓB} (x : Σ A B)
                        -> (h : {a : A} -> isProp (B a)  )
                        -> snd-path x x h refl == refl
        snd-path-refl x h = isOfHLevelPath 1 h _ _ _ _

  ΣProp-path : ∀ {x y : Σ A B}
               -> ({a : A} -> isProp (B a))
               -> (x .fst) == (y .fst)
               -> x == y
  ΣProp-path h p i .fst = p i
  ΣProp-path {x = x} {y = y} h p i .snd = a.snd-path x y h p i

  ΣProp-path-refl : {ℓB : Level} {B : A -> Type ℓB} {x : Σ A B}
                    -> (h : {a : A} -> isProp (B a))
                    -> ΣProp-path h (refl {x = x .fst}) == (refl {x = x})
  ΣProp-path-refl {x = x} h i j .fst = x .fst
  ΣProp-path-refl {x = x} h i j .snd = a.snd-path-refl x h i j


×-map : {ℓA ℓB ℓC ℓD : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} {D : Type ℓD}
        -> (A -> C) -> (B -> D) -> (A × B) -> (C × D)
×-map f g (a , b) = (f a , g b)


¬exists->forall : ¬ (Σ[ a ∈ A ] (B a)) -> (a : A) -> ¬ (B a)
¬exists->forall ne a b = ne (a , b)
