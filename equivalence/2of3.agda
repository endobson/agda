{-# OPTIONS --cubical --safe --exact-split #-}

module equivalence.2of3 where

open import base
open import cubical
open import functions
open import hlevel.base
open import hlevel.retract
open import equality-path
open import equivalence.base

module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         {f : B -> C} {g : A -> B} where

  isEquiv-2of3₁ : isEquiv g -> isEquiv (f ∘ g) -> isEquiv f
  isEquiv-2of3₁ eg efg .equiv-proof c = center , same
    where
    cg : ∀ b -> isContr (fiber g b)
    cg = equiv-proof eg
    cfg : ∀ c -> isContr (fiber (f ∘ g) c)
    cfg = equiv-proof efg

    reduce-fib : fiber (f ∘ g) c -> fiber f c
    reduce-fib (b , p) = g b , p

    center : (fiber f c)
    center = reduce-fib (fst (cfg c))

    same : ∀ fib -> center == fib
    same fib@(b , p) = path1 ∙∙ path2 ∙∙ path3
      where
      a' : A
      a' = fst (fst (cg b))
      ga=b : g a' == b
      ga=b = snd (fst (cg b))

      fib-fg : fiber (f ∘ g) c
      fib-fg = a' , cong f ga=b >=> p

      fib-f : fiber f c
      fib-f = reduce-fib fib-fg

      path2 : fib-f == (b , refl >=> p)
      path2 i = ga=b i , ((\j -> f (ga=b (i ∨ j))) >=> p)
      path3 : (b , refl >=> p) == (b , p)
      path3 i = b , compPath-refl-left p i

      path1 : center == fib-f
      path1 = cong reduce-fib (snd (cfg c) fib-fg)

  isEquiv-2of3₂ : isEquiv f -> isEquiv (f ∘ g) -> isEquiv g
  isEquiv-2of3₂ ef efg .equiv-proof b = 
    isContr-Retract change-fiber2 change-fiber change-fiber-twice (cfg (f b))
    where
    cf : ∀ c -> isContr (fiber f c)
    cf = equiv-proof ef
    cfg : ∀ c -> isContr (fiber (f ∘ g) c)
    cfg = equiv-proof efg

    change-fiber : fiber (f ∘ g) (f b) -> fiber g b
    change-fiber (a , p) = 
      a , cong fst (isContr->isProp (cf (f b)) fib₂ fib₁)
      where

      fib₁ : fiber f (f b)
      fib₁ = b , refl
      fib₂ : fiber f (f b)
      fib₂ = g a , p

    change-fiber2 : fiber g b -> fiber (f ∘ g) (f b)
    change-fiber2 (a , p) = a , cong f p

    change-fiber-twice : (fib : fiber g b) -> 
      change-fiber (change-fiber2 fib) == fib
    change-fiber-twice (a , p) i = (a , pp i)
      where
      pp : cong fst (isContr->isProp (cf (f b)) (g a , (cong f p)) (b , refl)) == p
      pp = cong (cong fst) full-path
        where
        manual : Path (fiber f (f b)) (g a , (cong f p)) (b , refl)
        manual i = p i , cong f (\j -> (p (i ∨ j)))

        full-path : (isContr->isProp (cf (f b)) (g a , (cong f p)) (b , refl)) == manual
        full-path = isProp->isSet (isContr->isProp (cf (f b))) _ _ _ _


  isEquiv-2of3₃ : isEquiv f -> isEquiv g -> isEquiv (f ∘ g)
  isEquiv-2of3₃ ef eg .equiv-proof c = 
    isContr-Retract step2 step1 step-twice (cf c)
    where
    cf : ∀ c -> isContr (fiber f c)
    cf = equiv-proof ef
    cfg : ∀ b -> isContr (fiber g b)
    cfg = equiv-proof eg

    step1 : fiber f c -> fiber (f ∘ g) c
    step1 (b , p) = fst center , cong f (snd center) >=> p
      where
      center : fiber g b
      center = fst (cfg b)

    step2 : fiber (f ∘ g) c -> fiber f c
    step2 (a , p) = g a , p

    step-twice : ∀ x -> step1 (step2 x) == x
    step-twice (a , p) = 
      (\i -> fst (center=fib i) , cong f (snd (center=fib i)) >=> p) >=>
      (\i -> a , compPath-refl-left p i)
      where
      fib : fiber g (g a)
      fib = a , refl
      center : fiber g (g a)
      center = fst (cfg (g a))

      center=fib : center == fib
      center=fib = snd (cfg (g a)) fib
