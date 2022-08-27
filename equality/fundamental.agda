{-# OPTIONS --cubical --safe --exact-split #-}

module equality.fundamental where

open import base
open import cubical
open import equivalence
open import functions
open import equality-path
open import hlevel
open import isomorphism
open import sigma
open import sigma.base

module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : A -> Type ℓB} {C : A -> Type ℓC} where
  isEquivFamily : (f : (a : A) -> B a -> C a) -> Type _
  isEquivFamily f = ∀ a -> isEquiv (f a)

  tot : (f : (a : A) -> B a -> C a) -> Σ A B -> Σ A C
  tot f (a , b) = a , f a b

  module _ (f : (a : A) -> B a -> C a) where

    private
      tot-fiber-eq : (ac : Σ A C) -> fiber (tot f) ac ≃ fiber (f (fst ac)) (snd ac)
      tot-fiber-eq = \ac -> isoToEquiv (iso (phi ac) (psi ac) (phi-psi ac) (psi-phi ac))
        where

        phi : (ac : Σ A C) -> fiber (tot f) ac -> fiber (f (fst ac)) (snd ac)
        phi (a , c) ((a2 , b) , p) = fib2
          where
          fib : fiber (f a2) (f a2 b)
          fib = b , refl
  
          fib2 : fiber (f a) c
          fib2 = transport (\i -> fiber (f (fst (p i))) (snd (p i))) fib
  
        psi : (ac : Σ A C) -> fiber (f (fst ac)) (snd ac) -> fiber (tot f) ac
        psi (a , c) (b , p) = (a , b) , (\i -> a , p i)
  
        phi-refl : (a : A) -> (b : B a) -> phi (a , f a b) ((a , b) , refl) == (b , refl)
        phi-refl a b = transportRefl (b , refl)
  
        psi-refl : (a : A) -> (b : B a) -> (psi (a , f a b) (b , refl)) == ((a , b) , refl)
        psi-refl a b = refl
  
        psi-phi-refl : (a : A) -> (b : B a) -> 
          (psi (a , f a b) (phi (a , f a b) ((a , b) , refl))) == ((a , b) , refl)
        psi-phi-refl a b = cong (psi (a , f a b)) (phi-refl a b) >=> psi-refl a b
  
        psi-phi-J : (a : A) -> (b : B a) -> {ac : Σ A C} -> (p : (a , f a b) == ac) ->
                    psi ac (phi ac ((a , b) , p)) == ((a , b) , p)
        psi-phi-J a b =
          J (\ ac p -> psi ac (phi ac ((a , b) , p)) == ((a , b) , p))
            (psi-phi-refl a b)
  
        psi-phi : (ac : Σ A C) (fib : fiber (tot f) ac) -> psi ac (phi ac fib) == fib
        psi-phi _ ((a , b) , p) = psi-phi-J a b p
  
  
        phi-psi : (ac : Σ A C) (fib : fiber (f (fst ac)) (snd ac)) -> phi ac (psi ac fib) == fib
        phi-psi (a , c) (b , p) = ans
          where
          trans1 : transport (\i -> fiber (f a) (p i)) (b , refl) == 
                   transport (\i -> fiber (f a) c) (b , p)
          trans1 j = transport (\i -> fiber (f a) (p (i ∨ j))) (b , (\i -> p (i ∧ j)))
  
          ans : transport (\i -> fiber (f a) (p i)) (b , refl) == (b , p)
          ans = trans1 >=> transportRefl (b , p)


    isEquivFamily-eq : isEquivFamily f ≃ isEquiv (tot f)
    isEquivFamily-eq =
      isoToEquiv (iso forward backward
                      (\_ -> isProp-isEquiv _ _)
                      (\_ -> isPropΠ (\_ -> isProp-isEquiv) _ _))
      where
      forward : isEquivFamily f -> isEquiv (tot f)
      forward eq-f = record { equiv-proof = fibC }
        where
        fibC : (ac : Σ A C) -> isContr (fiber (tot f) ac)
        fibC (a , c) = ≃-isContr (equiv⁻¹ (tot-fiber-eq (a , c))) (eq-f a .equiv-proof c)

      backward : isEquiv (tot f) -> isEquivFamily f
      backward eq-tf a = record { equiv-proof = fibC }
        where
        fibC : (c : C a) -> isContr (fiber (f a) c)
        fibC c = ≃-isContr (tot-fiber-eq (a , c)) (eq-tf .equiv-proof (a , c))




module _ {ℓA ℓB : Level} {A : Type ℓA} {B : A -> Type ℓB} {a : A}
  (f : (x : A) -> a == x -> B x)  where
  
  fundamental-id : isEquivFamily f ≃ isContr (Σ A B)
  fundamental-id = 
    isoToEquiv (iso forward backward 
                    (\_ -> isProp-isContr _ _) 
                    (\_ -> isPropΠ (\_ -> isProp-isEquiv) _ _))
    where
    forward : isEquivFamily f -> isContr (Σ A B)
    forward eq-f = ≃-isContr same (isContr-singleton a)
      where
      same : (Σ[ a2 ∈ A ] (a == a2)) ≃ Σ A B 
      same = existential-eq (\a2 -> f a2 , eq-f a2)

    backward : isContr (Σ A B) -> isEquivFamily f
    backward isC-AB = eqInv (isEquivFamily-eq f) isEq-tot-f
      where

      isEq-tot-f : isEquiv (tot f)
      isEq-tot-f .equiv-proof ab = 
        ((a , refl) , isContr->isProp isC-AB _ _) , 
        (\fib -> ΣProp-path (isProp->isSet (isContr->isProp isC-AB) _ _) 
                            (isContr->isProp (isContr-singleton a) _ _))
