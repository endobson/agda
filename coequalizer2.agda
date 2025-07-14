{-# OPTIONS --cubical --safe --exact-split #-}

module coequalizer2 where

open import base
open import cubical renaming (glue to cubical-glue)
open import equality-path
open import equivalence
open import univalence


module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} (f g : B -> A) where

  data Coequalizer : Type (ℓ-max ℓA ℓB) where
    [_] : A -> Coequalizer
    glue : (b : B) -> [ f b ] == [ g b ]



module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {f g : B -> A} 
  (C : A -> Type ℓC) (D : (b : B) -> C (f b) ≃ C (g b)) (magic : Magic) where
  private
    P : Coequalizer f g -> Type ℓC
    P [ a ] = C a
    P (glue b i) = ua (D b) i

  data CoequalizerP : Type (ℓ-max* 3 ℓA ℓB ℓC) where
    coeqP : (a : A) -> (C a) -> CoequalizerP
    glue : (b : B) -> (c : C (f b)) -> coeqP (f b) c == coeqP (g b) (eqFun (D b) c)


  ΣP≃CoeqP : Σ (Coequalizer f g) P ≃ CoequalizerP
  ΣP≃CoeqP = magic
    where

    coeqP' : (a : A) -> C a -> Σ (Coequalizer f g) P
    coeqP' a c = [ a ] , c

    glue' : (b : B) -> (c : C (f b)) -> coeqP' (f b) c == coeqP' (g b) (eqFun (D b) c)
    glue' b c i = glue b i , ua-filler (D b) c i

    backward : CoequalizerP -> Σ (Coequalizer f g) P
    backward (coeqP a c) = coeqP' a c
    backward (glue b c i) = glue' b c i

    forward : Σ (Coequalizer f g) P -> CoequalizerP
    forward ([ a ] , c) = coeqP a c
    forward (glue b i , c) = 
      hcomp (\k -> (\{ (i = i0) -> coeqP (f b) (eqRet (D b) c k)
                     ; (i = i1) -> ((glue b (eqInv (D b) c)) >=> 
                                    (\j -> coeqP (g b) (eqSec (D b) c j))) k
                     }))
        (coeqP (f b) (eqInv (D b) (unglue (i ∨ ~ i) c)))



    forward' : (x : Σ (Coequalizer f g) P) -> 
               Σ[ cp ∈ CoequalizerP ] (backward cp == x)
    forward' ([ a ] , c) = coeqP a c , refl
    forward' (glue b i , c) = ans i c
      where
      ans : PathP (\i -> (c : ua (D b) i) -> Σ[ cp ∈ CoequalizerP ] (backward cp == (glue b i , c)))
                  (\c -> (coeqP (f b) c , refl))
                  (\c -> (coeqP (g b) c , refl))
      ans = magic

      base : CoequalizerP
      base = (coeqP (f b) (eqInv (D b) (unglue (i ∨ ~ i) c)))

      bbase : Σ (Coequalizer f g) P
      bbase = backward base

      check-bbase : bbase == coeqP' (f b) (eqInv (D b) (unglue (i ∨ ~ i) c))
      check-bbase = refl

      base-path : bbase == (glue b i , c)
      base-path = magic
      
      -- side₀ : Partial (~ i) Top
      -- side₀ (i = i0) = tt
      --   where
      --   check-base : base == (coeqP (f b) (eqInv (D b) (unglue (i ∨ ~ i) c)))
      --   check-base = ?

