{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module type-algebra.sum where

open import base
open import cubical
open import equality-path
open import equivalence
open import functions
open import functions.embedding
open import functions.embedding.sum
open import hlevel.base
open import isomorphism
open import relation
open import sum
open import type-algebra

private
  module _ {ℓA ℓB ℓR : Level} {A : Type ℓA} {B : Type ℓB} {R : REL A B ℓR}
           (isContr-ΣAR : ∀ b -> isContr (Σ[ a ∈ A ] (R a b)))
           (isContr-ΣBR : ∀ a -> isContr (Σ[ b ∈ B ] (R a b))) where
    private
      f : A -> B
      f a = fst (fst (isContr-ΣBR a))
      g : B -> A
      g b = fst (fst (isContr-ΣAR b))

      fg : ∀ b -> f (g b) == b
      fg b = cong fst (snd (isContr-ΣBR (g b)) (b , r))
        where
        r : R (g b) b
        r = snd (fst (isContr-ΣAR b))

      gf : ∀ a -> g (f a) == a
      gf a = cong fst (snd (isContr-ΣAR (f a)) (a , r))
        where
        r : R a (f a)
        r = snd (fst (isContr-ΣBR a))

    isContrRel->eq : A ≃ B
    isContrRel->eq = isoToEquiv (iso f g fg gf)


module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (isProp-A : isProp A) (eq : (A ⊎ B) ≃ (A ⊎ C)) where

  private
    f : A ⊎ B -> A ⊎ C
    f = eqFun eq
    g : A ⊎ C -> A ⊎ B
    g = eqInv eq

    data R (b : B) (c : C) : Type (ℓ-max* 3 ℓA ℓB ℓC) where
      r-bc : f (inj-r b) == inj-r c -> R b c
      r-a : (a : A) -> f (inj-r b) == inj-l a -> g (inj-r c) == inj-l a -> R b c

    B->ΣCR : ∀ b -> Σ[ c ∈ C ] (R b c)
    B->ΣCR b = handle (f (inj-r b)) refl
      where
      handle : (x : A ⊎ C) -> f (inj-r b) == x -> Σ[ c ∈ C ] (R b c)
      handle (inj-r c) p = c , r-bc p
      handle (inj-l a) p = handle2 (f (inj-l a)) refl
        where
        handle2 : (x : A ⊎ C) -> f (inj-l a) == x -> Σ[ c ∈ C ] (R b c)
        handle2 (inj-r c) p2 = c , r-a a p p3
          where
          p3 : g (inj-r c) == (inj-l a)
          p3 = cong g (sym p2) >=> eqRet eq (inj-l a)
        handle2 (inj-l a2) p2 = bot-elim (inj-l!=inj-r p3)
          where
          p3 : inj-l a == inj-r b
          p3 = sym (eqRet eq (inj-l a)) >=>
               cong g (p2 >=> cong inj-l (isProp-A a2 a) >=> sym p) >=>
               eqRet eq (inj-r b)

    isProp-ΣCR : ∀ b -> isProp (Σ[ c ∈ C ] (R b c))
    isProp-ΣCR b (c1 , r-bc p1) (c2 , r-bc p2) =  \i -> p-c i , r-bc (pp' i)
      where
      p-Σac : Path (Σ[ ac ∈ A ⊎ C ] (f (inj-r b) == ac))
             (inj-r c1 , p1) (inj-r c2 , p2)
      p-Σac i =
        hcomp (\k -> \{ (i = i0) -> p1 k , \j -> p1 (k ∧ j)
                      ; (i = i1) -> p2 k , \j -> p2 (k ∧ j)
                      })
              (f (inj-r b) , refl)

      p-ac : inj-r c1 == inj-r c2
      p-ac i = fst (p-Σac i)
      p-c : c1 == c2
      p-c = isEqInv (isEmbedding-inj-r c1 c2) p-ac
      pp-ac : p-ac == cong inj-r p-c
      pp-ac = sym (isEqSec (isEmbedding-inj-r c1 c2) p-ac)

      pp : PathP (\i -> f (inj-r b) == (p-ac i)) p1 p2
      pp i = snd (p-Σac i)

      pp' : PathP (\i -> f (inj-r b) == (inj-r (p-c i))) p1 p2
      pp' = transport (\j -> PathP (\i -> f (inj-r b) == (pp-ac j i)) p1 p2) pp
    isProp-ΣCR b (c1 , r-a a1 p1 q1) (c2 , r-a a2 p2 q2) =
      \i -> fst (p-cq i) , r-a (a1=a2 i) (p-p i) (snd (p-cq i))
      where
      a1=a2 : a1 == a2
      a1=a2 = isProp-A a1 a2

      p-p : PathP (\i -> f (inj-r b) == inj-l (a1=a2 i)) p1 p2
      p-p = pp'
        where
        p-Σac : PathP (\i -> Σ[ ac ∈ A ⊎ C ] (f (inj-r b) == ac)) (inj-l a1 , p1) (inj-l a2 , p2)
        p-Σac i =
          hcomp (\k -> \{ (i = i0) -> p1 k , \j -> p1 (k ∧ j)
                        ; (i = i1) -> p2 k , \j -> p2 (k ∧ j)
                        })
                (f (inj-r b) , refl)

        p-ac : inj-l a1 == inj-l a2
        p-ac i = fst (p-Σac i)
        p-a : a1 == a2
        p-a = isEqInv (isEmbedding-inj-l a1 a2) p-ac
        pp-ac : p-ac == cong inj-l a1=a2
        pp-ac = sym (isEqSec (isEmbedding-inj-l a1 a2) p-ac) >=>
                cong (cong inj-l) (isProp->isSet isProp-A a1 a2 p-a a1=a2)

        pp : PathP (\i -> f (inj-r b) == (p-ac i)) p1 p2
        pp i = snd (p-Σac i)
        pp' : PathP (\i -> f (inj-r b) == (inj-l (a1=a2 i))) p1 p2
        pp' = transport (\j -> PathP (\i -> f (inj-r b) == (pp-ac j i)) p1 p2) pp


      p-cq : PathP (\i -> Σ[ c ∈ C ] (g (inj-r c) == inj-l (a1=a2 i)))
                    (c1 , q1) (c2 , q2)
      p-cq = isProp->PathP (\i -> eqFun isEmbedding-eq-hasPropFibers embed-gr (inj-l (a1=a2 i)))
        where
        embed-gr : isEmbedding (g ∘ inj-r)
        embed-gr = ∘-isEmbedding (isEquiv->isEmbedding (snd (equiv⁻¹ eq))) isEmbedding-inj-r
    isProp-ΣCR b (c1 , r-bc p1) (c2 , r-a a p2 p3) = bot-elim (inj-l!=inj-r (sym p2 >=> p1))
    isProp-ΣCR b (c1 , r-a a p1 p2) (c2 , r-bc p3) = bot-elim (inj-l!=inj-r (sym p1 >=> p3))


    C->ΣBR : ∀ c -> Σ[ b ∈ B ] (R b c)
    C->ΣBR c = handle (g (inj-r c)) refl
      where
      handle : (x : A ⊎ B) -> g (inj-r c) == x -> Σ[ b ∈ B ] (R b c)
      handle (inj-r b) p = b , r-bc (cong f (sym p) >=> eqSec eq (inj-r c))
      handle (inj-l a) p = handle2 (g (inj-l a)) refl
        where
        handle2 : (x : A ⊎ B) -> g (inj-l a) == x -> Σ[ b ∈ B ] (R b c)
        handle2 (inj-r b) p2 = b , r-a a p3 p
          where
          p3 : f (inj-r b) == (inj-l a)
          p3 = cong f (sym p2) >=> eqSec eq (inj-l a)
        handle2 (inj-l a2) p2 = bot-elim (inj-l!=inj-r p3)
          where
          p3 : inj-l a == inj-r c
          p3 = sym (eqSec eq (inj-l a)) >=>
               cong f (p2 >=> cong inj-l (isProp-A a2 a) >=> sym p) >=>
               eqSec eq (inj-r c)

    isProp-ΣBR : ∀ c -> isProp (Σ[ b ∈ B ] (R b c))
    isProp-ΣBR c (b1 , r-bc p1) (b2 , r-bc p2) = \i -> fst (p-fib i) , r-bc (snd (p-fib i))
      where
      p-fib : Path (fiber (f ∘ inj-r) (inj-r c)) (b1 , p1) (b2 , p2)
      p-fib = eqFun isEmbedding-eq-hasPropFibers embed-fr (inj-r c) _ _
        where
        embed-fr : isEmbedding (f ∘ inj-r)
        embed-fr = ∘-isEmbedding (isEquiv->isEmbedding (snd eq)) isEmbedding-inj-r

    isProp-ΣBR c (b1 , r-a a1 p1 q1) (b2 , r-a a2 p2 q2) =
      \i -> fst (p-fib i) , r-a (a1=a2 i) (snd (p-fib i)) (p-q i)
      where

      p-Σab : Path (Σ[ ab ∈ A ⊎ B ] (g (inj-r c) == ab)) (inj-l a1 , q1) (inj-l a2 , q2)
      p-Σab i =
        hcomp (\k -> \{ (i = i0) -> q1 k , \j -> q1 (j ∧ k)
                      ; (i = i1) -> q2 k , \j -> q2 (j ∧ k)
                      })
          (g (inj-r c) , refl)

      la1=la2 : inj-l a1 == inj-l a2
      la1=la2 i = fst (p-Σab i)

      a1=a2 : a1 == a2
      a1=a2 = isEqInv (isEmbedding-inj-l a1 a2) la1=la2

      p-la : cong inj-l a1=a2 == la1=la2
      p-la = isEqSec (isEmbedding-inj-l a1 a2) la1=la2

      p-q' : PathP (\i -> g (inj-r c) == la1=la2 i) q1 q2
      p-q' i = snd (p-Σab i)
      p-q : PathP (\i -> g (inj-r c) == inj-l (a1=a2 i)) q1 q2
      p-q = transport (\j -> PathP (\i -> g (inj-r c) == (p-la (~ j) i)) q1 q2) p-q'

      p-fib : PathP (\i -> fiber (f ∘ inj-r) (inj-l (a1=a2 i))) (b1 , p1) (b2 , p2)
      p-fib = isProp->PathP (\i -> (eqFun isEmbedding-eq-hasPropFibers embed-fr (inj-l (a1=a2 i))))
        where
        embed-fr : isEmbedding (f ∘ inj-r)
        embed-fr = ∘-isEmbedding (isEquiv->isEmbedding (snd eq)) isEmbedding-inj-r

    isProp-ΣBR c (b1 , r-bc p1) (b2 , r-a a p2 p3) = bot-elim (inj-l!=inj-r (sym p))
      where
      p : (inj-r b1) == (inj-l a)
      p = sym (eqRet eq (inj-r b1)) >=> cong g p1 >=> p3
    isProp-ΣBR c (b1 , r-a a p1 p2) (b2 , r-bc p3) = bot-elim (inj-l!=inj-r (sym p))
      where
      p : (inj-r b2) == (inj-l a)
      p = sym (eqRet eq (inj-r b2)) >=> cong g p3 >=> p2



  opaque
    ⊎-cancel-left-eq : (B ≃ C)
    ⊎-cancel-left-eq = isContrRel->eq (\c -> C->ΣBR c , isProp-ΣBR c _) (\b -> B->ΣCR b , isProp-ΣCR b _)

module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (isProp-C : isProp C) (eq : (A ⊎ C) ≃ (B ⊎ C)) where
  opaque
    ⊎-cancel-right-eq : (A ≃ B)
    ⊎-cancel-right-eq = ⊎-cancel-left-eq isProp-C (⊎-flip-eq >eq> eq >eq> ⊎-flip-eq)
