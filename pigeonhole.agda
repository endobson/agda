{-# OPTIONS --cubical --safe --exact-split #-}

module pigeonhole where

open import base
open import equality
open import fin
open import functions
open import nat
open import relation
open import sigma

module _ where
  private
    abstract
      shrink' : {n : Nat} -> (i : Nat) -> i < (suc n) -> (j : Nat) -> j < (suc n)
                -> i != j -> Fin n
      shrink'               zero    i-lt zero    j-lt np = bot-elim (np refl)
      shrink'               (suc i) i-lt zero    j-lt np = zero , (trans-≤-< zero-≤ (pred-≤ i-lt))
      shrink'               zero    i-lt (suc j) j-lt np = j , pred-≤ j-lt
      shrink' {n = zero}    (suc i) i-lt (suc j) j-lt np = bot-elim (zero-≮ (pred-≤ i-lt))
      shrink' {n = (suc n)} (suc i) i-lt (suc j) j-lt np =
        suc-fin (shrink' i (pred-≤ i-lt) j (pred-≤ j-lt) (np ∘ cong suc))

      shrink'-inj : {n : Nat}
                    -> (i : Nat) -> (i-lt : i < (suc n) )
                    -> (j1 : Nat) -> (j1-lt : j1 < (suc n)) -> (j1-np : i != j1)
                    -> (j2 : Nat) -> (j2-lt : j2 < (suc n)) -> (j2-np : i != j2)
                    -> shrink' i i-lt j1 j1-lt j1-np == shrink' i i-lt j2 j2-lt j2-np
                    -> j1 == j2
      shrink'-inj               zero    i-lt zero     j1-lt j1-np zero     j2-lt j2-np p =
        refl
      shrink'-inj               zero    i-lt zero     j1-lt j1-np (suc j2) j2-lt j2-np p =
        bot-elim (j1-np refl)
      shrink'-inj               zero    i-lt (suc j1) j1-lt j1-np zero     j2-lt j2-np p =
        bot-elim (j2-np refl)
      shrink'-inj               zero    i-lt (suc j1) j1-lt j1-np (suc j2) j2-lt j2-np p =
        cong (suc ∘ fst) p
      shrink'-inj {n = zero}    (suc i) i-lt j1       j1-lt j1-np j2       j2-lt j2-np p =
        bot-elim (zero-≮ (pred-≤ i-lt))
      shrink'-inj {n = (suc n)} (suc i) i-lt zero     j1-lt j1-np zero     j2-lt j2-np p =
        refl
      shrink'-inj {n = (suc n)} (suc i) i-lt zero     j1-lt j1-np (suc j2) j2-lt j2-np p =
        zero-suc-absurd (cong fst p)
      shrink'-inj {n = (suc n)} (suc i) i-lt (suc j1) j1-lt j1-np zero     j2-lt j2-np p =
        zero-suc-absurd (cong fst (sym p))
      shrink'-inj {n = (suc n)} (suc i) i-lt (suc j1) j1-lt j1-np (suc j2) j2-lt j2-np p =
        cong suc
          (shrink'-inj i (pred-≤ i-lt)
                       j1 (pred-≤ j1-lt) (j1-np ∘ cong suc)
                       j2 (pred-≤ j2-lt) (j2-np ∘ cong suc)
                       (suc-fin-injective p))

      shrink : {n : Nat} -> (i j : Fin (suc n)) -> i != j -> Fin n
      shrink (i , i-lt) (j , j-lt) np = shrink' i i-lt j j-lt (np ∘ ΣProp-path isProp≤)

      shrink-inj : {n : Nat} -> (i j1 j2 : Fin (suc n)) -> (j1-np : i != j1) -> (j2-np : i != j2)
                   -> shrink i j1 j1-np == shrink i j2 j2-np
                   -> j1 == j2
      shrink-inj (i , i-lt) (j1 , j1-lt) (j2 , j2-lt) j1-np j2-np p =
        ΣProp-path isProp≤
          (shrink'-inj i i-lt
                       j1 j1-lt (j1-np ∘ ΣProp-path isProp≤)
                       j2 j2-lt (j2-np ∘ ΣProp-path isProp≤)
                       p)

      smaller-fun : {n m : Nat} -> (f : Fin (suc n) -> Fin (suc m))
                    -> Injective f -> (Fin n -> Fin m)
      smaller-fun f inj-f x = shrink (f zero-fin) (f (suc-fin x)) (zero-fin!=suc-fin ∘ inj-f)

      smaller-fun-inj : {n m : Nat} -> (f : Fin (suc n) -> Fin (suc m))
                        -> (inj-f : Injective f) -> Injective (smaller-fun f inj-f)
      smaller-fun-inj f inj-f {x} {y} p =
        suc-fin-injective
          (inj-f
            (shrink-inj (f zero-fin) (f (suc-fin x)) (f (suc-fin y))
                        (zero-fin!=suc-fin ∘ inj-f) (zero-fin!=suc-fin ∘ inj-f)
                        p))

  pigeonhole-large : {n m : Nat} -> n > m -> (f : (Fin n) -> (Fin m)) -> ¬(Injective f)
  pigeonhole-large {n = zero}  gt f inj-f = zero-≮ gt
  pigeonhole-large {n = suc n} {m = zero}  gt f inj-f = bot-elim (¬fin-zero (f zero-fin))
  pigeonhole-large {n = suc n} {m = suc m} gt f inj-f =
    pigeonhole-large (pred-≤ gt) (smaller-fun f inj-f) (smaller-fun-inj f inj-f)
