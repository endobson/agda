{-# OPTIONS --cubical --safe --exact-split #-}

module pigeonhole where

open import base
open import equality
open import fin
open import fin.functions
open import functions
open import nat
open import nat.order
open import order
open import order.instances.nat

module _ where
  private
    abstract
      smaller-fun : {n m : Nat} -> (f : Fin (suc n) -> Fin (suc m))
                    -> Injective f -> (Fin n -> Fin m)
      smaller-fun f inj-f x = remove-fin (f zero-fin) (f (suc-fin x)) (zero-fin!=suc-fin ∘ inj-f)

      smaller-fun-inj : {n m : Nat} -> (f : Fin (suc n) -> Fin (suc m))
                        -> (inj-f : Injective f) -> Injective (smaller-fun f inj-f)
      smaller-fun-inj f inj-f {x} {y} p =
        suc-fin-injective
          (inj-f
            (remove-fin-inj (f zero-fin) (f (suc-fin x)) (f (suc-fin y))
                            (zero-fin!=suc-fin ∘ inj-f) (zero-fin!=suc-fin ∘ inj-f)
                            p))

  pigeonhole-large : {n m : Nat} -> n > m -> (f : (Fin n) -> (Fin m)) -> ¬(Injective f)
  pigeonhole-large {n = zero}  gt f inj-f = zero-≮ gt
  pigeonhole-large {n = suc n} {m = zero}  gt f inj-f = bot-elim (¬fin-zero (f zero-fin))
  pigeonhole-large {n = suc n} {m = suc m} gt f inj-f =
    pigeonhole-large (pred-≤ gt) (smaller-fun f inj-f) (smaller-fun-inj f inj-f)


module _ where
  abstract
    pigeonhole-small : {n m : Nat} -> (n < m) -> (f : Fin n -> Fin m)
                       -> Σ[ j ∈ Fin m ] ((i : Fin n) -> ¬(f i == j))
    pigeonhole-small {n} {m} lt f =
        case (find-right-inverse f)
          return (\_ -> Σ[ j ∈ Fin m ] ((i : Fin n) -> ¬(f i == j))) of \where
          (inj-l sat) -> sat
          (inj-r (g , g-inv)) -> bot-elim (pigeonhole-large lt g (g-inj g-inv))
      where
      g-inj : {g : Fin m -> Fin n}
              -> (∀ j -> f (g j) == j)
              -> Injective g
      g-inj g-inv {j1} {j2} p = sym (g-inv j1) >=> cong f p >=> g-inv j2
