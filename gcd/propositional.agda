{-# OPTIONS --cubical --safe --exact-split #-}

module gcd.propositional where

open import abs
open import base
open import equality
open import div
open import int
open import nat


record GCD (a : Int) (b : Int) (d : Int) : Type₀ where
  constructor gcd
  field
    non-neg : (NonNeg d)
    %a : d div a
    %b : d div b
    f : (x : Int) -> x div a -> x div b -> x div d

record GCD' (a : Nat) (b : Nat) (d : Nat) : Type₀ where
  field
    %a : d div' a
    %b : d div' b
    f : (x : Nat) -> x div' a -> x div' b -> x div' d

GCD⁺ : Nat⁺ -> Nat⁺ -> Nat⁺ -> Type₀
GCD⁺ (a , _) (b , _) (d , _) = GCD' a b d


-- Common constructions for integer GCD

gcd-refl : {n : Int} -> GCD n n (abs n)
gcd-refl {n} = gcd tt (div-abs-left div-refl) (div-abs-left div-refl)
 (\ _ _ d -> (div-abs-right d))

gcd-zero : {a : Int} -> GCD a zero-int (abs a)
gcd-zero {a} =
  (gcd tt (div-abs-left div-refl) div-zero (\ x xa xz -> (div-abs-right xa)))

gcd-sym : {a b d : Int} -> GCD a b d -> GCD b a d
gcd-sym (gcd non-neg div-a div-b f) =
  (gcd non-neg div-b div-a (\ x xb xa -> f x xa xb))

gcd-negate : ∀ {a b d : Int} -> GCD a b d -> GCD a (- b) d
gcd-negate {a} {b} {d} (gcd non-neg d-div-a d-div-b f) =
  (gcd non-neg d-div-a (div-negate d-div-b) g)
  where
  g : (x : Int) -> x div a -> x div (- b) -> x div d
  g x xa xb = f x xa
    (transport (\i -> x div (minus-double-inverse {b} i)) (div-negate xb))

gcd-remove-abs : {a b d : Int} -> GCD a (abs b) d -> GCD a b d
gcd-remove-abs {b = (nonneg _)} g = g
gcd-remove-abs {b = (neg _)} g = gcd-negate g

gcd-unique : {m n d1 d2 : Int} -> GCD m n d1 -> GCD m n d2 -> d1 == d2
gcd-unique {d1 = d1} {d2 = d2}
           (gcd d1-nn d1-div-m d1-div-n d1-f)
           (gcd d2-nn d2-div-m d2-div-n d2-f) =
  non-neg-same-abs d1-nn d2-nn (div-same-abs d1-div-d2 d2-div-d1)
  where
  d1-div-d2 : d1 div d2
  d1-div-d2 = (d2-f d1 d1-div-m d1-div-n)
  d2-div-d1 : d2 div d1
  d2-div-d1 = (d1-f d2 d2-div-m d2-div-n)

-- Common constructions for natural GCD

gcd'-zero : {a : Nat} -> GCD' a 0 a
gcd'-zero = record
  { %a = div'-refl
  ; %b = div'-zero
  ; f = (\ x xa xz -> xa)
  }

gcd'-one : {a : Nat} -> GCD' a 1 1
gcd'-one = record
  { %a = div'-one
  ; %b = div'-refl
  ; f = (\ x xa x1 -> x1)
  }

gcd'-sym : {a b d : Nat} -> GCD' a b d -> GCD' b a d
gcd'-sym g = record
  { %a = g.%b
  ; %b = g.%a
  ; f = \ x xb xa -> g.f x xa xb
  }
  where
  module g = GCD' g

gcd'-unique : {m n d1 d2 : Nat} -> GCD' m n d1 -> GCD' m n d2 -> d1 == d2
gcd'-unique {m} {n} {d1} {d2} g1 g2 =
  div'-antisym (g2.f _ g1.%a g1.%b) (g1.f _ g2.%a g2.%b)
  where
  module g1 = GCD' g1
  module g2 = GCD' g2
