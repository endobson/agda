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

-- Conversion between GCD and GCD'

gcd'->gcd/nat : {d n a : Nat} -> GCD' d n a -> GCD (int d) (int n) (int a)
gcd'->gcd/nat {d} {n} {a} g =
  (gcd tt (div'->div g.%a) (div'->div g.%b) f)
  where
  module g = GCD' g
  fix : {x : Int} -> {y : Nat} -> x div (int y) -> (abs' x) div' y
  fix {x} {y} x%y = (subst (\ z -> (abs' x) div' z) refl (div->div' x%y))
  f : (x : Int) -> x div (int d) -> x div (int n) -> x div (int a)
  f x@zero-int x%d x%n = div'->div (g.f zero (fix x%d) (fix x%n))
  f x@(pos x') x%d x%n = div'->div (g.f (suc x') (fix x%d) (fix x%n))
  f x@(neg x') x%d x%n = div-negate-left (div'->div (g.f (suc x') (fix x%d) (fix x%n)))

gcd'->gcd : {d n a : Int} -> {NonNeg a} -> GCD' (abs' d) (abs' n) (abs' a) -> GCD d n a
gcd'->gcd {zero-int} {zero-int} {zero-int} g = gcd'->gcd/nat g
gcd'->gcd {zero-int} {zero-int} {pos _} g = gcd'->gcd/nat g
gcd'->gcd {zero-int} {pos _} {zero-int} g = gcd'->gcd/nat g
gcd'->gcd {zero-int} {pos _} {pos _} g = gcd'->gcd/nat g
gcd'->gcd {zero-int} {neg _} {zero-int} g = (gcd-negate (gcd'->gcd/nat g))
gcd'->gcd {zero-int} {neg _} {pos _} g = (gcd-negate (gcd'->gcd/nat g))
gcd'->gcd {pos _} {zero-int} {zero-int} g = gcd'->gcd/nat g
gcd'->gcd {pos _} {zero-int} {pos _} g = gcd'->gcd/nat g
gcd'->gcd {pos _} {pos _} {zero-int} g = gcd'->gcd/nat g
gcd'->gcd {pos _} {pos _} {pos _} g = gcd'->gcd/nat g
gcd'->gcd {pos _} {neg _} {zero-int} g = (gcd-negate (gcd'->gcd/nat g))
gcd'->gcd {pos _} {neg _} {pos _} g = (gcd-negate (gcd'->gcd/nat g))
gcd'->gcd {neg _} {zero-int} {zero-int} g = (gcd-sym (gcd-negate (gcd-sym (gcd'->gcd/nat g))))
gcd'->gcd {neg _} {zero-int} {pos _} g = (gcd-sym (gcd-negate (gcd-sym (gcd'->gcd/nat g))))
gcd'->gcd {neg _} {pos _} {zero-int} g = (gcd-sym (gcd-negate (gcd-sym (gcd'->gcd/nat g))))
gcd'->gcd {neg _} {pos _} {pos _} g = (gcd-sym (gcd-negate (gcd-sym (gcd'->gcd/nat g))))
gcd'->gcd {neg _} {neg _} {zero-int} g = (gcd-negate ((gcd-sym (gcd-negate (gcd-sym (gcd'->gcd/nat g))))))
gcd'->gcd {neg _} {neg _} {pos _} g = (gcd-negate ((gcd-sym (gcd-negate (gcd-sym (gcd'->gcd/nat g))))))

gcd->gcd' : {d n a : Int} -> GCD d n a -> GCD' (abs' d) (abs' n) (abs' a)
gcd->gcd' {d} {n} {a} (gcd _ a%d a%n f) = record
  { %a = (div->div' a%d)
  ; %b = (div->div' a%n)
  ; f = f'
  }
  where
  f' : (x : Nat) -> x div' (abs' d) -> x div' (abs' n) -> x div' (abs' a)
  f' x x%d x%n = res
    where
    fix : {y : Int} -> x div' (abs' y) -> (int x) div y
    fix {nonneg _} x%y = (div'->div x%y)
    fix {neg _} x%y = (div-negate (div'->div x%y))
    res : x div' (abs' a)
    res = (div->div' (f (int x) (fix x%d) (fix x%n)))
