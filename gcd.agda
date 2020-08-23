{-# OPTIONS --cubical --safe --exact-split #-}

module gcd where

open import abs
open import base
open import div
open import equality
open import int
open import gcd.propositional
open import gcd.eulers-algorithm
open import linear-combo
open import nat
open import relation

open gcd.propositional using (gcd ; GCD ; GCD' ; GCD⁺) public

gcd-add-linear : ∀ {a b d : Int} -> GCD a b d -> (k : Int) -> GCD a (k * a + b) d
gcd-add-linear {a} {b} {d} (gcd non-neg d-div-a d-div-b f) k =
  (gcd non-neg d-div-a (div-sum (div-mult d-div-a k) d-div-b) g)
  where
  g : (x : Int) -> x div a -> x div (k * a + b) -> x div d
  g x xa xkab = f x xa xb
    where
    proof : (k * a + b) + (- k * a) == b
    proof =
      begin
        (k * a + b) + (- k * a)
      ==< +-commute {k * a + b} >
        (- k * a) + (k * a + b)
      ==< sym (+-assoc { - k * a}) >
        (- k * a + k * a) + b
      ==< +-left (+-left (minus-extract-left {k})) >
        (- (k * a) + k * a) + b
      ==< +-left (+-commute { - (k * a) }) >
        (k * a + - (k * a)) + b
      ==< +-left (add-minus-zero {k * a}) >
        b
      end

    xb : x div b
    xb = transport
           (\i -> x div (proof i))
           (div-sum xkab (div-mult xa (- k)))

gcd'-zero->id : {b d : Nat} -> GCD' 0 b d -> b == d
gcd'-zero->id {b} g = div'-antisym (g.f b div'-zero div'-refl) g.%b
  where
  module g = GCD' g

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

euclids-lemma : {a b c : Int} -> a div (b * c) -> GCD a b (int 1) -> a div c
euclids-lemma {a} {b} {c} a%bc ab-gcd = handle (gcd->linear-combo ab-gcd)
  where
  handle : (LinearCombination a b (int 1)) -> a div c
  handle (linear-combo _ _ _ x y {pr}) = a%c
    where
    c==stuff : c == x * c * a + y * (b * c)
    c==stuff =
      begin
        c
      ==< sym (+-right-zero {c})  >
        (int 1) * c
      ==< *-left (sym pr) >
        (x * a + y * b) * c
      ==< *-distrib-+ {x * a}  >
        x * a * c + y * b * c
      ==< +-left (*-assoc {x}) >
        x * (a * c) + y * b * c
      ==< +-left (*-right {x} (*-commute {a} {c})) >
        x * (c * a) + y * b * c
      ==< sym (+-left (*-assoc {x})) >
        x * c * a + y * b * c
      ==< (+-right {x * c * a} (*-assoc {y})) >
        x * c * a + y * (b * c)
      end
    a%stuff : a div (x * c * a + y * (b * c))
    a%stuff = div-linear div-refl a%bc {x * c} {y}

    a%c : a div c
    a%c = (subst (\ x -> a div x) (sym c==stuff) a%stuff)

gcd'-exists : (m : Nat) -> (n : Nat) -> Σ[ d ∈ Nat ] (GCD' m n d)
gcd'-exists m n = handle (gcd-exists (int m) (int n))
  where
  handle : Σ[ d ∈ Int ] (GCD (int m) (int n) d) -> Σ[ d ∈ Nat ] (GCD' m n d)
  handle (d , g) = (abs' d , (gcd->gcd' g))

gcd' : Nat -> Nat -> Nat
gcd' a b = fst (gcd'-exists a b)

gcd'-proof : (a b : Nat) -> GCD' a b (gcd' a b)
gcd'-proof a b = snd (gcd'-exists a b)

gcd⁺ : Nat⁺ -> Nat⁺ -> Nat⁺
gcd⁺ (a , a-pos) (b , _) = gcd' a b , div'-pos->pos (GCD'.%a (gcd'-proof a b)) a-pos

gcd⁺-proof : (a b : Nat⁺) -> GCD⁺ a b (gcd⁺ a b)
gcd⁺-proof (a , _) (b , _) = gcd'-proof a b
