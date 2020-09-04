{-# OPTIONS --cubical --safe --exact-split #-}

module prime-gcd where

open import abs
open import base
open import div
open import equality
open import gcd.propositional
open import gcd.euclidean-algorithm
open import int
open import lcm
open import nat
open import prime
open import relation
open import relatively-prime

private
  RP = RelativelyPrime⁰

relatively-prime->gcd : {a b : Nat} -> RP a b -> GCD' a b 1
relatively-prime->gcd {a} {b} rp = record
  { %a = div'-one
  ; %b = div'-one
  ; f = f
  }
  where
  f : (x : Nat) -> x div' a -> x div' b -> x div' 1
  f x xa xb = transport (cong (x div'_) (rp x xa xb)) div'-refl

gcd->relatively-prime : {a b : Nat} -> GCD' a b 1 -> RP a b
gcd->relatively-prime g d da db = div'-antisym (GCD'.f g d da db) div'-one


euclids-lemma' : {a b c : Nat} -> a div' (b *' c) -> RP a b -> a div' c
euclids-lemma' {a} {b} {c} a%bc rp = result
  where
  int-a%bc : (int a) div (int b * int c)
  int-a%bc = transport (\i -> (int a) div ((int-inject-*' {b} {c} i))) (div'->div a%bc)
  result : a div' c
  result = (div->div' (euclids-lemma int-a%bc (gcd'->gcd/nat (relatively-prime->gcd rp))))

prime-divides-a-factor : (p : Prime') -> {a b : Nat}
                         -> ⟨ p ⟩ div' (a *' b) -> (⟨ p ⟩ div' a) ⊎ (⟨ p ⟩ div' b)
prime-divides-a-factor p@(p' , _) {a} {b} p-div with (decide-div p' a)
... | yes p%a = inj-l p%a
... | no ¬p%a = inj-r (euclids-lemma' p-div (prime->relatively-prime p ¬p%a))

relatively-prime-*' : {a b c : Nat} -> RP a b -> RP a c -> RP a (b *' c)
relatively-prime-*'     {b = zero}                 g _ = g
relatively-prime-*' {a} {b = b@(suc _)} {c = zero} _ g =
  transport (\i -> RP a (*'-commute {b} {zero} (~ i))) g
relatively-prime-*' {a@(suc _)} {b = b@(suc _)} {c = c@(suc _)} f-b f-c =
  no-shared-primes a (b *' c) f
  where
  ¬prime-div-one : (p : Prime') -> ¬(⟨ p ⟩ div' 1)
  ¬prime-div-one (_ , p) p%1 with ≤->≤i (div'->≤ p%1)
  ...                           | zero-≤i = 0-is-¬prime p
  ...                           | (suc-≤i zero-≤i) = 1-is-¬prime p

  f : (p : Prime') -> ⟨ p ⟩ div' a -> ⟨ p ⟩ div' (b *' c) -> Bot
  f p@(p' , _) p%a p%bc with (prime-divides-a-factor p {b} {c} p%bc)
  ... | inj-l p%b = Prime'.!=1 p (f-b p' p%a p%b)
  ... | inj-r p%c = Prime'.!=1 p (f-c p' p%a p%c)
relatively-prime-*' {zero} b@{suc _} c@{suc _} rp-b rp-c
  with (rp-zero rp-b) | (rp-zero rp-c)
...  | b==1            | c==1            = transport (\ i -> RP 0 (path i)) rp-b
  where
  path : b == b *' c
  path = b==1 >=> (\i -> (sym b==1 i) *' (sym c==1 i))

relatively-prime-^' : {a b : Nat} -> RP a b -> (k : Nat) -> RP a (b ^' k)
relatively-prime-^' {a} {b} g zero    = rp-one
relatively-prime-^'     {b} g (suc k) =
  relatively-prime-*' g (relatively-prime-^' g k)



lcm-relatively-prime : {a b m : Nat} -> Pos' m -> (l : LCM' a b m) -> RP ⟨ LCM'.a%m l ⟩ ⟨ LCM'.b%m l ⟩
lcm-relatively-prime {a} {b} {m} pos-m l = no-shared-primes c d f
  where
  c = fst (LCM'.a%m l)
  d = fst (LCM'.b%m l)
  c-path = snd (LCM'.a%m l)
  d-path = snd (LCM'.b%m l)

  c%m : c div' m
  c%m = a , *'-commute {a} {c} >=> c-path
  d%m : d div' m
  d%m = b , *'-commute {b} {d} >=> d-path


  f : (p : Prime') -> ⟨ p ⟩ div' c -> ⟨ p ⟩ div' d -> Bot
  f p p%c@(xc , xc-path) p%d@(xd , xd-path) = Prime'.!=1 p p'==1
    where
    p' = ⟨ p ⟩

    p%m : p' div' m
    p%m = div'-trans p%c c%m

    n = ⟨ p%m ⟩
    n-path : n *' p' == m
    n-path = snd p%m

    n%m : n div' m
    n%m = p' , *'-commute {p'} {n} >=> n-path



    a%n : a div' n
    a%n = xc , *'-right-injective (Prime'.nat⁺ p) path
      where
      path : (xc *' a) *' p' == n *' p'
      path =
        *'-commute {xc *' a} {p'}
        >=> sym (*'-assoc {p'} {xc})
        >=> *'-left (*'-commute {p'} {xc})
        >=> *'-left xc-path
        >=> c-path
        >=> sym n-path

    b%n : b div' n
    b%n = xd , *'-right-injective (Prime'.nat⁺ p) path
      where
      path : (xd *' b) *' p' == n *' p'
      path =
        *'-commute {xd *' b} {p'}
        >=> sym (*'-assoc {p'} {xd})
        >=> *'-left (*'-commute {p'} {xd})
        >=> *'-left xd-path
        >=> d-path
        >=> sym n-path


    m%n : m div' n
    m%n = LCM'.f l n a%n b%n

    n⁺ : Nat⁺
    n⁺ = n , div'-pos->pos n%m pos-m


    p'==1 : p' == 1
    p'==1 =
      *'-left-injective
        n⁺
        (n-path >=> div'-antisym m%n n%m >=> (sym *'-right-one))
