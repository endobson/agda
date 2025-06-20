{-# OPTIONS --cubical --safe --exact-split #-}

module lcm where

open import base
open import equality
open import gcd.propositional
open import nat
open import hlevel.base
open import prime
open import relatively-prime
open import semiring
open import nat.division
open import semiring.division
open import truncation
open import semiring.instances.nat

record LCM' (a : Nat) (b : Nat) (m : Nat) : Type₀ where
  field
    a%m : a div m
    b%m : b div m
    f : (x : Nat) -> (a div x) -> (b div x) -> (m div x)

  m-pos : (Pos' a) -> (Pos' b) -> Pos' m
  m-pos a-pos b-pos = div-pos->pos (f (a *' b) a%ab b%ab) (*'-Pos'-Pos' a-pos b-pos)
    where
    a%ab : a div (a *' b)
    a%ab = ∣ b , *-commuteᵉ b a ∣
    b%ab : b div (a *' b)
    b%ab = ∣ a , refl ∣

  a%'m : (p : Pos' m) -> a div' m
  a%'m p = unsquash (isPropDiv'-ℕ₂ p) a%m
  b%'m : (p : Pos' m) -> b div' m
  b%'m p = unsquash (isPropDiv'-ℕ₂ p) b%m


  rp-ar-br : (p : Pos' m) -> RelativelyPrime⁰ ⟨ a%'m p ⟩ ⟨ b%'m p ⟩
  rp-ar-br pm = no-shared-primes ar br g'
    where
    ar = ⟨ a%'m pm ⟩
    br = ⟨ b%'m pm ⟩
    g : (p : Prime') -> ⟨ p ⟩ div' ar -> ⟨ p ⟩ div' br -> Bot
    g p@(p' , _) (ar' , ar'-path) (br' , br'-path) =
      Prime'.!=1 p (*'-right-injective (m , pm)
                      (cong (p' *_) m=m2 >=> sym m-path >=> sym *-left-one))
      where
      m2 = ar' * a
      m-path : m == p' * m2
      m-path =
        sym (snd (a%'m pm)) >=>
        cong (_* a) (sym ar'-path >=> *'-commute {ar'} {p'}) >=>
        *'-assoc {p'} {ar'}
      a%m2 : a div m2
      a%m2 = ∣ ar' , refl ∣
      b%m2 : b div m2
      b%m2 = ∣ br' , *'-left-injective (Prime'.nat⁺ p) path ∣
        where
        path : p' * (br' * b) == p' * m2
        path =
          sym (*'-assoc {p'} {br'}) >=>
          cong (_* b) (*'-commute {p'} {br'} >=> br'-path) >=>
          snd (b%'m pm) >=>
          m-path
      m%m2 : m div m2
      m%m2 = f m2 a%m2 b%m2
      m2%m : m2 div m
      m2%m = ∣ p' , sym m-path ∣
      m=m2 = div-antisym m%m2 m2%m
    g' : (p : Prime') -> ⟨ p ⟩ div ar -> ⟨ p ⟩ div br -> Bot
    g' p p%ar p%br = unsquash isPropBot (∥-map2 (g p) p%ar p%br)

LCM⁺ : Nat⁺ -> Nat⁺ -> Nat⁺ -> Type₀
LCM⁺ (a , _) (b , _) (m , _) = LCM' a b m

lcm-unique : {a b m1 m2 : Nat} -> LCM' a b m1 -> LCM' a b m2 -> m1 == m2
lcm-unique {a} {b} {m1} {m2} lcm1 lcm2 = div-antisym m1%m2 m2%m1
  where
  module m1 = LCM' lcm1
  module m2 = LCM' lcm2

  m1%m2 : m1 div m2
  m1%m2 = m1.f m2 m2.a%m m2.b%m
  m2%m1 : m2 div m1
  m2%m1 = m2.f m1 m1.a%m m1.b%m

lcm-zero : {b : Nat} -> LCM' 0 b 0
lcm-zero {b} = record
  { a%m = div-zero
  ; b%m = div-zero
  ; f = (\ _ 0%x _ -> 0%x)
  }

lcm-sym : {a b m : Nat} -> LCM' a b m -> LCM' b a m
lcm-sym l = record
  { a%m = LCM'.b%m l
  ; b%m = LCM'.a%m l
  ; f = (\ x b% a% -> LCM'.f l x a% b%)
  }

lcm-idempotent : {a b m : Nat} -> LCM' a b m -> LCM' a m m
lcm-idempotent l = record
  { a%m = LCM'.a%m l
  ; b%m = div-refl
  ; f = \ x a%x m%x -> m%x
  }

lcm-absorbs-gcd : {a b d : Nat} -> GCD' a b d -> LCM' a d a
lcm-absorbs-gcd g = record
  { a%m = div-refl
  ; b%m = GCD'.%a g
  ; f = \ x a%x d%x -> a%x
  }

gcd-absorbs-lcm : {a b m : Nat} -> LCM' a b m -> GCD' a m a
gcd-absorbs-lcm l = record
  { %a = div-refl
  ; %b = LCM'.a%m l
  ; f = \x x%a x%m -> x%a
  }
