{-# OPTIONS --cubical --safe --exact-split #-}

module gcd.properties where

open import base
open import div
open import equality
open import gcd
open import lcm
open import lcm.exists
open import nat
open import prime
open import prime-div-count
open import prime-gcd
open import relatively-prime
open import sigma
open import unique-prime-factorization


gcd-prime-div-count⁺ : (p : Prime') (a b : Nat⁺)
  -> prime-div-count p (gcd⁺ a b) == min (prime-div-count p a) (prime-div-count p b)
gcd-prime-div-count⁺ p a b =
  prime-div-count-unique
    (prime-div-count-proof p (gcd⁺ a b))
    (gcd-prime-div-count (gcd⁺-proof a b) p (prime-div-count-proof p a) (prime-div-count-proof p b))


private
  lcm-gcd-prod-path'⁺ : {a b : Nat⁺} -> {m d : Nat}
                       -> LCM' ⟨ a ⟩ ⟨ b ⟩ m
                       -> GCD' ⟨ a ⟩ ⟨ b ⟩ d -> ⟨ a *⁺ b ⟩ == m *' d
  lcm-gcd-prod-path'⁺ {a@(a' , a-pos)} {b@(b' , b-pos)} {m} {d} l g =
    prime-same-division-count left right same-div-count
    where
    m⁺ : Nat⁺
    m⁺ = m , LCM'.m-pos l a-pos b-pos
    d⁺ : Nat⁺
    d⁺ = d , div'-pos->pos (GCD'.%a g) a-pos

    left = a *⁺ b
    right = m⁺ *⁺ d⁺

    same-div-count : (p : Prime') {dl dr : Nat}
                     -> PrimeDivCount p ⟨ left ⟩ dl
                     -> PrimeDivCount p ⟨ right ⟩ dr
                     -> dl == dr
    same-div-count p {dl} {dr} l-dc r-dc =
      dl-path >=> sum==min-max na nb >=> (+'-commute {min na nb} {max na nb}) >=> sym dr-path
      where
      Σa-dc : Σ[ n ∈ Nat ] (PrimeDivCount p a' n)
      Σa-dc = compute-prime-div-count p a
      Σb-dc : Σ[ n ∈ Nat ] (PrimeDivCount p b' n)
      Σb-dc = compute-prime-div-count p b
      na = fst Σa-dc
      nb = fst Σb-dc
      a-dc = snd Σa-dc
      b-dc = snd Σb-dc

      dl-path : dl == na +' nb
      dl-path = prime-div-count-unique l-dc (*'-prime-div-count a-dc b-dc)

      dr-path : dr == max na nb +' min na nb
      dr-path =
        prime-div-count-unique r-dc
         (*'-prime-div-count
           (lcm-prime-div-count l p a-dc b-dc)
           (gcd-prime-div-count g p a-dc b-dc))

  lcm-gcd-prod-path' : {a b m d : Nat} -> LCM' a b m -> GCD' a b d -> a *' b == m *' d
  lcm-gcd-prod-path' {n} {zero} {m} {d} l g =
    *'-right-zero {n} >=> *'-left {d} (sym (lcm-unique l (lcm-sym lcm-zero)))
  lcm-gcd-prod-path' {zero} {suc n} {m} {d} l g =
    *'-left {d} (sym (lcm-unique l lcm-zero))
  lcm-gcd-prod-path' {suc _} {suc _} {m} {d} l g = lcm-gcd-prod-path'⁺ l g

lcm-gcd-prod-path : (a b : Nat) -> a *' b == (lcm a b) *' (gcd' a b)
lcm-gcd-prod-path a b = lcm-gcd-prod-path' (lcm-proof a b) (gcd'-proof a b)

lcm-gcd-prod-path⁺ : (a b : Nat⁺) -> a *⁺ b == (lcm⁺ a b) *⁺ (gcd⁺ a b)
lcm-gcd-prod-path⁺ a b = ΣProp-path isPropPos' (lcm-gcd-prod-path' (lcm⁺-proof a b) (gcd⁺-proof a b))

relatively-prime-gcd-path : {a b : Nat} -> RelativelyPrime⁰ a b -> gcd' a b == 1
relatively-prime-gcd-path {a} {b} rp = gcd'-unique (gcd'-proof a b) (relatively-prime->gcd rp)

relatively-prime-gcd-path⁺ : {a b : Nat⁺} -> RelativelyPrime⁺ a b -> gcd⁺ a b == 1⁺
relatively-prime-gcd-path⁺ rp = ΣProp-path isPropPos' (relatively-prime-gcd-path rp)
