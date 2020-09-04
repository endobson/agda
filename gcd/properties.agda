{-# OPTIONS --cubical --safe --exact-split #-}

module gcd.properties where

open import base
open import div
open import equality
open import gcd.propositional using (GCD' ; GCD⁺)
open import gcd.computational
open import lcm
open import lcm.exists
open import nat
open import prime
open import prime-div-count
open import prime-div-count.computational
open import prime-gcd
open import relatively-prime
open import sigma
open import unique-prime-factorization


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
relatively-prime-gcd-path {a} {b} rp = gcd'-unique (relatively-prime->gcd rp)

relatively-prime-gcd-path⁺ : {a b : Nat⁺} -> RelativelyPrime⁺ a b -> gcd⁺ a b == 1⁺
relatively-prime-gcd-path⁺ rp = ΣProp-path isPropPos' (relatively-prime-gcd-path rp)

relatively-prime-lcm-path : {a b : Nat} -> RelativelyPrime⁰ a b -> lcm a b == a *' b
relatively-prime-lcm-path {a} {b} rp =
  sym *'-right-one
  >=> *'-right {lcm a b} (sym (relatively-prime-gcd-path rp))
  >=> sym (lcm-gcd-prod-path a b)

relatively-prime-lcm-path⁺ : {a b : Nat⁺} -> RelativelyPrime⁺ a b -> lcm⁺ a b == a *⁺ b
relatively-prime-lcm-path⁺ {a} {b} rp = ΣProp-path isPropPos' (relatively-prime-lcm-path rp)

lcm-distrib-gcd⁺ : (a b c : Nat⁺) -> lcm⁺ a (gcd⁺ b c) == gcd⁺ (lcm⁺ a b) (lcm⁺ a c)
lcm-distrib-gcd⁺ a b c = prime-same-division-count⁺ x y f
  where
  x = (lcm⁺ a (gcd⁺ b c))
  y = gcd⁺ (lcm⁺ a b) (lcm⁺ a c)

  f : (p : Prime') -> prime-div-count p x == prime-div-count p y
  f p =
    begin
      ρ (lcm⁺ a (gcd⁺ b c))
    ==< lcm-prime-div-count⁺ p a (gcd⁺ b c) >
      max (ρ a) (ρ (gcd⁺ b c))
    ==< cong (max (ρ a)) (gcd-prime-div-count⁺ p b c) >
      max (ρ a) (min (ρ b) (ρ c))
    ==< max-distrib-min (ρ a) (ρ b) (ρ c) >
      min (max (ρ a) (ρ b)) (max (ρ a) (ρ c))
    ==< (\i -> (min (lcm-prime-div-count⁺ p a b (~ i)) (lcm-prime-div-count⁺ p a c (~ i)))) >
      min (ρ (lcm⁺ a b)) (ρ (lcm⁺ a c))
    ==< sym (gcd-prime-div-count⁺ p (lcm⁺ a b) (lcm⁺ a c)) >
      ρ (gcd⁺ (lcm⁺ a b) (lcm⁺ a c))
    end
    where
    ρ = prime-div-count p

gcd-distrib-lcm⁺ : (a b c : Nat⁺) -> gcd⁺ a (lcm⁺ b c) == lcm⁺ (gcd⁺ a b) (gcd⁺ a c)
gcd-distrib-lcm⁺ a b c = prime-same-division-count⁺ x y f
  where
  x = (gcd⁺ a (lcm⁺ b c))
  y = lcm⁺ (gcd⁺ a b) (gcd⁺ a c)

  f : (p : Prime') -> prime-div-count p x == prime-div-count p y
  f p =
    begin
      ρ (gcd⁺ a (lcm⁺ b c))
    ==< gcd-prime-div-count⁺ p a (lcm⁺ b c) >
      min (ρ a) (ρ (lcm⁺ b c))
    ==< cong (min (ρ a)) (lcm-prime-div-count⁺ p b c) >
      min (ρ a) (max (ρ b) (ρ c))
    ==< min-distrib-max (ρ a) (ρ b) (ρ c) >
      max (min (ρ a) (ρ b)) (min (ρ a) (ρ c))
    ==< (\i -> (max (gcd-prime-div-count⁺ p a b (~ i)) (gcd-prime-div-count⁺ p a c (~ i)))) >
      max (ρ (gcd⁺ a b)) (ρ (gcd⁺ a c))
    ==< sym (lcm-prime-div-count⁺ p (gcd⁺ a b) (gcd⁺ a c)) >
      ρ (lcm⁺ (gcd⁺ a b) (gcd⁺ a c))
    end
    where
    ρ = prime-div-count p
