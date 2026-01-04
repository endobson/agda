{-# OPTIONS --cubical --safe --exact-split #-}

module gcd.properties where

open import additive-group.instances.nat
open import base
open import chapter2.multiplicative
open import div
open import equality
open import gcd.propositional using (GCD' ; GCD⁺ ; gcd'-sym ; gcd'-zero ; gcd'-one)
open import gcd.computational
open import lcm
open import lcm.exists
open import nat
open import order.instances.nat
open import order.minmax
open import order.minmax.instances.nat
open import ordered-additive-group.instances.nat
open import ordered-additive-group.minmax
open import prime
open import prime-div-count
open import prime-div-count.computational
open import prime-gcd
open import relatively-prime
open import sigma.base
open import unique-prime-factorization

open EqReasoning

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
      dl-path >=> (sym min+max=sum) >=> (+'-commute {min na nb} {max na nb}) >=> sym dr-path
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
    ==< max-distrib-min >
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
    ==< min-distrib-max >
      max (min (ρ a) (ρ b)) (min (ρ a) (ρ c))
    ==< (\i -> (max (gcd-prime-div-count⁺ p a b (~ i)) (gcd-prime-div-count⁺ p a c (~ i)))) >
      max (ρ (gcd⁺ a b)) (ρ (gcd⁺ a c))
    ==< sym (lcm-prime-div-count⁺ p (gcd⁺ a b) (gcd⁺ a c)) >
      ρ (lcm⁺ (gcd⁺ a b) (gcd⁺ a c))
    end
    where
    ρ = prime-div-count p


gcd'-sym-path : (x y : Nat) -> gcd' x y == gcd' y x
gcd'-sym-path x y = gcd'-unique (gcd'-sym (gcd'-proof y x))

gcd⁺-sym-path : (x y : Nat⁺) -> gcd⁺ x y == gcd⁺ y x
gcd⁺-sym-path (x , _) (y , _) = ΣProp-path isPropPos' (gcd'-sym-path x y)

Multiplicative-gcd⁺₁ : (a : Nat⁺) -> Multiplicative (gcd⁺ a)
Multiplicative-gcd⁺₁ a .fst = gcd⁺-unique gcd'-one
Multiplicative-gcd⁺₁ a .snd x y rp = path3
  where
  a' = fst a
  x' = fst x
  y' = fst y

  d = gcd⁺ a (x *⁺ y)
  gd = gcd⁺-proof a (x *⁺ y)
  d' = fst d

  gcd-dxy : GCD⁺ d (x *⁺ y) d
  gcd-dxy = record
    { %a = div'-refl
    ; %b = (GCD'.%b (gcd⁺-proof a (x *⁺ y)))
    ; f = \z z%d _ -> z%d
    }

  dx = gcd⁺ d x
  gx = gcd⁺-proof d x
  dy = gcd⁺ d y
  gy = gcd⁺-proof d y
  dx' = ⟨ dx ⟩
  dy' = ⟨ dy ⟩

  gcd-ax : GCD⁺ a x dx
  gcd-ax = record
    { %a = div'-trans (GCD'.%a gx) (GCD'.%a gd)
    ; %b = (GCD'.%b gx)
    ; f = \z z%a z%x -> (GCD'.f gx z (GCD'.f gd z z%a (div'-mult' z%x y')) z%x)
    }
  gcd-ay : GCD⁺ a y dy
  gcd-ay = record
    { %a = div'-trans (GCD'.%a gy) (GCD'.%a gd)
    ; %b = (GCD'.%b gy)
    ; f = \z z%a z%y -> (GCD'.f gy z (GCD'.f gd z z%a (div'-mult z%y x')) z%y)
    }

  rp2 : RelativelyPrime⁺ dx dy
  rp2 z z%dx z%dy = rp z (div'-trans z%dx (GCD'.%b gx)) (div'-trans z%dy (GCD'.%b gy))

  path1 : (gcd' d' x' *' gcd' d' y') == d'
  path1 = prime-same-division-count (dx *⁺ dy) d f
    where
    f : (p : Prime') -> {n1 n2 : Nat}
        -> PrimeDivCount⁺ p (dx *⁺ dy) n1 -> PrimeDivCount⁺ p d n2
        -> n1 == n2
    f p {n1} {n2} dc1 dc2 =
      begin
        n1
      ==< prime-div-count-unique dc1 (prime-div-count-proof p (dx *⁺ dy)) >
         ρ (dx *⁺ dy)
      ==< cong ρ (sym (relatively-prime-lcm-path⁺ {dx} {dy} rp2)) >
        ρ (lcm⁺ dx dy)
      ==<>
        ρ (lcm⁺ (gcd⁺ d x) (gcd⁺ d y))
      ==< cong ρ (sym (gcd-distrib-lcm⁺ d x y)) >
        ρ (gcd⁺ d (lcm⁺ x y))
      ==< (\i -> (ρ (gcd⁺ d (relatively-prime-lcm-path⁺ {x} {y} rp i)))) >
        ρ (gcd⁺ d (x *⁺ y))
      ==< cong ρ (ΣProp-path isPropPos' (gcd'-unique gcd-dxy)) >
        ρ d
      ==< prime-div-count-unique (prime-div-count-proof p d) dc2 >
        n2
      end
      where
      ρ : Nat⁺ -> Nat
      ρ = prime-div-count p

  path2 : gcd' a' (x' *' y') == (gcd' a' x') *' (gcd' a' y')
  path2 = sym path1 >=> cong2 _*'_ (sym (gcd'-unique gcd-ax)) (sym (gcd'-unique gcd-ay))

  path3 : gcd⁺ a (x *⁺ y) == (gcd⁺ a x) *⁺ (gcd⁺ a y)
  path3 = ΣProp-path isPropPos' path2

Multiplicative-gcd⁺₂ : (a : Nat⁺) -> Multiplicative (\x -> gcd⁺ x a)
Multiplicative-gcd⁺₂ a .fst = gcd⁺-unique {b = a} (gcd'-sym gcd'-one)
Multiplicative-gcd⁺₂ a .snd x y rp =
  gcd⁺-sym-path (x *⁺ y) a >=> Multiplicative-gcd⁺₁ a .snd x y rp
  >=> cong2 _*⁺_ (gcd⁺-sym-path a x) (gcd⁺-sym-path a y)


Multiplicative-gcd'₁ : (a : Nat) -> Multiplicative⁰ (gcd' a)
Multiplicative-gcd'₁ _ .fst = gcd'-unique gcd'-one
Multiplicative-gcd'₁ zero  .snd   x y rp =
  p >=> (cong2 _*'_ (sym p) (sym p))
  where
  p : {n : Nat} -> gcd' 0 n == n
  p = gcd'-unique (gcd'-sym gcd'-zero)
Multiplicative-gcd'₁ a@(suc _) .snd zero y rp = sym (*'-right-one) >=> (\i -> (gcd' a 0) *' (p (~ i)))
  where
  y==1 : y == 1
  y==1 = rp-zero rp
  p : gcd' a y == 1
  p = gcd'-unique (transport (\i -> GCD' a (y==1 (~ i)) 1) gcd'-one)
Multiplicative-gcd'₁ a@(suc _) .snd x@(suc _) zero rp =
  (cong (\i -> gcd' a i) (*'-right-zero {x}))
  >=> sym (*'-left-one)
  >=> (\i -> (p (~ i)) *' (gcd' a 0))
  where
  x==1 : x == 1
  x==1 = rp-zero (rp-sym rp)
  p : gcd' a x == 1
  p = gcd'-unique (transport (\i -> GCD' a (x==1 (~ i)) 1) gcd'-one)
Multiplicative-gcd'₁ a@(suc _) .snd x@(suc _) y@(suc _) rp =
  cong fst (Multiplicative-gcd⁺₁ (a , tt) .snd (x , tt) (y , tt) rp)

Multiplicative-gcd'₂ : (a : Nat) -> Multiplicative⁰ (\x -> gcd' x a)
Multiplicative-gcd'₂ a .fst = gcd'-unique (gcd'-sym gcd'-one)
Multiplicative-gcd'₂ a .snd x y rp =
  gcd'-sym-path (x *' y) a >=> Multiplicative-gcd'₁ a .snd x y rp
  >=> cong2 _*'_ (gcd'-sym-path a x) (gcd'-sym-path a y)
