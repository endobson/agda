{-# OPTIONS --cubical --safe --exact-split #-}

module fraction.canonical where

open import additive-group
open import additive-group.instances.int
open import apartness.instances.int
open import base
open import div
open import equality-path
open import gcd.euclidean-algorithm
open import gcd.propositional
open import hlevel.base
open import int
open import int.base
open import int.order
open import int.sign
open import order
open import order.instances.int
open import order.minmax.instances.int
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.int
open import ordered-semiring
open import ordered-semiring.instances.int
open import rational
open import ring
open import ring.implementations.int
open import semidomain
open import semidomain.instances.int
open import semiring
open import truncation

private
  LowestTerms : ℚ' -> Type₀
  LowestTerms (ℚ'-cons n d _) = GCD n d 1#

record isCanonicalℚ' (q : ℚ') : Type₀ where
  field
    0<d : 0# < (ℚ'.denominator q)
    lowest-terms : LowestTerms q

isProp-isCanonicalℚ' : {q : ℚ'} -> isProp (isCanonicalℚ' q)
isProp-isCanonicalℚ' c₁ c₂ i = record
  { 0<d = isProp-< (isCanonicalℚ'.0<d c₁) (isCanonicalℚ'.0<d c₂) i
  ; lowest-terms = isProp-GCD (isCanonicalℚ'.lowest-terms c₁)
                              (isCanonicalℚ'.lowest-terms c₂) i
  }

private
  reduce-fraction : (q : ℚ') -> Σ[ r ∈ ℚ' ] (r r~ q × LowestTerms r)
  reduce-fraction q@(ℚ'-cons n d nz-d) = ans , sym q~ans , coprime
    where
    Σg = gcd-exists n d
    g : Int
    g = fst Σg
    module G = GCD (snd Σg)
    n' : Int
    n' = fst G.%a
    d' : Int
    d' = fst G.%b
    d'%d : d' div d
    d'%d = g , *-commute >=> snd G.%b
    nz-d' : NonZero d'
    nz-d' = div-non-zero->non-zero d'%d nz-d

    ans : ℚ'
    ans = ℚ'-cons n' d' nz-d'

    q~ans : q r~ ans
    q~ans =
      *-left (sym (snd G.%a)) >=>
      *-assoc >=>
      *-right (*-commute >=> snd G.%b)

    coprime : GCD n' d' 1#
    coprime .GCD.0≤d = 0≤1
    coprime .GCD.∣%a∣ = ∣ div-one ∣
    coprime .GCD.∣%b∣ = ∣ div-one ∣
    coprime .GCD.∣f∣ x (v1 , p1) (v2 , p2) = ∣ (v3 , p3') ∣
      where
      gx%g : (g * x) div g
      gx%g = GCD.f (snd Σg) (g * x)
        (v1 , *-right *-commute >=>
              sym *-assoc >=>
              *-left p1 >=>
              snd G.%a)
        (v2 , *-right *-commute >=>
              sym *-assoc >=>
              *-left p2 >=>
              snd G.%b)

      v3 : Int
      v3 = fst gx%g
      p3 : v3 * (g * x) == g
      p3 = snd gx%g
      p3' : v3 * x == 1#
      p3' = *₂-reflects-= (NonZero->!=0 (div-non-zero->non-zero G.%b nz-d))
              (*-assoc >=> *-right *-commute >=> p3 >=> sym *-left-one)


  normalize-denominator-sign : ℚ' -> ℚ'
  normalize-denominator-sign (ℚ'-cons n d (inj-l pd)) = ℚ'-cons n d (inj-l pd)
  normalize-denominator-sign (ℚ'-cons n d (inj-r nd)) = ℚ'-cons (- n) (- d) (inj-l (minus-flips-<0 nd))

  normalize-denominator-sign-r~ : (q : ℚ') -> (normalize-denominator-sign q) r~ q
  normalize-denominator-sign-r~ (ℚ'-cons n d (inj-l pd)) = refl
  normalize-denominator-sign-r~ (ℚ'-cons n d (inj-r nd)) =
    minus-extract-left >=> sym minus-extract-right

  normalize-denominator-sign-preserves-LowestTerms :
    (q : ℚ') -> LowestTerms q -> LowestTerms (normalize-denominator-sign q)
  normalize-denominator-sign-preserves-LowestTerms (ℚ'-cons n d (inj-l pd)) lt = lt
  normalize-denominator-sign-preserves-LowestTerms (ℚ'-cons n d (inj-r nd)) lt =
    gcd-sym (gcd-negate (gcd-sym (gcd-negate lt)))

  0<normalize-denominator-sign : (q : ℚ') -> 0# < (ℚ'.denominator (normalize-denominator-sign q))
  0<normalize-denominator-sign (ℚ'-cons n d (inj-l pd)) = pd
  0<normalize-denominator-sign (ℚ'-cons n d (inj-r nd)) = minus-flips-<0 nd

opaque
  ℚ'->canonical : (q : ℚ') -> Σ[ r ∈ ℚ' ] (r r~ q × isCanonicalℚ' r)
  ℚ'->canonical q =
    r2 ,
    (trans-r~ r2 r1 q (normalize-denominator-sign-r~ r1) (proj₁ (snd Σr1))) ,
    record
      { lowest-terms = normalize-denominator-sign-preserves-LowestTerms r1 (proj₂ (snd Σr1))
      ; 0<d = 0<normalize-denominator-sign r1
      }
    where
    Σr1 : Σ[ r ∈ ℚ' ] (r r~ q × LowestTerms r)
    Σr1 = reduce-fraction q
    r1 : ℚ'
    r1 = fst Σr1
    r2 : ℚ'
    r2 = normalize-denominator-sign r1

  ℚ'-r~-unique-canonical : (q r : ℚ') -> q r~ r -> isCanonicalℚ' q -> isCanonicalℚ' r -> q == r
  ℚ'-r~-unique-canonical (ℚ'-cons nq dq nz-dq) (ℚ'-cons nr dr nz-dr) q~r cq cr =
    \i -> ℚ'-cons (n-path i) (d-path i) (nz-path i)
    where
    module cq = isCanonicalℚ' cq

    dq%nq*dr : dq div (nq * dr)
    dq%nq*dr = nr , sym q~r
    dq%dr : dq div dr
    dq%dr = euclids-lemma dq%nq*dr (gcd-sym (isCanonicalℚ'.lowest-terms cq))
    dr%nr*dq : dr div (nr * dq)
    dr%nr*dq = nq , q~r
    dr%dq : dr div dq
    dr%dq = euclids-lemma dr%nr*dq (gcd-sym (isCanonicalℚ'.lowest-terms cr))

    d-path : dq == dr
    d-path =
      sym (abs-0≤-path (weaken-< (isCanonicalℚ'.0<d cq))) >=>
      div-same-abs dq%dr dr%dq >=>
      (abs-0≤-path (weaken-< (isCanonicalℚ'.0<d cr)))
    nz-path : PathP (\i -> NonZero (d-path i)) nz-dq nz-dr
    nz-path = isProp->PathP (\i -> isPropNonZero {d-path i})

    n-path : nq == nr
    n-path = *₂-reflects-= (\p -> irrefl-path-< (sym p) cq.0<d)
                           (*-right d-path >=> q~r)
