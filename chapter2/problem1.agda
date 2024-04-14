{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.problem1 where

open import additive-group
open import base
open import chapter2.prime-divisors
open import chapter2.totient
open import chapter2.totient-rational
open import div
open import equality
open import equivalence
open import finite-commutative-monoid
open import finite-commutative-monoid.small
open import finite-commutative-monoid.without-point
open import finite-product
open import finite-product.arithmetic
open import finset
open import finset.without-point
open import functions
open import relation
open import hlevel
open import int
open import isomorphism
open import nat
open import nat.order
open import order
open import ordered-additive-group
open import ordered-semiring
open import ordered-semiring.instances.nat
open import ordered-additive-group.absolute-value
open import order.minmax.instances.rational
open import order.instances.nat
open import order.instances.rational
open import prime
open import rational
open import rational.order
open import rational-prime
open import ring
open import ring.implementations.rational
open import semiring
open import semiring.instances.nat
open import sigma.base
open import without-point


problem1-a : (n : Nat⁺) -> (φ (2⁺ *⁺ n) == ⟨ n ⟩) ≃ (Σ[ i ∈ ℕ ] (2⁺ ^⁺ i == n))
problem1-a n⁺@(n , pos-n) = isoToEquiv (isProp->iso forward backward (isSetNat _ _) isProp-Σ2^i)
  where
  d2 : (PrimeDivisor 2⁺)
  d2 = ((2 , 2-is-prime) , div'-refl)

  isContr-PrimeDivisor2 : isContr (PrimeDivisor 2⁺)
  isContr-PrimeDivisor2 = d2 , f
    where
    f : (d : PrimeDivisor 2⁺) -> d2 == d
    f ((d , d-is-prime) , d∣2) = ΣProp-path (isPropDiv' 2⁺) (ΣProp-path isPropIsPrime' 2=d)
      where
      2=d : 2 == d
      2=d = antisym-≤ (IsPrime'.>1 d-is-prime) (div'->≤ d∣2)


  isContr-PrimeDivisor2^si : (i : ℕ) -> isContr (PrimeDivisor (2⁺ ^⁺ (suc i)))
  isContr-PrimeDivisor2^si i = isContr-PrimeDivisor-prime-power (2 , 2-is-prime) (suc i , tt)

  Injective-ℕ->ℚ : Injective ℕ->ℚ
  Injective-ℕ->ℚ = ∘-Injective Injective-ℤ->ℚ nonneg-injective

  isProp-Σ2^i : isProp (Σ[ i ∈ ℕ ] (2⁺ ^⁺ i == n⁺))
  isProp-Σ2^i (i1 , p1) (i2 , p2) =
    ΣProp-path (isSetNat⁺ _ _) (handle i1 i2 (cong fst (p1 >=> sym p2)))
    where
    2i!=1 : (i : ℕ) -> (2 * i) != 1
    2i!=1 zero    p = zero-suc-absurd p
    2i!=1 (suc i) p = zero-suc-absurd (sym (cong pred (*-commuteᵉ (suc i) 2 >=> p)))

    handle : (i j : ℕ) -> (2 ^' i == 2 ^' j) -> i == j
    handle zero    zero    _ = refl
    handle (suc i) zero    p = bot-elim (2i!=1 (2 ^' i) p)
    handle zero (suc j)    p = bot-elim (2i!=1 (2 ^' j) (sym p))
    handle (suc i) (suc j) p = cong suc (handle i j (*'-left-injective 2⁺ p))

  path-half : (fst (RationalRing.u1/ (ℚUnit-prime (2 , 2-is-prime)))) == 1/2r
  path-half =
    sym *-right-one >=>
    *-right (sym 2r-1/2r-path) >=>
    sym *-assoc >=>
    *-left (cong fst (RationalRing.u1/-left-inverse {x = (ℚUnit-prime (2 , 2-is-prime))})) >=>
    *-left-one

  path-half2 :
    (1r + (r- (fst (RationalRing.u1/ (ℚUnit-prime (2 , 2-is-prime)))))) == 1/2r
  path-half2 =
    +-cong (sym 1/2r-1/2r-path) (cong -_ path-half) >=>
    +-assoc >=> +-right +-inverse >=> +-right-zero


  instance
    FinSetStr-PrimeDivisor : {n : Nat⁺} -> FinSetStr (PrimeDivisor n)
    FinSetStr-PrimeDivisor {n} = record { isFin = isFinSet-PrimeDivisor n }

  φℚ-path2 : (i : ℕ) -> ℕ->ℚ (φ (2⁺ *⁺ (2⁺ ^⁺ i))) ==
                        ℕ->ℚ (2 ^' i)
  φℚ-path2 i =
    φℚ-finiteProduct >=>
    *-right (finiteMerge-isContr (Semiring.*-CommMonoid useⁱ)
               {{ record { isFin = isFinSet-PrimeDivisor (2⁺ ^⁺ (suc i)) } }}
               (isContr-PrimeDivisor2^si i) _) >=>
    *-right path-half2 >=>
    *-commute >=>
    *-right (Semiringʰ.preserves-* Semiringʰ-ℕ->ℚ _ _) >=>
    sym *-assoc >=> *-left (*-commute >=> 2r-1/2r-path) >=>
    *-left-one

  φ-path2 : (i : ℕ) -> φ (2⁺ *⁺ (2⁺ ^⁺ i)) == (2 ^' i)
  φ-path2 i = Injective-ℕ->ℚ (φℚ-path2 i)

  backward : (Σ[ i ∈ ℕ ] (2⁺ ^⁺ i == n⁺)) -> (φ (2⁺ *⁺ n⁺) == n)
  backward (i , path) = cong (\x -> φ (2⁺ *⁺ x)) (sym path) >=> φ-path2 i >=> cong fst path

  PrimeDivisor2n-2 : PrimeDivisor (2⁺ *⁺ n⁺)
  PrimeDivisor2n-2 = (2 , 2-is-prime) , (n , *-commuteᵉ n 2)


  φℚ-path3 : φℚ (2⁺ *⁺ n⁺) ==
             (ℕ->ℚ n) *
             (finiteProduct (FinSet-WithoutPoint (FinSet-PrimeDivisor (2⁺ *⁺ n⁺)) PrimeDivisor2n-2)
               (\((p , _) , _) -> (1r r+ (r- (fst (RationalRing.u1/ (ℚUnit-prime p)))))))
  φℚ-path3 =
    φℚ-finiteProduct >=>
    *-cong (Semiringʰ.preserves-* Semiringʰ-ℕ->ℚ 2 n)
           (finiteMerge-WithoutPoint _ PrimeDivisor2n-2 _ >=> *-left path-half2) >=>
    *-swap >=>
    *-left 2r-1/2r-path >=>
    *-left-one

  forward : (φ (2⁺ *⁺ n⁺) == n) -> (Σ[ i ∈ ℕ ] (2⁺ ^⁺ i == n⁺))
  forward path1 = adjust-prime-power-path prime-power-path
    where
    unit-path : (p : Prime') -> (fst (RationalRing.u1/ (ℚUnit-prime p))) == 1/ℕ (Prime'.nat⁺ p)
    unit-path p =
      cong (fst ∘ RationalRing.u1/_) (\i -> ℕ->ℚ ⟨ p ⟩ , isUnit-path i)
      where
      isUnit-path : snd (ℚUnit-prime p) ==
                    RationalRing.is-unit (1/ℕ (Prime'.nat⁺ p)) (*-commute >=> 1/ℕ-ℕ-path (Prime'.nat⁺ p))
      isUnit-path = RationalRing.isProp-isUnit _ _

    f : PrimeDivisor (2⁺ *⁺ n⁺) -> ℚ
    f (p , _) = 1r r+ (r- (fst (RationalRing.u1/ (ℚUnit-prime p))))

    f' : WithoutPoint (PrimeDivisor (2⁺ *⁺ n⁺)) PrimeDivisor2n-2  -> ℚ
    f' (pd , _) = f pd

    p2 : (finiteProduct (FinSet-WithoutPoint (FinSet-PrimeDivisor (2⁺ *⁺ n⁺)) PrimeDivisor2n-2) f') == 1#
    p2 =
      sym *-left-one >=>
      *-left (sym (1/ℕ-ℕ-path n⁺)) >=>
      *-assoc >=>
      cong (1/ℕ n⁺ *_) (sym φℚ-path3 >=> cong ℕ->ℚ path1) >=>
      1/ℕ-ℕ-path n⁺

    f<1 : (p : PrimeDivisor (2⁺ *⁺ n⁺)) -> f p < 1#
    f<1 (p , _) =
      trans-<-= (+₁-preserves-< (minus-flips-0< (subst (0# <_) (sym (unit-path p))
                                                  (Pos-1/ℕ (Prime'.nat⁺ p)))))
                +-right-zero
    0≤f : (p : PrimeDivisor (2⁺ *⁺ n⁺)) -> 0# ≤ f p
    0≤f (p , _) =
      trans-≤-= (diff-0≤⁺ (1/ℕ≤1 (Prime'.nat⁺ p)))
                (cong (\x -> 1r r+ (r- x)) (sym (unit-path p)))

    af<1 : (p : PrimeDivisor (2⁺ *⁺ n⁺)) -> abs (f p) < 1#
    af<1 p = trans-=-< (abs-0≤-path (0≤f p)) (f<1 p)

    af'<1' : (p : WithoutPoint (PrimeDivisor (2⁺ *⁺ n⁺)) PrimeDivisor2n-2) -> abs (f' p) < 1#
    af'<1' (p , _) = af<1 p

    ¬wp : ¬ (WithoutPoint (PrimeDivisor (2⁺ *⁺ n⁺)) PrimeDivisor2n-2)
    ¬wp = finiteProductᵉ-empty-abs<1 _ af'<1' p2

    isContr-PD : isContr (PrimeDivisor (2⁺ *⁺ n⁺))
    isContr-PD = PrimeDivisor2n-2 ,
                 \ pd -> handle (Discrete-PrimeDivisor (2⁺ *⁺ n⁺) pd PrimeDivisor2n-2)
      where
      handle : {pd : PrimeDivisor (2⁺ *⁺ n⁺)} -> Dec (pd == PrimeDivisor2n-2) -> PrimeDivisor2n-2 == pd
      handle (yes path) = sym path
      handle (no ¬path) = bot-elim (¬wp (_ , ¬path))

    prime-power-path : Σ[ i ∈ ℕ ] (2 ^' i == (2 * n))
    prime-power-path = isContr-PrimeDivisor->prime-power (2⁺ *⁺ n⁺) isContr-PD

    adjust-prime-power-path : Σ[ i ∈ ℕ ] (2 ^' i == (2 * n)) -> Σ[ i ∈ ℕ ] (2⁺ ^⁺ i == n⁺)
    adjust-prime-power-path (zero , 1=2n) = bot-elim (irrefl-path-< 1=2n 1<2n)
      where
      1<2 : 1 < 2
      1<2 = suc-≤ (suc-≤ zero-≤)
      1≤n : 1 ≤ n
      1≤n = Pos'->< pos-n
      1<2n : 1 < (2 * n)
      1<2n = trans-=-< (sym *-left-one)
               (trans-<-≤ (*₂-preserves-< 1<2 zero-<) (*₁-preserves-≤ (zero-≤ {2}) 1≤n))
    adjust-prime-power-path (suc i , 2*2^i=2n) =
      i , ΣProp-path isPropPos' (*'-left-injective 2⁺ 2*2^i=2n)
