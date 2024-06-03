{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.nth-root.bound-sequence where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import equality
open import functions
open import funext
open import heyting-field.instances.rational
open import heyting-field.instances.real
open import isomorphism
open import monoid
open import nat
open import nat.even-odd
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-field.mean
open import ordered-ring.exponentiation
open import ordered-semiring
open import ordered-semiring.exponentiation
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import rational.open-interval
open import rational.open-interval.containment
open import rational.open-interval.sequence
open import rational.order
open import real
open import real.arithmetic.rational
open import real.epsilon-bounded
open import real.order
open import real.rational
open import real.sequence.cauchy
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.sequence.open-interval
open import real.series.geometric
open import relation
open import ring
open import ring.exponentiation
open import ring.implementations.real
open import semiring
open import semiring.exponentiation
open import sequence
open import sign
open import sign.instances.rational
open import truncation

isNthPower : (n : Nat) -> Pred ℚ ℓ-zero
isNthPower n q = Σ[ a ∈ ℚ ] (a ^ℕ n == q)

private
  Seq : Type₁
  Seq = Sequence ℝ

  ℚ->ℝ-preserves-^ℕ : {q : ℚ} (n : ℕ) -> ℚ->ℝ (q ^ℕ n) == (ℚ->ℝ q) ^ℕ n
  ℚ->ℝ-preserves-^ℕ = Semiringʰ-preserves-^ℕ Semiringʰ-ℚ->ℝ

  module _ (ls : Sequence ℝ) (us : Sequence ℝ) (m : ℝ)
           (lim-ls : isLimit ls m)
           (lim-us : isLimit us m)
     where

     lim-diff^ℕ : ∀ n -> isLimit (\i -> diff ((ls i) ^ℕ n) ((us i) ^ℕ n)) 0#
     lim-diff^ℕ n =
       subst2 isLimit refl +-inverse
         (diff-preserves-limit (^ℕ-preserves-limit lim-ls n)
                               (^ℕ-preserves-limit lim-us n))

  lim0->ArbitrarilySmall :
    (qs : Sequence ℚ) -> isLimit (ℚ->ℝ ∘ qs) 0# -> ArbitrarilySmall qs
  lim0->ArbitrarilySmall qs lim (ε , 0<ε) =
    ∀Largeℕ-map U->ℚ< (isLimit.upper lim ε (ℚ<->U 0<ε))

  ^ℕ-preserves-< : ∀ {q r : ℚ} -> q < r -> (n : Nat) -> Odd n -> (q ^ℕ n) < (r ^ℕ n)
  ^ℕ-preserves-< q<r n odd-n = Iso.fun (x<y<->x^n<y^n n odd-n _ _) q<r

  Iℚ^ℕ : Iℚ -> (Σ Nat Odd) -> Iℚ
  Iℚ^ℕ i (n , odd-n) =
    Iℚ-cons (i.l ^ℕ n) (i.u ^ℕ n) (^ℕ-preserves-< i.l<u n odd-n)
    where
    module i = Iℚ i


module _ (n'@(n , odd-n) : Σ Nat Odd) (q : ℚ) where
  private

    Elem : Type ℓ-zero
    Elem = Σ[ i ∈ Iℚ ] (ℚ∈Iℚ q (Iℚ^ℕ i n'))

    next' : (e1 : Elem) -> Σ[ e2 ∈ Elem ] (i-width (fst e2) == 1/2 * i-width (fst e1) ×
                                           (fst e2 i⊆ fst e1))
    next' (i@(Iℚ-cons l u l<u) , (l^n<q , q<u^n)) =
      handle (trichotomous-< q (m2 ^ℕ n))
      where
      m2 : ℚ
      m2 = mean l u
      l<m2 = mean-<₁ l<u
      m2<u = mean-<₂ l<u

      m1 : ℚ
      m1 = mean l m2
      m3 : ℚ
      m3 = mean m2 u

      l<m1 = mean-<₁ l<m2
      m1<m2 = mean-<₂ l<m2
      m2<m3 = mean-<₁ m2<u
      m3<u = mean-<₂ m2<u
      m1<m3 = trans-< m1<m2 m2<m3
      m1^n<m2^n = ^ℕ-preserves-< m1<m2 n odd-n
      m2^n<m3^n = ^ℕ-preserves-< m2<m3 n odd-n
      m1^n<m3^n = ^ℕ-preserves-< m1<m3 n odd-n

      upper-width : diff m2 u == 1/2 * (diff l u)
      upper-width = diff-mean

      lower-width : diff l m2 == 1/2 * (diff l u)
      lower-width = diff-mean'


      mid-width : diff m1 m3 == 1/2 * (diff l u)
      mid-width =
        sym diff-trans >=>
        +-cong mid-width₁ mid-width₂ >=>
        1/2-path
        where
        mid-width₁ : diff m1 m2 == 1/2 * (1/2 * (diff l u))
        mid-width₁ = diff-mean >=> *-right lower-width

        mid-width₂ : diff m2 m3 == 1/2 * (1/2 * (diff l u))
        mid-width₂ = diff-mean' >=> *-right upper-width

      module _ (m2^n<q : (m2 ^ℕ n) < q) where
        upper-ans : Elem
        upper-ans = (Iℚ-cons m2 u m2<u) , (m2^n<q , q<u^n)

        upper-⊆ : fst upper-ans i⊆ i
        upper-⊆ = i⊆-cons (weaken-< l<m2) refl-≤

      module _ (q<m2^n : q < (m2 ^ℕ n)) where
        lower-ans : Elem
        lower-ans = (Iℚ-cons l m2 l<m2) , (l^n<q , q<m2^n)

        lower-⊆ : fst lower-ans i⊆ i
        lower-⊆ = i⊆-cons refl-≤ (weaken-< m2<u)

      module _ (q=m2^n : q == (m2 ^ℕ n)) where
        mid-ans : Elem
        mid-ans =
          (Iℚ-cons m1 m3 m1<m3) ,
          (trans-<-= m1^n<m2^n (sym q=m2^n) ,
           trans-=-< q=m2^n m2^n<m3^n)

        mid-⊆ : fst mid-ans i⊆ i
        mid-⊆ = i⊆-cons (weaken-< l<m1) (weaken-< m3<u)

      handle : (Tri< q (m2 ^ℕ n)) -> _
      handle (tri< lt _ _) = lower-ans lt , lower-width , lower-⊆ lt
      handle (tri= _ eq _) = mid-ans eq , mid-width , mid-⊆ eq
      handle (tri> _ _ gt) = upper-ans gt , upper-width , upper-⊆ gt


    next : Elem -> Elem
    next e = fst (next' e)

    elem₀ : Elem
    elem₀ = handle (split-< (- 1#) q) (split-< q 1#)
      where
      1^n=1 : 1# ^ℕ n == 1#
      1^n=1 = ^ℕ-preserves-1# n
      -1^n=-1 : (- 1#) ^ℕ n == - 1#
      -1^n=-1 = (minus-^ℕ-odd 1# n odd-n >=> cong -_ 1^n=1)
      0^n=0 : (0# ^ℕ n) == 0#
      0^n=0 = case n odd-n
        where
        case : (n : Nat) -> Odd n -> (0# ^ℕ n) == 0#
        case (suc n) _ = *-left-zero


      module _ (-1<q : (- 1#) < q) (q<1 : q < 1#) where
        zero-ans : Elem
        zero-ans =
          (Iℚ-cons (- 1#) 1# (trans-< -1<q q<1)) ,
          (trans-=-< -1^n=-1 -1<q , trans-<-= q<1 (sym 1^n=1))

      module _ (q≤-1 : q ≤ (- 1#)) where
        -1<0 = minus-flips-0< 0<1
        q<0 = (trans-≤-< q≤-1 -1<0)

        q-1<q = trans-<-= (+₁-preserves-< -1<0) +-right-zero
        q-1≤-1 = weaken-< (trans-<-≤ q-1<q q≤-1)

        [q-1]^n<q : ((q + (- 1#)) ^ℕ n) < q
        [q-1]^n<q =
          trans-≤-< (^ℕ-odd-≤-1 q-1≤-1 n odd-n) q-1<q

        q-1<0 : (q + (- 1#)) < 0#
        q-1<0 = +-preserves-<0 q<0 -1<0

        neg-ans : Elem
        neg-ans =
          Iℚ-cons (q + (- 1#)) 0# q-1<0 ,
          ([q-1]^n<q , (trans-<-= q<0 (sym 0^n=0)))

      module _ (1≤q : 1# ≤ q) where
        q<q+1 = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<1)
        1≤q+1 = weaken-< (trans-≤-< 1≤q q<q+1)
        0<q = (trans-<-≤ 0<1 1≤q)
        0<q+1 = trans-< 0<q q<q+1

        q<[q+1]^n : q < ((q + 1#) ^ℕ n)
        q<[q+1]^n =
          trans-<-≤ q<q+1 (^ℕ-odd-1≤ 1≤q+1 n odd-n)

        pos-ans : Elem
        pos-ans =
          Iℚ-cons 0# (q + 1#) 0<q+1 ,
          (trans-=-< 0^n=0 0<q , q<[q+1]^n)

      handle : (- 1#) < q ⊎ q ≤ (- 1#) -> q < 1# ⊎ 1# ≤ q -> Elem
      handle (inj-r q≤-1) _           = neg-ans q≤-1
      handle (inj-l -1<q) (inj-r 1≤q) = pos-ans 1≤q
      handle (inj-l -1<q) (inj-l q<1) = zero-ans -1<q q<1

    base-seq : ℕ -> Elem
    base-seq zero = elem₀
    base-seq (suc n) = next (base-seq n)

    seq' : ℕ -> Iℚ
    seq' i = (fst (base-seq i))

    width₀ : ℚ
    width₀ = i-width (fst elem₀)

    widthℝ : ℕ -> ℝ
    widthℝ i = ℚ->ℝ (i-width (fst (base-seq i)))

    width-path : ∀ i -> i-width (fst (base-seq i)) == width₀ * (1/2 ^ℕ i)
    width-path zero = sym *-right-one
    width-path (suc i) =
      (fst (snd (next' (base-seq i)))) >=>
      *-right (width-path i) >=>
      sym *-assoc >=> *-left *-commute >=> *-assoc

    widthℝ-path : ∀ i -> widthℝ i == ℚ->ℝ width₀ * (1/2 ^ℕ i)
    widthℝ-path i =
      cong ℚ->ℝ (width-path i) >=>
      ℚ->ℝ-preserves-* >=>
      *-right (ℚ->ℝ-preserves-^ℕ i >=>
               (cong (_^ℕ i) (Semiringʰ-preserves-1/ℕ Semiringʰ-ℚ->ℝ 2⁺)))

    lim1 : isLimit (\i -> 1/2 ^ℕ i) 0#
    lim1 = isLimit-geometric-sequence 1/2 (weaken-< 0<1/2) 1/2<1

    lim-width : isLimit widthℝ 0#
    lim-width =
      subst2 isLimit (\j i -> (widthℝ-path i (~ j))) *-right-zero check2
      where
      check2 : isLimit (\i -> ℚ->ℝ width₀ * (1/2 ^ℕ i)) (ℚ->ℝ width₀ * 0#)
      check2 = *₁-preserves-limit lim1

    lim-width^ℕ : _
    lim-width^ℕ =
      subst2 isLimit (funExt (\i -> cong2 diff (sym (ℚ->ℝ-preserves-^ℕ n))
                                               (sym (ℚ->ℝ-preserves-^ℕ n)) >=>
                                    sym ℚ->ℝ-preserves-diff)) refl
        (lim-diff^ℕ (ℚ->ℝ ∘ Iℚ.l ∘ seq') (ℚ->ℝ ∘ Iℚ.u ∘ seq') _
          (Iℚs->ℝ-lower-limit seq' step-⊆ lim-width)
          (Iℚs->ℝ-upper-limit seq' step-⊆ lim-width) n)
      where
      step-⊆ : ∀ i -> seq' (suc i) i⊆ seq' i
      step-⊆ i = snd (snd (next' (base-seq i)))

  opaque
    Root-seq : ℕ -> Iℚ
    Root-seq i = Iℚ^ℕ (fst (base-seq i)) n'

    Root-q∈s : (i : ℕ) -> ℚ∈Iℚ q (Root-seq i)
    Root-q∈s i = snd (base-seq i)

    Root-root-bound : ∀ i -> isNthPower n (Iℚ.l (Root-seq i))
    Root-root-bound i = Iℚ.l (fst (base-seq i)) , refl

    Root-small-s : ArbitrarilySmall (i-width ∘ Root-seq)
    Root-small-s = lim0->ArbitrarilySmall (i-width ∘ Root-seq) lim-width^ℕ
