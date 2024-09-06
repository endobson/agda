{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponential.order.positive where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import combinatorics.factorial
open import equality
open import fin
open import finite-commutative-monoid.instances
open import finset.instances
open import finsum.arithmetic
open import finsum.order
open import functions
open import funext
open import heyting-field.instances.real
open import nat.order
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-ring.exponentiation
open import ordered-semiring
open import ordered-semiring.exponentiation
open import ordered-semiring.initial
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import real
open import real.exponential-series
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.sequence.limit.order
open import real.series.geometric
open import ring.implementations.real
open import semiring
open import semiring.exponentiation
open import semiring.initial
open import semiring.instances.nat
open import sequence
open import sequence.partial-sums
open import truncation

private
  1/4 : ℝ
  1/4 = 1/ℕ (4 , tt)
  0<1/4 : 0# < 1/4
  0<1/4 = (0<1/ℕ _)
  0≤1/4 : 0# ≤ 1/4
  0≤1/4 = weaken-< 0<1/4
  1/4<1 : 1/4 < 1#
  1/4<1 = trans-<-= (1/ℕ-flips-< _ _ (2 , refl)) 1/1-path

  1/4s : Sequence ℝ
  1/4s n = 1/4 ^ℕ n
  1/4-lim : ℝ
  1/4-lim = geometric-series-limit 1/4 0≤1/4 1/4<1
  1/4-lim-path : (1/4-lim * (diff 1/4 1#)) == 1#
  1/4-lim-path = (geometric-series-limit-path 1/4 0≤1/4 1/4<1)
  isLimit-1/4s : isLimit (partial-sums 1/4s) 1/4-lim
  isLimit-1/4s = isLimit-geometric-series 1/4 0≤1/4 1/4<1

  0<1/4-lim : 0# < 1/4-lim
  0<1/4-lim = *₂-reflects-0< 0<1/4-lim*d 0≤d
    where
    0<1/4-lim*d : 0# < (1/4-lim * (diff 1/4 1#))
    0<1/4-lim*d = trans-<-= 0<1 (sym 1/4-lim-path)
    0≤d : 0# ≤ (diff 1/4 1#)
    0≤d = diff-0≤⁺ (weaken-< 1/4<1)

  2seq : Sequence ℝ
  2seq zero = 2#
  2seq (suc _) = 0#

  isLimit-2seq : isLimit (partial-sums 2seq) 2#
  isLimit-2seq = dropN-reflects-limit isLimit-2seq'
    where
    isLimit-2seq' : isLimit (partial-sums 2seq ∘ suc) 2#
    isLimit-2seq' =
      subst2 isLimit (funExt (\n -> sym (p1 n >=> +-right (p2 n)))) (+-right-zero)
        (+-preserves-limit (isLimit-constant-seq 2#) (isLimit-constant-seq 0#))
      where
      p1 : ∀ n -> (partial-sums 2seq (suc n)) == 2# + (partial-sums (2seq ∘ suc) n)
      p1 n = partial-sums-suc
      p2 : ∀ n -> (partial-sums (2seq ∘ suc) n) == 0#
      p2 n = finiteMerge-ε _ (\_ -> refl)

  adj-seq : Sequence ℝ
  adj-seq n = diff (1/4s n) (2seq n)

  adj-lim : ℝ
  adj-lim = (diff 1/4-lim 2#)

  0<adj-lim : 0# < adj-lim
  0<adj-lim = diff-0<⁺ 1/4-lim<2
    where
    ℕ-2+1<4 : (2 + 1) < 4
    ℕ-2+1<4 = refl-≤

    ℕ->ℝ-2+1<4 : (ℕ->Semiring 2# + ℕ->Semiring 1#) < ℕ->Semiring 4
    ℕ->ℝ-2+1<4 =
      trans-=-< (sym (Semiringʰ.preserves-+ (∃!-prop ∃!ℕ->Semiring) 2 1))
                (ℕ->Semiring-preserves-< ℕ-2+1<4)

    2/4=1/2 : ℕ->Semiring 2# * 1/4 == 1/2
    2/4=1/2 =
      *-right (1/ℕ-preserves-* (2 , tt) (2 , tt)) >=>
      sym *-assoc >=>
      *-left (*-left ℕ->Semiring-preserves-2# >=> 2*1/2-path) >=>
      *-left-one

    1/2+1/4<1 : (1/2 + 1/4) < 1#
    1/2+1/4<1 =
      subst2 _<_
        (*-distrib-+-right >=>
         +-cong 2/4=1/2 (*-left ℕ->Semiring-preserves-1# >=> *-left-one))
        (∃!-prop (∃!1/ℕ _))
        (*₂-preserves-< ℕ->ℝ-2+1<4 0<1/4)

    1/2<1-1/4 : 1/2 < diff 1/4 1#
    1/2<1-1/4 =
      trans-=-< (sym +-right-zero >=> +-right (sym +-inverse) >=> sym +-assoc)
                (+₂-preserves-< 1/2+1/4<1)

    0<2*1/4-lim : 0# < (2# * 1/4-lim)
    0<2*1/4-lim = *-preserves-0< 0<2 0<1/4-lim

    1/4-lim<2 : 1/4-lim < 2#
    1/4-lim<2 =
      subst2 _<_
        (sym *-assoc >=> (*-left (*-commute >=> 2*1/2-path)) >=> *-left-one)
        (*-commute >=> *-assoc >=> *-right 1/4-lim-path >=> *-right-one)
        (*₂-preserves-< 1/2<1-1/4 0<2*1/4-lim)


  isLimit-adj : isLimit (partial-sums adj-seq) adj-lim
  isLimit-adj =
    subst2 isLimit (funExt (\n -> sym finiteSum-diff)) refl
      (diff-preserves-limit isLimit-1/4s isLimit-2seq)


module _ {x : ℝ} (ax<1/4 : abs x < 1/4) where
  private
    adj-seq≤exp-terms : ∀ n -> adj-seq n ≤ exp-terms x n
    adj-seq≤exp-terms zero =
      path-≤ (+-assoc >=> +-right +-inverse >=> +-right-zero >=> sym exp-term0)
    adj-seq≤exp-terms n@(suc _) = trans-=-≤ +-left-zero (weaken-< (trans-≤-< lt3 lt2))
      where
      lt1 : abs (x ^ℕ n) < (1/4 ^ℕ n)
      lt1 = trans-=-< (abs-^ℕ-path n) (^ℕ-0≤-preserves-< abs-0≤ (n , tt) ax<1/4)

      lt2 : (1/ℕ (factorial⁺ n) * (- (1/4 ^ℕ n))) < exp-terms x n
      lt2 =
        *₁-preserves-<
          (0<1/ℕ (factorial⁺ n))
          (trans-<-=
            (minus-flips-< (trans-≤-< max-≤-right lt1))
            minus-double-inverse)

      lt3 : (- (1/4 ^ℕ n)) ≤ (1/ℕ (factorial⁺ n) * (- (1/4 ^ℕ n)))
      lt3 =
        trans-=-≤ (sym *-left-one)
          (*₂-flips-≤
            (trans-≤-= (1/ℕ-flips-≤ (1 , tt) (factorial⁺ n) (Pos'->< (snd (factorial⁺ n)))) 1/1-path)
            (minus-flips-0≤ (^ℕ-preserves-0≤ (weaken-< (0<1/ℕ (4 , tt))) n)))

    adj-lim≤exp : adj-lim ≤ exp x
    adj-lim≤exp =
      isLimit-preserves-≤ isLimit-adj (isLimit-exp x)
        (\_ -> finiteSum-preserves-≤ (\(i , _) -> adj-seq≤exp-terms i))

  opaque
    small-abs-exp-0< : 0# < exp x
    small-abs-exp-0< = trans-<-≤ 0<adj-lim adj-lim≤exp
