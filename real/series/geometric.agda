{-# OPTIONS --cubical --safe --exact-split #-}

module real.series.geometric where

open import additive-group
open import additive-group.instances.real
open import additive-group.instances.nat
open import apartness
open import base
open import equality
open import finset.instances
open import funext
open import functions
open import finsum.arithmetic
open import heyting-field
open import nat
open import nat.order
open import order
open import order.instances.real
open import order.instances.nat
open import order.instances.rational
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import ordered-semiring.archimedean
open import ordered-semiring.archimedean.instances.rational
open import ordered-additive-group.instances.real
open import rational
open import rational.order
open import real
open import real.arithmetic.rational
open import real.arithmetic.multiplication.inverse
open import real.epsilon-bounded
open import real.heyting-field
open import real.order
open import real.sequence.limit.arithmetic
open import real.rational
open import real.series
open import real.sequence.limit
open import ring
open import ring.solver-equations
open import ring.implementations.real
open import ring.implementations.rational
open import semiring
open import semiring.instances.nat
open import semiring.initial
open import sequence
open import sequence.partial-sums
open import truncation

private
  Seq : Type₁
  Seq = Sequence ℝ

-- TODO make this named ^ℕ
geometric-sequence : ℝ -> Seq
geometric-sequence x zero = 1#
geometric-sequence x (suc n) = x * geometric-sequence x n


_ℚ^ℕ_ : ℚ -> ℕ -> ℚ
_ℚ^ℕ_ = _r^ℕ⁰_

private
  _^ℕ_ : ℝ -> ℕ -> ℝ
  _^ℕ_ = geometric-sequence

  _ℝ^ℕ_ : ℝ -> ℕ -> ℝ
  _ℝ^ℕ_ = geometric-sequence


  ℚ^ℕ-distrib-+₂ : {q : ℚ} (n1 n2 : ℕ) -> q ℚ^ℕ (n1 + n2) == (q ℚ^ℕ n1) * (q ℚ^ℕ n2)
  ℚ^ℕ-distrib-+₂ zero     n2 = sym *-left-one
  ℚ^ℕ-distrib-+₂ {q} (suc n1) n2 =
    cong (q *_) (ℚ^ℕ-distrib-+₂ n1 n2) >=>
    sym *-assoc

  ℚ^ℕ-one : {q : ℚ} -> q ℚ^ℕ 1 == q
  ℚ^ℕ-one = *-right-one

  ℚ^ℕ⁺-distrib-*₂ : {q : ℚ} (n1 n2 : Nat⁺) ->
                    q ℚ^ℕ (⟨ n1 ⟩ * ⟨ n2 ⟩) == (q ℚ^ℕ ⟨ n1 ⟩) ℚ^ℕ ⟨ n2 ⟩
  ℚ^ℕ⁺-distrib-*₂ {q} n1 n2 = cong (q ℚ^ℕ_) (*-commuteᵉ ⟨ n1 ⟩ ⟨ n2 ⟩) >=> ℚ^ℕ⁺-distrib-*₂' n2 n1
    where
    ℚ^ℕ⁺-distrib-*₂' : (n1 n2 : Nat⁺) ->
                      q ℚ^ℕ (⟨ n1 ⟩ * ⟨ n2 ⟩) == (q ℚ^ℕ ⟨ n2 ⟩) ℚ^ℕ ⟨ n1 ⟩
    ℚ^ℕ⁺-distrib-*₂' (suc zero , _) n2 =
      cong (q ℚ^ℕ_) (*-left-oneᵉ ⟨ n2 ⟩) >=> (sym ℚ^ℕ-one)
    ℚ^ℕ⁺-distrib-*₂' (suc (suc n) , tt) n2@(n2' , _) =
      (ℚ^ℕ-distrib-+₂ n2' ((suc n) * n2')) >=>
      (*-right (ℚ^ℕ⁺-distrib-*₂' (suc n , tt) n2)) >=>
      (*-left (sym ℚ^ℕ-one)) >=>
      sym (ℚ^ℕ-distrib-+₂ 1 (suc n))

  ℚ^ℕ-preserves-0≤ : {q : ℚ} -> 0# ≤ q -> (n : ℕ) -> 0# ≤ (q ℚ^ℕ n)
  ℚ^ℕ-preserves-0≤ {q} 0≤q zero = weaken-< Pos-1r
  ℚ^ℕ-preserves-0≤ {q} 0≤q (suc n) =
    *-preserves-0≤ 0≤q (ℚ^ℕ-preserves-0≤ 0≤q n)

  ℚ^ℕ-preserves-≤ : {q r : ℚ} -> 0# ≤ q -> q ≤ r -> (n : ℕ) -> (q ℚ^ℕ n) ≤ (r ℚ^ℕ n)
  ℚ^ℕ-preserves-≤ {q} {r} 0≤q q≤r zero = refl-≤
  ℚ^ℕ-preserves-≤ {q} {r} 0≤q q≤r (suc n) =
    trans-≤ (*₂-preserves-≤ q≤r (ℚ^ℕ-preserves-0≤ 0≤q n))
            (*₁-preserves-≤ (trans-≤ 0≤q q≤r) (ℚ^ℕ-preserves-≤ 0≤q q≤r n))

ℚ^ℕ-ℝ^ℕ-path : {q : ℚ} (n : ℕ) -> ℚ->ℝ (q ℚ^ℕ n) == (ℚ->ℝ q) ℝ^ℕ n
ℚ^ℕ-ℝ^ℕ-path zero = refl
ℚ^ℕ-ℝ^ℕ-path (suc n) =
  ℚ->ℝ-preserves-* >=> *-right (ℚ^ℕ-ℝ^ℕ-path n)



geometric-sequence-1 : (n : ℕ) -> geometric-sequence 1# n == 1#
geometric-sequence-1 zero = refl
geometric-sequence-1 (suc n) = *-left-one >=> geometric-sequence-1 n


geometric-sequence-0≤ : {x : ℝ} -> 0# ≤ x -> (n : ℕ) -> 0# ≤ geometric-sequence x n
geometric-sequence-0≤ 0≤x zero = weaken-< 0ℝ<1ℝ
geometric-sequence-0≤ 0≤x (suc n) = *-preserves-0≤ 0≤x (geometric-sequence-0≤ 0≤x n)

geometric-sequence-0< : {x : ℝ} -> 0# < x -> (n : ℕ) -> 0# < geometric-sequence x n
geometric-sequence-0< 0<x zero = 0ℝ<1ℝ
geometric-sequence-0< 0<x (suc n) = *-preserves-0< 0<x (geometric-sequence-0< 0<x n)


geometric-sequence-≤ : {x y : ℝ} -> 0# ≤ x -> x ≤ y -> (n : ℕ) ->
                       (geometric-sequence x n) ≤ (geometric-sequence y n)
geometric-sequence-≤ 0≤x x≤y zero = refl-≤
geometric-sequence-≤ 0≤x x≤y (suc n) =
  trans-≤ (*₁-preserves-≤ 0≤x (geometric-sequence-≤ 0≤x x≤y n))
          (*₂-preserves-≤ x≤y (geometric-sequence-0≤ (trans-≤ 0≤x x≤y) n))

geometric-sequence-≤1' : {x : ℝ} -> 0# ≤ x -> x ≤ 1# -> (n : ℕ) ->
                        (geometric-sequence x n) ≤ 1#
geometric-sequence-≤1' 0≤x x≤1 n =
  subst2 _≤_ refl (geometric-sequence-1 n) (geometric-sequence-≤ 0≤x x≤1 n)


geometric-sequence-≤1 : {x : ℝ} -> 0# ≤ x -> x ≤ 1# -> (n m : ℕ) -> n ≤ m ->
                        (geometric-sequence x m) ≤ (geometric-sequence x n)
geometric-sequence-≤1 0≤x x≤1 zero m _ =
  geometric-sequence-≤1' 0≤x x≤1 m
geometric-sequence-≤1 0≤x x≤1 (suc n) zero = bot-elim ∘ zero-≮
geometric-sequence-≤1 0≤x x≤1 (suc n) (suc m) sn≤sm =
  *₁-preserves-≤ 0≤x (geometric-sequence-≤1 0≤x x≤1 n m (pred-≤ sn≤sm))


ℝ^ℕ-preserves-0≤ : {x : ℝ} -> 0# ≤ x -> (n : ℕ) -> 0# ≤ (x ℝ^ℕ n)
ℝ^ℕ-preserves-0≤ = geometric-sequence-0≤

ℝ^ℕ-preserves-0< : {x : ℝ} -> 0# < x -> (n : ℕ) -> 0# < (x ℝ^ℕ n)
ℝ^ℕ-preserves-0< = geometric-sequence-0<

ℝ^ℕ-preserves-≤ : {x y : ℝ} -> 0# ≤ x -> x ≤ y -> (n : ℕ) -> (x ℝ^ℕ n) ≤ (y ℝ^ℕ n)
ℝ^ℕ-preserves-≤ = geometric-sequence-≤


ℝ^ℕ-distrib-*-right : {x y : ℝ} -> (n : ℕ) -> (x * y) ℝ^ℕ n == (x ℝ^ℕ n) * (y ℝ^ℕ n)
ℝ^ℕ-distrib-*-right zero = sym *-left-one
ℝ^ℕ-distrib-*-right (suc n) = *-right (ℝ^ℕ-distrib-*-right n) >=> *-swap

ℝ^ℕ-distrib-+-left : {x : ℝ} -> (m n : ℕ) -> x ℝ^ℕ (m + n) == (x ℝ^ℕ m) * (x ℝ^ℕ n)
ℝ^ℕ-distrib-+-left zero    n = sym *-left-one
ℝ^ℕ-distrib-+-left (suc m) n = *-right (ℝ^ℕ-distrib-+-left m n) >=> sym *-assoc

geometric-sequence-<1 : {x : ℝ} -> 0# < x -> x < 1# -> {m n : ℕ} -> m < n ->
                        (geometric-sequence x n) < (geometric-sequence x m)
geometric-sequence-<1 {x} 0<x x<1 {m} {n} (i , p) =
  trans-=-< p1 (trans-<-= (*₂-preserves-< p2 (ℝ^ℕ-preserves-0< 0<x m)) *-left-one)
  where
  p1 : geometric-sequence x n == (x ℝ^ℕ (suc i)) * (x ℝ^ℕ m)
  p1 = cong (geometric-sequence x) (sym p >=> +'-right-suc) >=>
       ℝ^ℕ-distrib-+-left (suc i) m

  p2 : (x ℝ^ℕ suc i) < 1#
  p2 = trans-<-≤ (*₂-preserves-< x<1 (ℝ^ℕ-preserves-0< 0<x i))
                 (trans-=-≤ *-left-one (geometric-sequence-≤1' (weaken-< 0<x) (weaken-< x<1) i))


geometric-series : ℝ -> Seq
geometric-series x = partial-sums (geometric-sequence x)

abstract
  geometric-series-path :
    (x : ℝ) (n : ℕ) -> (geometric-series x n) * (1# + (- x)) == 1# + - (x ^ℕ n)
  geometric-series-path x zero =
    *-left partial-sums-zero >=>
    *-left-zero >=>
    sym +-inverse
  geometric-series-path x (suc n) = ans
    where
    expand : (geometric-series x (suc n)) == 1# + x * geometric-series x n
    expand = partial-sums-suc >=> +-right finiteSum-*

    ans : (geometric-series x (suc n)) * (1# + (- x)) == 1# + - (x ^ℕ (suc n))
    ans =
     *-left expand >=>
     *-distrib-+-right >=>
     +-right (*-assoc >=>
              *-right (geometric-series-path x n) >=>
              *-distrib-+-left >=>
              +-cong *-right-one minus-extract-right) >=>
     +-left (*-left-one >=> +-commute) >=>
     +-swap >=>
     +-left (+-commute >=> +-inverse) >=>
     +-left-zero


private
  lemma1 : (n : ℕ) -> 3 ≤ n -> 0# < (((ℕ->ℚ n * ℕ->ℚ n) + (- ((ℕ->ℚ 3) * (ℕ->ℚ n)))) + 1#)
  lemma1 n 3≤n = trans-≤-< 0≤n²-3n (trans-=-< (sym +-right-zero) (+₁-preserves-< Pos-1r))
    where
    0≤n²-3n : 0# ≤ ((ℕ->ℚ n * ℕ->ℚ n) + (- ((ℕ->ℚ 3) * (ℕ->ℚ n))))
    0≤n²-3n = trans-≤-= (*-preserves-0≤ (diff-0≤⁺ (ℕ->ℚ-preserves-≤ 3 n 3≤n))
                                        (ℕ->ℚ-preserves-≤ 0 n zero-≤))
                        (*-distrib-+-right >=> +-right minus-extract-left)

  lemma2 : (n : Nat⁺) -> 3 ≤ ⟨ n ⟩ -> 0# < (1# + (- ((ℕ->ℚ 3) * 1/ℕ n)) + (1/ℕ n * 1/ℕ n))
  lemma2 n 3≤n =
    trans-<-= (*-preserves-0< (lemma1 n' 3≤n) (*-preserves-0< (Pos-1/ℕ n) (Pos-1/ℕ n))) p4
    where
    n' : ℕ
    n' = ⟨ n ⟩
    p1 : (ℕ->ℚ n' * ℕ->ℚ n') * (1/ℕ n * 1/ℕ n) == 1#
    p1 = *-swap >=>
         *-cong (*-commute >=> 1/ℕ-ℕ-path n) (*-commute >=> 1/ℕ-ℕ-path n) >=>
         *-right-one

    p2 : (- ((ℕ->ℚ 3) * ℕ->ℚ n')) * (1/ℕ n * 1/ℕ n) == (- ((ℕ->ℚ 3) * 1/ℕ n))
    p2 = minus-extract-left >=>
         cong -_ (*-swap >=> *-right (*-commute >=> 1/ℕ-ℕ-path n) >=> *-right-one)

    p3 : 1# * (1/ℕ n * 1/ℕ n) == (1/ℕ n * 1/ℕ n)
    p3 = *-left-one

    p4 : (((ℕ->ℚ n' * ℕ->ℚ n') + (- ((ℕ->ℚ 3) * (ℕ->ℚ n')))) + 1#) * (1/ℕ n * 1/ℕ n) ==
         (1# + (- ((ℕ->ℚ 3) * 1/ℕ n)) + (1/ℕ n * 1/ℕ n))
    p4 = *-distrib-+-right >=> +-cong (*-distrib-+-right >=> +-cong p1 p2) p3

  lemma3 : (n : Nat⁺) ->
    (1# + (- (1/ℕ n))) ℚ^ℕ 3 ==
    (1# + (- ((ℕ->ℚ 2) * 1/ℕ n))) +
    (1# + (- ((ℕ->ℚ 3) * 1/ℕ n)) + (1/ℕ n * 1/ℕ n)) * (- (1/ℕ n))
  lemma3 n =
    subst (\f -> (f 1# + (- (1/ℕ n))) ℚ^ℕ 3 ==
                 (f 1# + (- ((f 2) * 1/ℕ n))) +
                 (f 1# + (- ((f 3) * 1/ℕ n)) + (1/ℕ n * 1/ℕ n)) * (- (1/ℕ n)))
      (funExt ℕ->Semiring-ℚ-path) p1
    where
    p1 : (ℕ->Semiring 1 + (- (1/ℕ n))) ℚ^ℕ 3 ==
         (ℕ->Semiring 1# + (- ((ℕ->Semiring 2) * 1/ℕ n))) +
         (ℕ->Semiring 1# + (- ((ℕ->Semiring 3) * 1/ℕ n)) + (1/ℕ n * 1/ℕ n)) * (- (1/ℕ n))
    p1 = [1-x]^3-expand (1/ℕ n)

  lemma4 : (n : Nat⁺) -> 3 ≤ ⟨ n ⟩ -> ((1# + (- (1/ℕ n))) ℚ^ℕ 3) < (1# + (- ((ℕ->ℚ 2) * 1/ℕ n)))
  lemma4 n 3≤n =
    trans-=-< (lemma3 n) (trans-<-= (+₁-preserves-< (*₂-flips-< (lemma2 n 3≤n)
                                                                (minus-flips-0< (Pos-1/ℕ n))))
                                    (+-right *-left-zero >=> +-right-zero))

  lemma5 : (n : Nat⁺) -> (1# + (- ((ℕ->ℚ 2) * 1/ℕ (suc ⟨ n ⟩ , tt)))) ≤ (1# + (- (1/ℕ n)))
  lemma5 n⁺@(suc n' , _) = +₁-preserves-≤ (minus-flips-≤ p4)
    where
    n = ⟨ n⁺ ⟩
    p1 : suc n ≤ (2 * n)
    p1 = suc-≤ (trans-≤-= (suc-≤ (trans-=-≤ (sym +-right-zero) (+₁-preserves-≤ zero-≤)))
                          (+-commuteᵉ (suc n') n' >=> cong (n' +_) (sym *-left-one)))

    p2 : 1/ℕ (2⁺ *⁺ n⁺) ≤ 1/ℕ (suc n , tt)
    p2 = 1/ℕ-flips-≤ _ _ p1

    p3 : (1/2r * (1/ℕ n⁺)) ≤ 1/ℕ (suc n , tt)
    p3 = trans-=-≤ (sym (1/2ℕ-path n⁺)) p2
    p4 : (1/ℕ n⁺) ≤ (ℕ->ℚ 2 * (1/ℕ (suc n , tt)))
    p4 = trans-=-≤ (sym *-left-one >=> *-left (sym 2r-1/2r-path) >=> *-assoc)
                   (*₁-preserves-≤ (ℕ->ℚ-preserves-≤ _ _ zero-≤) p3)

  0≤1-1/n : (n : Nat⁺) -> 0# ≤ (1# + (- (1/ℕ n)))
  0≤1-1/n n = diff-0≤⁺ (1/ℕ≤1 n)


  lemma6 : (n : Nat⁺) -> Σ[ m ∈ Nat⁺ ] ((1# + (- (1/ℕ n))) ℚ^ℕ ⟨ m ⟩) ≤ 1/2r
  lemma6 (zero , ())
  lemma6 (suc zero , _) =
    (1 , tt) , trans-=-≤ (*-right-one >=> +-inverse) (weaken-< Pos-1/2r)
  lemma6 (suc (suc i) , _) = lemma6' i
    where
    lemma6' : (i : Nat) -> Σ[ m ∈ Nat⁺ ] ((1# + (- (1/ℕ (suc (suc i) , tt)))) ℚ^ℕ ⟨ m ⟩) ≤ 1/2r
    lemma6' zero =
      (1 , tt) , path-≤ (*-right-one >=>
                         +-left (sym 1/2r-1/2r-path) >=>
                         +-assoc >=>
                         +-right +-inverse >=>
                         +-right-zero)
    lemma6' i@(suc i') = ((3 , tt) *⁺ m⁺) , p5
      where
      n = suc (suc i)
      n' = suc (suc i')
      n⁺ : Nat⁺
      n⁺ = n , tt
      rec : Σ[ m ∈ Nat⁺ ] ((1# + (- (1/ℕ (n' , tt)))) ℚ^ℕ ⟨ m ⟩) ≤ 1/2r
      rec = lemma6' i'
      m⁺ : Nat⁺
      m⁺ = fst rec
      m = fst m⁺
      p1 = snd rec
      3≤n : 3 ≤ n
      3≤n = suc-≤ (suc-≤ (suc-≤ zero-≤))

      p2 : ((1# + (- (1/ℕ n⁺))) ℚ^ℕ (3 * m)) == ((1# + (- (1/ℕ n⁺))) ℚ^ℕ 3) ℚ^ℕ m
      p2 = ℚ^ℕ⁺-distrib-*₂ (3 , tt) m⁺

      p3 : ((1# + (- (1/ℕ n⁺))) ℚ^ℕ 3) ≤ (1# + (- (1/ℕ (n' , tt))))
      p3 = weaken-< (trans-<-≤ (lemma4 n⁺ 3≤n) (lemma5 (n' , _)) )

      p4 : 0# ≤ ((1# + (- (1/ℕ n⁺))) ℚ^ℕ 3)
      p4 = ℚ^ℕ-preserves-0≤ (0≤1-1/n n⁺) 3

      p5 : ((1# + (- (1/ℕ n⁺))) ℚ^ℕ (3 * m)) ≤ 1/2r
      p5 = trans-≤ (trans-=-≤ p2 (ℚ^ℕ-preserves-≤ p4 p3 m)) p1


  lemma7 : (n : Nat⁺) (ε : ℚ⁺) -> ∃[ m ∈ ℕ ] ((1# + (- (1/ℕ n))) ℚ^ℕ m) < ⟨ ε ⟩
  lemma7 n ε = ∥-map handle (small-1/2^ℕ' ε)
    where
    handle : Σ[ m ∈ Nat⁺ ] ((1/2r r^ℕ⁰ ⟨ m ⟩) < ⟨ ε ⟩) ->
             Σ[ m ∈ ℕ ] ((1# + (- (1/ℕ n))) ℚ^ℕ m) < ⟨ ε ⟩
    handle (m1⁺ , 1/2^m1<ε) =
      ⟨ m2⁺ *⁺ m1⁺ ⟩ ,
      trans-=-< (ℚ^ℕ⁺-distrib-*₂ m2⁺ m1⁺)
                (trans-≤-< (ℚ^ℕ-preserves-≤ (ℚ^ℕ-preserves-0≤ (0≤1-1/n n) m2) (snd Σm2) m1)
                           1/2^m1<ε)
      where
      m1 = fst m1⁺
      Σm2 : Σ[ m ∈ Nat⁺ ] ((1# + (- (1/ℕ n))) ℚ^ℕ ⟨ m ⟩) ≤ 1/2r
      Σm2 = lemma6 n
      m2⁺ = (fst Σm2)
      m2 = fst m2⁺


Archimedean-ℚ' : (ε : ℚ⁺) (q : ℚ) -> 0# ≤ q -> q < 1# -> ∃[ m ∈ ℕ ] (q ℚ^ℕ m) < ⟨ ε ⟩
Archimedean-ℚ' ε q 0≤q q<1 = ∥-bind handle (small-1/ℕ (r , 0<r))
  where
  r = diff q 1#
  0<r : 0# < r
  0<r = diff-0<⁺ q<1

  handle : Σ[ n ∈ Nat⁺ ] (1/ℕ n < r) -> ∃[ m ∈ ℕ ] (q ℚ^ℕ m) < ⟨ ε ⟩
  handle (n , 1/n<r) = ∥-map handle2 (lemma7 n ε)
    where
    1-1/n = diff (1/ℕ n) 1#
    q<1-1/n : q < 1-1/n
    q<1-1/n = trans-=-< (sym diff-step >=> +-right diff-anticommute)
                        (+₁-preserves-< (minus-flips-< 1/n<r))
    q≤1-1/n : q ≤ 1-1/n
    q≤1-1/n = weaken-< q<1-1/n

    handle2 : Σ[ m ∈ ℕ ] ((1# + (- (1/ℕ n))) ℚ^ℕ m) < ⟨ ε ⟩ ->
              Σ[ m ∈ ℕ ] (q ℚ^ℕ m) < ⟨ ε ⟩
    handle2 (m , 1-1/n^m<ε) =
      m , trans-≤-< (ℚ^ℕ-preserves-≤ 0≤q q≤1-1/n m) 1-1/n^m<ε





module _ (x : ℝ) (0≤x : 0# ≤ x) (x<1 : x < 1#) where
  private
    x≤1 : x ≤ 1#
    x≤1 = weaken-< x<1
    0<1-x : 0# < (1# + - x)
    0<1-x = diff-0<⁺ x<1
    1-x#0 : (1# + - x) # 0#
    1-x#0 = inj-r 0<1-x
    isUnit-1-x = Field.#0->isUnit ℝField 1-x#0
    y : ℝ
    y = ℝ1/ (diff x 1#) 1-x#0
    y-path : (1# + (- x)) * y == 1#
    y-path = *-commute >=> ℝ1/-inverse (diff x 1#) 1-x#0

  isLimit-geometric-sequence : isLimit (geometric-sequence x) 0#
  isLimit-geometric-sequence = εBounded-diff->isLimit f
    where
    f : (ε : ℚ⁺) -> ∀Largeℕ (\n -> εBounded ⟨ ε ⟩ (diff 0# (geometric-sequence x n)))
    f (ε , 0<ε) = ∥-bind handle (Real.isLowerOpen-U x 1# (ℝ<->U x<1))
      where
      -ε<0 : (- ε) < 0#
      -ε<0 = minus-flips-0< 0<ε
      handle : Σ[ q ∈ ℚ ] (q < 1# × Real.U x q) ->
               ∀Largeℕ (\n -> εBounded ε (diff 0# (geometric-sequence x n)))
      handle (q , (q<1 , xU-q)) = ∥-bind handle2 (Archimedean-ℚ' (ε , 0<ε) q (weaken-< 0<q) q<1)
        where
        x<q : x < ℚ->ℝ q
        x<q = U->ℝ< xU-q
        0<q : 0# < q
        0<q = U->ℚ< (trans-ℝ≤-U 0≤x xU-q)
        0≤q = weaken-< (ℚ->ℝ-preserves-< _ _ 0<q)
        q≤1 = weaken-< (ℚ->ℝ-preserves-< _ _ q<1)
        handle2 : Σ[ m ∈ ℕ ] (q ℚ^ℕ m) < ε ->
                  ∀Largeℕ (\n -> εBounded ε (diff 0# (geometric-sequence x n)))
        handle2 (m , q^m<ε) = ∣ m , g ∣
          where
          g : (n : ℕ) -> m ≤ n -> εBounded ε (diff 0# (geometric-sequence x n))
          g n m≤n = subst (εBounded ε) (sym diff-step >=> +-left-zero)
                      (ℝ<->L (trans-<-≤ (ℚ->ℝ-preserves-< _ _ -ε<0)
                                        (geometric-sequence-0≤ 0≤x n)) ,
                       ℝ<->U (trans-≤-<
                               (trans-≤-=
                                 (trans-≤ (ℝ^ℕ-preserves-≤ 0≤x (weaken-< x<q) n)
                                          (geometric-sequence-≤1 0≤q q≤1 m n m≤n))
                                 (sym (ℚ^ℕ-ℝ^ℕ-path m)))
                               (ℚ->ℝ-preserves-< _ _ q^m<ε)))


  isLimit-geometric-series : isLimit (geometric-series x) y
  isLimit-geometric-series =
    subst2 isLimit
      (sym (funExt gs-path')) (*-left (+-right minus-zero >=> +-right-zero) >=> *-left-one)
      (*-preserves-limit (+-preserves-limit
                           (isLimit-constant-seq 1#)
                           (minus-preserves-limit isLimit-geometric-sequence))
                         (isLimit-constant-seq y))
    where
    gs-path' : (n : ℕ) -> geometric-series x n == (1# + (- geometric-sequence x n)) * y
    gs-path' n =
      sym *-right-one >=>
      *-right (sym y-path) >=>
      sym *-assoc >=>
      *-left (geometric-series-path x n)

  isConvergentSeries-geometric-sequence : isConvergentSeries (geometric-sequence x)
  isConvergentSeries-geometric-sequence = y , isLimit-geometric-series
