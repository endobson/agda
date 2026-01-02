{-# OPTIONS --cubical --safe --exact-split #-}

module real.series.geometric where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import finset.instances
open import finsum.arithmetic
open import functions
open import funext
open import heyting-field
open import heyting-field.instances.rational
open import heyting-field.instances.real
open import nat
open import nat.order
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.nat
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-field.archimedean
open import ordered-ring.exponentiation
open import ordered-semiring
open import ordered-semiring.archimedean
open import ordered-semiring.archimedean.instances.rational
open import ordered-semiring.exponentiation
open import ordered-semiring.initial
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational hiding (1/ℕ ; 1/ℕ-distrib-*)
open import rational.order hiding (1/ℕ-flips-≤)
open import real
open import real.arithmetic.multiplication.inverse
open import real.arithmetic.multiplication.inverse.order
open import real.arithmetic.rational
open import real.epsilon-bounded
open import real.order
open import real.rational
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.sequence.limit.zero
open import real.series
open import real.subspace
open import ring
open import ring.implementations.rational
open import ring.implementations.real
open import ring.solver-equations
open import semiring
open import semiring.exponentiation
open import semiring.initial
open import semiring.instances.nat
open import sequence
open import sequence.partial-sums
open import subset.subspace
open import truncation

private
  Seq : Type₁
  Seq = Sequence ℝ

-- TODO make this named ^ℕ
geometric-sequence : ℝ -> Seq
geometric-sequence = _^ℕ_

ℚ^ℕ-ℝ^ℕ-path : {q : ℚ} (n : ℕ) -> ℚ->ℝ (q ^ℕ n) == (ℚ->ℝ q) ^ℕ n
ℚ^ℕ-ℝ^ℕ-path zero = refl
ℚ^ℕ-ℝ^ℕ-path (suc n) =
  ℚ->ℝ-preserves-* >=> *-right (ℚ^ℕ-ℝ^ℕ-path n)

geometric-sequence-1 : (n : ℕ) -> geometric-sequence 1# n == 1#
geometric-sequence-1 zero = refl
geometric-sequence-1 (suc n) = *-left-one >=> geometric-sequence-1 n

geometric-sequence-0≤ : {x : ℝ} -> 0# ≤ x -> (n : ℕ) -> 0# ≤ geometric-sequence x n
geometric-sequence-0≤ = ^ℕ-preserves-0≤

geometric-sequence-0< : {x : ℝ} -> 0# < x -> (n : ℕ) -> 0# < geometric-sequence x n
geometric-sequence-0< = ^ℕ-preserves-0<

geometric-sequence-≤ : {x y : ℝ} -> 0# ≤ x -> x ≤ y -> (n : ℕ) ->
                       (geometric-sequence x n) ≤ (geometric-sequence y n)
geometric-sequence-≤ 0≤x x≤y n = ^ℕ-0≤-preserves-≤ 0≤x n x≤y

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

geometric-sequence-<1 : {x : ℝ} -> 0# < x -> x < 1# -> {m n : ℕ} -> m < n ->
                        (geometric-sequence x n) < (geometric-sequence x m)
geometric-sequence-<1 {x} 0<x x<1 {m} {n} (i , p) =
  trans-=-< p1 (trans-<-= (*₂-preserves-< p2 (^ℕ-preserves-0< 0<x m)) *-left-one)
  where
  p1 : geometric-sequence x n == (x ^ℕ (suc i)) * (x ^ℕ m)
  p1 = cong (geometric-sequence x) (sym p >=> +'-right-suc) >=>
       ^ℕ-distrib-+-left (suc i) m

  p2 : (x ^ℕ suc i) < 1#
  p2 = trans-<-≤ (*₂-preserves-< x<1 (^ℕ-preserves-0< 0<x i))
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
  opaque
    lemma1 : (n : ℕ) -> 3 ≤ n -> 0# < (((ℕ->ℚ n * ℕ->ℚ n) +
                                        (- ((ℕ->ℚ 3) * (ℕ->ℚ n)))) + 1#)
    lemma1 n 3≤n = trans-≤-< 0≤n²-3n (trans-=-< (sym +-right-zero) (+₁-preserves-< 0<1))
      where
      0≤n²-3n : 0# ≤ ((ℕ->ℚ n * ℕ->ℚ n) + (- ((ℕ->ℚ 3) * (ℕ->ℚ n))))
      0≤n²-3n =
        trans-≤-=
          (*-preserves-0≤ (diff-0≤⁺ (ℕ->Semiring-preserves-≤ 3≤n))
                          (ℕ->Semiring-preserves-0≤ zero-≤))
          (*-distrib-+-right >=> +-right minus-extract-left)

  opaque
    lemma2 : (n : Nat⁺) -> 3 ≤ ⟨ n ⟩ -> 0# < (1# + (- ((ℕ->ℚ 3) * 1/ℕ n)) + (1/ℕ n * 1/ℕ n))
    lemma2 n 3≤n =
      trans-<-= (*-preserves-0< (lemma1 n' 3≤n) (*-preserves-0< (0<1/ℕ n) (0<1/ℕ n))) p4
      where
      n' : ℕ
      n' = ⟨ n ⟩
      n-inv : ℕ->ℚ n' * 1/ℕ n == 1#
      n-inv = ∃!-prop (∃!1/ℕ n)

      p1 : (ℕ->ℚ n' * ℕ->ℚ n') * (1/ℕ n * 1/ℕ n) == 1#
      p1 = *-swap >=>
           *-cong n-inv n-inv >=>
           *-right-one

      p2 : (- ((ℕ->ℚ 3) * ℕ->ℚ n')) * (1/ℕ n * 1/ℕ n) == (- ((ℕ->ℚ 3) * 1/ℕ n))
      p2 = minus-extract-left >=>
           cong -_ (*-swap >=> *-right n-inv >=> *-right-one)

      p3 : Path ℚ (1# * (1/ℕ n * 1/ℕ n)) (1/ℕ n * 1/ℕ n)
      p3 = *-left-one

      p4 : (((ℕ->ℚ n' * ℕ->ℚ n') + (- ((ℕ->ℚ 3) * (ℕ->ℚ n')))) + 1#) * (1/ℕ n * 1/ℕ n) ==
           (1# + (- ((ℕ->ℚ 3) * 1/ℕ n)) + (1/ℕ n * 1/ℕ n))
      p4 = *-distrib-+-right >=> +-cong (*-distrib-+-right >=> +-cong p1 p2) p3

  opaque
    lemma3 : (n : Nat⁺) ->
      (1# + (- (1/ℕ n))) ^ℕ 3 ==
      (1# + (- ((ℕ->ℚ 2) * 1/ℕ n))) +
      (1# + (- ((ℕ->ℚ 3) * 1/ℕ n)) + (1/ℕ n * 1/ℕ n)) * (- (1/ℕ n))
    lemma3 n = [1-x]^3-expand (1/ℕ n)

  α : Nat⁺ -> ℚ
  α n = 1# + (- (1/ℕ n))

  0≤αn : (n : Nat⁺) -> 0# ≤ (α n)
  0≤αn n = diff-0≤⁺ (trans-≤-= (1/ℕ-flips-≤ 1⁺ n (Pos'->< (snd n))) 1/1-path)

  opaque
    lemma4 : (n : Nat⁺) -> 3 ≤ ⟨ n ⟩ -> (α n ^ℕ 3) < (1# + (- (2# * 1/ℕ n)))
    lemma4 n 3≤n =
      trans-=-< (lemma3 n) (trans-<-= (+₁-preserves-< (*₂-flips-< (lemma2 n 3≤n)
                                                                  (minus-flips-0< (0<1/ℕ n))))
                                      (+-right *-left-zero >=> +-right-zero >=>
                                       +-right (cong -_ (*-left ℕ->Semiring-preserves-2#))))


  opaque
    lemma5 : (n : Nat⁺) -> (1# + (- (2# * 1/ℕ (suc ⟨ n ⟩ , tt)))) ≤ α n
    lemma5 n⁺@(suc n' , _) = +₁-preserves-≤ (minus-flips-≤ p3)
      where
      module _ where
        n : Nat
        n = ⟨ n⁺ ⟩
        p1 : suc n ≤ (2 * n)
        p1 = suc-≤ (trans-≤-= (suc-≤ (trans-=-≤ (sym +-right-zero) (+₁-preserves-≤ zero-≤)))
                              (+-commuteᵉ (suc n') n' >=> cong (n' +_) (sym *-left-one)))

        p2 : (1/2 * (1/ℕ n⁺)) ≤ 1/ℕ (suc n , tt)
        p2 = trans-=-≤ (sym (1/ℕ-distrib-* 2⁺ n⁺)) (1/ℕ-flips-≤ _ _ p1)
        p3 : (1/ℕ n⁺) ≤ (2# * (1/ℕ (suc n , tt)))
        p3 = trans-=-≤ (sym *-left-one >=> *-left (sym 2*1/2-path) >=> *-assoc)
                       (*₁-preserves-≤ (weaken-< 0<2) p2)



  opaque
    lemma6 : (n : Nat⁺) -> Σ[ m ∈ Nat⁺ ] (α n ^ℕ ⟨ m ⟩) ≤ 1/2
    lemma6 (zero , ())
    lemma6 (suc zero , _) =
      (1 , tt) , trans-=-≤ (^ℕ-one >=> (+-right (cong -_ 1/1-path)) >=> +-inverse)
                           (weaken-< 0<1/2)
    lemma6 (suc (suc i) , _) = lemma6' i
      where
      lemma6' : (i : Nat) -> Σ[ m ∈ Nat⁺ ] (α (suc (suc i) , tt) ^ℕ ⟨ m ⟩) ≤ 1/2
      lemma6' zero =
        (1 , tt) , path-≤ (*-right-one >=>
                           +-left (sym 1/2-+-path) >=>
                           +-assoc >=>
                           +-right +-inverse >=>
                           +-right-zero)
      lemma6' i@(suc i') = ((3 , tt) *⁺ m⁺) , p5
        where
        n n' : Nat
        n = suc (suc i)
        n' = suc (suc i')
        n⁺ : Nat⁺
        n⁺ = n , tt
        rec : Σ[ m ∈ Nat⁺ ] (α (n' , tt) ^ℕ ⟨ m ⟩) ≤ 1/2
        rec = lemma6' i'
        m⁺ : Nat⁺
        m⁺ = fst rec
        m : ℕ
        m = fst m⁺
        p1 : (α (n' , tt) ^ℕ m) ≤ 1/2
        p1 = snd rec
        3≤n : 3 ≤ n
        3≤n = suc-≤ (suc-≤ (suc-≤ zero-≤))

        p2 : (α n⁺ ^ℕ (3 * m)) == ((α n⁺) ^ℕ 3) ^ℕ m
        p2 = ^ℕ-distrib-*-left {x = (1# + (- (1/ℕ n⁺)))} 3 m

        p3 : (α n⁺ ^ℕ 3) ≤ (α (n' , tt))
        p3 = weaken-< (trans-<-≤ (lemma4 n⁺ 3≤n) (lemma5 (n' , _)) )

        p4 : 0# ≤ (α n⁺ ^ℕ 3)
        p4 = ^ℕ-preserves-0≤ (0≤αn n⁺) 3

        p5 : (α n⁺ ^ℕ (3 * m)) ≤ 1/2
        p5 = trans-≤ (trans-=-≤ p2 (^ℕ-0≤-preserves-≤ p4 m p3)) p1


  opaque
    lemma7 : (n : Nat⁺) (ε : ℚ⁺) -> ∃[ m ∈ ℕ ] (α n ^ℕ m) < ⟨ ε ⟩
    lemma7 n ε = ∥-map handle (small-1/2^ℕ ε)
      where
      handle : Σ[ m ∈ Nat ] ((1/2 ^ℕ m) < ⟨ ε ⟩) ->
               Σ[ m ∈ ℕ ] ((1# + (- (1/ℕ n))) ^ℕ m) < ⟨ ε ⟩
      handle (m1 , 1/2^m1<ε) =
        m2 * m1 ,
        trans-=-< (^ℕ-distrib-*-left m2 m1)
                  (trans-≤-< (^ℕ-0≤-preserves-≤ (^ℕ-preserves-0≤ (0≤αn n) m2) m1 (snd Σm2))
                             1/2^m1<ε)
        where
        Σm2 : Σ[ m ∈ Nat⁺ ] (α n ^ℕ ⟨ m ⟩) ≤ 1/2
        Σm2 = lemma6 n
        m2 : ℕ
        m2 = fst (fst Σm2)

Archimedean-ℚ' : (ε : ℚ⁺) (q : ℚ) -> 0# ≤ q -> q < 1# -> ∃[ m ∈ ℕ ] (q ^ℕ m) < ⟨ ε ⟩
Archimedean-ℚ' ε q 0≤q q<1 = ∥-bind handle (small-1/ℕ (r , 0<r))
  where
  r = diff q 1#
  0<r : 0# < r
  0<r = diff-0<⁺ q<1

  handle : Σ[ n ∈ Nat⁺ ] (1/ℕ n < r) -> ∃[ m ∈ ℕ ] (q ^ℕ m) < ⟨ ε ⟩
  handle (n , 1/n<r) = ∥-map handle2 (lemma7 n ε)
    where
    1-1/n = diff (1/ℕ n) 1#
    q<1-1/n : q < 1-1/n
    q<1-1/n = trans-=-< (sym diff-step >=> +-right diff-anticommute)
                        (+₁-preserves-< (minus-flips-< 1/n<r))
    q≤1-1/n : q ≤ 1-1/n
    q≤1-1/n = weaken-< q<1-1/n

    handle2 : Σ[ m ∈ ℕ ] ((1# + (- (1/ℕ n))) ^ℕ m) < ⟨ ε ⟩ ->
              Σ[ m ∈ ℕ ] (q ^ℕ m) < ⟨ ε ⟩
    handle2 (m , 1-1/n^m<ε) =
      m , trans-≤-< (^ℕ-0≤-preserves-≤ 0≤q m q≤1-1/n) 1-1/n^m<ε


module _ ((x , ax<1) : ∣ℝ∣< 1#) where
  private
    ∀Largeℕ-abs-geometric-sequence<ε-ℚ :
      ((ε , _) : ℚ⁺) -> ∀Largeℕ (\i -> (abs (geometric-sequence x i)) < ℚ->ℝ ε)
    ∀Largeℕ-abs-geometric-sequence<ε-ℚ ε⁺@(ε , _) =
      ∥-bind handle (Real.isLowerOpen-U (abs x) 1# (ℝ<->U ax<1))
      where
      handle : Σ[ q ∈ ℚ ] (q < 1# × Real.U (abs x) q) ->
               ∀Largeℕ (\i -> (abs (geometric-sequence x i)) < ℚ->ℝ ε)
      handle (q , q<1 , axU-q) = ∥-bind handle2 (Archimedean-ℚ' ε⁺ q (weaken-< 0<q) q<1)
        where
        0<q : 0# < q
        0<q = U->ℚ< (trans-ℝ≤-U abs-0≤ axU-q)
        handle2 : Σ[ n ∈ ℕ ] (q ^ℕ n) < ε ->
                  ∀Largeℕ (\i -> (abs (geometric-sequence x i)) < ℚ->ℝ ε)
        handle2 (n , q^n<ε) = ∣ n , lt ∣
          where
          lt : (m : ℕ) -> n ≤ m -> (abs (geometric-sequence x m)) < ℚ->ℝ ε
          lt m n≤m =
            trans-≤-<
              (trans-=-≤ (abs-^ℕ-path m)
                (trans-≤
                  (geometric-sequence-≤1 abs-0≤ (weaken-< ax<1) n m n≤m)
                  (^ℕ-0≤-preserves-≤ abs-0≤ n (weaken-< (U->ℝ< axU-q)))))
              (trans-=-<
                (sym (Semiringʰ-preserves-^ℕ Semiringʰ-ℚ->ℝ n))
                (ℚ->ℝ-preserves-< q^n<ε))

    ∀Largeℕ-abs-geometric-sequence<ε :
      ((ε , _) : ℝ⁺) -> ∀Largeℕ (\i -> (abs (geometric-sequence x i)) < ε)
    ∀Largeℕ-abs-geometric-sequence<ε (ε , 0<ε) = ∥-bind handle 0<ε
      where
      handle : 0# ℝ<' ε -> ∀Largeℕ (\i -> (abs (geometric-sequence x i)) < ε)
      handle (ℝ<'-cons x 0U-x εL-x) =
        ∀Largeℕ-map (\s<x -> trans-< s<x (L->ℝ< εL-x))
          (∀Largeℕ-abs-geometric-sequence<ε-ℚ (x , U->ℚ< 0U-x))

  opaque
    isLimit-geometric-sequence : isLimit (geometric-sequence x) 0#
    isLimit-geometric-sequence = abs<ε->isLimit0 ∀Largeℕ-abs-geometric-sequence<ε


  private
    0<1-x : 0# < (1# + - x)
    0<1-x = diff-0<⁺ (trans-≤-< abs-≤ ax<1)
    1-x#0 : (1# + - x) # 0#
    1-x#0 = inj-r 0<1-x

  opaque
    geometric-series-limit : ℝ
    geometric-series-limit = ℝ1/ (diff x 1# , 1-x#0)

    geometric-series-limit-path : geometric-series-limit * (diff x 1#) == 1#
    geometric-series-limit-path = ℝ1/-inverse


    isLimit-geometric-series : isLimit (geometric-series x) geometric-series-limit
    isLimit-geometric-series =
      subst2 isLimit
        (sym (funExt gs-path')) (*-left (+-right minus-zero >=> +-right-zero) >=> *-left-one)
        (*-preserves-limit (+-preserves-limit
                             (isLimit-constant-seq 1#)
                             (minus-preserves-limit isLimit-geometric-sequence))
                           (isLimit-constant-seq geometric-series-limit))
      where
      gs-path' : (n : ℕ) -> geometric-series x n ==
                            (1# + (- geometric-sequence x n)) * geometric-series-limit
      gs-path' n =
        sym *-right-one >=>
        *-right (sym (*-commute >=> geometric-series-limit-path)) >=>
        sym *-assoc >=>
        *-left (geometric-series-path x n)

  isConvergentSeries-geometric-sequence : isConvergentSeries (geometric-sequence x)
  isConvergentSeries-geometric-sequence = geometric-series-limit , isLimit-geometric-series

opaque
  unfolding geometric-series-limit

  geometric-series-limit-preserves-≤ :
    {x∈@(x , _) y∈@(y , _) : ∣ℝ∣< 1#} -> x ≤ y ->
    geometric-series-limit x∈ ≤ geometric-series-limit y∈
  geometric-series-limit-preserves-≤ {x , _} {y , ay<1} x≤y =
    ℝ1/⁺-flips-≤ 0<1-y (+₁-preserves-≤ (minus-flips-≤ x≤y))
    where
    0<1-y : 0# < diff y 1#
    0<1-y = diff-0<⁺ (trans-≤-< abs-≤ ay<1)

  geometric-series-limit-0< : ∀ {x} -> 0# < geometric-series-limit x
  geometric-series-limit-0< {x , ax<1} = ℝ1/-preserves-0< 0<1-x
    where
    0<1-x : 0# < diff x 1#
    0<1-x = diff-0<⁺ (trans-≤-< abs-≤ ax<1)


module _ ((x , ax<1) : ∣ℝ∣< 1#) where
  opaque
    isAbsConvergentSeries-geometric-sequence : isAbsConvergentSeries (geometric-sequence x)
    isAbsConvergentSeries-geometric-sequence =
      subst isConvergentSeries (funExt (\n -> sym (abs-^ℕ-path n)))
        (isConvergentSeries-geometric-sequence (abs x , (trans-=-< (abs-0≤-path abs-0≤) ax<1)))
