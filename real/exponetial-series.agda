{-# OPTIONS --cubical --safe --exact-split #-}

module real.exponetial-series where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.reader
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import factorial
open import fin
open import finite-commutative-monoid.instances
open import finset.instances
open import finsum
open import finsum.arithmetic
open import functions
open import funext
open import heyting-field
open import hlevel
open import integral-domain.instances.real
open import nat
open import nat.order
open import order
open import order.minmax
open import order.minmax.instances.nat
open import order.minmax.instances.real
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.nat
open import ordered-additive-group.instances.real
open import ordered-integral-domain
open import ordered-ring
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.instances.nat
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import rational.heyting-field
open import rational.integral-domain
open import rational.order
open import rational.proper-interval
open import real
open import real.arithmetic
open import real.arithmetic.rational
open import real.epsilon-bounded.base
open import real.heyting-field
open import real.interval
open import real.order
open import real.rational
open import real.sequence
open import real.sequence.cauchy
open import real.sequence.limit
open import real.series
open import relation
open import ring
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import sequence
open import sequence.drop
open import sequence.partial-sums
open import truncation

private
  Seq : Type₁
  Seq = Sequence ℝ

  exponential-sequence1 : Seq
  exponential-sequence1 n = ℚ->ℝ (1/ℕ (factorial⁺ n))

  exponential-series1 : Seq
  exponential-series1 = partial-sums exponential-sequence1

  2ℝ : ℝ
  2ℝ = 1# + 1#


  module _  {ℓ : Level} {D : Type ℓ}
            {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} where
    areInverses : D -> D -> Type ℓ
    areInverses x y = x * y == 1#

    isProp-areInverses : {x y : D} -> isProp (areInverses x y)
    isProp-areInverses = Semiring.isSet-Domain S _ _


  inverse-preserves-0< : {a b : ℚ} -> areInverses a b -> 0# < a -> 0# < b
  inverse-preserves-0< ab=1 0<a = *₁-reflects-0< (asym-< 0<a) (subst (0# <_) (sym ab=1) 0<1)

  inverse-flips-< : {a b c d : ℚ} -> areInverses a b -> areInverses c d ->
                    0# < a -> 0# < c -> a < c -> d < b
  inverse-flips-< ab=1 cd=1 0<a 0<c a<c =
    subst2 _<_ (*-right ab=1 >=> *-right-one)
               (sym *-assoc >=> *-left (*-commute >=> cd=1) >=> *-left-one)
           (*₁-preserves-< 0<d (*₂-preserves-< a<c 0<b))
    where
    0<b = inverse-preserves-0< ab=1 0<a
    0<d = inverse-preserves-0< cd=1 0<c

  drop-preserves-limit :
    {s : Seq} {v : ℝ} -> (n : ℕ) -> isLimit s v -> isLimit (drop n s) v
  drop-preserves-limit {s} {v} zero    l = l
  drop-preserves-limit {s} {v} (suc n) l =
    close->isLimit handle
    where
    handle : (qi : Iℚ) -> ℝ∈Iℚ v qi -> ∃[ n2 ∈ ℕ ] ((m : ℕ) -> m ≥ n2 -> ℝ∈Iℚ (drop (suc n) s m) qi)
    handle qi v∈qi = ∥-map handle2 (isLimit.close (drop-preserves-limit n l) qi v∈qi)
      where
      handle2 : Σ[ n2 ∈ ℕ ] ((m : ℕ) -> m ≥ n2 -> ℝ∈Iℚ (drop n s m) qi) ->
                Σ[ n2 ∈ ℕ ] ((m : ℕ) -> m ≥ n2 -> ℝ∈Iℚ (drop (suc n) s m) qi)
      handle2 (n2 , f) = (n2 , g)
        where
        g : (m : ℕ) -> m ≥ n2 -> ℝ∈Iℚ (drop (suc n) s m) qi
        g m m≥n2 = f (suc m) (right-suc-≤ m≥n2)

  -- isInfiniteSum-cons :
  --   {s : Seq} {v : ℝ} -> (x : ℝ) -> isInfiniteSum s v ->
  --   isInfiniteSum (seq-cons x s) (x + v)
  -- isInfiniteSum-cons = ?


  partial-sums-drop1 : (s : Seq) (n : ℕ) ->
    partial-sums (drop 1 s) n == partial-sums s (suc n) + - s zero
  partial-sums-drop1 s n =
    sym +-right-zero >=>
    +-right (sym +-inverse) >=>
    sym +-assoc >=>
    +-left (+-commute >=> sym p >=> (\i -> partial-sums (s'=s i) (suc n)))
    where
    s' = seq-cons (s zero) (s ∘ suc)
    s'=s : s' == s
    s'=s = funExt (\{ zero -> refl ; (suc n) -> refl })
    p : partial-sums s' (suc n) == (s zero) + partial-sums (s ∘ suc) n
    p = partial-sums-cons (s zero) (s ∘ suc) n



  isInfiniteSum-drop1 :
    {s : Seq} {v : ℝ} -> isInfiniteSum s v ->
    isInfiniteSum (drop 1 s) (v + - (s zero))
  isInfiniteSum-drop1 {s} {v} sum1 =
    subst (\r -> isLimit r (v + - (s zero))) (funExt p1) l4
    where
    l1 : isLimit (partial-sums s) v
    l1 = sum1
    l2 : isLimit (constant-seq (- (s zero))) (- (s zero))
    l2 = isLimit-constant-seq _
    l3 : isLimit (\n -> partial-sums s n + - s zero) (v + - (s zero))
    l3 = +-preserves-limit l1 l2
    l4 : isLimit (\n -> partial-sums s (suc n) + - s zero) (v + - (s zero))
    l4 = drop-preserves-limit 1 l3
    p1 : (n : ℕ) -> partial-sums s (suc n) + - s zero == partial-sums (drop 1 s) n
    p1 n = sym (partial-sums-drop1 s n)

  drop-suc : (m : ℕ) (s : Seq) -> (drop (suc m) s) == drop m (s ∘ suc)
  drop-suc zero    s = refl
  drop-suc (suc n) s = cong (_∘ suc) (drop-suc n s)


  drop-+ : (m n : ℕ) (s : Seq) -> (drop m s n) == s (m +' n)
  drop-+ zero    n s = refl
  drop-+ (suc m) n s = (drop-+ m (suc n) s) >=> cong s +'-right-suc


  partial-sums-drop : (s : Seq) (n m : ℕ) ->
    partial-sums (drop n s) m == partial-sums s (n + m) + - partial-sums s n
  partial-sums-drop s n zero =
    finiteMerge-Fin0 _ _ >=>
    sym (+-left (cong (partial-sums s) +-right-zero) >=> +-inverse)
  partial-sums-drop s n (suc m) = ans
    where
    ans : partial-sums (drop n s) (suc m) == partial-sums s (n + (suc m)) + - partial-sums s n
    ans =
      finiteMerge-FinSuc _ _ >=>
      +-cong (drop-+ n zero s) (partial-sums-drop s (suc n) m) >=>
      +-right +-commute >=>
      sym +-assoc >=>
      +-commute >=>
      +-cong
        (cong (partial-sums s) (sym +'-right-suc))
        (+-left (sym minus-double-inverse) >=>
         sym minus-distrib-plus >=>
         cong -_ (+-commute >=>
                  +-left (partial-sums-split s n >=> +-commute) >=>
                  +-assoc >=>
                  +-right (+-right (cong -_ (cong s +-right-zero)) >=> +-inverse) >=>
                  +-right-zero))

  isInfiniteSum-drop :
    {s : Seq} {v : ℝ} -> (n : ℕ) -> isInfiniteSum s v ->
    isInfiniteSum (drop n s) (v + - (partial-sums s n))
  isInfiniteSum-drop {s} {v} zero = subst (isInfiniteSum s) path
    where
    path = sym +-right-zero >=>
           +-right (sym minus-zero >=>
                    cong -_ (sym (finiteMerge-Fin0 _ _)))
  isInfiniteSum-drop {s} {v} (suc n) sum1 =
    subst (isInfiniteSum (drop (suc n) s)) p2 sum3
    where
    sum2 : isInfiniteSum (drop n s) (v + - (partial-sums s n))
    sum2 = isInfiniteSum-drop n sum1

    sum3 : isInfiniteSum (drop (suc n) s) ((v + - (partial-sums s n)) + - (drop n s zero))
    sum3 = isInfiniteSum-drop1 sum2

    p1 : (drop n s zero) == s n
    p1 = drop-+ n zero s >=> cong s (+'-commute {n} {zero})

    p2 : ((v + - (partial-sums s n)) + - (drop n s zero)) ==
         (v + - (partial-sums s (suc n)))
    p2 = +-assoc >=>
         +-right (sym minus-distrib-plus >=>
                  cong -_ (+-right p1 >=> +-commute >=> (sym (partial-sums-split s n))))



  isCauchy' : Pred Seq ℓ-one
  isCauchy' s = (ε : ℚ⁺) -> ∃[ n ∈ Nat ] ((m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                                        (diff (s m₁) (s m₂)) < ℚ->ℝ ⟨ ε ⟩)

  isCauchy'->isCauchy : {s : Seq} -> isCauchy' s -> isCauchy s
  isCauchy'->isCauchy {s} f ε = ∥-map handle (f ε)
    where
    handle : Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                           (diff (s m₁) (s m₂)) < ℚ->ℝ ⟨ ε ⟩) ->
             Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                           εBounded ⟨ ε ⟩ (diff (s m₁) (s m₂)))
    handle (n , g) = (n , g2)
      where
      g2 : (m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n -> εBounded ⟨ ε ⟩ (diff (s m₁) (s m₂))
      g2 m₁ m₂ m₁≥n m₂≥n =
        ℝ<->L (subst2 _<_ (sym ℚ->ℝ-preserves--) (sym diff-anticommute)
                      (minus-flips-< (g m₂ m₁ m₂≥n m₁≥n))) ,
        ℝ<->U (g m₁ m₂ m₁≥n m₂≥n)

  ∀Largeℕ2' : {ℓ : Level} -> ((m1 m2 : ℕ) -> Type ℓ) -> Type ℓ
  ∀Largeℕ2' P = Σ[ n ∈ ℕ ] ((m1 m2 : ℕ) -> m1 ≥ n -> m2 ≥ n -> P m1 m2)

  EventuallyClose0-abs : Pred Seq ℓ-one
  EventuallyClose0-abs s = (ε : ℚ⁺) -> ∀Largeℕ (\m -> abs (s m) < ℚ->ℝ ⟨ ε ⟩)

  1/2r⁺ : ℚ⁺
  1/2r⁺ = 1/2r , Pos-1/ℕ (2 , tt)

  module _
    (abs-distrib-+ : {x y : ℝ} -> abs (x + y) ≤ (abs x + abs y))
    (abs-≤ : {x : ℝ} -> x ≤ abs x)
    where
    EventuallyClose0-abs->Cauchy' :
      (s : Seq) -> EventuallyClose0-abs s -> isCauchy' s
    EventuallyClose0-abs->Cauchy' s f (ε , 0<ε) = ∥-map handle (f ε/2)
      where
      ε/2 : ℚ⁺
      ε/2 = 1/2r * ε , *-preserves-0< (snd 1/2r⁺) 0<ε
      handle : ∀Largeℕ' (\m -> abs (s m) < ℚ->ℝ ⟨ ε/2 ⟩) ->
               ∀Largeℕ2' (\m1 m2 -> (diff (s m1) (s m2) < ℚ->ℝ ε))
      handle (n , g) = (n , g2)
        where
        g2 : (m1 m2 : ℕ) -> m1 ≥ n -> m2 ≥ n -> (diff (s m1) (s m2) < ℚ->ℝ ε)
        g2 m1 m2 m1≥n m2≥n = d<ε
          where
          -sm1<ε/2 : abs (- (s m1)) < ℚ->ℝ ⟨ ε/2 ⟩
          -sm1<ε/2 = subst2 _<_ (sym abs-minus) refl (g m1 m1≥n)
          sm2<ε/2 : abs (s m2) < ℚ->ℝ ⟨ ε/2 ⟩
          sm2<ε/2 = g m2 m2≥n
          d<ε : (diff (s m1) (s m2)) < ℚ->ℝ ε
          d<ε =
            trans-≤-<
              (trans-≤ abs-≤ abs-distrib-+)
              (subst2 _<_ refl (sym ℚ->ℝ-preserves-+ >=>
                                cong ℚ->ℝ (1/2r-path' ε))
                     (+-preserves-< sm2<ε/2 -sm1<ε/2))

  bound-partial-sums :
    (s1 s2 : Seq) ->
    ∀Largeℕ (\m -> s1 m ≤ s2 m) ->
    ∃[ n ∈ ℕ ] (∀Largeℕ' (\m -> partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m))
  bound-partial-sums s1 s2 = ∥-map handle
    where
    handle : ∀Largeℕ' (\m -> s1 m ≤ s2 m) ->
             Σ[ n ∈ ℕ ] (∀Largeℕ' (\m -> partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m))
    handle (n , f) = n , 0# , f4
      where
      f4 : (m : ℕ) -> m ≥ 0# -> partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m
      f4 zero m≥0 =
        subst2 _≤_
               (finiteMerge-Fin0 _ _ >=>
                sym (finiteMerge-Fin0 _ _))
               refl refl-≤
      f4 (suc m) m≥0 =
        subst2 _≤_ (sym p1) (sym p2) (+-preserves-≤ lt-e (f4 m zero-≤))
        where
        p1 : partial-sums (drop n s1) (suc m) == s1 (n + m) + partial-sums (drop n s1) m
        p1 = partial-sums-split (drop n s1) m >=> +-left (drop-+ n m s1)
        p2 : partial-sums (drop n s2) (suc m) == s2 (n + m) + partial-sums (drop n s2) m
        p2 = partial-sums-split (drop n s2) m >=> +-left (drop-+ n m s2)
        lt-e : s1 (n + m) ≤ s2 (n + m)
        lt-e = f (n + m) (subst2 _≤_ +-right-zero refl (+-preserves-≤ refl-≤ zero-≤))

  bound-partial-sums' :
    (s1 s2 : Seq) ->
    ∀Largeℕ (\m -> s1 m ≤ s2 m) ->
    ∃[ n₀ ∈ ℕ ] Σ[ m₀ ∈ ℕ ] ((n m : ℕ) -> n ≥ n₀ -> m ≥ m₀ ->
                             partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m)
  bound-partial-sums' s1 s2 = ∥-map handle
    where
    handle : ∀Largeℕ' (\m -> s1 m ≤ s2 m) ->
             Σ[ n₀ ∈ ℕ ] Σ[ m₀ ∈ ℕ ] ((n m : ℕ) -> n ≥ n₀ -> m ≥ m₀ ->
                                      partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m)
    handle (n₀ , f) = n₀ , 0 , f2
      where
      f2 : (n m : ℕ) -> n ≥ n₀ -> m ≥ 0 ->
           partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m
      f2 n zero n≥n₀ _ =
        subst2 _≤_
               (finiteMerge-Fin0 _ _ >=>
                sym (finiteMerge-Fin0 _ _))
               refl refl-≤
      f2 n (suc m) n≥n₀ _ =
        subst2 _≤_ (sym p1) (sym p2) (+-preserves-≤ lt-e (f2 n m n≥n₀ zero-≤))
        where
        p1 : partial-sums (drop n s1) (suc m) == s1 (n + m) + partial-sums (drop n s1) m
        p1 = partial-sums-split (drop n s1) m >=> +-left (drop-+ n m s1)
        p2 : partial-sums (drop n s2) (suc m) == s2 (n + m) + partial-sums (drop n s2) m
        p2 = partial-sums-split (drop n s2) m >=> +-left (drop-+ n m s2)
        lt-e : s1 (n + m) ≤ s2 (n + m)
        lt-e = f (n + m) (subst2 _≤_ +-right-zero refl (+-preserves-≤ n≥n₀ zero-≤))

  bound-partial-sums'2 :
    (s1 s2 : Seq) ->
    ∀Largeℕ (\m -> s1 m ≤ s2 m) ->
    ∃[ n₀ ∈ ℕ ] ((n m : ℕ) -> n ≥ n₀ ->
                 partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m)
  bound-partial-sums'2 s1 s2 = ∥-map handle
    where
    handle : ∀Largeℕ' (\m -> s1 m ≤ s2 m) ->
             Σ[ n₀ ∈ ℕ ] ((n m : ℕ) -> n ≥ n₀ ->
                          partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m)
    handle (n₀ , f) = n₀ , f2
      where
      f2 : (n m : ℕ) -> n ≥ n₀ ->
           partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m
      f2 n zero n≥n₀ =
        subst2 _≤_
               (finiteMerge-Fin0 _ _ >=>
                sym (finiteMerge-Fin0 _ _))
               refl refl-≤
      f2 n (suc m) n≥n₀ =
        subst2 _≤_ (sym p1) (sym p2) (+-preserves-≤ lt-e (f2 n m n≥n₀))
        where
        p1 : partial-sums (drop n s1) (suc m) == s1 (n + m) + partial-sums (drop n s1) m
        p1 = partial-sums-split (drop n s1) m >=> +-left (drop-+ n m s1)
        p2 : partial-sums (drop n s2) (suc m) == s2 (n + m) + partial-sums (drop n s2) m
        p2 = partial-sums-split (drop n s2) m >=> +-left (drop-+ n m s2)
        lt-e : s1 (n + m) ≤ s2 (n + m)
        lt-e = f (n + m) (subst2 _≤_ +-right-zero refl (+-preserves-≤ n≥n₀ zero-≤))


  squeeze-partial-sums :
    (s1 s2 s3 : Seq) ->
    ∀Largeℕ (\m -> s1 m ≤ s2 m) ->
    ∀Largeℕ (\m -> s2 m ≤ s3 m) ->
    ∃[ n₀ ∈ ℕ ] ((n m : ℕ) -> n ≥ n₀ ->
                 partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m ×
                 partial-sums (drop n s2) m ≤ partial-sums (drop n s3) m)
  squeeze-partial-sums s1 s2 s3 s1≤s2 s2≤s3 =
    ∥-map2 handle (bound-partial-sums'2 s1 s2 s1≤s2) (bound-partial-sums'2 s2 s3 s2≤s3)
    where
    handle :
      Σ[ n₀ ∈ ℕ ] ((n m : ℕ) -> n ≥ n₀ ->
                   partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m) ->
      Σ[ n₀ ∈ ℕ ] ((n m : ℕ) -> n ≥ n₀ ->
                   partial-sums (drop n s2) m ≤ partial-sums (drop n s3) m) ->
      Σ[ n₀ ∈ ℕ ] ((n m : ℕ) -> n ≥ n₀ ->
                   partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m ×
                   partial-sums (drop n s2) m ≤ partial-sums (drop n s3) m)
    handle (n₀1 , f12) (n₀2 , f23) = n₀ , f
      where
      n₀ = max n₀1 n₀2
      f : (n m : ℕ) -> n ≥ n₀ -> (partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m) ×
                                 (partial-sums (drop n s2) m ≤ partial-sums (drop n s3) m)
      f n m n≥n₀ =
        f12 n m (trans-≤ max-≤-left n≥n₀) ,
        f23 n m (trans-≤ max-≤-right n≥n₀)

  εI : ℚ⁺ -> Iℚ
  εI (ε , 0<ε) = Iℚ-cons (- ε) ε (weaken-< (trans-< (minus-flips-0< 0<ε) 0<ε))

  module _
    (ConvergentSeries->small-partial-sums :
      (s : Seq) -> isConvergentSeries s ->
      (ε : ℚ⁺) -> ∀Largeℕ (\n -> ((m : ℕ) -> ℝ∈Iℚ (partial-sums (drop n s) m) (εI ε))))
    where
    squeeze-ConvergentSeries :
      (s1 s2 s3 : Seq) ->
      (∀Largeℕ (\ m -> s1 m ≤ s2 m)) ->
      (∀Largeℕ (\ m -> s2 m ≤ s3 m)) ->
      isConvergentSeries s1 ->
      isConvergentSeries s3 ->
      isConvergentSeries s2
    squeeze-ConvergentSeries s1 s2 s3 s1<s2 s2<s3 CS-s1 CS-s3 =
      isCauchy->isConvergentSequence (isCauchy'->isCauchy f)
      where
      f : isCauchy' (partial-sums s2)
      f ε = ∥-bind3 handle
              (squeeze-partial-sums s1 s2 s3 s1<s2 s2<s3)
              (ConvergentSeries->small-partial-sums s1 CS-s1 ε)
              (ConvergentSeries->small-partial-sums s3 CS-s3 ε)
        where
        handle :
          Σ[ n₀ ∈ ℕ ] ((n m : ℕ) -> n ≥ n₀ ->
                       partial-sums (drop n s1) m ≤ partial-sums (drop n s2) m ×
                       partial-sums (drop n s2) m ≤ partial-sums (drop n s3) m) ->
          ∀Largeℕ' (\n -> ((m : ℕ) -> ℝ∈Iℚ (partial-sums (drop n s1) m) (εI ε))) ->
          ∀Largeℕ' (\n -> ((m : ℕ) -> ℝ∈Iℚ (partial-sums (drop n s3) m) (εI ε))) ->
          ∃[ n ∈ Nat ] ((m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                        (diff (partial-sums s2 m₁) (partial-sums s2 m₂)) < ℚ->ℝ ⟨ ε ⟩)
        handle (n₀-ps , ps≤-f) (n₀-1 , f-1) (n₀-3 , f-3) = ∣ n , f-ans ∣
          where
          n = max n₀-ps (max n₀-1 n₀-3)
          f-ans2 : (m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n -> m₁ ≤ m₂ ->
                   (diff (partial-sums s2 m₁) (partial-sums s2 m₂)) < ℚ->ℝ ⟨ ε ⟩
          f-ans2 m₁ m₂ m₁≥n m₂≥n (d , d+m₁=m₂) = lt2
            where
            m₁≥n-ps = trans-≤ max-≤-left m₁≥n
            m₁≥n-13 : m₁ ≥ max n₀-1 n₀-3
            m₁≥n-13 = (trans-≤ max-≤-right m₁≥n)
            m₁≥n-1 : m₁ ≥ n₀-1
            m₁≥n-1 = trans-≤ max-≤-left m₁≥n-13
            m₁≥n-3 : m₁ ≥ n₀-3
            m₁≥n-3 = trans-≤ max-≤-right m₁≥n-13
            p0 : m₂ == m₁ + d
            p0 = sym d+m₁=m₂ >=> +'-commute {d} {m₁}
            p1 : (diff (partial-sums s2 m₁) (partial-sums s2 m₂)) == partial-sums (drop m₁ s2) d
            p1 = (\i -> diff (partial-sums s2 m₁) (partial-sums s2 (p0 i))) >=>
                 sym (partial-sums-drop s2 m₁ d)
            lt1 : partial-sums (drop m₁ s2) d ≤ partial-sums (drop m₁ s3) d
            lt1 = proj₂ (ps≤-f m₁ d m₁≥n-ps)
            lt2 : (diff (partial-sums s2 m₁) (partial-sums s2 m₂)) < ℚ->ℝ ⟨ ε ⟩
            lt2 = subst2 _<_ (sym p1) refl (trans-≤-< lt1 (U->ℝ< (proj₂ (f-3 m₁ m₁≥n-3 d))))

          f-ans3 : (m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n -> m₁ ≤ m₂ ->
                   (- ℚ->ℝ ⟨ ε ⟩) < (diff (partial-sums s2 m₁) (partial-sums s2 m₂))
          f-ans3 m₁ m₂ m₁≥n m₂≥n (d , d+m₁=m₂) = lt2
            where
            m₁≥n-ps = trans-≤ max-≤-left m₁≥n
            m₁≥n-13 : m₁ ≥ max n₀-1 n₀-3
            m₁≥n-13 = (trans-≤ max-≤-right m₁≥n)
            m₁≥n-1 : m₁ ≥ n₀-1
            m₁≥n-1 = trans-≤ max-≤-left m₁≥n-13
            m₁≥n-3 : m₁ ≥ n₀-3
            m₁≥n-3 = trans-≤ max-≤-right m₁≥n-13
            p0 : m₂ == m₁ + d
            p0 = sym d+m₁=m₂ >=> +'-commute {d} {m₁}
            p1 : (diff (partial-sums s2 m₁) (partial-sums s2 m₂)) == partial-sums (drop m₁ s2) d
            p1 = (\i -> diff (partial-sums s2 m₁) (partial-sums s2 (p0 i))) >=>
                 sym (partial-sums-drop s2 m₁ d)
            lt1 : partial-sums (drop m₁ s1) d ≤ partial-sums (drop m₁ s2) d
            lt1 = proj₁ (ps≤-f m₁ d m₁≥n-ps)
            lt2 : (- ℚ->ℝ ⟨ ε ⟩) < diff (partial-sums s2 m₁) (partial-sums s2 m₂)
            lt2 = subst2 _<_ ℚ->ℝ-preserves-- (sym p1) (trans-<-≤ (L->ℝ< (proj₁ (f-1 m₁ m₁≥n-1 d))) lt1)

          f-ans : (m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                  (diff (partial-sums s2 m₁) (partial-sums s2 m₂)) < ℚ->ℝ ⟨ ε ⟩
          f-ans m₁ m₂ m₁≥n m₂≥n = unsquash isProp-< (∥-map handle2 (connex-≤ m₁ m₂))
            where
            handle2 : (m₁ ≤ m₂) ⊎ (m₂ ≤ m₁) ->
                      (diff (partial-sums s2 m₁) (partial-sums s2 m₂)) < ℚ->ℝ ⟨ ε ⟩
            handle2 (inj-l m₁≤m₂) = f-ans2 m₁ m₂ m₁≥n m₂≥n m₁≤m₂
            handle2 (inj-r m₂≤m₁) =
              subst2 _<_ (sym diff-anticommute) minus-double-inverse
                     (minus-flips-< (f-ans3 m₂ m₁ m₂≥n m₁≥n m₂≤m₁))



    module _
      (ℚ->ℝ-preserves-* : {q r : ℚ} -> ℚ->ℝ (q * r) == ℚ->ℝ q * ℚ->ℝ r)
      (1/ℕ-preserves-* : {m n : Nat⁺} -> 1/ℕ (m *⁺ n) == 1/ℕ m * 1/ℕ n)
      (*-preserves-limit : {s1 s2 : Seq} -> {v1 v2 : ℝ} ->
                           isLimit s1 v1 -> isLimit s2 v2 -> isLimit (\n -> s1 n * s2 n) (v1 * v2))
      (minus-preserves-limit : {s : Seq} -> {v : ℝ} ->
                               isLimit s v -> isLimit (-_ ∘ s) (- v))
      (ℚ->ℝ-preserves-* : {q r : ℚ} -> ℚ->ℝ (q * r) == ℚ->ℝ q * ℚ->ℝ r)

      (Archimedian-ℝ : {a b : ℝ} -> (0# < b) -> ∃[ n ∈ Nat ] (a < (ℚ->ℝ (ℕ->ℚ n) * b)))
      (Archimedian-ℚ : {a b : ℚ} -> (0# < b) -> ∃[ n ∈ Nat ] (a < ((ℕ->ℚ n) * b)))
      (Archimedian-ℚ' : {a b : ℚ} -> (0# < a) -> (0# < b) -> (b < 1#) ->
                        ∃[ n ∈ Nat ] ((geometric-ℚ-sequence b n) < a))

      where
      1/2^n=1/2ℝ^n : (n : Nat) -> ℚ->ℝ (1/ℕ (2 ^' n , ^'-Pos' tt n)) == geometric-sequence 1/2ℝ n
      1/2^n=1/2ℝ^n zero    = refl
      1/2^n=1/2ℝ^n (suc n) =
        cong ℚ->ℝ 1/ℕ-preserves-* >=>
        ℚ->ℝ-preserves-* >=>
        *-right (1/2^n=1/2ℝ^n n)

      exponential-sequence1<2^n :
        (n : ℕ) -> n ≥ 4 -> exponential-sequence1 n < geometric-sequence 1/2ℝ n
      exponential-sequence1<2^n n n≥4 =
        subst2 _<_ refl (1/2^n=1/2ℝ^n n) (ℚ->ℝ-preserves-< _ _ fn<1/2^n)
        where
        2^n = 2 ^' n
        2^n⁺ : Nat⁺
        2^n⁺ = 2^n , ^'-Pos' tt n

        2^n<f : (2 ^' n) < factorial n
        2^n<f = 2^n<factorial n n≥4

        inv-2^n-1/2^n : areInverses (ℕ->ℚ 2^n) (1/ℕ 2^n⁺)
        inv-2^n-1/2^n = *-commute >=> 1/ℕ-ℕ-path 2^n⁺

        inv-fn-1/fn : areInverses (ℕ->ℚ (factorial n)) (1/ℕ (factorial⁺ n))
        inv-fn-1/fn = *-commute >=> 1/ℕ-ℕ-path (factorial⁺ n)

        fn<1/2^n : 1/ℕ (factorial⁺ n) < (1/ℕ 2^n⁺)
        fn<1/2^n = inverse-flips-< inv-2^n-1/2^n inv-fn-1/fn
                     (ℕ->ℚ-preserves-order _ _ (Pos'->< (snd 2^n⁺)))
                     (ℕ->ℚ-preserves-order _ _ (Pos'->< (snd (factorial⁺ n))))
                     (ℕ->ℚ-preserves-order _ _ 2^n<f)

      isConvergentSeries-exponential-sequence1 : isConvergentSeries exponential-sequence1
      isConvergentSeries-exponential-sequence1 =
        squeeze-ConvergentSeries
          (constant-seq 0#) exponential-sequence1 (geometric-sequence 1/2ℝ)
          0≤es es≤1/2^n
          isConvergentSeries-zero isConvergentSeries-1/2^n
        where
        0≤es : ∀Largeℕ (\n -> 0# ≤ exponential-sequence1 n)
        0≤es = ∣ 0 , (\n n≥0 -> weaken-< (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ _))) ∣

        es≤1/2^n : ∀Largeℕ (\n -> exponential-sequence1 n ≤ geometric-sequence 1/2ℝ n)
        es≤1/2^n = ∣ 4 , (\n n≥4 -> weaken-< (exponential-sequence1<2^n n n≥4)) ∣

        isConvergentSeries-zero : isConvergentSeries (constant-seq 0#)
        isConvergentSeries-zero =
          0# , subst (\s -> isLimit s 0#) (sym (funExt p)) (isLimit-constant-seq 0#)
          where
          p : (n : ℕ) -> partial-sums (constant-seq 0#) n == 0#
          p zero = finiteMerge-Fin0 _ _
          p (suc n) =
            partial-sums-split (constant-seq 0#) n >=>
            +-left-zero >=>
            p n

        isConvergentSeries-1/2^n : isConvergentSeries (geometric-sequence 1/2ℝ)
        isConvergentSeries-1/2^n =
          _ , isLimit-geometric-series
                *-preserves-limit
                minus-preserves-limit
                ℚ->ℝ-preserves-*
                Archimedian-ℝ
                Archimedian-ℚ
                Archimedian-ℚ'
                1/2ℝ (ℚ->ℝ-preserves-< _ _ (Pos-1/ℕ _)) (ℚ->ℝ-preserves-< _ _ 1/2r<1r)

        eulers-number : ℝ
        eulers-number = fst isConvergentSeries-exponential-sequence1
