{-# OPTIONS --cubical --safe --exact-split #-}

module real.series where

open import apartness
open import additive-group
open import additive-group.instances.reader
open import additive-group.instances.real
open import base
open import equality
open import fin
open import funext
open import finset.instances
open import finsum
open import finsum.arithmetic
open import functions
open import finite-commutative-monoid.instances
open import hlevel
open import heyting-field
open import nat
open import nat.order
open import order
open import integral-domain.instances.real
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import ordered-semiring
open import ordered-ring
open import ordered-integral-domain
open import ordered-semiring.instances.real
open import semiring
open import sequence
open import sequence.partial-sums
open import rational
open import rational.proper-interval
open import real
open import real.rational
open import real.heyting-field
open import real.arithmetic
open import real.interval
open import real.order
open import real.sequence hiding (Cauchy)
open import real.sequence.limit
open import relation
open import ring
open import ring.implementations.rational
open import ring.implementations.real
open import truncation

private
  Seq : Type₁
  Seq = Sequence ℝ

instance
  AdditiveCommMonoid-Seq : AdditiveCommMonoid Seq
  AdditiveCommMonoid-Seq = AdditiveCommMonoid-Reader AdditiveCommMonoid-ℝ Nat
  AdditiveGroup-Seq : AdditiveGroup AdditiveCommMonoid-Seq
  AdditiveGroup-Seq = AdditiveGroup-Reader AdditiveGroup-ℝ Nat


isInfiniteSum : REL Seq ℝ ℓ-one
isInfiniteSum s r = isLimit (partial-sums s) r

isProp-isInfiniteSum : ∀ {s} {r} -> isProp (isInfiniteSum s r)
isProp-isInfiniteSum = isProp-isLimit

isConvergentSeries : Pred Seq ℓ-one
isConvergentSeries s = isConvergentSequence (partial-sums s)

isProp-isConvergentSeries : {s : Seq} -> isProp (isConvergentSeries s)
isProp-isConvergentSeries = isProp-isConvergentSequence


ℝ∈Iℚ-+ᵉ⁻ : (x y : ℝ) (a : Iℚ) -> ℝ∈Iℚ (x ℝ+ᵉ y) a ->
           ∃[ qi1 ∈ Iℚ ] Σ[ qi2 ∈ Iℚ ] (ℝ∈Iℚ x qi1 × ℝ∈Iℚ y qi2 × (qi1 i+ qi2) i⊆ a)
ℝ∈Iℚ-+ᵉ⁻ x y a@(Iℚ-cons l u l≤u) (L-a , U-a) = ∥-map2 handle L-a U-a
  where
  handle : Σ[ l1 ∈ ℚ ] Σ[ l2 ∈ ℚ ] (Real.L x l1 × Real.L y l2 × (l1 + l2) == l) ->
           Σ[ u1 ∈ ℚ ] Σ[ u2 ∈ ℚ ] (Real.U x u1 × Real.U y u2 × (u1 + u2) == u) ->
           Σ[ qi1 ∈ Iℚ ] Σ[ qi2 ∈ Iℚ ] (ℝ∈Iℚ x qi1 × ℝ∈Iℚ y qi2 × (qi1 i+ qi2) i⊆ a)
  handle (l1 , l2 , L-l1 , L-l2 , l1+l2=l) (u1 , u2 , U-u1 , U-u2 , u1+u2=u) =
    (ℝ-bounds->Iℚ x L-l1 U-u1) ,
    (ℝ-bounds->Iℚ y L-l2 U-u2) ,
    (L-l1 , U-u1) ,
    (L-l2 , U-u2) ,
    (i⊆-cons (subst2 _≤_ l1+l2=l refl refl-≤) (subst2 _≤_ refl u1+u2=u refl-≤))

ℝ∈Iℚ-+⁻ : (x y : ℝ) (a : Iℚ) -> ℝ∈Iℚ (x + y) a ->
          ∃[ qi1 ∈ Iℚ ] Σ[ qi2 ∈ Iℚ ] (ℝ∈Iℚ x qi1 × ℝ∈Iℚ y qi2 × (qi1 i+ qi2) i⊆ a)
ℝ∈Iℚ-+⁻ x y a x+y∈a =
  ℝ∈Iℚ-+ᵉ⁻ x y a (subst (\z -> ℝ∈Iℚ z a) ℝ+-eval x+y∈a)

+-preserves-limit : {s1 s2 : Seq} -> {v1 v2 : ℝ} ->
                    isLimit s1 v1 -> isLimit s2 v2 -> isLimit (s1 + s2) (v1 + v2)
+-preserves-limit {s1} {s2} {v1} {v2} l1 l2 = close->isLimit f
  where
  f : (qi : Iℚ) -> (ℝ∈Iℚ (v1 + v2) qi) -> ∃[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ ((s1 + s2) m) qi)
  f qi v12∈qi = ∥-bind handle (ℝ∈Iℚ-+⁻ v1 v2 qi v12∈qi)
    where
    Ans = ∃[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ ((s1 + s2) m) qi)
    handle : Σ[ qi1 ∈ Iℚ ] Σ[ qi2 ∈ Iℚ ] (ℝ∈Iℚ v1 qi1 × ℝ∈Iℚ v2 qi2 × (qi1 i+ qi2) i⊆ qi) -> Ans
    handle (qi1 , qi2 , v1∈qi1 , v2∈qi2 , qi1+qi2⊆qi) =
      ∥-bind2 handle2 (isLimit.close l1 qi1 v1∈qi1) (isLimit.close l2 qi2 v2∈qi2)
      where
      handle2 : Σ[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ (s1 m) qi1) ->
                Σ[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ (s2 m) qi2) ->
                Ans
      handle2 (n1 , f1) (n2 , f2) =
        ∣ n , (\m m≥n -> ℝ∈Iℚ-⊆ ((s1 + s2) m) qi1+qi2⊆qi (ℝ∈Iℚ-+ (s1 m) (s2 m) qi1 qi2
                                                                 (f1 m (trans-≤ n1≤n m≥n))
                                                                 (f2 m (trans-≤ n2≤n m≥n)))) ∣
        where
        n = max n1 n2
        n1≤n = ≤-max-left
        n2≤n = ≤-max-right

isLimit-constant-seq : (x : ℝ) -> isLimit (constant-seq x) x
isLimit-constant-seq x = 
  close->isLimit (\qi x∈qi -> ∣ 0 , (\_ _ -> x∈qi) ∣)

isLimit-seq-cons : (x : ℝ) (s : Seq) (v : ℝ) -> isLimit s v -> isLimit (seq-cons x s) v
isLimit-seq-cons x s v l = close->isLimit f
  where
  f : (qi : Iℚ) -> (ℝ∈Iℚ v qi) -> ∃[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ (seq-cons x s m) qi)
  f qi v∈qi = ∥-map handle (isLimit.close l qi v∈qi)
    where
    handle : Σ[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ (s m) qi) ->
             Σ[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ (seq-cons x s m) qi)
    handle (n , g) = suc n , h
      where
      h : (m : ℕ) -> m ≥ (suc n) -> ℝ∈Iℚ (seq-cons x s m) qi
      h zero sn≤z = bot-elim (zero-≮ sn≤z)
      h (suc m) sn≤sm = g m (pred-≤ sn≤sm)


geometric-sequence : ℝ -> Seq
geometric-sequence x zero = 1#
geometric-sequence x (suc n) = x * geometric-sequence x n

geometric-series : ℝ -> Seq
geometric-series x = partial-sums (geometric-sequence x)

geometric-series-path : 
  (x : ℝ) (n : ℕ) -> (geometric-series x n) * (1# + (- x)) == 1# + - (geometric-sequence x n)
geometric-series-path x zero =
  *-left (finiteMerge-Fin0 _ _) >=>
  *-left-zero >=>
  sym +-inverse
geometric-series-path x (suc n) = ans
  where
  expand : (geometric-series x (suc n)) == 1# + x * geometric-series x n
  expand =
    finiteMerge-FinSuc _ _ >=>
    +-right finiteSum-*

  ans : (geometric-series x (suc n)) * (1# + (- x)) == 1# + - (geometric-sequence x (suc n))
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

geometric-sequence-1 : (n : ℕ) -> geometric-sequence 1# n == 1#
geometric-sequence-1 zero = refl
geometric-sequence-1 (suc n) = *-left-one >=> geometric-sequence-1 n


geometric-Iℚ-sequence : Iℚ -> ℕ -> Iℚ
geometric-Iℚ-sequence qi zero    = (Iℚ-cons 1# 1# refl-≤)
geometric-Iℚ-sequence qi (suc n) = qi i* (geometric-Iℚ-sequence qi n)

geometric-ℚ-sequence : ℚ -> ℕ -> ℚ
geometric-ℚ-sequence q zero    = 1#
geometric-ℚ-sequence q (suc n) = q * (geometric-ℚ-sequence q n)

geometric-sequence-0≤ : {x : ℝ} -> 0# ≤ x -> (n : ℕ) -> 0# ≤ geometric-sequence x n 
geometric-sequence-0≤ {x} 0≤x zero = 0≤1
geometric-sequence-0≤ {x} 0≤x (suc n) = *-preserves-0≤ 0≤x (geometric-sequence-0≤ 0≤x n)


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



-- geometric-sequence-ℝ∈Iℚ : (x : ℝ) (qi : Iℚ) -> (ℝ∈Iℚ x qi) -> 
--                           (n : ℕ) -> ℝ∈Iℚ (geometric-sequence x n) (geometric-Iℚ-sequence qi n)
-- geometric-sequence-ℝ∈Iℚ = ? 

module _
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

  ℚ->ℝ-geometric-sequence : (q : ℚ) -> (n : ℕ) -> 
                            ℚ->ℝ (geometric-ℚ-sequence q n) == (geometric-sequence (ℚ->ℝ q) n)
  ℚ->ℝ-geometric-sequence q zero    = refl
  ℚ->ℝ-geometric-sequence q (suc n) = 
    ℚ->ℝ-preserves-* >=> *-right (ℚ->ℝ-geometric-sequence q n)


  module _ (x : ℝ) (0<x : 0# < x) (x<1 : x < 1#) where
    private
      0<1-x : 0# < (1# + - x)
      0<1-x = (subst2 _<_ +-inverse refl (+₂-preserves-< x<1))
      1-x#0 : (1# + - x) # 0#
      1-x#0 = inj-r 0<1-x
      isUnit-1-x = Field.#0->isUnit ℝField 1-x#0
      y = Ring.isUnit.inv isUnit-1-x
      y-path : (1# + (- x)) * y == 1#
      y-path = Ring.isUnit.path isUnit-1-x

    isLimit-geometric-sequence : isLimit (geometric-sequence x) 0#
    isLimit-geometric-sequence = close->isLimit f
      where
      f : (qi : Iℚ) -> (ℝ∈Iℚ 0# qi) -> ∃[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ (geometric-sequence x m) qi)
      f qi@(Iℚ-cons l u _) (L-l , U-u) =
        ∥-bind2 handle (Archimedian-ℝ 0<1-x) 
                       (Real.isLowerOpen-U x 1# xU-1)
        where
        xU-1 : Real.U x 1#
        xU-1 = ℝ<->U x 1# x<1
        handle : Σ[ n ∈ Nat ] (ℚ->ℝ u < (ℚ->ℝ (ℕ->ℚ n) * (1# + - x))) -> 
                 Σ[ q ∈ ℚ ] (q < 1# × Real.U x q) ->
                 ∃[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ (geometric-sequence x m) qi)
        handle _ (q , q<1 , xU-q) = ∥-bind handle2 (Archimedian-ℚ' 0<u 0<q q<1)
          where
          0<u = U->ℚ< U-u
          0<q = ℝ-bounds->ℚ< x (ℝ<->L 0# x 0<x) xU-q
          handle2 : Σ[ n ∈ Nat ] ((geometric-ℚ-sequence q n) < u) ->
                    ∃[ n ∈ ℕ ] ((m : ℕ) -> m ≥ n -> ℝ∈Iℚ (geometric-sequence x m) qi)
          handle2 (n , q^n<u) = ∣ n , g ∣
            where
            g : (m : ℕ) -> m ≥ n -> ℝ∈Iℚ (geometric-sequence x m) qi
            g m m≥n = ℝ<->L l (geometric-sequence x m) 
                            (trans-<-≤ (L->ℝ< L-l) (geometric-sequence-0≤ (weaken-< 0<x) m)) ,
                      ℝ<->U (geometric-sequence x m) u x^m<u
              where
              x^m≤q^m : (geometric-sequence x m) ≤ (geometric-sequence (ℚ->ℝ q) m)
              x^m≤q^m = (geometric-sequence-≤ (weaken-< 0<x) (weaken-< (U->ℝ< xU-q)) m)
              q^m≤q^n : (geometric-sequence (ℚ->ℝ q) m) ≤ (geometric-sequence (ℚ->ℝ q) n)
              q^m≤q^n = geometric-sequence-≤1 (weaken-< (ℚ->ℝ-preserves-< _ _ 0<q)) 
                                              (weaken-< (ℚ->ℝ-preserves-< _ _ q<1)) n m m≥n
              q^n=q^n : (geometric-sequence (ℚ->ℝ q) n) == ℚ->ℝ (geometric-ℚ-sequence q n)
              q^n=q^n = sym (ℚ->ℝ-geometric-sequence q n)
              x^m<u : (geometric-sequence x m) < (ℚ->ℝ u)
              x^m<u = trans-≤-< (trans-≤ x^m≤q^m q^m≤q^n) 
                                (subst2 _<_ (sym q^n=q^n) refl (ℚ->ℝ-preserves-< _ _ q^n<u))

                        

      
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
