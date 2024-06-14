{-# OPTIONS --cubical --safe --exact-split #-}

module real.derivative2.continuous where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import funext
open import heyting-field.instances.rational
open import nat
open import order
open import order.instances.rational
open import order.instances.real
open import order.instances.nat
open import order.minmax
open import order.minmax.instances.rational
open import order.minmax.instances.real
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.instances.real
open import rational
open import real
open import real.arithmetic.multiplication.inverse
open import real.derivative2
open import real.epsilon-bounded
open import real.rational
open import real.sequence.limit
open import real.sequence.cauchy
open import real.sequence.limit.arithmetic
open import real.subspace
open import ring
open import ring.implementations.real
open import semiring
open import sequence
open import subset
open import subset.subspace
open import truncation

distance : ℝ -> ℝ -> ℝ
distance x y = abs (diff x y)

isContinuousAt : {ℓS : Level} (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) (x : ∈-Subtype S) ->
                 Type (ℓ-max ℓS ℓ-one)
isContinuousAt S f x@(x' , _) =
  ∀ ((ε , _) : ℝ⁺) -> ∃[ (δ , _) ∈ ℝ⁺ ] ∀ (y@(y' , _) : ∈-Subtype S) ->
    distance x' y' < δ -> distance (f x) (f y) < ε

isContinuous : {ℓS : Level} (S : Subtype ℝ ℓS) (f : ∈-Subtype S -> ℝ) -> Type (ℓ-max ℓS ℓ-one)
isContinuous S f = ∀ x -> isContinuousAt S f x

isContinuous->isSequentiallyContinuous :
  {ℓS : Level} (S : Subtype ℝ ℓS) {f : ∈-Subtype S -> ℝ} ->
  isContinuous S f -> isSequentiallyContinuous S f
isContinuous->isSequentiallyContinuous S {f} cf s l lim =
  distance<ε->isLimit handle
  where
  handle : ((ε , _) : ℝ⁺) -> ∀Largeℕ (\i -> distance (f l) (f (s i)) < ε)
  handle ε⁺@(ε , 0<ε) = ∥-bind handle2 (cf l ε⁺)
    where
    handle2 : Σ[ (δ , _) ∈ ℝ⁺ ]
                (∀ (y@(y' , _) : ∈-Subtype S) -> distance ⟨ l ⟩ y' < δ -> distance (f l) (f y) < ε) ->
              _
    handle2 (δ⁺@(δ , _) , dis-f) =
      ∀Largeℕ-map (\{i} -> dis-f (s i)) (isLimit.distance<ε lim δ⁺)



module _ {ℓS : Level} {S : Subtype ℝ ℓS} {f : ∈-Subtype S -> ℝ}
         ((f' , df) : isDifferentiable S f) (magic : Magic) where

  isDifferentiable->isContinuous : isContinuous S f
  isDifferentiable->isContinuous l∈@(l , _) ε⁺@(ε , _) =
    ∥-bind handle (isDerivativeAt.limit-point (df l∈))
    where
    limit-points : (p∈@(p , _) : ∈-Subtype S) -> isLimitPoint S p
    limit-points p∈ = (isDerivativeAt.limit-point (df p∈))


    module _ (t : LimitTestSeq S l) where
      module t = LimitTestSeq t


      mod'-t : ((ε , _) : ℚ⁺) -> Σ[ n ∈ Nat ] ((m : Nat) -> n ≤ m -> abs (diff l (t.seq m)) < ℚ->ℝ ε)
      mod'-t = magic

      lim-t : isLimit t.seq l
      lim-t = t.isLimit-seq

      lim-d : isLimit (\i -> diff (f (t.∈S i)) (f l∈) * 1/diff (t.seq#x i)) (f' l∈)
      lim-d = isDerivativeAt.isLimit-∀seq (df l∈) t

      -- -- TODO maybe add +₁-preserves-limit
      -- lim-d : isLimit (\i -> diff (s i) l) 0#
      -- lim-d =
      --   subst (isLimit (\i -> diff (s i) l)) +-inverse
      --     (+-preserves-limit
      --       (isLimit-constant-seq l)
      --       (minus-preserves-limit lim-s))


      handle : ∃[ (δ , _) ∈ ℝ⁺ ] ∀ (y∈@(y , _) : ∈-Subtype S) ->
                 distance l y < δ -> distance (f l∈) (f y∈) < ε
      handle = ∣ (δ , 0<δ) , handle2 ∣
        where
        1/δ : ℝ
        1/δ = max (f' l∈) 1#
        0<1/δ : 0# < 1/δ
        0<1/δ = trans-<-≤ 0<1 max-≤-right
        δ : ℝ
        δ = ℝ1/ 1/δ (inj-r 0<1/δ)
        0<δ : 0# < δ
        0<δ = ℝ1/-preserves-0< 1/δ (inj-r 0<1/δ) 0<1/δ

        handle2 : ∀ (y∈@(y , _) : ∈-Subtype S) -> distance l y < δ -> distance (f l∈) (f y∈) < ε
        handle2 y∈@(y , _) dis-ly<δ = magic



--    lim-f : isLimit (\i -> diff (f (s∈ i)) (f l) * 1/diff (t.seq#x i)) (f' x)
--    lim-f = isDerivativeAt.isLimit-∀seq (df x) t

--    lim-f2 : isLimit (\i -> diff (f (t.∈S i)) (f x)) 0#
--    lim-f2 =
--      subst2 isLimit (funExt (\_ -> *-assoc >=> *-right (ℝ1/-inverse _ _) >=> *-right-one))
--                     *-right-zero
--        (*-preserves-limit lim-f lim-d)
--
--
--    lim-fi : isLimit (\i -> f (t.∈S i)) (f x)
--    lim-fi =
--      subst2 isLimit (funExt (\i -> +-right (sym diff-anticommute) >=> diff-step))
--                     (+-right minus-zero >=> +-right-zero)
--        (+-preserves-limit
--          (isLimit-constant-seq (f x))
--          (minus-preserves-limit lim-f2))
--
