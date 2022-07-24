{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence.cauchy where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import hlevel
open import nat.arithmetic
open import nat.properties
open import order
open import order.instances.nat
open import order.instances.real
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import real
-- open import real.arithmetic.rational
open import real.rational
open import real.sequence.limit
open import relation hiding (U)
open import ring.implementations.real
open import semiring
open import sequence
open import truncation

open import nat using (≤-max-left ; ≤-max-right)

{-
private
  Seq : Type₁
  Seq = Sequence ℝ

εBounded : ℚ -> ℝ -> Type₀
εBounded ε x = Real.L x (- ε) × Real.U x ε

Cauchy : Pred Seq ℓ-zero
Cauchy s = (ε : ℚ⁺) -> ∃[ n ∈ Nat ] ((m₁ m₂ : Nat) -> n ≤ m₁ -> n ≤ m₂ ->
                                     εBounded ⟨ ε ⟩ (diff (s m₁) (s m₂)))

isProp-Cauchy : {s : Seq} -> isProp (Cauchy s)
isProp-Cauchy = isPropΠ (\ _ -> squash)

private
  OpenEventualUpperBound : Seq -> Pred ℚ ℓ-zero
  OpenEventualUpperBound s q =
    ∃[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.U (s m) (q r+ (- ⟨ ε ⟩)))

  OpenEventualLowerBound : Seq -> Pred ℚ ℓ-zero
  OpenEventualLowerBound s q =
    ∃[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.L (s m) (q r+ ⟨ ε ⟩))

module _
  {s : Seq} (cauchy : Cauchy s)
  where

  private
    L : Pred ℚ ℓ-zero
    L = OpenEventualLowerBound s

    U : Pred ℚ ℓ-zero
    U = OpenEventualUpperBound s

    1/2r⁺ : ℚ⁺
    1/2r⁺ = 1/2r , Pos-1/ℕ (2 , tt)
    1r⁺ : ℚ⁺
    1r⁺ = 1r , Pos-1/ℕ (1 , tt)

    Inhabited-L : Inhabited L
    Inhabited-L = ∥-bind handle (cauchy 1/2r⁺)
      where
      handle : Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                             εBounded 1/2r (diff (s m₁) (s m₂))) ->
               ∃ ℚ L
      handle (n , f) = ∥-bind handle2 (Real.Inhabited-L lb)
        where
        lb = s n + (- 1#)
        lb-1/2-path : lb + 1/2ℝ == s n + (- 1/2ℝ)
        lb-1/2-path =
          +-assoc >=>
          +-right (+-commute >=>
                   +-right (cong -_ (sym 1/2ℝ-1-path) >=> minus-distrib-plus) >=>
                   sym +-assoc >=>
                   +-left +-inverse >=>
                   +-left-zero)

        handle2 : (Σ ℚ (Real.L lb)) -> ∃ ℚ L
        handle2 (q , q<lb) = ∣ q , ∣ n , 1/2r⁺ , q+1/2<sm ∣ ∣
          where
          module _ (m : Nat) (m≥n : m ≥ n) where
            lb+1/2<sm : (lb + 1/2ℝ) < s m
            lb+1/2<sm =
              subst2 _<_ (sym lb-1/2-path) (+-assoc >=> +-right +-inverse >=> +-right-zero)
                     (+₂-preserves-< sn<sm+1/2)
              where
              diffU : Real.U (diff (s m) (s n)) 1/2r
              diffU = proj₂ (f m n m≥n refl-≤)

              d<1/2 : diff (s m) (s n) < 1/2ℝ
              d<1/2 = U->ℝ< diffU

              sn<sm+1/2 : s n < (s m + 1/2ℝ)
              sn<sm+1/2 = trans-=-< (sym diff-step) (+₁-preserves-< d<1/2)


            q+1/2<sm : Real.L (s m) (q + 1/2r)
            q+1/2<sm = ℝ<->L _ _ q+1/2r<sm
              where
              q+1/2r<sm : ℚ->ℝ (q + 1/2r) < s m
              q+1/2r<sm =
                subst (_< s m) (sym ℚ->ℝ-preserves-+)
                      (trans-< (+₂-preserves-< (L->ℝ< q<lb)) lb+1/2<sm)

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-bind handle (cauchy 1/2r⁺)
      where
      handle : Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                             εBounded 1/2r (diff (s m₁) (s m₂))) ->
               ∃ ℚ U
      handle (n , f) = ∥-bind handle2 (Real.Inhabited-U ub)
        where
        ub = s n + 1#
        ub-1/2-path : ub + (- 1/2ℝ) == s n + 1/2ℝ
        ub-1/2-path =
          +-assoc >=>
          +-right (+-left (sym 1/2ℝ-1-path) >=>
                   +-assoc >=>
                   +-right +-inverse >=>
                   +-right-zero)

        handle2 : (Σ ℚ (Real.U ub)) -> ∃ ℚ U
        handle2 (q , ub<q) = ∣ q , ∣ n , 1/2r⁺ , sm<q-1/2 ∣ ∣
          where
          module _ (m : Nat) (m≥n : m ≥ n) where
            sm<ub-1/2 : s m < (ub + (- 1/2ℝ))
            sm<ub-1/2 =
              subst2 _<_ diff-step (sym ub-1/2-path) (+₁-preserves-< d<1/2)
              where
              diffU : Real.U (diff (s n) (s m)) 1/2r
              diffU = proj₂ (f n m refl-≤ m≥n)

              d<1/2 : diff (s n) (s m) < 1/2ℝ
              d<1/2 = U->ℝ< diffU

            sm<ub-1/2' : s m < (ub + (ℚ->ℝ (- 1/2r)))
            sm<ub-1/2' = trans-<-= sm<ub-1/2 (+-right (sym ℚ->ℝ-preserves--))

            sm<q-1/2 : Real.U (s m) (q + (- 1/2r))
            sm<q-1/2 = ℝ<->U _ _ sm<q-1/2r
              where
              sm<q-1/2r : s m < ℚ->ℝ (q + (- 1/2r))
              sm<q-1/2r =
                trans-<-=
                  (trans-< sm<ub-1/2' (+₂-preserves-< (U->ℝ< ub<q)))
                  (sym ℚ->ℝ-preserves-+)


    isLowerSet-L : isLowerSet L
    isLowerSet-L q r q<r r-L = ∥-map handle r-L
      where
      handle : Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.L (s m) (r + ⟨ ε ⟩)) ->
               Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.L (s m) (q + ⟨ ε ⟩))
      handle (n , ε⁺ , f) =
        (n , ε⁺ , (\ m m≥n -> Real.isLowerSet-L (s m) _ _ (+₂-preserves-< q<r) (f m m≥n)))


    isUpperSet-U : isUpperSet U
    isUpperSet-U q r q<r q-U = ∥-map handle q-U
      where
      handle : Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.U (s m) (q + (- ⟨ ε ⟩))) ->
               Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.U (s m) (r + (- ⟨ ε ⟩)))
      handle (n , ε⁺ , f) =
        (n , ε⁺ , (\ m m≥n -> Real.isUpperSet-U (s m) _ _ (+₂-preserves-< q<r) (f m m≥n)))


    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q q-L = ∥-map handle q-L
      where
      handle : Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.L (s m) (q + ⟨ ε ⟩)) ->
               Σ[ r ∈ ℚ ] (q < r ×
                           ∃[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.L (s m) (r + ⟨ ε ⟩)))
      handle (n , (ε , 0<ε) , f) = (q + 1/2ε , q<q+1/2ε , ∣ n , (1/2ε , 0<1/2ε) , g ∣)
        where
        1/2ε = 1/2r * ε
        0<1/2ε = *-preserves-0< Pos-1/2r 0<ε
        q<q+1/2ε = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<1/2ε)
        g : (m : Nat) -> m ≥ n -> Real.L (s m) ((q + 1/2ε) + 1/2ε)
        g m m≥n = subst (Real.L (s m)) (+-right (sym (1/2r-path' ε)) >=> sym +-assoc) (f m m≥n)

    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q q-U = ∥-map handle q-U
      where
      handle : Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.U (s m) (q + (- ⟨ ε ⟩))) ->
               Σ[ r ∈ ℚ ] (r < q ×
                           ∃[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.U (s m) (r + (- ⟨ ε ⟩))))
      handle (n , (ε , 0<ε) , f) = (q + - 1/2ε , q-1/2ε<q , ∣ n , (1/2ε , 0<1/2ε) , g ∣)
        where
        1/2ε = 1/2r * ε
        0<1/2ε = *-preserves-0< Pos-1/2r 0<ε
        q-1/2ε<q = trans-<-= (+₁-preserves-< (minus-flips-0< 0<1/2ε)) +-right-zero

        g : (m : Nat) -> m ≥ n -> Real.U (s m) ((q + (- 1/2ε)) + (- 1/2ε))
        g m m≥n = subst (Real.U (s m)) (sym path) (f m m≥n)
          where
          path = +-assoc >=>
                 +-right (sym minus-distrib-plus >=>
                          cong -_ (1/2r-path' ε))

    disjoint : (q : ℚ) -> ¬ (L q × U q)
    disjoint q (L-q , U-q) = unsquash isPropBot (∥-map2 handle L-q U-q)
      where
      handle : Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.L (s m) (q + ⟨ ε ⟩)) ->
               Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.U (s m) (q + (- ⟨ ε ⟩))) ->
               Bot
      handle (n1 , (ε1 , 0<ε1) , f1) (n2 , (ε2 , 0<ε2) , f2) =
        sn.disjoint q (sn.isLowerSet-L _ _ q<q+ε1 (f1 n n≥n1) ,
                       sn.isUpperSet-U _ _ q-ε2<q (f2 n n≥n2))
        where
        n = max n1 n2
        module sn = Real (s n)
        n≥n1 : n ≥ n1
        n≥n1 = ≤-max-left
        n≥n2 : n ≥ n2
        n≥n2 = ≤-max-right
        q<q+ε1 : q < (q + ε1)
        q<q+ε1 = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<ε1)
        q-ε2<q = trans-<-= (+₁-preserves-< (minus-flips-0< 0<ε2)) +-right-zero

    located : (q r : ℚ) -> q < r -> ∥ L q ⊎ U r ∥
    located q r q<r = ∥-bind handle (cauchy (ε , 0<ε))
      where
      0<r-q = trans-=-< (sym +-inverse) (+₂-preserves-< q<r)
      d = (diff q r)
      1/4r = (1/2r * 1/2r)
      0<1/4r = (*-preserves-0< Pos-1/2r Pos-1/2r)
      1/8r = (1/2r * 1/4r)
      0<1/8r = *-preserves-0< Pos-1/2r 0<1/4r

      1/2d = 1/2r * d
      0<1/2d = *-preserves-0< Pos-1/2r 0<r-q
      1/4d = 1/4r * d
      0<1/4d = *-preserves-0< 0<1/4r 0<r-q
      1/8d = 1/8r * d
      0<1/8d = *-preserves-0< 0<1/8r 0<r-q

      ε = 1/8d
      0<ε = 0<1/8d
      ε⁺ = ε , 0<ε
      mid1 = q + 1/4r * d
      mid2 = r + (- (1/4r * d))

      1/2d+1/4d=d-1/4d : 1/2d + 1/4d == d + - 1/4d
      1/2d+1/4d=d-1/4d =
        sym (+-left (sym (1/2r-path' d)) >=>
             +-assoc >=>
             +-right (+-left (sym (1/2r-path' 1/2d)) >=>
                      +-left (+-cong (sym *-assoc) (sym *-assoc)) >=>
                      +-assoc >=>
                      +-right +-inverse >=>
                      +-right-zero))

      1/8d=1/4d-1/8d : 1/8d == 1/4d + - 1/8d
      1/8d=1/4d-1/8d =
        sym (+-left (sym (1/2r-path' 1/4d)) >=>
             +-left (+-cong (sym *-assoc) (sym *-assoc)) >=>
             +-assoc >=>
             +-right +-inverse >=>
             +-right-zero)


      mid1+1/2d=mid2 : mid1 + 1/2d == mid2
      mid1+1/2d=mid2 =
        +-assoc >=>
        +-right (+-commute >=> 1/2d+1/4d=d-1/4d) >=>
        sym +-assoc >=>
        +-left diff-step

      mid1<mid2 : mid1 < mid2
      mid1<mid2 = subst2 _<_ +-right-zero mid1+1/2d=mid2 (+₁-preserves-< (*-preserves-0< Pos-1/2r 0<r-q))

      q+ε=mid1-ε : (q + ε) == mid1 + (- ε)
      q+ε=mid1-ε = +-right 1/8d=1/4d-1/8d >=> sym +-assoc

      mid2+ε=r-ε : (mid2 + ε) == r + (- ε)
      mid2+ε=r-ε = +-right 1/8d=1/4d-1/8d >=> sym +-assoc >=>
                   +-left (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)

      handle : Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                             εBounded ε (diff (s m₁) (s m₂))) ->
               ∥ L q ⊎ U r ∥
      handle (n , f) = ∥-map handle2 (Real.located (s n) mid1 mid2 mid1<mid2)
        where
        handle2 : (Real.L (s n) mid1) ⊎ (Real.U (s n) mid2) -> L q ⊎ U r
        handle2 (inj-l mid1<sn) = inj-l ∣ n , ε⁺ , g ∣
          where
          g : (m : Nat) -> m ≥ n -> Real.L (s m) (q + ε)
          g m m≥n = ℝ<->L _ _ q+ε<sm
            where
            -ε<d : ℚ->ℝ (- ε) < (diff (s n) (s m))
            -ε<d = L->ℝ< (proj₁ (f n m refl-≤ m≥n))
            sn-ε<sm : (s n + ℚ->ℝ (- ε)) < s m
            sn-ε<sm = trans-<-= (+₁-preserves-< -ε<d) diff-step
            mid1-ε<sm : (ℚ->ℝ mid1 + ℚ->ℝ (- ε)) < s m
            mid1-ε<sm = trans-< (+₂-preserves-< (L->ℝ< mid1<sn)) sn-ε<sm
            q+ε<sm : ℚ->ℝ (q + ε) < s m
            q+ε<sm = subst (_< s m) (sym ℚ->ℝ-preserves-+ >=> cong ℚ->ℝ (sym q+ε=mid1-ε))
                            mid1-ε<sm
        handle2 (inj-r sn<mid2) = inj-r ∣ n , ε⁺ , g ∣
          where
          g : (m : Nat) -> m ≥ n -> Real.U (s m) (r + (- ε))
          g m m≥n = ℝ<->U _ _ sm<r-ε
            where
            d<ε : (diff (s n) (s m)) < (ℚ->ℝ ε)
            d<ε = U->ℝ< (proj₂ (f n m refl-≤ m≥n))
            sm<sn+ε : s m < (s n + ℚ->ℝ ε)
            sm<sn+ε = trans-=-< (sym diff-step) (+₁-preserves-< d<ε)
            sm<mid2+ε : s m < (ℚ->ℝ mid2 + ℚ->ℝ ε)
            sm<mid2+ε = trans-< sm<sn+ε (+₂-preserves-< (U->ℝ< sn<mid2))
            sm<r-ε : s m < ℚ->ℝ (r + (- ε))
            sm<r-ε = subst (s m <_) (sym ℚ->ℝ-preserves-+ >=> cong ℚ->ℝ mid2+ε=r-ε)
                           sm<mid2+ε

  CauchySeq->ℝ : ℝ
  CauchySeq->ℝ = record
    { L = L
    ; U = U
    ; isProp-L = \_ -> squash
    ; isProp-U = \_ -> squash
    ; Inhabited-L = Inhabited-L
    ; Inhabited-U = Inhabited-U
    ; isLowerSet-L = isLowerSet-L
    ; isUpperSet-U = isUpperSet-U
    ; isUpperOpen-L = isUpperOpen-L
    ; isLowerOpen-U = isLowerOpen-U
    ; disjoint = disjoint
    ; located = located
    }

  isLimit-CauchySeq->ℝ : isLimit s CauchySeq->ℝ
  isLimit-CauchySeq->ℝ .isLimit.lower q = ∥-map handle
    where
    handle : Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.L (s m) (q r+ ⟨ ε ⟩)) ->
             Σ[ n ∈ ℕ ] ((m : Nat) -> m ≥ n -> Real.L (s m) q)
    handle (n , (ε , 0<ε) , f) = (n , g)
      where
      g : (m : Nat) -> m ≥ n -> Real.L (s m) q
      g m m≥n = Real.isLowerSet-L (s m) _ _ (trans-=-< (sym +-right-zero) (+₁-preserves-< 0<ε))
                                  (f m m≥n)

  isLimit-CauchySeq->ℝ .isLimit.upper q = ∥-map handle
    where
    handle : Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> Real.U (s m) (q r+ (- ⟨ ε ⟩))) ->
             Σ[ n ∈ ℕ ] ((m : Nat) -> m ≥ n -> Real.U (s m) q)
    handle (n , (ε , 0<ε) , f) = (n , g)
      where
      g : (m : Nat) -> m ≥ n -> Real.U (s m) q
      g m m≥n = Real.isUpperSet-U (s m) _ _ (trans-<-= (+₁-preserves-< (minus-flips-0< 0<ε))
                                                       +-right-zero)
                                  (f m m≥n)

  Cauchy->isConvergentSequence : isConvergentSequence s
  Cauchy->isConvergentSequence = _ , isLimit-CauchySeq->ℝ
-}
