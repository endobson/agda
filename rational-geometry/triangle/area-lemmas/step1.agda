{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.triangle.area-lemmas.step1 where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import combinatorics.triangular-numbers.rational-path
open import combinatorics.triangular-numbers.sum-path
open import equality-path
open import fin
open import abs
open import finite-commutative-monoid.instances
open import finset
open import finset.instances
open import finsum
open import finsum.arithmetic
open import funext
open import hlevel.base
open import hlevel.sigma
open import int.add1
open import int.addition
open import int.base
open import int.order
open import nat
open import nat.order
open import order
open import order.instances.int
open import order.minmax.instances.int
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.int
open import ordered-semiring.instances.real
open import ordered-semiring.instances.rational
open import ordered-semiring.archimedean.instances.rational
open import ordered-semiring.archimedean.small
open import heyting-field.instances.real
open import heyting-field.instances.rational
open import real.apartness
open import ordered-semiring
open import ordered-semiring.natural-reciprocal
open import rational
open import rational-geometry.area.base
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.boxes.area
open import rational-geometry.point
open import rational-geometry.region
open import rational.order
open import rational.quotient
open import real
open import real.rational
open import real.arithmetic.rational
open import ring
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import semiring.natural-reciprocal
open import semiring.initial
open import semiring.instances.nat
open import truncation


private
  suc-pred-Pos : ∀ ((n , _) : Nat⁺) -> suc (pred n) == n
  suc-pred-Pos (suc n , _) = refl

unit-right-triangle-Region : Region ℓ-zero
unit-right-triangle-Region = record { predicate = \p -> P p , isProp-P p }
  where
  P : Point -> Type₀
  P (x , y) = (0# ≤ y) × (x < 1#) × (y ≤ x)

  isProp-P : ∀ p -> isProp (P p)
  isProp-P _ = isProp× isProp-≤ (isProp× isProp-< isProp-≤)



private
  module over-approx (n⁺@(n , pos-n) : Nat⁺) where
    0<n : 0 < n
    0<n = Pos'->< pos-n
    1/n : ℚ
    1/n = 1/ℕ n⁺

    I : Type₀
    I = Fin n

    box : I -> Box
    box (i , _) = record
      { left = ℕ->ℚ i * 1/n
      ; right = ℕ->ℚ (suc i) * 1/n
      ; bottom = 0#
      ; top = ℕ->ℚ (suc i) * 1/n
      ; left<right = *₂-preserves-< (ℕ->ℚ-preserves-< refl-≤) (0<1/ℕ n⁺)
      ; bottom<top = *-preserves-0< (ℕ->ℚ-preserves-< zero-<) (0<1/ℕ n⁺)
      }

    boxes : Boxes ℓ-zero
    boxes = record
      { Index = I , isFinSetⁱ
      ; box = box
      }

    box-area-path : ∀ i -> Box.area (box i) == ℕ->ℚ (suc (Fin.i i)) * (1/n * 1/n)
    box-area-path ii@(i , _) = *-cong l-path r-path >=> *-commute >=> *-assoc
      where
      module b = Box (box ii)
      l-path : diff b.left b.right == 1/n
      l-path =
        sym *-distrib-diff-right >=>
        *-left (sym (ℤ->ℚ-preserves-diff _ _) >=>
                cong ℤ->ℚ (add1-extract-left >=> cong add1 +-inverse)) >=>
        *-left-one
      r-path : diff b.bottom b.top == ℕ->ℚ (suc i) * 1/n
      r-path = sym +-left-zero >=> diff-step

    no-overlap : hasNoOverlap boxes
    no-overlap p (i₁ , _) (i₂ , _) (l₁≤px , px<r₁ , _ , _) (l₂≤px , px<r₂ , _ , _) =
      fin-i-path (cong pred (antisym-≤ lt₁ lt₂))
      where
      lt₁ : i₁ < (suc i₂)
      lt₁ =
        ℕ->ℤ-reflects-< (ℤ->ℚ-reflects-< _ _
          (*₂-reflects-< (trans-≤-< l₁≤px px<r₂) (asym-< (0<1/ℕ n⁺))))

      lt₂ : i₂ < (suc i₁)
      lt₂ =
        ℕ->ℤ-reflects-< (ℤ->ℚ-reflects-< _ _
          (*₂-reflects-< (trans-≤-< l₂≤px px<r₁) (asym-< (0<1/ℕ n⁺))))

    contains : ∀ p -> Region.contains unit-right-triangle-Region p ->
                      Boxes.contains boxes p
    contains (x , y) (0≤y , x<1 , y≤x) = ∣ (i , i<n) , (l≤x , x<r , 0≤y , (trans-≤-< y≤x x<r)) ∣
      where
      iℤ : ℤ
      iℤ = quotientℚ x (1/n , 0<1/ℕ n⁺)
      i : ℕ
      i = abs' iℤ

      iℤ-path : ℕ->ℤ i == iℤ
      iℤ-path = abs'-abs-path >=> abs-0≤-path (quotientℚ-preserves-0≤ _ _ (trans-≤ 0≤y y≤x))


      lt₁ : (ℤ->ℚ iℤ * 1/n) ≤ x
      lt₁ = trans-=-≤ (sym +-right-zero) (trans-≤-= (+₁-preserves-≤ (0≤remainderℚ _ _))
                                                    (quotient-remainderℚ x (1/n , 0<1/ℕ n⁺)))

      lt₂ : ℕ->ℚ i < ℕ->ℚ n
      lt₂ =
        trans-=-<
          (cong ℤ->ℚ iℤ-path >=> sym *-right-one >=> *-right (sym (1/ℕ-ℕ-path n⁺)) >=> sym *-assoc)
          (trans-<-=
            (*₂-preserves-< (trans-≤-< lt₁ x<1) (ℕ->ℚ-preserves-< 0<n))
            *-left-one)

      i<n : i < n
      i<n = ℕ->ℤ-reflects-< (ℤ->ℚ-reflects-< _ _ lt₂)

      l≤x : (ℕ->ℚ i * 1/n) ≤ x
      l≤x = trans-=-≤ (*-left (cong ℤ->ℚ iℤ-path)) lt₁
      x<r : x < (ℕ->ℚ (suc i) * 1/n)
      x<r =
        trans-=-<
          (sym (quotient-remainderℚ x (1/n , 0<1/ℕ n⁺)))
          (trans-<-=
            (+₁-preserves-< (small-remainderℚ x (1/n , 0<1/ℕ n⁺)))
            (+-right (sym *-left-one) >=>
             sym *-distrib-+-right >=>
             *-left (+-commute >=> sym (Semiringʰ.preserves-+ Semiringʰ-ℤ->ℚ _ _) >=>
                     cong ℤ->ℚ (ℤ+-eval >=> cong add1 (sym iℤ-path)))))

    boxes-area-path : boxes-area boxes == 1/2 + (1/2 * 1/n)
    boxes-area-path =
      boxes-area-hasNoOverlap boxes no-overlap >=>
      cong finiteSum (funExt (\i -> box-area-path i >=> *-commute)) >=>
      finiteSum-* >=>
      *-commute >=>
      *-left ((finiteMerge-homo-inject (record { monoidʰ = (Semiringʰ.+ʰ Semiringʰ-ℕ->ℚ) })) >=>
              cong ℕ->ℚ (triangular-number-sum-path n) >=>
              (triangular-number-rational-path n)) >=>
      simplify
      where
      module h = Semiringʰ Semiringʰ-ℕ->ℚ
      simplify₁ : (ℕ->ℚ (suc n * n)) == ((ℕ->ℚ n) * (ℕ->ℚ n)) * (1# + 1/n)
      simplify₁ =
        h.preserves-+ n (n * n) >=>
        +-commute >=>
        +-left (h.preserves-* n n >=> sym *-right-one >=> *-assoc) >=>
        +-right (sym *-right-one >=> (*-right (sym (1/ℕ-ℕ-path n⁺) >=> *-commute))) >=>
        sym *-distrib-+-left >=>
        *-right (sym *-distrib-+-left) >=>
        sym *-assoc
      simplify₂ : (1/n * 1/n) * ((ℕ->ℚ n) * (ℕ->ℚ n)) == 1#
      simplify₂ = *-swap >=> *-cong (1/ℕ-ℕ-path n⁺) (1/ℕ-ℕ-path n⁺) >=> *-left-one


      simplify : (ℕ->ℚ (suc n * n) * 1/2) * (1/n * 1/n) == 1/2 + (1/2 * 1/n)
      simplify =
        *-left (*-left simplify₁ >=> *-assoc >=> *-right *-commute) >=>
        *-commute >=> sym *-assoc >=>
        *-left simplify₂ >=>
        *-left-one >=>
        *-distrib-+-left >=>
        +-left (*-right-one)


  outer-approx : ∀ (q : ℚ) -> Real.U 1/2 q ->
                 ∃[ b ∈ (Boxes ℓ-zero) ] (isOuterApproximation unit-right-triangle-Region q b)
  outer-approx q 1/2'<q = ∥-map (\ (n , n<ε) -> answer n n<ε) small-n
    where

    1/2<q : 1/2 < q
    1/2<q = U->ℚ< (subst (\x -> Real.U x q) path 1/2'<q)
      where
      path : 1/2 == ℚ->ℝ 1/2
      path = sym (Semiringʰ-preserves-1/ℕ Semiringʰ-ℚ->ℝ 2⁺) >=>
             cong ℚ->ℝ (∃!-unique (∃!1/ℕ 2⁺) _ (*-commute >=> 1/ℕ-ℕ-path 2⁺))

    ε : ℚ
    ε = diff 1/2 q
    0<ε : 0# < ε
    0<ε = diff-0<⁺ 1/2<q

    small-n : ∃[ n ∈ Nat⁺ ] (1/ℕ n < ε)
    small-n = small-1/ℕ (ε , 0<ε)

    module _ (n : Nat⁺) (1/n<ε : 1/ℕ n < ε) where
      B : Boxes ℓ-zero
      B = over-approx.boxes n
      small-boxes : boxes-area B < q
      small-boxes =
        trans-=-< (over-approx.boxes-area-path n)
          (trans-<-= (+₁-preserves-< (trans-≤-< 1/2*1/n≤1/n 1/n<ε)) diff-step)
        where
        n=n : ℕ->Semiring ⟨ n ⟩ == ℕ->ℚ ⟨ n ⟩
        n=n i = ∃!-unique ∃!ℕ->Semiring _ Semiringʰ-ℕ->ℚ i ⟨ n ⟩
        1/2*1/n≤1/n : (1/2 * 1/ℕ n) ≤ 1/ℕ n
        1/2*1/n≤1/n =
          trans-≤-= (*₂-preserves-≤ (1/ℕ≤1 2⁺) (0≤1/ℕ n))
                    (*-left-one >=> (sym (∃!-unique (∃!1/ℕ n) _ (*-left n=n >=> *-commute >=> 1/ℕ-ℕ-path n))))



      answer : Σ[ b ∈ (Boxes ℓ-zero) ] (isOuterApproximation unit-right-triangle-Region q b)
      answer = B , record
        { contains = over-approx.contains n
        ; bounded = weaken-< small-boxes
        }


  module under-approx (n⁺@(n , pos-n) : Nat⁺) where
    1/n : ℚ
    1/n = 1/ℕ n⁺

    n₀ : Nat
    n₀ = pred n

    I : Type₀
    I = Fin n₀

    box : I -> Box
    box (i , _) = record
      { left = ℕ->ℚ (suc i) * 1/n
      ; right = ℕ->ℚ (suc (suc i)) * 1/n
      ; bottom = 0#
      ; top = ℕ->ℚ (suc i) * 1/n
      ; left<right = *₂-preserves-< (ℕ->ℚ-preserves-< refl-≤) (0<1/ℕ n⁺)
      ; bottom<top = *-preserves-0< (ℕ->ℚ-preserves-< zero-<) (0<1/ℕ n⁺)
      }

    boxes : Boxes ℓ-zero
    boxes = record
      { Index = I , isFinSetⁱ
      ; box = box
      }


    box-area-path : ∀ i -> Box.area (box i) == ℕ->ℚ (suc (Fin.i i)) * (1/n * 1/n)
    box-area-path ii@(i , _) = *-cong l-path r-path >=> *-commute >=> *-assoc
      where
      module b = Box (box ii)
      l-path : diff b.left b.right == 1/n
      l-path =
        sym *-distrib-diff-right >=>
        *-left (sym (ℤ->ℚ-preserves-diff _ _) >=>
                cong ℤ->ℚ (add1-extract-left >=> cong add1 +-inverse)) >=>
        *-left-one
      r-path : diff b.bottom b.top == ℕ->ℚ (suc i) * 1/n
      r-path = sym +-left-zero >=> diff-step

    no-overlap : hasNoOverlap boxes
    no-overlap p (i₁ , _) (i₂ , _) (l₁≤px , px<r₁ , _ , _) (l₂≤px , px<r₂ , _ , _) =
      fin-i-path (cong pred (cong pred (antisym-≤ lt₁ lt₂)))
      where
      lt₁ : (suc i₁) < (suc (suc i₂))
      lt₁ =
        ℕ->ℤ-reflects-< (ℤ->ℚ-reflects-< _ _
          (*₂-reflects-< (trans-≤-< l₁≤px px<r₂) (asym-< (0<1/ℕ n⁺))))

      lt₂ : (suc i₂) < (suc (suc i₁))
      lt₂ =
        ℕ->ℤ-reflects-< (ℤ->ℚ-reflects-< _ _
          (*₂-reflects-< (trans-≤-< l₂≤px px<r₁) (asym-< (0<1/ℕ n⁺))))

    contains : ∀ p -> Boxes.contains boxes p ->
                      Region.contains unit-right-triangle-Region p
    contains p@(x , y) c =
      unsquash (snd (Region.predicate unit-right-triangle-Region p))
        (∥-map answer c)
      where
      module _ ((ii@(i , i<n₀) , bl≤x , x<br , bb≤y , y<bt) : Σ[ i ∈ I ] (Box.contains (box i) p)) where
        module b = Box (box ii)
        br≤1 : b.right ≤ 1#
        br≤1 = trans-≤-= (*₂-preserves-≤ (ℕ->ℚ-preserves-≤ ssi≤n)
                                         (weaken-< (0<1/ℕ n⁺)))
                         (*-commute >=> 1/ℕ-ℕ-path n⁺)

          where
          ssi≤n : suc (suc i) ≤ n
          ssi≤n = trans-≤-= (suc-< i<n₀) (suc-pred-Pos n⁺)


        answer : Region.contains unit-right-triangle-Region p
        answer = bb≤y , (trans-<-≤ x<br br≤1) , (weaken-< (trans-<-≤ y<bt bl≤x))


    boxes-area-path : boxes-area boxes == 1/2 + (- (1/2 * 1/n))
    boxes-area-path =
      boxes-area-hasNoOverlap boxes no-overlap >=>
      cong finiteSum (funExt (\i -> box-area-path i >=> *-commute)) >=>
      finiteSum-* >=>
      *-commute >=>
      *-left ((finiteMerge-homo-inject (record { monoidʰ = (Semiringʰ.+ʰ Semiringʰ-ℕ->ℚ) })) >=>
              cong ℕ->ℚ (triangular-number-sum-path n₀) >=>
              (triangular-number-rational-path n₀)) >=>
      simplify
      where
      module h = Semiringʰ Semiringʰ-ℕ->ℚ
      simplify₁ : (ℕ->ℚ (suc n₀ * n₀)) == ((ℕ->ℚ n) * (ℕ->ℚ n)) * (1# + (- 1/n))
      simplify₁ =
        h.preserves-* (suc n₀) n₀ >=>
        *-left (cong ℕ->ℚ sn₀-path) >=>
        *-right (n₀-path >=> sym *-left-one >=> (*-left (sym (1/ℕ-ℕ-path n⁺) >=> *-commute) >=> *-assoc)) >=>
        sym *-assoc >=>
        *-right (*-distrib-diff-left >=> cong2 diff *-right-one (1/ℕ-ℕ-path n⁺))
        where
        sn₀-path : (suc n₀) == n
        sn₀-path = suc-pred-Pos n⁺

        n₀-path : ℕ->ℚ n₀ == diff (ℕ->ℚ 1) (ℕ->ℚ n)
        n₀-path =
          sym +-left-zero >=>
          +-left (sym +-inverse >=> +-commuteᵉ 1# (- 1#)) >=>
          +-assoc >=>
          +-right (sym (h.preserves-+ 1# n₀) >=> cong ℕ->ℚ sn₀-path) >=>
          +-commute

      simplify₂ : (1/n * 1/n) * ((ℕ->ℚ n) * (ℕ->ℚ n)) == 1#
      simplify₂ = *-swap >=> *-cong (1/ℕ-ℕ-path n⁺) (1/ℕ-ℕ-path n⁺) >=> *-left-one

      simplify : (ℕ->ℚ (suc n₀ * n₀) * 1/2) * (1/n * 1/n) == 1/2 + (- (1/2 * 1/n))
      simplify =
        *-left (*-left simplify₁ >=> *-assoc >=> *-right *-commute) >=>
        *-commute >=> sym *-assoc >=>
        *-left simplify₂ >=>
        *-left-one >=>
        *-distrib-diff-left >=>
        +-left (*-right-one)


  inner-approx : ∀ (q : ℚ) -> Real.L 1/2 q ->
                 ∃[ b ∈ (Boxes ℓ-zero) ] (isInnerApproximation unit-right-triangle-Region q b)
  inner-approx q q<1/2' = ∥-map (\ (n , n<ε) -> answer n n<ε) small-n
    where

    q<1/2 : q < 1/2
    q<1/2 = L->ℚ< (subst (\x -> Real.L x q) path q<1/2')
      where
      path : 1/2 == ℚ->ℝ 1/2
      path = sym (Semiringʰ-preserves-1/ℕ Semiringʰ-ℚ->ℝ 2⁺) >=>
             cong ℚ->ℝ (∃!-unique (∃!1/ℕ 2⁺) _ (*-commute >=> 1/ℕ-ℕ-path 2⁺))

    ε : ℚ
    ε = diff q 1/2
    0<ε : 0# < ε
    0<ε = diff-0<⁺ q<1/2

    small-n : ∃[ n ∈ Nat⁺ ] (1/ℕ n < ε)
    small-n = small-1/ℕ (ε , 0<ε)

    module _ (n : Nat⁺) (1/n<ε : 1/ℕ n < ε) where
      B : Boxes ℓ-zero
      B = under-approx.boxes n
      small-boxes : q < boxes-area B
      small-boxes =
        trans-<-= (trans-<-≤ step₂ step₁) (sym (under-approx.boxes-area-path n))
        where
        n=n : ℕ->Semiring ⟨ n ⟩ == ℕ->ℚ ⟨ n ⟩
        n=n i = ∃!-unique ∃!ℕ->Semiring _ Semiringʰ-ℕ->ℚ i ⟨ n ⟩

        1/2*1/n≤1/n : (1/2 * 1/ℕ n) ≤ 1/ℕ n
        1/2*1/n≤1/n =
          trans-≤-= (*₂-preserves-≤ (1/ℕ≤1 2⁺) (weaken-< (0<1/ℕ n)))
                    (*-left-one >=> (sym (∃!-unique (∃!1/ℕ n) _ (*-left n=n >=> *-commute >=> 1/ℕ-ℕ-path n))))

        step₁ : (1/2 + (- (1/ℕ n))) ≤ (1/2 + (- (1/2 * 1/ℕ n)))
        step₁ = +₁-preserves-≤  (minus-flips-≤ 1/2*1/n≤1/n)

        step₂ : q < (1/2 + (- (1/ℕ n)))
        step₂ =
          trans-=-< (sym +-right-zero)
           (trans-<-= (+₁-preserves-< (diff-0<⁺ 1/n<ε))
             (sym +-assoc >=> +-left diff-step))


      answer : Σ[ b ∈ (Boxes ℓ-zero) ] (isInnerApproximation unit-right-triangle-Region q b)
      answer = B , record
        { contains = under-approx.contains n
        ; bounded = weaken-< small-boxes
        }


opaque
  isArea-unit-right-triangle : isArea unit-right-triangle-Region 1/2
  isArea-unit-right-triangle = record
    { inner = inner-approx
    ; outer = outer-approx
    }
