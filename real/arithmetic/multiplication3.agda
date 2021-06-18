{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication3 where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.factor-order
open import rational.minmax
open import real
open import real.sequence
open import real.arithmetic.absolute-value
open import relation hiding (U)
open import ring.implementations.rational
open import sign
open import sign.instances.rational
open import truncation

module _ (x y : ℝ)
  -- (minℚ-preserves-< : (a b c d : ℚ) -> (a < c) -> (b < d) -> (minℚ a b < minℚ c d))
  -- (lowerOpenLℚ⁺ : (z : ℝ) -> (q : ℚ⁺) -> (Real.L z ⟨ q ⟩) ->
  --                 ∃[ r ∈ ℚ⁺ ] (⟨ r ⟩ < ⟨ q ⟩ × Real.L z ⟨ r ⟩))
  -- (lowerOpenUℚ⁺ : (z : ℝ) -> (q : ℚ⁺) -> (Real.U z ⟨ q ⟩) ->
  --                 ∃[ r ∈ ℚ⁺ ] (⟨ r ⟩ < ⟨ q ⟩ × Real.U z ⟨ r ⟩))
  where
  private
    module x = Real x
    module y = Real y

    minℚ4 : (a b c d : ℚ) -> ℚ
    minℚ4 a b c d = minℚ (minℚ a b) (minℚ c d)

    maxℚ4 : (a b c d : ℚ) -> ℚ
    maxℚ4 a b c d = maxℚ (maxℚ a b) (maxℚ c d)

    minProd : (a b c d : ℚ) -> ℚ
    minProd a b c d = (minℚ4 (a r* c) (a r* d) (b r* c) (b r* d))

    maxProd : (a b c d : ℚ) -> ℚ
    maxProd a b c d = (maxℚ4 (a r* c) (a r* d) (b r* c) (b r* d))

    data L' : (q : ℚ) -> Type₀ where
      L'-cons : (a b c d : ℚ) -> x.L a -> x.U b -> y.L c -> y.U d -> L' (minProd a b c d)

    data U' : (q : ℚ) -> Type₀ where
      U'-cons : (a b c d : ℚ) -> x.L a -> x.U b -> y.L c -> y.U d -> U' (maxProd a b c d)

    L : Pred ℚ ℓ-zero
    L q = ∥ L' q ∥
    U : Pred ℚ ℓ-zero
    U q = ∥ U' q ∥


    module _ (a b c d : ℚ) (xl-a : x.L a) (xu-b : x.U b) (yl-c : y.L c) (yu-d : y.U d) where
      private
        Ans : Type₀
        Ans = ∃[ q ∈ ℚ ] (q < minProd a b c d × L' q)

        a<b : a < b
        a<b = ℝ-bounds->ℚ< x a b xl-a xu-b
        c<d : c < d
        c<d = ℝ-bounds->ℚ< y c d yl-c yu-d


      Neg<NonNeg : {q r : ℚ} -> Neg q -> NonNeg r -> q < r
      Neg<NonNeg {q} {r} nq (inj-l pr) = r+-preserves-Pos r (r- q) pr (r--flips-sign _ _ nq)
      Neg<NonNeg {q} {r} nq (inj-r zr) =
        subst Pos (sym (cong (_r+ (r- q)) (Zero-path _ zr) >=> (r+-left-zero (r- q))))
                  (r--flips-sign _ _ nq)

      case-nna-nnc : (NonNeg a) -> (NonNeg c) -> Ans
      case-nna-nnc nn-a nn-c =
        ∣ minProd a' b c d ,
          lt ,
          L'-cons a' b c d xl-a' xu-b yl-c yu-d ∣
        where
        0≤a : 0r ℚ≤ a
        0≤a = NonNeg-0≤ a nn-a
        0≤c : 0r ℚ≤ c
        0≤c = NonNeg-0≤ c nn-c

        c≤d : c ℚ≤ d
        c≤d = inj-l c<d

        a' = (r- 1r)

        a'<a : a' < a
        a'<a = Neg<NonNeg (r--flips-sign _ _ Pos-1r) nn-a

        xl-a' : x.L a'
        xl-a' = x.isLowerSet-L a' a a'<a xl-a

        0<b : 0r < b
        0<b = trans-≤-< {0r} {a} {b} 0≤a a<b

        pos-b : Pos b
        pos-b = 0<-Pos b 0<b

        b-min : minℚ (b r* c) (b r* d) == b r* c
        b-min = sym (r*₁-distrib-min (b , inj-l pos-b) c d) >=>
                cong (b r*_) (minℚ-left c d c≤d)

        a-min : minℚ (a r* c) (a r* d) == a r* c
        a-min = sym (r*₁-distrib-min (a , nn-a) c d) >=>
                cong (a r*_) (minℚ-left c d c≤d)


        full-min : minProd a b c d == (a r* c)
        full-min = cong2 minℚ a-min b-min >=>
                   minℚ-left _ _ (r*₂-preserves-≤ a b (c , nn-c) (inj-l a<b))

        a-lt : (minℚ (a' r* c) (a' r* d)) < (minℚ (a r* c) (a r* d))
        a-lt = subst2 _<_ (sym minℚ'-path) (sym minℚ-path) a'd<ac
          where

          a'c≤ac : (a' r* c) ℚ≤ (a r* c)
          a'c≤ac = r*₂-preserves-≤ a' a (c , nn-c) (inj-l a'<a)

          ac≤ad : (a r* c) ℚ≤ (a r* d)
          ac≤ad = r*₁-preserves-≤ (a , nn-a) c d c≤d

          a'-path : (q : ℚ) -> a' r* q == (r- q)
          a'-path q = RationalRing.minus-extract-left >=> cong r-_ (r*-left-one q)

          a'd<a'c : (a' r* d) < (a' r* c)
          a'd<a'c = subst2 _<_ (sym (a'-path d)) (sym (a'-path c)) (r--flips-order c d c<d)

          a'd<ac : (a' r* d) < (a r* c)
          a'd<ac = trans-<-≤ {a' r* d} {a' r* c} {a r* c} a'd<a'c a'c≤ac


          minℚ'-path : (minℚ (a' r* c) (a' r* d)) == (a' r* d)
          minℚ'-path = minℚ-right (a' r* c) (a' r* d) (inj-l a'd<a'c)
          minℚ-path : (minℚ (a r* c) (a r* d)) == (a r* c)
          minℚ-path = minℚ-left (a r* c) (a r* d) ac≤ad


        a-lt2 : minProd a' b c d ℚ≤ (minℚ (a' r* c) (a' r* d))
        a-lt2 = minℚ-≤-left (minℚ (a' r* c) (a' r* d)) (minℚ (b r* c) (b r* d))

        lt : minProd a' b c d < minProd a b c d
        lt = trans-≤-< {minProd a' b c d} {minℚ (a' r* c) (a' r* d)} {minProd a b c d}
                       a-lt2 (subst ((minℚ (a' r* c) (a' r* d)) <_) (a-min >=> sym full-min) a-lt)




    -- find-smaller-xL-pos : (a : ℚ) -> Pos a -> (c d : ℚ) -> x.L a -> y.L c -> y.U d ->
    --                       ∃[ a' ∈ ℚ ] (x.L a' × (minℚ (a' r* c) (a' r* d) < minℚ (a r* c) (a r* d)))
    -- find-smaller-xL-pos a pos-a c d xl-a yl-c yu-d =
    --   where
    --   a⁺ : ℚ⁺
    --   a⁺ = a , pos-a
    --   c<d : c < d
    --   c<d = ℝ-bounds->ℚ< y c d yl-c yu-d
    --   handle : Σ[ a' ∈ ℚ⁺ ] (⟨ a' ⟩ < a × x.L ⟨ a' ⟩) -> _
    --   handle (a'⁺@(a' , _) , a'<a , xl-a') = a' , (xl-a' , lt)
    --     where
    --     lt : (minℚ (a' r* c) (a' r* d)) < (minℚ (a r* c) (a r* d))
    --     lt = ?
    --       where
    --       a'c<a'd = r*₁-preserves-order a'⁺ c d c<d
    --       ac<ad = r*₁-preserves-order a⁺ c d c<d
    --       minℚ'-path : (minℚ (a' r* c) (a' r* d)) == (a' r* c)
    --       minℚ'-path = minℚ-left (a' r* c) (a' r* d) (inj-l a'c<a'd)
    --       minℚ-path : (minℚ (a r* c) (a r* d)) == (a r* c)
    --       minℚ-path = minℚ-left (a r* c) (a r* d) (inj-l ac<ad)


    -- find-smaller-xL : (a c d : ℚ) -> x.L a -> y.L c -> y.L d ->
    --                   ∃[ a' ∈ ℚ ] (x.L a' × (minℚ (a' r* c) (a' r* d) < minℚ (a r* c) (a r* d)))
    -- find-smaller-xL = ?


    -- isLowerSet-L : is
