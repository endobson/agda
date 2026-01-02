{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.nth-root.odd where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import functions
open import hlevel
open import isomorphism
open import nat.even-odd
open import order
open import order.instances.nat
open import order.instances.rational
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.real
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
open import real.rational
open import real.open-interval
open import real.arithmetic.rational
open import real.arithmetic.nth-root.bound-sequence
open import real.arithmetic.nth-root.base
open import relation hiding (U)
open import ring.implementations.real
open import semiring
open import semiring.exponentiation
open import sequence
open import sigma.base
open import truncation

module _ ((n , odd-n) : Σ Nat Odd) (x : ℝ) where
  private
    module x = Real x

    ℝ^ℕ-preserves-< : ∀ {x y : ℝ} -> x < y -> (x ^ℕ n) < (y ^ℕ n)
    ℝ^ℕ-preserves-< = Iso.fun (x<y<->x^n<y^n n odd-n _ _)
    ℝ^ℕ-reflects-< : ∀ {x y : ℝ} -> (x ^ℕ n) < (y ^ℕ n) -> x < y
    ℝ^ℕ-reflects-< = Iso.inv (x<y<->x^n<y^n n odd-n _ _)

  opaque
    isProp-ΣisOddNthRoot : isProp (Σ ℝ (isNthRoot n x))
    isProp-ΣisOddNthRoot (y1 , y1^n=x) (y2 , y2^n=x) =
      ΣProp-path (isSet-ℝ _ _) (antisym-≤ y1≤y2 y2≤y1)
      where
      y1^n=y2^n : y1 ^ℕ n == y2 ^ℕ n
      y1^n=y2^n = y1^n=x >=> sym y2^n=x

      y1≤y2 : y1 ≤ y2
      y1≤y2 = path-≤ y1^n=y2^n ∘ ℝ^ℕ-preserves-<
      y2≤y1 : y2 ≤ y1
      y2≤y1 = path-≤ (sym y1^n=y2^n) ∘ ℝ^ℕ-preserves-<

  private
    ^ℕ-isDense : ∀ {q r : ℚ} -> q < r -> ∃[ a ∈ ℚ ] (q < (a ^ℕ n) × (a ^ℕ n) < r)
    ^ℕ-isDense {q} {r} q<r = ∥-bind handle-mid (dense-< q<r)
      where
      Ans : Type₀
      Ans = ∃[ a ∈ ℚ ] (q < (a ^ℕ n) × (a ^ℕ n) < r)
      module _ ((m , q<m , m<r) : Σ[ m ∈ ℚ ] (q < m × m < r)) where
        i1 : Iℚ
        i1 = Iℚ-cons q r (trans-< q<m m<r)
        s : Sequence Iℚ
        s = Root-seq (n , odd-n) m

        root-bound : ∀ i -> Σ[ l ∈ ℚ ] (l ^ℕ n == Iℚ.l (s i))
        root-bound = Root-root-bound (n , odd-n) m

        m∈s : ∀ n -> ℚ∈Iℚ m (s n)
        m∈s = Root-q∈s (n , odd-n) m
        small-s : ArbitrarilySmall (i-width ∘ s)
        small-s = Root-small-s (n , odd-n) m

        s⊂i1 : ∀Largeℕ (\n -> s n i⊂ i1)
        s⊂i1 = ArbitrarilySmall->i⊂ s small-s m∈s i1 (q<m , m<r)

        module _ (idx : Nat) (si⊂i1 : s idx i⊂ i1)
          where
          module si⊂i1 = _i⊂_ si⊂i1

          Σroot-lsi : Σ[ l ∈ ℚ ] (l ^ℕ n == Iℚ.l (s idx))
          Σroot-lsi = root-bound idx

          handle-idx : Ans
          handle-idx =
            ∣ fst Σroot-lsi ,
              trans-<-= si⊂i1.l (sym (snd Σroot-lsi)) ,
              trans-=-< (snd Σroot-lsi) (trans-< (Iℚ.l<u (s idx)) si⊂i1.u) ∣

        handle-mid : Ans
        handle-mid = ∥-bind (\(i , f) -> handle-idx i (f i refl-≤)) s⊂i1


    ^ℕ-preserves-< : ∀ {q r : ℚ} -> q < r -> (q ^ℕ n) < (r ^ℕ n)
    ^ℕ-preserves-< = Iso.fun (x<y<->x^n<y^n n odd-n _ _)
    ^ℕ-reflects-< : ∀ {q r : ℚ} -> (q ^ℕ n) < (r ^ℕ n) -> q < r
    ^ℕ-reflects-< = Iso.inv (x<y<->x^n<y^n n odd-n _ _)

    L : Pred ℚ ℓ-zero
    L q = x.L (q ^ℕ n)
    U : Pred ℚ ℓ-zero
    U q = x.U (q ^ℕ n)

    isLowerSet-L : isLowerSet L
    isLowerSet-L q<r Lr = x.isLowerSet-L (^ℕ-preserves-< q<r) Lr
    isUpperSet-U : isUpperSet U
    isUpperSet-U q<r Lq = x.isUpperSet-U (^ℕ-preserves-< q<r) Lq

    Inhabited-L : Inhabited L
    Inhabited-L = ∥-bind handle x.Inhabited-L
      where
      handle : Σ ℚ x.L -> ∃ ℚ L
      handle (q , xL-q) = ∥-bind handle2 (^ℕ-isDense q1<q)
        where
        q1 : ℚ
        q1 = (q + (- 1#))
        q1<q : q1 < q
        q1<q = trans-<-= (+₁-preserves-< (minus-flips-0< 0<1)) +-right-zero

        handle2 : Σ[ a ∈ ℚ ] (q1 < (a ^ℕ n) × (a ^ℕ n) < q) -> ∃ ℚ L
        handle2 (a , _ , a^n<q) = ∣ a , x.isLowerSet-L a^n<q xL-q ∣

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-bind handle x.Inhabited-U
      where
      handle : Σ ℚ x.U -> ∃ ℚ U
      handle (q , xU-q) = ∥-bind handle2 (^ℕ-isDense q<q1)
        where
        q1 : ℚ
        q1 = (q + 1#)
        q<q1 : q < q1
        q<q1 = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<1)

        handle2 : Σ[ a ∈ ℚ ] (q < (a ^ℕ n) × (a ^ℕ n) < q1) -> ∃ ℚ U
        handle2 (a , q<a^n , _) = ∣ a , x.isUpperSet-U q<a^n xU-q ∣

    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q Lq = ∥-bind handle (x.isUpperOpen-L _ Lq)
      where
      handle : Σ[ r ∈ ℚ ] ((q ^ℕ n) < r × x.L r) -> _
      handle (r , q^n<r , xL-r) = ∥-bind handle2 (^ℕ-isDense q^n<r)
        where
        handle2 : Σ[ p ∈ ℚ ] ((q ^ℕ n) < (p ^ℕ n) × (p ^ℕ n) < r) -> _
        handle2 (p , q^n<p^n , p^n<r) = ∣ p , ^ℕ-reflects-< q^n<p^n , x.isLowerSet-L p^n<r xL-r ∣

    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q Uq = ∥-bind handle (x.isLowerOpen-U _ Uq)
      where
      handle : Σ[ r ∈ ℚ ] (r < (q ^ℕ n) × x.U r) -> _
      handle (r , r<q^n , xU-r) = ∥-bind handle2 (^ℕ-isDense r<q^n)
        where
        handle2 : Σ[ p ∈ ℚ ] (r < (p ^ℕ n) × (p ^ℕ n) < (q ^ℕ n)) -> _
        handle2 (p , r<p^n , p^n<q^n) = ∣ p , ^ℕ-reflects-< p^n<q^n , x.isUpperSet-U r<p^n xU-r ∣

    disjoint : Universal (Comp (L ∩ U))
    disjoint _ = x.disjoint _

    located : (q r : ℚ) -> q < r -> ∥ L q ⊎ U r ∥
    located _ _ q<r = x.located _ _ (^ℕ-preserves-< q<r)


  opaque
    oddNthRoot : ℝ
    oddNthRoot = record
      { L = L
      ; U = U
      ; isProp-L = \_ -> x.isProp-L _
      ; isProp-U = \_ -> x.isProp-U _
      ; Inhabited-L = Inhabited-L
      ; Inhabited-U = Inhabited-U
      ; isLowerSet-L = isLowerSet-L
      ; isUpperSet-U = isUpperSet-U
      ; isUpperOpen-L = isUpperOpen-L
      ; isLowerOpen-U = isLowerOpen-U
      ; disjoint = disjoint
      ; located = located
      }

    isNthRoot-oddNthRoot : isNthRoot n x oddNthRoot
    isNthRoot-oddNthRoot = ℝ∈Iℚ->path (oddNthRoot ^ℕ n) x handle
      where
      o : ℝ
      o = oddNthRoot
      o^n : ℝ
      o^n = o ^ℕ n

      handle : (i : Iℚ) -> ℝ∈Iℚ (oddNthRoot ^ℕ n) i -> ℝ∈Iℚ x i
      handle i@(Iℚ-cons l u l<u) (l<o^n , o^n<u) =
        unsquash (isProp-ℝ∈Iℚ x i)
          (∥-bind2 handle2
            (Real.isUpperOpen-L o^n l l<o^n)
            (Real.isLowerOpen-U o^n u o^n<u))
        where

        handle2 : Σ[ l2 ∈ ℚ ] (l < l2 × Real.L o^n l2) ->
                  Σ[ u2 ∈ ℚ ] (u2 < u × Real.U o^n u2) ->
                  ∥ ℝ∈Iℚ x i ∥
        handle2 (l2 , l<l2 , l2<o^n) (u2 , u2<u , o^n<u2) =
          ∥-map2 handle3 (^ℕ-isDense l<l2) (^ℕ-isDense u2<u)
          where
          handle3 : Σ[ l' ∈ ℚ ] (l < (l' ^ℕ n) × (l' ^ℕ n) < l2) ->
                    Σ[ u' ∈ ℚ ] (u2 < (u' ^ℕ n) × (u' ^ℕ n) < u) ->
                    ℝ∈Iℚ x i
          handle3 (l' , l<l'^n , l'^n<l2) (u' , u2<u'^n , u'^n<u) =
            ℝ<->L (trans-< (ℚ->ℝ-preserves-< l<l'^n) l'^n<x) ,
            ℝ<->U (trans-< x<u'^n (ℚ->ℝ-preserves-< u'^n<u))
            where
            l'^n<o^n : ℚ->ℝ (l' ^ℕ n) < (o ^ℕ n)
            l'^n<o^n = trans-< (ℚ->ℝ-preserves-< l'^n<l2) (L->ℝ< l2<o^n)
            l'<o : ℚ->ℝ l' < o
            l'<o = ℝ^ℕ-reflects-< (trans-=-< (sym (Semiringʰ-preserves-^ℕ Semiringʰ-ℚ->ℝ n)) l'^n<o^n)
            l'^n<x : ℚ->ℝ (l' ^ℕ n) < x
            l'^n<x = L->ℝ< (ℝ<->L l'<o)

            o^n<u'^n : (o ^ℕ n) < ℚ->ℝ (u' ^ℕ n)
            o^n<u'^n = trans-< (U->ℝ< o^n<u2) (ℚ->ℝ-preserves-< u2<u'^n)
            o<u' : o < ℚ->ℝ u'
            o<u' = ℝ^ℕ-reflects-< (trans-<-= o^n<u'^n (Semiringʰ-preserves-^ℕ Semiringʰ-ℚ->ℝ n))
            x<u'^n : x < ℚ->ℝ (u' ^ℕ n)
            x<u'^n = U->ℝ< (ℝ<->U o<u')

  ∃!OddNthRoot : ∃! ℝ (isNthRoot n x)
  ∃!OddNthRoot = (oddNthRoot , isNthRoot-oddNthRoot) ,
                 (isProp-ΣisOddNthRoot _)

  oddNthRoot-preserves-0≤ : 0# ≤ x -> 0# ≤ oddNthRoot
  oddNthRoot-preserves-0≤ 0≤x o<0 = 0≤x x<0
    where
    0^n≤0 : (0# ^ℕ n) ≤ 0#
    0^n≤0 = ^ℕ-odd-≤0 refl-≤ n odd-n
    x<0 : x < 0#
    x<0 = trans-<-≤ (trans-=-< (sym isNthRoot-oddNthRoot) (ℝ^ℕ-preserves-< o<0)) 0^n≤0

  oddNthRoot-preserves-0< : 0# < x -> 0# < oddNthRoot
  oddNthRoot-preserves-0< 0<x = 0<o
    where
    0^n≤0 : (0# ^ℕ n) ≤ 0#
    0^n≤0 = ^ℕ-odd-≤0 refl-≤ n odd-n

    0<o : 0# < oddNthRoot
    0<o = ℝ^ℕ-reflects-< (trans-≤-< 0^n≤0 (trans-<-= 0<x (sym isNthRoot-oddNthRoot)))
