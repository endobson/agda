{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence where

open import base
open import equality
open import hlevel
open import nat.arithmetic
open import nat.properties
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-< )
open import rational.minmax
open import relation hiding (U)
open import ring.implementations.rational
open import real
open import semiring
open import truncation
open import order
open import order.instances.nat
open import order.instances.rational
open import sign
open import sign.instances.rational

open import nat using (≤-max-left ; ≤-max-right)

private
  variable
    ℓ : Level

ℚSequence : Type₀
ℚSequence = Nat -> ℚ

private
  Seq = ℚSequence

Cauchy : Pred Seq ℓ-zero
Cauchy s = (ε : ℚ⁺) -> ∃[ n ∈ Nat ] ((m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                                     (abs-diffℚ (s m₁) (s m₂)) < ⟨ ε ⟩)

OpenEventualUpperBound : Seq -> Pred ℚ ℓ-zero
OpenEventualUpperBound s q = ∃[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> (s m r+ ⟨ ε ⟩) < q)

OpenEventualLowerBound : Seq -> Pred ℚ ℓ-zero
OpenEventualLowerBound s q = ∃[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> (q r+ ⟨ ε ⟩) < s m)


private
  diff-swap : (a b c : ℚ) -> (a r+ (r- b)) < c -> (a r+ (r- c)) < b
  diff-swap a b c = subst Pos path
    where
    path : c r+ (r- (a r+ (r- b))) == b r+ (r- (a r+ (r- c)))
    path =
      cong (c r+_) ((RationalRing.minus-distrib-plus {a} {r- b}) >=>
                    cong ((r- a) r+_) (RationalRing.minus-double-inverse {b}) >=>
                    (r+-commute (r- a) b)) >=>
      r+-commute c (b r+ (r- a)) >=>
      cong ((b r+ (r- a)) r+_) (sym (RationalRing.minus-double-inverse {c})) >=>
      r+-assoc b (r- a) (r- (r- c)) >=>
      cong (b r+_) (sym (RationalRing.minus-distrib-plus {a} {r- c}))

  ε-weaken-< : (q r : ℚ) -> (ε : ℚ⁺) -> (q r+ ⟨ ε ⟩) < r -> q < r
  ε-weaken-< q r ε⁺@(ε , _) lt =
    rational.order.trans-< {q} {q r+ ε} {r} (r+-Pos->order q ε⁺) lt

  abs-diffℚ-weaken-< : (x y z : ℚ) -> (abs-diffℚ x y) < z -> (diffℚ x y) < z
  abs-diffℚ-weaken-< x y z lt =
    maxℚ-weaken-<₁ (diffℚ x y) (r- (diffℚ x y)) z lt

  midℚ-plus-half-diffℚ : (x y : ℚ) -> (midℚ x y r+ (1/2r r* (diffℚ x y))) == y
  midℚ-plus-half-diffℚ x y =
    sym (*-distrib-+-left {_} {_} {1/2r} {x r+ y} {diffℚ x y}) >=>
    cong (1/2r r*_)
      (cong2 _r+_ (r+-commute x y) (r+-commute y (r- x)) >=>
       r+-assoc y x ((r- x) r+ y) >=>
       cong (y r+_) ((sym (r+-assoc x (r- x) y)) >=>
                     cong (_r+ y) (r+-inverse x) >=>
                     r+-left-zero y)) >=>
    (*-distrib-+-left {_} {_} {1/2r} {y} {y}) >=>
    1/2r-path' y

  midℚ-commute : (x y : ℚ) -> midℚ x y == midℚ y x
  midℚ-commute x y = cong (1/2r r*_) (r+-commute x y)

  midℚ-minus-half-diffℚ : (x y : ℚ) -> (midℚ x y r+ (r- (1/2r r* (diffℚ x y)))) == x
  midℚ-minus-half-diffℚ x y =
    cong2 _r+_ (midℚ-commute x y)
      (sym (RationalRing.minus-extract-right {1/2r} {diffℚ x y}) >=>
       cong (1/2r r*_) (sym (diffℚ-anticommute y x))) >=>
    midℚ-plus-half-diffℚ y x

  diffℚ-midℚ : (a b : ℚ) -> diffℚ (midℚ a b) b == 1/2r * diffℚ a b
  diffℚ-midℚ a b =
    cong (_r+ (r- (midℚ a b))) (sym (midℚ-plus-half-diffℚ a b)) >=>
    r+-assoc (midℚ a b) (1/2r r* diffℚ a b) (r- (midℚ a b)) >=>
    diffℚ-step (midℚ a b) (1/2r r* diffℚ a b)

  diffℚ-midℚ' : (a b : ℚ) -> diffℚ a (midℚ a b) == 1/2r * diffℚ a b
  diffℚ-midℚ' a b =
    cong ((midℚ a b) r+_) (cong r-_ (sym (midℚ-minus-half-diffℚ a b)) >=>
                           sym (diffℚ-anticommute (midℚ a b) (1/2r r* (diffℚ a b)))) >=>
    diffℚ-step (midℚ a b) (1/2r r* diffℚ a b)

midℚ-<₁ : (a b : ℚ) -> (a < b) -> a < (midℚ a b)
midℚ-<₁ a b a<b = subst Pos (sym (diffℚ-midℚ' a b)) (r*-preserves-Pos 1/2r _ (Pos-1/ℕ _) a<b)

midℚ-<₂ : (a b : ℚ) -> (a < b) -> (midℚ a b) < b
midℚ-<₂ a b a<b = subst Pos (sym (diffℚ-midℚ a b)) (r*-preserves-Pos 1/2r _ (Pos-1/ℕ _) a<b)


module _
  (s : Seq) (cauchy : Cauchy s)
  where

  private
    L : Pred ℚ ℓ-zero
    L = OpenEventualLowerBound s

    U : Pred ℚ ℓ-zero
    U = OpenEventualUpperBound s

    1r⁺ : ℚ⁺
    1r⁺ = 1r , Pos-1r
    1/2r⁺ : ℚ⁺
    1/2r⁺ = 1/2r , Pos-1/ℕ (2 , tt)


    Inhabited-L : Inhabited L
    Inhabited-L = ∥-map handle (cauchy 1/2r⁺)
      where
      handle : Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                             (abs-diffℚ (s m₁) (s m₂)) < 1/2r) ->
               Σ ℚ L
      handle (n , f) = lb , ∣ n , 1/2r⁺ , g ∣
        where
        lb = s n r+ (r- 1r)

        lb-path : lb r+ 1/2r == s n r+ (r- 1/2r)
        lb-path =
          r+-assoc (s n) (r- 1r) 1/2r >=>
          cong (s n r+_)
            (r+-commute (r- 1r) 1/2r >=>
             cong (1/2r r+_) (cong r-_ (sym (1/2r-path 1r) >=>
                                        cong2 _r+_ (r*-left-one 1/2r) (r*-left-one 1/2r)) >=>
                              (RationalRing.minus-distrib-plus {1/2r} {1/2r})) >=>
             sym (r+-assoc 1/2r (r- 1/2r) (r- 1/2r)) >=>
             cong (_r+ (r- 1/2r)) (r+-inverse 1/2r) >=>
             r+-left-zero (r- 1/2r))

        g : (m : Nat) -> m ≥ n -> (lb r+ 1/2r) < s m
        g m gt = subst (_< s m) (sym lb-path) lt3
          where
          lt : (abs-diffℚ (s m) (s n)) < 1/2r
          lt = f m n gt refl-≤

          lt2 : ((s n) r+ (r- (s m))) < 1/2r
          lt2 = abs-diffℚ-weaken-< (s m) (s n) 1/2r lt

          lt3 : (s n r+ (r- 1/2r)) < s m
          lt3 = diff-swap (s n) (s m) 1/2r lt2

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-map handle (cauchy 1/2r⁺)
      where
      handle : Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                             (abs-diffℚ (s m₁) (s m₂)) < 1/2r) ->
               Σ ℚ U
      handle (n , f) = ub , ∣ n , 1/2r⁺ , g ∣
        where
        ub = s n r+ 1r

        g : (m : Nat) -> m ≥ n -> (s m r+ 1/2r) < ub
        g m gt = subst (_< ub) path lt4
          where
          lt : (abs-diffℚ (s n) (s m)) < 1/2r
          lt = f n m refl-≤ gt

          lt2 : diffℚ (s n) (s m) < 1/2r
          lt2 = abs-diffℚ-weaken-< (s n) (s m) 1/2r lt

          lt3 : (s m r+ (r- 1/2r)) < s n
          lt3 = diff-swap (s m) (s n) 1/2r lt2

          lt4 : ((s m r+ (r- 1/2r)) r+ 1r) < ub
          lt4 = r+₂-preserves-order (s m r+ (r- 1/2r)) (s n) 1r lt3

          path : (s m r+ (r- 1/2r)) r+ 1r == s m r+ 1/2r
          path =
            r+-assoc (s m) (r- 1/2r) 1r >=>
            cong (s m r+_)
              (r+-commute (r- 1/2r) 1r >=>
               cong (_r+ (r- 1/2r)) (sym (1/2r-path 1r) >=>
                                     cong2 _r+_ (r*-left-one 1/2r) (r*-left-one 1/2r)) >=>
               r+-assoc 1/2r 1/2r (r- 1/2r) >=>
               cong (1/2r r+_) (r+-inverse 1/2r) >=>
               r+-right-zero 1/2r)


    isLowerSet-L : isLowerSet L
    isLowerSet-L q r q<r lr = ∥-map handle lr
      where
      handle : Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : ℕ) -> (m ≥ n) -> (r r+ ⟨ ε ⟩) < s m) ->
               Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : ℕ) -> (m ≥ n) -> (q r+ ⟨ ε ⟩) < s m)
      handle (n , ε⁺@(ε , _) , f) = n , ε⁺ , g
        where
        g : (m : ℕ) -> (m ≥ n) -> (q r+ ε) < s m
        g m gt = rational.order.trans-< {q r+ ε} {r r+ ε} {s m} q<r' (f m gt)
          where
          q<r' : (q r+ ε) < (r r+ ε)
          q<r' = r+₂-preserves-order q r ε q<r

    isUpperSet-U : isUpperSet U
    isUpperSet-U q r q<r uq = ∥-map handle uq
      where
      handle : Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : ℕ) -> (m ≥ n) -> (s m r+ ⟨ ε ⟩) < q) ->
               Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : ℕ) -> (m ≥ n) -> (s m r+ ⟨ ε ⟩) < r)
      handle (n , ε⁺@(ε , _) , f) = n , ε⁺ , g
        where
        g : (m : ℕ) -> (m ≥ n) -> (s m r+ ε) < r
        g m gt = rational.order.trans-< {s m r+ ε} {q} {r} (f m gt) q<r

    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q lq = ∥-map handle lq
      where
      handle : Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : ℕ) -> (m ≥ n) -> (q r+ ⟨ ε ⟩) < s m) ->
               Σ[ r ∈ ℚ ] (q < r ×
                           ∃[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : ℕ) -> (m ≥ n) -> (r r+ ⟨ ε ⟩) < s m))
      handle (n , ((ε , pos-ε) , f)) = (r , (q<r , ∣ n , (ε/2 , pos-ε/2) , g ∣))
        where
        ε/2 = (ε r* 1/2r)
        pos-ε/2 : Pos ε/2
        pos-ε/2 = r*-preserves-Pos ε 1/2r pos-ε (Pos-1/ℕ (2 , tt))
        r = q r+ ε/2
        q<r : q < r
        q<r = r+-Pos->order q (ε/2 , pos-ε/2)
        g : (m : ℕ) -> (m ≥ n) -> (r r+ ε/2) < s m
        g m gt = subst (_< s m) p (f m gt)
          where
          p : (q r+ ε) == (r r+ ε/2)
          p = cong (q r+_) (sym (1/2r-path ε)) >=>
              sym (r+-assoc q ε/2 ε/2)

    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q uq = ∥-map handle uq
      where
      handle : Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : ℕ) -> (m ≥ n) -> (s m r+ ⟨ ε ⟩) < q) ->
               Σ[ r ∈ ℚ ] (r < q ×
                           ∃[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : ℕ) -> (m ≥ n) -> (s m r+ ⟨ ε ⟩) < r))
      handle (n , ((ε , pos-ε) , f)) = (r , (r<q , ∣ n , (ε/2 , pos-ε/2) , g ∣))
        where
        ε/2 = (ε r* 1/2r)
        pos-ε/2 : Pos ε/2
        pos-ε/2 = r*-preserves-Pos ε 1/2r pos-ε (Pos-1/ℕ (2 , tt))
        r = q r+ (r- ε/2)
        q-path : r r+ ε/2 == q
        q-path = r+-assoc q (r- ε/2) ε/2 >=>
                 (cong (q r+_) (r+-commute (r- ε/2) ε/2 >=> r+-inverse ε/2)) >=>
                 (r+-right-zero q)

        r<q : r < q
        r<q = subst (r <_) q-path (r+-Pos->order r (ε/2 , pos-ε/2))
        g : (m : ℕ) -> (m ≥ n) -> (s m r+ ε/2) < r
        g m gt = subst (_< r) p lt2
          where
          lt1 : (s m r+ ε) < q
          lt1 = (f m gt)

          lt2 : ((s m r+ ε) r+ (r- ε/2)) < r
          lt2 = r+₂-preserves-order (s m r+ ε) q (r- ε/2) lt1

          p : (s m r+ ε) r+ (r- ε/2) == s m r+ ε/2
          p = cong (_r+ (r- ε/2)) (cong (s m r+_) (sym (1/2r-path ε)) >=>
                                   sym (r+-assoc (s m) ε/2 ε/2)) >=>
              (r+-assoc (s m r+ ε/2) ε/2 (r- ε/2)) >=>
              (cong ((s m r+ ε/2) r+_) (r+-inverse ε/2)) >=>
              r+-right-zero (s m r+ ε/2)


    disjoint : Universal (Comp (L ∩ U))
    disjoint q (l , u) = unsquash isPropBot (∥-map2 handle l u)
      where
      handle : Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : ℕ) -> (m ≥ n) -> (q r+ ⟨ ε ⟩) < s m) ->
               Σ[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : ℕ) -> (m ≥ n) -> (s m r+ ⟨ ε ⟩) < q) ->
               Bot
      handle (nl , (εl , fl))  (nu , (εu , fu)) =
        irrefl-< {a = q} (trans-< {a = q} {b = s n} {c = q}
                           (ε-weaken-< q (s n) εl (fl n ≤-max-left))
                           (ε-weaken-< (s n) q εu (fu n ≤-max-right)))
        where
        n = max nl nu

    private
      1/4r = (1/ℕ (2 , tt)) r* (1/ℕ (2 , tt))
      Pos-1/2r = (Pos-1/ℕ (2 , tt))
      Pos-1/4r = r*-preserves-Pos 1/2r 1/2r Pos-1/2r Pos-1/2r

    located : (x y : Rational) -> x < y -> ∥ L x ⊎ U y ∥
    located x y x<y = ∥-map handle (cauchy d⁺)
      where
      d = 1/2r r* (1/2r r* (diffℚ x y))
      dd = d r+ d
      mid = midℚ x y

      dd-path : dd == (1/2r r* diffℚ x y)
      dd-path = 1/2r-path' (1/2r r* diffℚ x y)

      pos-d : Pos d
      pos-d =
        r*-preserves-Pos 1/2r (1/2r r* (y r+ (r- x)))
          Pos-1/2r
          (r*-preserves-Pos 1/2r (y r+ (r- x)) Pos-1/2r x<y)
      d⁺ : ℚ⁺
      d⁺ = d , pos-d
      handle : Σ[ n ∈ Nat ] ((m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                             (abs-diffℚ (s m₁) (s m₂)) < d) ->
               L x ⊎ U y
      handle (n , f) = handle2 (trichotomous-< t mid)
        where
        t = s n
        handle2 : Tri (t < mid) (t == mid) (t > mid) -> L x ⊎ U y
        handle2 (tri< lt _ _) = inj-r ∣ n , d⁺ ,  g ∣
          where
          g : (m : Nat) -> m ≥ n -> (s m r+ d) < y
          g m m≥n = subst2 _<_ path2 path1 lt5
            where
            lt1 : (abs-diffℚ (s n) (s m)) < d
            lt1 = f n m refl-≤ m≥n
            lt2 : (s m r+ (r- s n)) < d
            lt2 = abs-diffℚ-weaken-< (s n) (s m) d lt1

            lt3 : (s m r+ (r- d)) < t
            lt3 = diff-swap (s m) (s n) d lt2

            lt4 : (s m r+ (r- d)) < mid
            lt4 = rational.order.trans-< {s m r+ (r- d)} {t} {mid} lt3 lt

            lt5 : ((s m r+ (r- d)) r+ dd) < (mid r+ dd)
            lt5 = r+₂-preserves-order (s m r+ (r- d)) mid dd lt4

            path1 : (mid r+ dd) == y
            path1 = cong (mid r+_) dd-path >=> midℚ-plus-half-diffℚ x y

            path2 : ((s m r+ (r- d)) r+ (d r+ d)) == s m r+ d
            path2 =
              r+-assoc (s m) (r- d) dd >=>
              cong (s m r+_)
                (sym (r+-assoc (r- d) d d) >=>
                 cong (_r+ d) (r+-commute (r- d) d >=> r+-inverse d) >=>
                 r+-left-zero d)

        handle2 (tri= _ t==mid _) = inj-r ∣ n , d⁺ ,  g ∣
          where
          g : (m : Nat) -> m ≥ n -> (s m r+ d) < y
          g m m≥n = subst2 _<_ path2 path1 lt5
            where
            lt1 : (abs-diffℚ (s n) (s m)) < d
            lt1 = f n m refl-≤ m≥n
            lt2 : (s m r+ (r- s n)) < d
            lt2 = abs-diffℚ-weaken-< (s n) (s m) d lt1

            lt3 : (s m r+ (r- d)) < t
            lt3 = diff-swap (s m) (s n) d lt2

            lt4 : (s m r+ (r- d)) < mid
            lt4 = subst ((s m r+ (r- d)) <_) t==mid lt3

            lt5 : ((s m r+ (r- d)) r+ dd) < (mid r+ dd)
            lt5 = r+₂-preserves-order (s m r+ (r- d)) mid dd lt4

            path1 : (mid r+ dd) == y
            path1 = cong (mid r+_) dd-path >=> midℚ-plus-half-diffℚ x y

            path2 : ((s m r+ (r- d)) r+ (d r+ d)) == s m r+ d
            path2 =
              r+-assoc (s m) (r- d) dd >=>
              cong (s m r+_)
                (sym (r+-assoc (r- d) d d) >=>
                 cong (_r+ d) (r+-commute (r- d) d >=> r+-inverse d) >=>
                 r+-left-zero d)

        handle2 (tri> _ _ mid<t) = inj-l ∣ n , d⁺ ,  g ∣
          where
          g : (m : Nat) -> m ≥ n -> (x r+ d) < s m
          g m m≥n = subst (_< s m) path1 lt5
            where
            lt1 : (abs-diffℚ (s m) (s n)) < d
            lt1 = f m n m≥n refl-≤
            lt2 : (s n r+ (r- s m)) < d
            lt2 = abs-diffℚ-weaken-< (s m) (s n) d lt1

            lt3 : (t r+ (r- d)) < s m
            lt3 = diff-swap (s n) (s m) d lt2

            lt4 : (mid r+ (r- d)) < (t r+ (r- d))
            lt4 = r+₂-preserves-order mid t (r- d) mid<t

            lt5 : (mid r+ (r- d)) < s m
            lt5 = rational.order.trans-< {mid r+ (r- d)} {t r+ (r- d)} {s m} lt4 lt3

            path1 : mid r+ (r- d) == (x r+ d)
            path1 =
              sym (r+-right-zero (mid r+ (r- d))) >=>
              cong ((mid r+ (r- d)) r+_) (sym (r+-inverse d) >=> r+-commute d (r- d)) >=>
              sym (r+-assoc (mid r+ (r- d)) (r- d) d) >=>
              cong (_r+ d)
                (r+-assoc mid (r- d) (r- d) >=>
                 cong (mid r+_) (sym (RationalRing.minus-distrib-plus {d} {d}) >=>
                                 cong r-_ (1/2r-path' (1/2r r* diffℚ x y))) >=>
                 midℚ-minus-half-diffℚ x y)

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



CenteredBall : ℝ -> ℚ -> Type₀
CenteredBall x ε = Σ[ q ∈ ℚ ] (Real.L x (q r+ (r- ε)) × Real.U x (q r+ ε))

OpenBall : ℝ -> ℚ -> Type₀
OpenBall x ε = Σ[ q1 ∈ ℚ ] Σ[ q2 ∈ ℚ ] (Real.L x q1 × Real.U x q2 × diffℚ q1 q2 == ε)


centered-ball->Pos-ε : (x : ℝ) (ε : ℚ) -> CenteredBall x ε -> Pos ε
centered-ball->Pos-ε x e (q , lq , uq) = subst Pos 1/2-2e==e Pos-1/2-2e
  where
  q-e<q+e : (q r+ (r- e)) < (q r+ e)
  q-e<q+e = ℝ-bounds->ℚ< x _ _ lq uq

  path : diffℚ (q r+ (r- e)) (q r+ e) == 2r r* e
  path = sym (r+-swap-diffℚ q q (r- e) e) >=>
         cong2 _r+_ (r+-inverse q) (cong (e r+_) (RationalRing.minus-double-inverse {e})) >=>
         r+-left-zero (e r+ e) >=>
         2r-path e

  Pos-2e : Pos (2r r* e)
  Pos-2e = subst Pos path q-e<q+e

  Pos-1/2-2e : Pos (1/2r r* (2r r* e))
  Pos-1/2-2e = r*-preserves-Pos 1/2r _ (Pos-1/ℕ _) Pos-2e

  1/2-2e==e : (1/2r r* (2r r* e)) == e
  1/2-2e==e = sym (r*-assoc 1/2r 2r e) >=>
              cong (_r* e) (r*-commute 1/2r 2r >=> 2r-1/2r-path) >=>
              r*-left-one e


center-ball :
  (z : ℝ) (q1 q2 : ℚ) -> (Real.L z q1) -> (Real.U z q2) -> CenteredBall z (1/2r r* (diffℚ q1 q2))
center-ball z q1 q2 Lq Uq =
  (midℚ q1 q2) ,
  subst (Real.L z) (sym (midℚ-minus-half-diffℚ q1 q2)) Lq ,
  subst (Real.U z) (sym (midℚ-plus-half-diffℚ q1 q2)) Uq

weaken-centered-ball : (x : ℝ) (ε₁ ε₂ : ℚ) -> (ε₁ < ε₂) -> CenteredBall x ε₁ -> CenteredBall x ε₂
weaken-centered-ball x e1 e2 e1<e2 (q , lq , uq) =
  (q , x.isLowerSet-L _ _ q-e2<q-e1 lq , x.isUpperSet-U _ _ q+e1<q+e2 uq)
  where
  module x = Real x
  q-e2<q-e1 : (q r+ (r- e2)) < (q r+ (r- e1))
  q-e2<q-e1 = r+₁-preserves-order q (r- e2) (r- e1) (r--flips-order e1 e2 e1<e2)
  q+e1<q+e2 : (q r+ e1) < (q r+ e2)
  q+e1<q+e2 = r+₁-preserves-order q e1 e2 e1<e2


strengthen-centered-ball : (x : ℝ) (ε : ℚ) -> CenteredBall x ε -> ∥ CenteredBall x (1/2r r* ε) ∥
strengthen-centered-ball x e b@(q , l-p1 , u-p5) =
  ∥-map2 handle (x.located p2 p3 p2<p3) (x.located p3 p4 p3<p4)
  where
  module x = Real x
  p1 = q r+ (r- e)
  p3 = q
  p5 = q r+ e
  p2 = midℚ p1 p3
  p4 = midℚ p3 p5

  Pos-e : Pos e
  Pos-e = centered-ball->Pos-ε x e b

  diffℚ-p1p3 : diffℚ p1 p3 == e
  diffℚ-p1p3 = cong (p3 r+_) (sym (diffℚ-anticommute q e)) >=> diffℚ-step q e
  diffℚ-p3p5 : diffℚ p3 p5 == e
  diffℚ-p3p5 = r+-assoc q e (r- q) >=> diffℚ-step q e

  p3<p5 : p3 < p5
  p3<p5 = subst Pos (sym diffℚ-p3p5) Pos-e
  p1<p3 : p1 < p3
  p1<p3 = subst Pos (sym diffℚ-p1p3) Pos-e

  p2<p3 : p2 < p3
  p2<p3 = midℚ-<₂ p1 p3 p1<p3
  p3<p4 : p3 < p4
  p3<p4 = midℚ-<₁ p3 p5 p3<p5


  diffℚ-p2p4 : diffℚ p2 p4 == e
  diffℚ-p2p4 =
    sym (diffℚ-trans p2 p3 p4) >=>
    cong2 _+_ (diffℚ-midℚ p1 p3 >=> cong (1/2r r*_) diffℚ-p1p3)
              (diffℚ-midℚ' p3 p5 >=> cong (1/2r r*_) diffℚ-p3p5) >=>
    1/2r-path' e


  handle : (x.L p2 ⊎ x.U p3) -> (x.L p3 ⊎ x.U p4) -> CenteredBall x (1/2r r* e)
  handle (inj-r u-p3) _ =
    subst (CenteredBall x) (cong (1/2r r*_) diffℚ-p1p3) (center-ball x p1 p3 l-p1 u-p3)
  handle (inj-l l-p2) (inj-l l-p3) =
    subst (CenteredBall x) (cong (1/2r r*_) diffℚ-p3p5) (center-ball x p3 p5 l-p3 u-p5)
  handle (inj-l l-p2) (inj-r u-p4) =
    subst (CenteredBall x) (cong (1/2r r*_) diffℚ-p2p4) (center-ball x p2 p4 l-p2 u-p4)


private
  repeated-strengthen-centered-ball :
    (x : ℝ) (ε : ℚ) (n : ℕ) -> CenteredBall x ε -> ∥ CenteredBall x ((1/2r r^ℕ⁰ n) r* ε) ∥
  repeated-strengthen-centered-ball x e zero b = ∣ subst (CenteredBall x) (sym (r*-left-one e)) b ∣
  repeated-strengthen-centered-ball x e (suc n) b =
    ∥-bind handle (repeated-strengthen-centered-ball x e n b)
    where
    handle : CenteredBall x ((1/2r r^ℕ⁰ n) r* e) -> ∥ CenteredBall x ((1/2r r^ℕ⁰ (suc n)) r* e) ∥
    handle b = subst (\z -> ∥ (CenteredBall x z) ∥)
                 (sym (r*-assoc 1/2r (1/2r r^ℕ⁰ n) e))
                 (strengthen-centered-ball x _ b)

  initial-centered-ball : (x : ℝ) -> ∃[ ε ∈ ℚ ] (CenteredBall x ε)
  initial-centered-ball x = ∥-map2 handle x.Inhabited-L x.Inhabited-U
    where
    module x = Real x

    handle : Σ ℚ x.L -> Σ ℚ x.U -> Σ[ ε ∈ ℚ ] (CenteredBall x ε)
    handle (q1 , lq1) (q2 , uq2) = _ , center-ball x q1 q2 lq1 uq2


find-centered-ball : (x : ℝ) -> (ε : ℚ⁺) -> ∥ CenteredBall x ⟨ ε ⟩ ∥
find-centered-ball x e1⁺@(e1 , _) = ∥-bind handle (initial-centered-ball x)
  where
  handle : Σ[ e2 ∈ ℚ ] (CenteredBall x e2) -> ∥ CenteredBall x e1 ∥
  handle (e2 , b) = ∥-bind handle2 (ℚ-archimedian (e2 , centered-ball->Pos-ε x e2 b) e1⁺)
    where
    handle2 : (Σ[ n ∈ Nat ] (((1/2r r^ℕ⁰ n) r* e2) < e1)) -> ∥ CenteredBall x e1 ∥
    handle2 (n , lt) = ∥-map handle3 (repeated-strengthen-centered-ball x e2 n b)
      where
      handle3 : CenteredBall x ((1/2r r^ℕ⁰ n) r* e2) -> CenteredBall x e1
      handle3 b2 = weaken-centered-ball x _ _ lt b2

find-open-ball : (x : ℝ) -> (ε : ℚ⁺) -> ∥ OpenBall x ⟨ ε ⟩ ∥
find-open-ball x e@(e' , pos-e') = ∥-map handle (find-centered-ball x e2)
  where
  e2' = 1/2r r* e'
  e2 : ℚ⁺
  e2 = e2' , r*-preserves-Pos 1/2r _ (Pos-1/ℕ _) pos-e'

  handle : CenteredBall x e2' -> OpenBall x e'
  handle (q , l , u) = q r+ (r- e2') , q r+ e2' , l , u , path
    where
    path : (q r+ e2') r+ (r- (diffℚ e2' q)) == e'
    path =
      cong2 _r+_ (r+-commute q e2') (sym (diffℚ-anticommute q e2')) >=>
      r+-assoc e2' q (diffℚ q e2') >=>
      cong (e2' r+_) (diffℚ-step q e2') >=>
      1/2r-path' e'



-- OpenBallPred : ℚ⁺ -> ℚ -> Pred ℚ ℓ-zero
-- OpenBallPred (ε , _) center q = abs-diffℚ center q < ε
--
-- record OpenBallℚ : Type₀ where
--   constructor open-ballℚ
--   field
--     ε⁺ : ℚ⁺
--     center : ℚ
--
--   ε : ℚ
--   ε = fst ε⁺
--
--   contains : Pred ℚ ℓ-zero
--   contains = OpenBallPred ε⁺ center
--
-- OpenBallℚ-⊆ : Rel OpenBallℚ ℓ-zero
-- OpenBallℚ-⊆ b1 b2 = OpenBallℚ.contains b1 ⊆ OpenBallℚ.contains b2
--
-- OpenBallℚ-RawSeq : Type₀
-- OpenBallℚ-RawSeq = Nat -> OpenBallℚ
--
-- OpenBallℚ-Concentric : Pred OpenBallℚ-RawSeq ℓ-zero
-- OpenBallℚ-Concentric s = (m n : ℕ) -> m ℕ< n -> OpenBallℚ-⊆ (s m) (s n)
-- Seq+ : Seq -> Seq -> Seq
-- Seq+ s₁ s₂ n = s₁ n r+ s₂ n
--
-- Seq- : Seq -> Seq
-- Seq- s n = r- (s n)
--
-- SeqDiff : Seq -> Seq -> Seq
-- SeqDiff s₁ s₂ = Seq+ s₂ (Seq- s₁)
--
-- Increasing : Pred Seq ℓ-zero
-- Increasing s = (m n : Nat) -> (m ℕ< n) -> (s m < s n)
--
-- Decreasing : Pred Seq ℓ-zero
-- Decreasing s = (m n : Nat) -> (m ℕ< n) -> (s m > s n)
--
-- EventualUpperBound : Seq -> Pred ℚ ℓ-zero
-- EventualUpperBound s q = ∃[ n ∈ Nat ] ((m : Nat) -> m ≥ n -> s m < q)
--
-- EventualLowerBound : Seq -> Pred ℚ ℓ-zero
-- EventualLowerBound s q = ∃[ n ∈ Nat ] ((m : Nat) -> m ≥ n -> q < s m)
--
-- UpperBound : Seq -> Pred ℚ ℓ-zero
-- UpperBound s q = (n : Nat) -> s n < q
--
-- LowerBound : Seq -> Pred ℚ ℓ-zero
-- LowerBound s q = (n : Nat) -> q < s n
--
-- BoundedAbove : Pred Seq ℓ-zero
-- BoundedAbove s = ∃ ℚ (UpperBound s)
--
-- BoundedBelow : Pred Seq ℓ-zero
-- BoundedBelow s = ∃ ℚ (LowerBound s)
