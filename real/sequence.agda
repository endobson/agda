{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence where

open import base
open import equality
open import hlevel
open import nat.arithmetic
open import nat.properties
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-< )
open import relation hiding (U)
open import ring.implementations.rational
open import real
open import truncation
open import order
open import order.instances.nat
open import order.instances.rational

open import nat using (≤-max-left ; ≤-max-right)

private
  variable
    ℓ : Level

ℚSequence : Type₀
ℚSequence = Nat -> ℚ

private
  Seq = ℚSequence
  ℚPos = rational.order.Pos

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
    sym (RationalRing.*-distrib-+-left {1/2r} {x r+ y} {diffℚ x y}) >=>
    cong (1/2r r*_)
      (cong2 _r+_ (r+-commute x y) (r+-commute y (r- x)) >=>
       r+-assoc y x ((r- x) r+ y) >=>
       cong (y r+_) ((sym (r+-assoc x (r- x) y)) >=>
                     cong (_r+ y) (r+-inverse x) >=>
                     r+-left-zero y)) >=>
    (RationalRing.*-distrib-+-left {1/2r} {y} {y}) >=>
    1/2r-path' y

  midℚ-commute : (x y : ℚ) -> midℚ x y == midℚ y x
  midℚ-commute x y = cong (1/2r r*_) (r+-commute x y)

  midℚ-minus-half-diffℚ : (x y : ℚ) -> (midℚ x y r+ (r- (1/2r r* (diffℚ x y)))) == x
  midℚ-minus-half-diffℚ x y =
    cong2 _r+_ (midℚ-commute x y)
      (sym (RationalRing.minus-extract-right {1/2r} {diffℚ x y}) >=>
       cong (1/2r r*_) (sym (diffℚ-anticommute y x))) >=>
    midℚ-plus-half-diffℚ y x


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

      pos-d : ℚPos d
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
