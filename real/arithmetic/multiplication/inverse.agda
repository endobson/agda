{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication.inverse where

open import base
open import equality
open import hlevel
open import isomorphism
open import order
open import order.instances.rational
open import order.instances.real
open import ordered-ring
open import ordered-ring.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.minmax
open import rational.proper-interval
open import rational.proper-interval.multiplication-assoc
open import real
open import real.arithmetic
open import real.arithmetic.multiplication
open import real.arithmetic.multiplication.associative
open import relation hiding (U)
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import sign
open import sign.instances.rational
open import truncation
open import univalence


private
  module _ (x : ℝ) (0L : Real.L x 0r)
    where
    private
      module x = Real x

      data L : ℚ -> Type₀ where
        L-pos : {q : ℚ} -> (p : Pos q) -> x.U (r1/ q (Pos->Inv p)) -> L q
        L-nonpos : {q : ℚ} -> NonPos q -> L q

      data U : ℚ -> Type₀ where
        U-pos : {q : ℚ} -> (p : Pos q) -> x.L (r1/ q (Pos->Inv p)) -> U q

      isProp-L : (q : ℚ) -> isProp (L q)
      isProp-L q (L-pos p1 u1) (L-pos p2 u2) =
        (\i -> L-pos (pos-path i) (isProp->PathP (\i -> x.isProp-U (r1/ q (Pos->Inv (pos-path i))))
                                                 u1 u2 i))
        where
        pos-path : p1 == p2
        pos-path = isProp-Pos q p1 p2
      isProp-L q (L-nonpos np1) (L-nonpos np2) = cong L-nonpos (isProp-NonPos q np1 np2)
      isProp-L q (L-pos p _) (L-nonpos np) = bot-elim (NonPos->¬Pos np p)
      isProp-L q (L-nonpos np) (L-pos p _) = bot-elim (NonPos->¬Pos np p)


      isProp-U : (q : ℚ) -> isProp (U q)
      isProp-U q (U-pos p1 l1) (U-pos p2 l2) =
        (\i -> U-pos (pos-path i) (isProp->PathP (\i -> x.isProp-L (r1/ q (Pos->Inv (pos-path i))))
                                                 l1 l2 i))
        where
        pos-path : p1 == p2
        pos-path = isProp-Pos q p1 p2

      Inhabited-U : Inhabited U
      Inhabited-U = ∥-map handle (x.isUpperOpen-L 0r 0L)
        where
        handle : Σ[ q ∈ ℚ ] (0r < q × x.L q) -> Σ ℚ U
        handle (q , 0<q , xl-q) =
          q' , U-pos pos-q'
                     (subst x.L (sym (r1/-double-inverse q inv-q inv-q')) xl-q)
          where
          pos-q = 0<-Pos q 0<q
          inv-q = (Pos->Inv pos-q)
          q' = r1/ q inv-q
          pos-q' = (r1/-preserves-Pos q inv-q pos-q)
          inv-q' = (Pos->Inv pos-q')

      Inhabited-L : Inhabited L
      Inhabited-L = ∣ 0r , L-nonpos (inj-r Zero-0r) ∣

      isLowerSet-L : isLowerSet L
      isLowerSet-L q r q<r (L-nonpos np-r) = (L-nonpos (NonPos-≤ q r np-r (inj-l q<r)))
      isLowerSet-L q r q<r (L-pos p-r xu-1/r) = handle _ (isSign-self q)
        where
        handle : (s : Sign) -> (isSign s q) -> L q
        handle pos-sign  p-q =
          L-pos p-q (x.isUpperSet-U (r1/ r (Pos->Inv p-r)) (r1/ q (Pos->Inv p-q))
                                    (r1/-Pos-flips-order (q , p-q) (r , p-r) q<r) xu-1/r)
        handle zero-sign z-q = L-nonpos (inj-r z-q)
        handle neg-sign  n-q = L-nonpos (inj-l n-q)


      isUpperSet-U : isUpperSet U
      isUpperSet-U q r q<r (U-pos pos-q xl-1/q) =
        U-pos pos-r (x.isLowerSet-L r' q' (r1/-Pos-flips-order (q , pos-q) (r , pos-r) q<r) xl-1/q)
        where
        pos-r = (Pos-≤ q r pos-q (inj-l q<r))
        inv-q = (Pos->Inv pos-q)
        inv-r = (Pos->Inv pos-r)
        q' = r1/ q inv-q
        r' = r1/ r inv-r

      isUpperOpen-L : isUpperOpen L
      isUpperOpen-L q (L-pos pos-q xu-1/q) = ∥-map handle (LowerOpen-Pos x (q' , pos-q') xu-1/q)
        where
        inv-q = (Pos->Inv pos-q)
        q' = r1/ q inv-q
        pos-q' = (r1/-preserves-Pos q inv-q pos-q)
        inv-q' = (Pos->Inv pos-q')

        handle : Σ[ r' ∈ ℚ⁺ ] (⟨ r' ⟩ < q' × x.U ⟨ r' ⟩) -> Σ[ r ∈ ℚ ] (q < r × L r)
        handle ((r' , pos-r') , r'<q' , xu-r') = r , q<r , (L-pos pos-r xu-1/r)
          where
          inv-r' = (Pos->Inv pos-r')
          r = r1/ r' inv-r'
          pos-r = (r1/-preserves-Pos r' inv-r' pos-r')
          inv-r = (Pos->Inv pos-r)
          1/r = r1/ r inv-r

          q<r : q < r
          q<r = subst (_< r) (r1/-double-inverse q inv-q inv-q')
                      (r1/-Pos-flips-order (r' , pos-r') (q' , pos-q') r'<q')

          xu-1/r : x.U 1/r
          xu-1/r = subst x.U (sym (r1/-double-inverse r' inv-r' inv-r)) xu-r'
      isUpperOpen-L q (L-nonpos (inj-l neg-q)) = ∣ q/2 , q<q/2 , (L-nonpos (inj-l neg-q/2)) ∣
        where
        q/2 = 1/2r r* q
        neg-q/2 = r*₁-preserves-sign (1/2r , Pos-1/ℕ _) q neg-q
        q<q/2 = subst (_< q/2) (r*-left-one q) (r*₂-flips-order 1/2r 1r (q , neg-q) 1/2r<1r)

      isUpperOpen-L q (L-nonpos (inj-r zero-q)) = ∥-map handle (ℝ->Pos-U x)
        where
        handle : Σ[ r ∈ ℚ⁺ ] (x.U ⟨ r ⟩) -> Σ[ r ∈ ℚ ] (q < r × L r)
        handle ((r , pos-r) , xu-r) = r' , q<r' , L-pos pos-r' (subst x.U (sym r''==r) xu-r)
          where
          inv-r = (Pos->Inv pos-r)
          r' = r1/ r inv-r
          pos-r' = (r1/-preserves-Pos r inv-r pos-r)
          inv-r' = (Pos->Inv pos-r')
          r'' = r1/ r' inv-r'
          r''==r = r1/-double-inverse r inv-r inv-r'



          q==0 = Zero-path q zero-q
          0<r' = Pos-0< r' pos-r'
          q<r' = subst (_< r') (sym q==0) 0<r'


      isLowerOpen-U : isLowerOpen U
      isLowerOpen-U q (U-pos pos-q xl-1/q) = ∥-map handle (x.isUpperOpen-L q' xl-1/q)
        where
        inv-q = (Pos->Inv pos-q)
        q' = r1/ q inv-q
        pos-q' = (r1/-preserves-Pos q inv-q pos-q)
        inv-q' = (Pos->Inv pos-q')

        handle : Σ[ r' ∈ ℚ ] (q' < r' × x.L r') -> Σ[ r ∈ ℚ ] (r < q × U r)
        handle (r' , q'<r' , xl-r') = r , r<q , U-pos pos-r xl-1/r
          where
          pos-r' = Pos-< q' r' (inj-l pos-q') q'<r'
          inv-r' = (Pos->Inv pos-r')
          r = r1/ r' inv-r'
          pos-r = (r1/-preserves-Pos r' inv-r' pos-r')
          inv-r = (Pos->Inv pos-r)
          1/r = r1/ r inv-r

          r<q : r < q
          r<q = subst (r <_) (r1/-double-inverse q inv-q inv-q')
                      (r1/-Pos-flips-order (q' , pos-q') (r' , pos-r') q'<r')

          xl-1/r : x.L 1/r
          xl-1/r = subst x.L (sym (r1/-double-inverse r' inv-r' inv-r)) xl-r'

      disjoint : Universal (Comp (L ∩ U))
      disjoint q (L-pos q-pos xu-1/q , U-pos q-pos2 xl-1/q2) =
        x.disjoint q' (xl-1/q , xu-1/q)
        where
        inv-q = Pos->Inv q-pos
        q' = r1/ q inv-q

        xl-1/q : x.L q'
        xl-1/q = subst (\p -> x.L (r1/ q (Pos->Inv p))) (isProp-Pos q q-pos2 q-pos) xl-1/q2
      disjoint q (L-nonpos q-nonpos , U-pos q-pos _) = NonPos->¬Pos q-nonpos q-pos


      located : (q r : Rational) -> (q < r) -> ∥ L q ⊎ U r ∥
      located q r q<r = handle _ (isSign-self q)
        where
        handle : (s : Sign) -> isSign s q -> ∥ L q ⊎ U r ∥
        handle neg-sign  n-q = ∣ inj-l (L-nonpos (inj-l n-q)) ∣
        handle zero-sign z-q = ∣ inj-l (L-nonpos (inj-r z-q)) ∣
        handle pos-sign pos-q = ∥-map handle2 (x.located r' q' r'<q')
          where
          pos-r = Pos-< q r (inj-l pos-q) q<r
          inv-q = Pos->Inv pos-q
          inv-r = Pos->Inv pos-r
          q' = r1/ q inv-q
          r' = r1/ r inv-r

          r'<q' = r1/-Pos-flips-order (q , pos-q) (r , pos-r) q<r

          handle2 : x.L r' ⊎ x.U q' -> L q ⊎ U r
          handle2 (inj-l xl-r') = inj-r (U-pos pos-r xl-r')
          handle2 (inj-r xu-q') = inj-l (L-pos pos-q xu-q')

    ℝ1/-Pos : ℝ
    ℝ1/-Pos = record
      { L = L
      ; U = U
      ; isProp-L = isProp-L
      ; isProp-U = isProp-U
      ; Inhabited-L = Inhabited-L
      ; Inhabited-U = Inhabited-U
      ; isLowerSet-L = isLowerSet-L
      ; isUpperSet-U = isUpperSet-U
      ; isUpperOpen-L = isUpperOpen-L
      ; isLowerOpen-U = isLowerOpen-U
      ; disjoint = disjoint
      ; located = located
      }

  module _ (x : ℝ) (0U : Real.U x 0r) where
    private
      -x = ℝ-ᵉ x

      module x = Real x
      module -x = Real -x

      -0L : -x.L 0r
      -0L = 0U

    ℝ1/-Neg : ℝ
    ℝ1/-Neg = ℝ-ᵉ (ℝ1/-Pos -x -0L)

module _ (x : ℝ)  where
  ℝ1/ᵉ :  (xinv : ℝInv x) -> ℝ
  ℝ1/ᵉ (inj-l x<0) = ℝ1/-Neg x (ℝ<->U x 0r x<0)
  ℝ1/ᵉ (inj-r 0<x) = ℝ1/-Pos x (ℝ<->L 0r x 0<x)

  abstract
    ℝ1/ : (xinv : ℝInv x) -> ℝ
    ℝ1/ = ℝ1/ᵉ

    ℝ1/-eval : (xinv : ℝInv x) -> ℝ1/ xinv == ℝ1/ᵉ xinv
    ℝ1/-eval _ = refl

private
  abstract
    ℝ--zero : ℝ- 0ℝ == 0ℝ
    ℝ--zero = sym (+-left-zero) >=> ℝRing.+-inverse

ℝ--preserves-ℝInv : (x : ℝ) -> ℝInv x -> ℝInv (ℝ- x)
ℝ--preserves-ℝInv x (inj-l x<0) = inj-r (subst (_< (ℝ- x)) ℝ--zero (minus-flips-< x 0ℝ x<0))
ℝ--preserves-ℝInv x (inj-r 0<x) = inj-l (subst ((ℝ- x) <_) ℝ--zero (minus-flips-< 0ℝ x 0<x))



module _ (x : ℝ)  where
  private
    -x = ℝ-ᵉ x
    module x = Real x
    module -x = Real -x

    ℝ-ᵉ-double-inverse : (z : ℝ) -> ℝ-ᵉ (ℝ-ᵉ z) == z
    ℝ-ᵉ-double-inverse z =
      LU-paths->path (ℝ-ᵉ (ℝ-ᵉ z)) z
        (\q -> cong (Real.L z) (RationalRing.minus-double-inverse))
        (\q -> cong (Real.U z) (RationalRing.minus-double-inverse))


    ℝ-ᵉ-ℝ1/ᵉ-commute' : (xinv : ℝInv x) -> (-xinv : ℝInv -x) -> ℝ-ᵉ (ℝ1/ᵉ x xinv) == ℝ1/ᵉ -x -xinv
    ℝ-ᵉ-ℝ1/ᵉ-commute' xinv@(inj-r 0<x) -xinv@(inj-l -x<0) = cong ℝ-ᵉ_ (sym p2)
      where
      p1 : ℝ-ᵉ (ℝ-ᵉ x) == x
      p1 = ℝ-ᵉ-double-inverse x

      p2 : (ℝ1/-Pos (ℝ-ᵉ -x) (ℝ<->U -x 0r -x<0)) == (ℝ1/-Pos x (ℝ<->L 0r x 0<x))
      p2 = cong2-dep ℝ1/-Pos p1
           (isProp->PathP (\i -> (Real.isProp-L (p1 i) 0r)) _ _)

    ℝ-ᵉ-ℝ1/ᵉ-commute' xinv@(inj-l x<0) -xinv@(inj-r 0<-x) =
      ℝ-ᵉ-double-inverse (ℝ1/-Pos -x (ℝ<->U x 0r x<0)) >=>
      cong (ℝ1/-Pos -x) (x.isProp-U 0r _ _)

    ℝ-ᵉ-ℝ1/ᵉ-commute' (inj-r 0<x) (inj-r 0<-x) = bot-elim (asym-ℝ< {0ℝ} {x} 0<x x<0)
      where
      x<0 : x ℝ< 0ℝ
      x<0 = subst2 _ℝ<_ +-right-zero (+-right (sym ℝ--eval) >=> ℝ+-inverse x)
                        (+₁-preserves-< x 0ℝ -x 0<-x)

    ℝ-ᵉ-ℝ1/ᵉ-commute' (inj-l x<0) (inj-l -x<0) = bot-elim (asym-ℝ< {0ℝ} {x} 0<x x<0)
      where
      0<x : 0ℝ ℝ< x
      0<x = subst2 _ℝ<_ (+-right (sym ℝ--eval) >=> ℝ+-inverse x) +-right-zero
                        (+₁-preserves-< x -x 0ℝ -x<0)


  ℝ--ℝ1/-commute : (xinv : ℝInv x) -> ℝ- (ℝ1/ x xinv) == ℝ1/ (ℝ- x) (ℝ--preserves-ℝInv x xinv)
  ℝ--ℝ1/-commute xinv =
    ℝ--eval >=>
    cong ℝ-ᵉ_ (ℝ1/-eval x xinv) >=>
    ℝ-ᵉ-ℝ1/ᵉ-commute' xinv (subst ℝInv ℝ--eval (ℝ--preserves-ℝInv x xinv)) >=>
    cong2-dep ℝ1/ᵉ (sym ℝ--eval) (isProp->PathP (\i -> isProp-ℝInv (ℝ--eval {x} (~ i)))
                                                (subst ℝInv ℝ--eval (ℝ--preserves-ℝInv x xinv))
                                                (ℝ--preserves-ℝInv x xinv)) >=>
    sym (ℝ1/-eval (ℝ- x) (ℝ--preserves-ℝInv x xinv))


module _ (x : ℝ) where
  private

    module _ (x y : ℝ) where
      L' : Pred ℚ ℓ-zero
      L' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Lower (xi i* yi) q)

      U' : Pred ℚ ℓ-zero
      U' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Upper (xi i* yi) q)

    module _ (0L : Real.L x 0r) where
      1/x = ℝ1/-Pos x 0L
      prod = (1/x ℝ*ᵉ x)

      module x = Real x
      module 1/x = Real 1/x
      module prod = Real prod

      -- interval-f : (a : Iℚ) -> ℝ∈Iℚ prod a -> ℝ∈Iℚ 1ℝ a
      -- interval-f a@(Iℚ-cons al au al≤au) (pl-al , pu-au) =
      --   unsquash (isProp-ℝ∈Iℚ 1ℝ a) (∥-map4 handle pl-al pu-au (x.isUpperOpen-L 0r 0L) x.Inhabited-U)
      --   where
      --   handle : L' 1/x x al -> U' 1/x x au -> Σ[ q ∈ ℚ ] (0r < q × x.L q) -> Σ ℚ x.U -> ℝ∈Iℚ 1ℝ a
      --   handle (bi , ci , 1/x∈b , x∈c , al≤bc) (di , ei , 1/x∈d , x∈e , de≤au)
      --          (fl , 0<fl , xl-fl) (fu , xu-fu) = al<1 , 1<au
      --     where
      --     fl<fu = ℝ-bounds->ℚ< x fl fu xl-fl xu-fu
      --     fi = Iℚ-cons fl fu (inj-l fl<fu)
      --     x∈f : ℝ∈Iℚ x fi
      --     x∈f = xl-fl , xu-fu

      --     bc = bi i* ci
      --     bc-l = Iℚ.l bc
      --     bc-l<1 : bc-l < 1r
      --     bc-l<1 = ?

      --     al<1 : al < 1r
      --     al<1 = trans-≤-< {al} al≤bc bc-l<1

      --     1<au : 1r < au
      --     1<au = ?


      -- 1/ℝ-Pos-inverse : 1/x ℝ*ᵉ x == 1ℝ
      -- 1/ℝ-Pos-inverse = ℝ∈Iℚ->path (1/x ℝ*ᵉ x) 1ℝ interval-f
