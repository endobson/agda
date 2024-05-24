{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication.inverse where

open import additive-group
open import additive-group.instances.real
open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import order.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import rational.proper-interval
open import real
open import real.arithmetic
open import real.arithmetic.multiplication
open import real.interval
open import real.order
open import real.rational
open import relation hiding (U)
open import ring
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import sign
open import sign.instances.rational
open import sum
open import truncation

private
  abstract
    ℝ--zero : ℝ- 0# == 0#
    ℝ--zero = sym (+-left-zero) >=> +-inverse

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

    private

      isProp-L : (q : ℚ) -> isProp (L q)
      isProp-L q (L-pos p1 u1) (L-pos p2 u2) =
        (\i -> L-pos (pos-path i) (isProp->PathPᵉ (\i -> x.isProp-U (r1/ q (Pos->Inv (pos-path i))))
                                                  u1 u2 i))
        where
        pos-path : p1 == p2
        pos-path = isProp-Pos q p1 p2
      isProp-L q (L-nonpos np1) (L-nonpos np2) = cong L-nonpos (isProp-NonPos q np1 np2)
      isProp-L q (L-pos p _) (L-nonpos np) = bot-elim (NonPos->¬Pos np p)
      isProp-L q (L-nonpos np) (L-pos p _) = bot-elim (NonPos->¬Pos np p)


      isProp-U : (q : ℚ) -> isProp (U q)
      isProp-U q (U-pos p1 l1) (U-pos p2 l2) =
        (\i -> U-pos (pos-path i) (isProp->PathPᵉ (\i -> x.isProp-L (r1/ q (Pos->Inv (pos-path i))))
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
      isLowerSet-L {q} {r} q<r (L-nonpos np-r) = (L-nonpos (NonPos-≤ q r np-r (weaken-< q<r)))
      isLowerSet-L {q} {r} q<r (L-pos p-r xu-1/r) = handle (decide-sign q)
        where
        handle : Σ[ s ∈ Sign ] (isSign s q) -> L q
        handle (pos-sign  , p-q) =
          L-pos p-q (x.isUpperSet-U (r1/-Pos-flips-order (q , p-q) (r , p-r) q<r) xu-1/r)
        handle (zero-sign , z-q) = L-nonpos (inj-r z-q)
        handle (neg-sign  , n-q) = L-nonpos (inj-l n-q)


      isUpperSet-U : isUpperSet U
      isUpperSet-U {q} {r} q<r (U-pos pos-q xl-1/q) =
        U-pos pos-r (x.isLowerSet-L (r1/-Pos-flips-order (q , pos-q) (r , pos-r) q<r) xl-1/q)
        where
        pos-r = (Pos-≤ q r pos-q (weaken-< q<r))
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
        neg-q/2 = r*₁-preserves-sign (1/2r , Pos-1/ℕ _) q {neg-sign} neg-q
        q<q/2 = subst (_< q/2) (r*-left-one q) (*₂-flips-< 1/2r<1r neg-q)

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
      located q r q<r = handle (decide-sign q)
        where
        handle : Σ[ s ∈ Sign ] isSign s q -> ∥ L q ⊎ U r ∥
        handle (neg-sign  , n-q) = ∣ inj-l (L-nonpos (inj-l n-q)) ∣
        handle (zero-sign , z-q) = ∣ inj-l (L-nonpos (inj-r z-q)) ∣
        handle (pos-sign  , pos-q) = ∥-map handle2 (x.located r' q' r'<q')
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

    0<ℝ1/-Pos : 0# < ℝ1/-Pos
    0<ℝ1/-Pos = ∥-map handle (isUpperOpen-L 0r (L-nonpos (inj-r Zero-0r)))
      where
      handle : Σ[ q ∈ ℚ ] (0r < q × L q) -> 0# ℝ<' ℝ1/-Pos
      handle (q , 0<q , lq) = ℝ<'-cons q (ℚ<->U 0<q) lq

  module _ (x : ℝ) (0U : Real.U x 0r) where
    private
      -x = ℝ-ᵉ x

      module x = Real x
      module -x = Real -x

      -0L : -x.L 0r
      -0L = subst x.U (sym minus-zero) 0U

    ℝ1/-Neg : ℝ
    ℝ1/-Neg = ℝ-ᵉ (ℝ1/-Pos -x -0L)

    ℝ1/-Neg<0 : ℝ1/-Neg < 0#
    ℝ1/-Neg<0 = subst2 _<_ ℝ--eval ℝ--zero p2
      where
      p : 0# < (ℝ1/-Pos -x -0L)
      p = 0<ℝ1/-Pos -x -0L

      p2 : (- (ℝ1/-Pos -x -0L)) < (- 0#)
      p2 = minus-flips-<  p




module _ (x : ℝ)  where
  ℝ1/ᵉ : (xinv : ℝInv x) -> ℝ
  ℝ1/ᵉ (inj-l x<0) = ℝ1/-Neg x (ℝ<->U x<0)
  ℝ1/ᵉ (inj-r 0<x) = ℝ1/-Pos x (ℝ<->L 0<x)

  abstract
    ℝ1/ : (xinv : ℝInv x) -> ℝ
    ℝ1/ = ℝ1/ᵉ

    ℝ1/-eval : (xinv : ℝInv x) -> ℝ1/ xinv == ℝ1/ᵉ xinv
    ℝ1/-eval _ = refl

    ℝ1/-preserves-0< : (xinv : ℝInv x) -> (0# < x) -> 0# < (ℝ1/ xinv)
    ℝ1/-preserves-0< (inj-l x<0) 0<x = bot-elim (asym-< x<0 0<x)
    ℝ1/-preserves-0< (inj-r 0<x) _   = 0<ℝ1/-Pos x (ℝ<->L 0<x)

    ℝ1/-preserves-<0 : (xinv : ℝInv x) -> (x < 0#) -> (ℝ1/ xinv) < 0#
    ℝ1/-preserves-<0 (inj-l x<0) _   = ℝ1/-Neg<0 x (ℝ<->U x<0)
    ℝ1/-preserves-<0 (inj-r 0<x) x<0 = bot-elim (asym-< x<0 0<x)

    ℝ1/-preserves-ℝInv : (xinv : ℝInv x) -> ℝInv (ℝ1/ xinv)
    ℝ1/-preserves-ℝInv xinv =
      ⊎-map (ℝ1/-preserves-<0 xinv) (ℝ1/-preserves-0< xinv) xinv


ℝ--preserves-ℝInv : (x : ℝ) -> ℝInv x -> ℝInv (ℝ- x)
ℝ--preserves-ℝInv x (inj-l x<0) = inj-r (minus-flips-<0 x<0)
ℝ--preserves-ℝInv x (inj-r 0<x) = inj-l (minus-flips-0< 0<x)



module _ (x : ℝ)  where
  private
    -x = ℝ-ᵉ x
    module x = Real x
    module -x = Real -x

    ℝ-ᵉ-double-inverse : (z : ℝ) -> ℝ-ᵉ (ℝ-ᵉ z) == z
    ℝ-ᵉ-double-inverse z =
      LU-paths->path (ℝ-ᵉ (ℝ-ᵉ z)) z
        (\q -> cong (Real.L z) minus-double-inverse)
        (\q -> cong (Real.U z) minus-double-inverse)


    ℝ-ᵉ-ℝ1/ᵉ-commute' : (xinv : ℝInv x) -> (-xinv : ℝInv -x) -> ℝ-ᵉ (ℝ1/ᵉ x xinv) == ℝ1/ᵉ -x -xinv
    ℝ-ᵉ-ℝ1/ᵉ-commute' xinv@(inj-r 0<x) -xinv@(inj-l -x<0) = cong ℝ-ᵉ_ (sym p2)
      where
      p1 : ℝ-ᵉ (ℝ-ᵉ x) == x
      p1 = ℝ-ᵉ-double-inverse x

      L0 : Real.L (ℝ-ᵉ -x) 0r
      L0 = subst (Real.U -x) (sym minus-zero) (ℝ<->U -x<0)

      p2 : (ℝ1/-Pos (ℝ-ᵉ -x) L0) == (ℝ1/-Pos x (ℝ<->L 0<x))
      p2 = cong2-dep ℝ1/-Pos p1 (isProp->PathP (\i -> (Real.isProp-L (p1 i) 0r)))

    ℝ-ᵉ-ℝ1/ᵉ-commute' xinv@(inj-l x<0) -xinv@(inj-r 0<-x) =
      ℝ-ᵉ-double-inverse (ℝ1/-Pos -x L0) >=>
      cong (ℝ1/-Pos -x) (x.isProp-U (- 0r) _ _)
      where
      L0 : Real.L -x 0r
      L0 = subst x.U (sym minus-zero) (ℝ<->U x<0)

    ℝ-ᵉ-ℝ1/ᵉ-commute' (inj-r 0<x) (inj-r 0<-x) = bot-elim (asym-ℝ< {0#} {x} 0<x x<0)
      where
      x<0 : x ℝ< 0#
      x<0 = subst2 _ℝ<_ +-right-zero (+-right (sym ℝ--eval) >=> ℝ+-inverse x)
                        (+₁-preserves-< 0<-x)

    ℝ-ᵉ-ℝ1/ᵉ-commute' (inj-l x<0) (inj-l -x<0) = bot-elim (asym-ℝ< {0#} {x} 0<x x<0)
      where
      0<x : 0# < x
      0<x = subst2 _<_ (+-right (sym ℝ--eval) >=> ℝ+-inverse x) +-right-zero
                       (+₁-preserves-< -x<0)


  ℝ--ℝ1/-commute : (xinv : ℝInv x) -> ℝ- (ℝ1/ x xinv) == ℝ1/ (ℝ- x) (ℝ--preserves-ℝInv x xinv)
  ℝ--ℝ1/-commute xinv =
    ℝ--eval >=>
    cong ℝ-ᵉ_ (ℝ1/-eval x xinv) >=>
    ℝ-ᵉ-ℝ1/ᵉ-commute' xinv (subst ℝInv ℝ--eval (ℝ--preserves-ℝInv x xinv)) >=>
    cong2-dep ℝ1/ᵉ (\i -> ℝ--eval (~ i)) (isProp->PathP (\i -> isProp-ℝInv (ℝ--eval {x} (~ i)))) >=>
    sym (ℝ1/-eval (ℝ- x) (ℝ--preserves-ℝInv x xinv))


private

  module _ (x y : ℝ) where
    L' : Pred ℚ ℓ-zero
    L' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Lower (xi i* yi) q)

    U' : Pred ℚ ℓ-zero
    U' q = Σ[ xi ∈ Iℚ ] Σ[ yi ∈ Iℚ ] (ℝ∈Iℚ x xi × ℝ∈Iℚ y yi × i-Upper (xi i* yi) q)

  module _ (x : ℝ) (0L : Real.L x 0r) where
    private
      1/x = ℝ1/-Pos x 0L
      prod = (1/x ℝ*ᵉ x)

      module x = Real x
      module 1/x = Real 1/x
      module prod = Real prod

      0<x : 0# < x
      0<x = ∥-map handle (x.isUpperOpen-L 0r 0L)
        where
        handle : Σ[ q ∈ ℚ ] (0r < q × x.L q) -> 0# ℝ<' x
        handle (q , 0<q , xl-q) = ℝ<'-cons q (ℚ<->U 0<q) xl-q

      0<1/x : 0# < 1/x
      0<1/x = ∥-map handle x.Inhabited-U
        where
        handle : Σ ℚ x.U -> 0# ℝ<' 1/x
        handle (q , xu-q) = ℝ<'-cons q' (ℚ<->U 0<q') (L-pos pos-q' (subst x.U (sym q''-path) xu-q))
          where
          0<q = ℝ-bounds->ℚ< x 0L xu-q
          pos-q = 0<-Pos q 0<q
          inv-q = (Pos->Inv pos-q)
          q' = r1/ q inv-q
          pos-q' = r1/-preserves-Pos q inv-q pos-q
          inv-q' = (Pos->Inv pos-q')
          0<q' = Pos-0< q' pos-q'
          q'' = r1/ q' inv-q'
          q''-path = r1/-double-inverse q inv-q inv-q'

      extract-U : {q : ℚ} -> (p : Pos q) -> L x 0L q -> x.U (r1/ q (Pos->Inv p))
      extract-U p (L-nonpos np) = bot-elim (NonPos->¬Pos np p)
      extract-U {q} _ (L-pos _ xu) = subst (\i -> (x.U (r1/ q (Pos->Inv i)))) (isProp-Pos q _ _) xu

      extract-L : {q : ℚ} -> (p : Pos q) -> U x 0L q -> x.L (r1/ q (Pos->Inv p))
      extract-L {q} _ (U-pos _ xl) = subst (\i -> (x.L (r1/ q (Pos->Inv i)))) (isProp-Pos q _ _) xl


      interval-f : (a : Iℚ) -> ℝ∈Iℚ prod a -> ℝ∈Iℚ 1ℝ a
      interval-f a@(Iℚ-cons al au al≤au) p∈a =
        unsquash (isProp-ℝ∈Iℚ 1ℝ a) (∥-bind handle (ℝ∈Iℚ-*ᵉ⁻ 1/x x a p∈a))
        where
        handle : Σ[ b ∈ Iℚ ] Σ[ c ∈ Iℚ ] (ℝ∈Iℚ 1/x b × ℝ∈Iℚ x c × (b i* c) i⊆ a) -> ∥ ℝ∈Iℚ 1ℝ a ∥
        handle (b , c , 1/x∈b , x∈c , bc⊆a) =
          ∥-map2 handle2 (ℝ∈Iℚ-Pos-⊆ 1/x b 1/x∈b 0<1/x) (ℝ∈Iℚ-Pos-⊆ x c x∈c 0<x)
          where
          handle2 : Σ[ d ∈ Iℚ ] (d i⊆ b × ℝ∈Iℚ 1/x d × PosI d) ->
                    Σ[ e ∈ Iℚ ] (e i⊆ c × ℝ∈Iℚ x e × PosI e) -> ℝ∈Iℚ 1ℝ a
          handle2 (d@(Iℚ-cons dl du dl≤du) , d⊆b , (1/xl-dl , 1/xu-du) , pos-dl)
                  (e@(Iℚ-cons el eu el≤eu) , e⊆c , (xl-el , xu-eu) , pos-el) =
            ℝ∈Iℚ-⊆ 1ℝ de⊆a 1∈de
            where
            pos-du = Pos-≤ dl du pos-dl dl≤du
            pos-eu = Pos-≤ el eu pos-el el≤eu
            1/dl = (r1/ dl (Pos->Inv pos-dl))
            1/du = (r1/ du (Pos->Inv pos-du))

            xu-1/dl : x.U 1/dl
            xu-1/dl = extract-U pos-dl 1/xl-dl
            xl-1/du : x.L 1/du
            xl-1/du = extract-L pos-du 1/xu-du

            el<1/dl = ℝ-bounds->ℚ< x xl-el xu-1/dl
            1/du<eu = ℝ-bounds->ℚ< x xl-1/du xu-eu


            dlel<1 = subst2 _<_ *-commute (r1/-inverse dl (Pos->Inv pos-dl))
                            (*₂-preserves-< el<1/dl pos-dl)

            1<dueu = subst2 _<_ (r1/-inverse du (Pos->Inv pos-du)) *-commute
                            (*₂-preserves-< 1/du<eu pos-du)

            de' = i*-NN d e (weaken-< pos-dl) (weaken-< pos-el)
            de'==de : de' == (d i* e)
            de'==de = i*-NN-path d e (weaken-< pos-dl) (weaken-< pos-el)

            1∈de' : ℝ∈Iℚ 1ℝ de'
            1∈de' = ℚ<->L dlel<1 , ℚ<->U 1<dueu

            1∈de = subst (ℝ∈Iℚ 1ℝ) de'==de 1∈de'

            de⊆bc : (d i* e) i⊆ (b i* c)
            de⊆bc = i*-preserves-⊆ d⊆b e⊆c

            de⊆a = trans-i⊆ de⊆bc bc⊆a

      1/ℝ-Pos-inverse' : 1/x ℝ*ᵉ x == 1ℝ
      1/ℝ-Pos-inverse' = ℝ∈Iℚ->path (1/x ℝ*ᵉ x) 1ℝ interval-f

    1/ℝ-Pos-inverse : 1/x ℝ* x == 1ℝ
    1/ℝ-Pos-inverse = ℝ*-eval {1/x} {x} >=> 1/ℝ-Pos-inverse'

  module _ (x : ℝ) (0U : Real.U x 0r) where
    private
      1/x = ℝ1/-Neg x 0U
      0L = (subst (Real.U x) (sym minus-zero) 0U)

    1/ℝ-Neg-inverse : 1/x ℝ* x == 1ℝ
    1/ℝ-Neg-inverse =
      cong (_ℝ* x) (sym (ℝ--eval {ℝ1/-Pos (ℝ-ᵉ x) 0L})) >=>
      minus-extract-left >=>
      sym minus-extract-right >=>
      cong ((ℝ1/-Pos (ℝ-ᵉ x) 0L) ℝ*_) (ℝ--eval {x}) >=>
      1/ℝ-Pos-inverse (ℝ-ᵉ x) 0L


module _ (x : ℝ)  where
  ℝ1/ᵉ-inverse : (xinv : ℝInv x) -> ℝ1/ᵉ x xinv ℝ* x == 1ℝ
  ℝ1/ᵉ-inverse (inj-l x<0) = 1/ℝ-Neg-inverse x (ℝ<->U x<0)
  ℝ1/ᵉ-inverse (inj-r 0<x) = 1/ℝ-Pos-inverse x (ℝ<->L 0<x)

  abstract
    ℝ1/-inverse : (xinv : ℝInv x) -> ℝ1/ x xinv ℝ* x == 1ℝ
    ℝ1/-inverse = ℝ1/ᵉ-inverse
