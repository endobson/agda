{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.absolute-value where

open import base
open import equality
open import functions
open import hlevel
open import isomorphism
open import order
open import order.instances.rational
open import order.instances.real
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import rational.proper-interval
open import rational.proper-interval.abs
open import rational.minmax
open import rational.order using
 ( ℚ⁻
 ; ℚ⁺
 ; r--flips-sign
 ; r--flips-order
 ; r--flips-≤
 ; r+-preserves-Pos
 ; Pos-1r
 ; Neg-<0
 ; Pos-0<
 ; <0-Neg
 ; 0<-Pos
 ; NonNeg-0≤
 ; NonPos-≤0
 ; trans-<-≤
 ; trans-≤-<
 ; trans-ℚ≤
 )
open import rational.sign
open import real
open import real.interval
open import real.arithmetic.multiplication
open import real.arithmetic
open import real.sequence
open import relation hiding (U)
open import ring
open import ring.implementations.rational
open import ring.implementations.real
open import semiring
open import sign
open import sign.instances.rational
open import truncation
open import univalence

module _ (x : ℝ)
  where
  private
    module x = Real x

    L' : Pred ℚ ℓ-zero
    L' q = (x.L q) ⊎ (x.U (r- q))

    L : Pred ℚ ℓ-zero
    L q = ∥ L' q ∥

    U : Pred ℚ ℓ-zero
    U q = (x.L (r- q)) × (x.U q)

    isProp-L : (q : ℚ) -> isProp (L q)
    isProp-L _ = squash

    isProp-U : (q : ℚ) -> isProp (U q)
    isProp-U q (l1 , u1) (l2 , u2) i =
      (x.isProp-L (r- q) l1 l2 i) , (x.isProp-U q u1 u2 i)

    L-neg : (q : ℚ⁻) -> L ⟨ q ⟩
    L-neg (q , nq) = x.located q (r- q) q<-q
      where
      pmq : Pos (r- q)
      pmq = r--flips-sign _ _ nq

      q<-q : q < (r- q)
      q<-q = r+-preserves-Pos _ _ pmq pmq

    Inhabited-L : Inhabited L
    Inhabited-L = ∣ (r- 1r) , L-neg (_ , r--flips-sign _ _ Pos-1r) ∣

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-map2 handle (ℝ->Neg-L x) (ℝ->Pos-U x)
      where
      handle : Σ[ q ∈ ℚ⁻ ] (x.L ⟨ q ⟩) -> Σ[ r ∈ ℚ⁺ ] (x.U ⟨ r ⟩) -> Σ ℚ U
      handle (q⁻@(q , _) , xl-q) (r⁺@(r , _) , xu-r) = handle2 (trichotomous-< q (r- r))
        where
        handle2 : Tri (q < (r- r)) (q == (r- r)) ((r- r) < q) -> Σ ℚ U
        handle2 (tri< q<-r _ _) =
          (r- q) , (subst x.L (sym minus-double-inverse) xl-q) ,
                   (x.isUpperSet-U r (r- q) r<-q xu-r)
          where
          r<-q : r < (r- q)
          r<-q = subst Pos (r+-commute (r- r) (r- q)) q<-r
        handle2 (tri= _ q=-r _ ) = r , (subst x.L q=-r xl-q) , xu-r
        handle2 (tri> _ _ -r<q) = r , (x.isLowerSet-L (r- r) q -r<q xl-q) , xu-r

    isLowerSet-L : isLowerSet L
    isLowerSet-L q r q<r = ∥-map handle
      where
      handle : L' r -> L' q
      handle (inj-l xl-r) = inj-l (x.isLowerSet-L q r q<r xl-r)
      handle (inj-r xu-r) = inj-r (x.isUpperSet-U (r- r) (r- q) (r--flips-order q r q<r) xu-r)

    isUpperSet-U : isUpperSet U
    isUpperSet-U q r q<r (xl-q , xu-q) =
      (x.isLowerSet-L (r- r) (r- q) (r--flips-order q r q<r) xl-q) ,
      (x.isUpperSet-U q r q<r xu-q)

    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q = ∥-bind handle
      where
      handle : L' q -> ∃[ r ∈ ℚ ] (q < r × L r)
      handle (inj-l xl-q) = ∥-map (\ (r , lt , l) -> r , lt , ∣ (inj-l l) ∣) (x.isUpperOpen-L q xl-q)
      handle (inj-r xu-q) = ∥-map handle2 (x.isLowerOpen-U (r- q) xu-q)
        where
        handle2 : Σ[ r ∈ ℚ ] (r < (r- q) × x.U r ) -> Σ[ r ∈ ℚ ] (q < r × L r)
        handle2 (r , lt , xu-r) =
          (r- r) , subst Pos (r+-commute (r- q) (r- r)) lt
                 , ∣ inj-r (subst x.U (sym minus-double-inverse) xu-r) ∣


    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q (xl-q , xu-q) =
      ∥-map2 handle (x.isUpperOpen-L (r- q) xl-q) (x.isLowerOpen-U q xu-q)
      where
      handle : Σ[ r1 ∈ ℚ ] ((r- q) < r1 × x.L r1) -> Σ[ r2 ∈ ℚ ] (r2 < q × x.U r2) ->
               Σ[ r3 ∈ ℚ ] (r3 < q × U r3)
      handle (r1 , -q<r1 , xl-r1) (r2 , r2<q , xu-r2) = handle2 (trichotomous-< r1 (r- r2))
        where
        handle2 : Tri (r1 < (r- r2)) (r1 == (r- r2)) ((r- r2) < r1) ->
                  Σ[ r3 ∈ ℚ ] (r3 < q × U r3)
        handle2 (tri< r1<-r2 _ _) =
          (r- r1) , -r1<q , (subst x.L (sym minus-double-inverse) xl-r1) ,
                            (x.isUpperSet-U r2 (r- r1) r2<-r1 xu-r2)
          where
          r2<-r1 : r2 < (r- r1)
          r2<-r1 = subst Pos (r+-commute (r- r2) (r- r1)) r1<-r2

          -r1<q : (r- r1) < q
          -r1<q = subst ((r- r1) <_) minus-double-inverse
                        (r--flips-order (r- q) r1 -q<r1)

        handle2 (tri= _ r1=-r2 _) =
          r2 , r2<q , (subst x.L r1=-r2 xl-r1) , xu-r2
        handle2 (tri> _ _ -r2<r1) =
          r2 , r2<q , (x.isLowerSet-L (r- r2) r1 -r2<r1 xl-r1) , xu-r2


    disjoint : Universal (Comp (L ∩ U))
    disjoint q (l , (xl-mq , xu-q)) = unsquash isPropBot (∥-map handle l)
      where
      handle : (x.L q ⊎ x.U (r- q)) -> Bot
      handle (inj-l xl-q) = x.disjoint q (xl-q , xu-q)
      handle (inj-r xu-mq) = x.disjoint (r- q) (xl-mq , xu-mq)


    located : (q r : ℚ) -> (q < r) -> ∥ L q ⊎ U r ∥
    located q r q<r =  ∥-map2 handle (x.located q r q<r)
                                     (x.located (r- r) (r- q) (r--flips-order q r q<r))
      where
      handle : (x.L q ⊎ x.U r) -> (x.L (r- r) ⊎ x.U (r- q)) -> L q ⊎ U r
      handle (inj-l xl-q) _ = inj-l (∣ (inj-l xl-q) ∣)
      handle (inj-r xu-r) (inj-r xu-mq) = inj-l (∣ (inj-r xu-mq) ∣)
      handle (inj-r xu-r) (inj-l xl-mr) = inj-r (xl-mr , xu-r)

  absℝ : ℝ
  absℝ = record
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

abstract
  absℝ-0≤ : (x : ℝ) -> (q : ℚ⁻) -> Real.L (absℝ x) ⟨ q ⟩
  absℝ-0≤ x (q , neg-q) = Real.located x q (- q) q<-q
    where
    q<-q : q < (- q)
    q<-q = trans-< {_} {_} {_} {q} (Neg-<0 q neg-q) (Pos-0< (- q) (r--flips-sign q _ neg-q))

  absℝ-≮0 : (x : ℝ) -> absℝ x ≮ 0ℝ
  absℝ-≮0 x = unsquash isPropBot ∘ ∥-map handle
    where
    handle : Σ[ q ∈ ℚ ] (Real.U (absℝ x) q × q < 0r) -> Bot
    handle (q , axu-q , q<0) = Real.disjoint (absℝ x) q (absℝ-0≤ x (q , <0-Neg _ q<0) , axu-q)


  absℝ-NonNeg-idem : (x : ℝ) -> (x ≮ 0ℝ) -> absℝ x == x
  absℝ-NonNeg-idem x 0≤x = LU-paths->path (absℝ x) x L-path U-path
    where
    module ax = Real (absℝ x)
    module x = Real x

    ≤0->¬xU : {q : ℚ} -> (q ≤ 0r) -> ¬ (x.U q)
    ≤0->¬xU {q} q≤0 xU-q = unsquash isPropBot (∥-map handle (x.isLowerOpen-U q xU-q))
      where
      handle : Σ[ r ∈ ℚ ] (r < q × x.U r) -> Bot
      handle (r , r<q , xU-r) = 0≤x ∣ (r , xU-r , trans-<-≤ {r} {q} {0r} r<q q≤0) ∣

    <0->xL : {q : ℚ} -> (q < 0r) -> x.L q
    <0->xL {q} q<0r = unsquash (x.isProp-L q) (∥-map handle (x.located q 0r q<0r))
      where
      handle : (x.L q ⊎ x.U 0r) -> x.L q
      handle (inj-l xl) = xl
      handle (inj-r xu) = bot-elim (≤0->¬xU refl-≤ xu)

    L-path : (q : ℚ) -> ax.L q == x.L q
    L-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (ax.L q) (x.L q)
      i .fun axl = unsquash (x.isProp-L q) (∥-map handle axl)
        where
        handle : ((x.L q) ⊎ (x.U (r- q))) -> (x.L q)
        handle (inj-l lq) = lq
        handle (inj-r u-q) = handle2 (split-< q 0r)
          where
          handle2 : (q < 0r ⊎ 0r ≤ q) -> x.L q
          handle2 (inj-l lt) = <0->xL lt
          handle2 (inj-r ge) = bot-elim (≤0->¬xU (r--flips-≤ 0r q ge) u-q)
      i .inv xl = ∣ inj-l xl ∣
      i .rightInv _ = x.isProp-L q _ _
      i .leftInv _ = ax.isProp-L q _ _

    U-path : (q : ℚ) -> ax.U q == x.U q
    U-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (ax.U q) (x.U q)
      i .fun (_ , xu) = xu
      i .inv xu = <0->xL -q<0 , xu
        where
        -q<0 : (- q) < 0r
        -q<0 = handle (split-< (- q) 0r)
          where
          handle : ((- q) < 0r ⊎ 0r ≤ (- q)) -> (- q) < 0r
          handle (inj-l lt) = lt
          handle (inj-r ge) = bot-elim (≤0->¬xU (r--flips-≤ 0r (- q) ge)
                                                (subst x.U (sym minus-double-inverse) xu))
      i .rightInv _ = x.isProp-U q _ _
      i .leftInv _ = ax.isProp-U q _ _

  absℝ-absℝ-idem : (x : ℝ) -> absℝ (absℝ x) == (absℝ x)
  absℝ-absℝ-idem x = absℝ-NonNeg-idem (absℝ x) (absℝ-≮0 x)

  split-small-absℝ : (x : ℝ) -> (q : ℚ⁺) -> ∥ (absℝ x ℝ< (ℚ->ℝ ⟨ q ⟩)) ⊎ ℝInv x ∥
  split-small-absℝ x q⁺@(q , Pos-q) = ∥-map handle (find-open-ball x q⁺)
    where
    module x = Real x
    Res = (absℝ x ℝ< (ℚ->ℝ q)) ⊎ ℝInv x

    handle : OpenBall x q -> Res
    handle (r1 , r2 , xl-r1 , xu-r2 , diff-path) = handle2 (split-< r1 0r) (split-< 0r r2)
      where
      handle2 : (r1 < 0r) ⊎ (0r ≤ r1) -> (0r < r2) ⊎ (r2 ≤ 0r) -> Res
      handle2 (inj-r 0≤r1) _ = inj-r (inj-r ans)
        where
        ans : 0ℝ < x
        ans = ∥-map (\ (s , r1<s , xl) -> s , trans-≤-< {0r} 0≤r1 r1<s , xl) (x.isUpperOpen-L r1 xl-r1)
      handle2 (inj-l r1<0) (inj-r r2≤0) = inj-r (inj-l ans)
        where
        ans : x < 0ℝ
        ans = ∥-map (\ (s , s<r2 , xu) -> s , xu , trans-<-≤ {s} s<r2 r2≤0) (x.isLowerOpen-U r2 xu-r2)
      handle2 (inj-l r1<0) (inj-l 0<r2) = inj-l (∣ s , (xl--s , xu-s) , s<q ∣)
        where
        -r1<q : (- r1) < q
        -r1<q = subst2 _<_ +-left-zero diff-path (+₂-preserves-< 0r r2 (- r1) 0<r2)
        r2<q : r2 < q
        r2<q = subst2 _<_ +-right-zero diff-path (+₁-preserves-< r2 0r (- r1) (minus-flips-< r1 0r r1<0))


        s = maxℚ (- r1) r2
        s<q : s < q
        s<q = maxℚ-property (- r1) r2 -r1<q r2<q

        xl--s : x.L (- s)
        xl--s = isLowerSet≤ x (- s) r1 lt xl-r1
          where
          lt : (- s) ≤ r1
          lt = subst (_≤ r1) (sym (r--maxℚ (- r1) r2 >=> (cong2 minℚ minus-double-inverse refl)))
                              (minℚ-≤-left r1 (- r2))

        xu-s : x.U s
        xu-s = isUpperSet≤ x r2 s (maxℚ-≤-right (- r1) r2) xu-r2

  absℝ-- : (x : ℝ) -> absℝ (- x) == absℝ x
  absℝ-- x = cong absℝ (ℝ--eval {x}) >=> LU-paths->path amx ax L-path U-path
    where
    mx = ℝ-ᵉ x
    ax = absℝ x
    amx = absℝ mx
    module x = Real x
    module ax = Real ax
    module mx = Real mx
    module amx = Real amx

    L-path : (q : ℚ) -> amx.L q == ax.L q
    L-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (amx.L q) (ax.L q)
      i .fun = ∥-map handle
        where
        handle : (mx.L q) ⊎ (mx.U (- q)) -> (x.L q) ⊎ (x.U (- q))
        handle (inj-l p) = inj-r p
        handle (inj-r p) = inj-l (subst x.L minus-double-inverse p)
      i .inv = ∥-map handle
        where
        handle : (x.L q) ⊎ (x.U (- q)) -> (mx.L q) ⊎ (mx.U (- q))
        handle (inj-l p) = inj-r (subst x.L (sym minus-double-inverse) p)
        handle (inj-r p) = inj-l p
      i .rightInv _ = ax.isProp-L q _ _
      i .leftInv _ = amx.isProp-L q _ _

    U-path : (q : ℚ) -> amx.U q == ax.U q
    U-path q = ua (isoToEquiv i)
      where
      open Iso
      i : Iso (amx.U q) (ax.U q)
      i .fun (p1 , p2) = (p2 , subst x.U minus-double-inverse p1)
      i .inv (p1 , p2) = (subst x.U (sym minus-double-inverse) p2 , p1)
      i .rightInv _ = ax.isProp-U q _ _
      i .leftInv _ = amx.isProp-U q _ _



ℝ∈Iℚ-absℝ-StrictCrossZeroI :
  (x : ℝ) (a : Iℚ) -> ¬ (StrictCrossZeroI a) -> ℝ∈Iℚ x a -> ℝ∈Iℚ (absℝ x) (i-abs a)
ℝ∈Iℚ-absℝ-StrictCrossZeroI x (Iℚ-cons l u l≤u) ¬scz (xl-l , xu-u) = axl-l0 , axu--lu
  where
  module x = Real x
  ax = (absℝ x)
  module ax = Real ax
  axl-l0 : ax.L (maxℚ l 0r)
  axl-l0 = handle (split-< l 0r)
    where
    handle : (l < 0r) ⊎ (0r ≤ l) -> ax.L (maxℚ l 0r)
    handle (inj-r 0≤l) = ∣ inj-l (subst x.L (sym (maxℚ-left l 0r 0≤l)) xl-l) ∣
    handle (inj-l l<0) = handle2 (split-< 0r u)
      where
      l0=0 : (maxℚ l 0r) == 0r
      l0=0 = maxℚ-right l 0r (inj-l l<0)

      handle2 : (0r < u) ⊎ (u ≤ 0r) -> ax.L (maxℚ l 0r)
      handle2 (inj-r u≤0) = isLowerSet≤ ax (maxℚ l 0r) (- u) l0≤-u axl--u
        where
        l0≤-u : (maxℚ l 0r) ≤ (- u)
        l0≤-u = subst (_≤ (- u)) (sym l0=0) (r--flips-≤ u 0r u≤0)

        axl--u : ax.L (- u)
        axl--u = ∣ inj-r (subst x.U (sym minus-double-inverse) xu-u) ∣
      handle2 (inj-l 0<u) = bot-elim (¬scz (<0-Neg l l<0 , 0<-Pos u 0<u))

  axu--lu : ax.U (maxℚ (- l) u)
  axu--lu = subst x.L (sym p) xl-l-u , xu--lu
    where
    xu--lu : x.U (maxℚ (- l) u)
    xu--lu = isUpperSet≤ x u (maxℚ (- l) u) (maxℚ-≤-right (- l) u) xu-u

    p : (- (maxℚ (- l) u)) == minℚ l (- u)
    p = (r--maxℚ (- l) u >=> (cong2 minℚ minus-double-inverse refl))

    xl-l-u : x.L (minℚ l (- u))
    xl-l-u = isLowerSet≤ x (minℚ l (- u)) l (minℚ-≤-left l (- u)) xl-l

ℝ∈Iℚ-absℝ-dual : (x : ℝ) (a : Iℚ) -> ℝ∈Iℚ x a -> ℝ∈Iℚ x (i- a) ->
                 ℝ∈Iℚ (absℝ x) a
ℝ∈Iℚ-absℝ-dual x (Iℚ-cons l u l≤u) (xl-l , xu-u) (xl--u , xu--l) =
  ∣ inj-l xl-l ∣ , (xl--u , xu-u)

ℝ∈Iℚ-absℝ-NonNegI : (x : ℝ) (a : Iℚ) -> NonNegI a -> ℝ∈Iℚ x a -> ℝ∈Iℚ (absℝ x) a
ℝ∈Iℚ-absℝ-NonNegI x (Iℚ-cons l u l≤u) nn-l (xl-l , xu-u) =
  ∣ inj-l xl-l ∣ , (isLowerSet≤ x (- u) l -u≤l xl-l , xu-u)
  where
  0≤l : 0r ≤ l
  0≤l = NonNeg-0≤ l nn-l
  -u≤l : (- u) ≤ l
  -u≤l = (trans-ℚ≤ { - u} (r--flips-≤ l u l≤u) (trans-ℚ≤ { - l} (r--flips-≤ 0r l 0≤l) 0≤l))

ℝ∈Iℚ-absℝ-NonPosI : (x : ℝ) (a : Iℚ) -> NonPosI a -> ℝ∈Iℚ x a -> ℝ∈Iℚ (absℝ x) (i- a)
ℝ∈Iℚ-absℝ-NonPosI x (Iℚ-cons l u l≤u) np-u (xl-l , xu-u) =
  ∣ inj-r (subst x.U (sym minus-double-inverse) xu-u) ∣ ,
  ( subst x.L (sym minus-double-inverse) xl-l , isUpperSet≤ x u (- l) u≤-l xu-u)
  where
  module x = Real x
  u≤0 : u ≤ 0r
  u≤0 = NonPos-≤0 u np-u

  u≤-l : u ≤ (- l)
  u≤-l = (trans-ℚ≤ {u} (trans-ℚ≤ {u} u≤0 (r--flips-≤ u 0r u≤0)) (r--flips-≤ l u l≤u))

private
  ℝ∈Iℚ-absℝ-ImbalancedI : (x : ℝ) (a : Iℚ) -> ImbalancedI a -> ℝ∈Iℚ x a -> ℝ∈Iℚ (absℝ x) a
  ℝ∈Iℚ-absℝ-ImbalancedI x (Iℚ-cons l u l≤u) -l≤u (xl-l , xu-u) =
    ∣ inj-l xl-l ∣ , (isLowerSet≤ x (- u) l -u≤l xl-l , xu-u)
    where
    -u≤l : (- u) ≤ l
    -u≤l = subst ((- u) ≤_) minus-double-inverse (r--flips-≤ (- l) u -l≤u)

  ℝ∈Iℚ-absℝ-ΣImbalancedI : (x : ℝ) (a : Iℚ) -> ℝ∈Iℚ (absℝ x) a ->
                           Σ[ b ∈ Iℚ ] (ℝ∈Iℚ (absℝ x) b × ImbalancedI b × b i⊆ a)
  ℝ∈Iℚ-absℝ-ΣImbalancedI x a@(Iℚ-cons l u l≤u) ax∈a@(axl-l , (xl--u , xu-u)) = handle (split-< u (- l))
    where
    ax = absℝ x
    module x = Real x
    module ax = Real ax
    Res = Σ[ b ∈ Iℚ ] (ℝ∈Iℚ (absℝ x) b × ImbalancedI b × b i⊆ a)

    handle : (u < (- l) ⊎ (- l) ≤ u) -> Res
    handle (inj-r -l≤u) = a , ax∈a , -l≤u , (i⊆-cons refl-≤ refl-≤)
    handle (inj-l u<-l) = b , (ℝ∈Iℚ-absℝ-ImbalancedI x b mmu≤u (xl--u , xu-u)) , mmu≤u , b⊆a
      where
      l≤-u : l ≤ (- u)
      l≤-u = inj-l (subst (_< (- u)) (minus-double-inverse {_} {_} {_} {l}) (r--flips-order u (- l) u<-l))

      b : Iℚ
      b = (Iℚ-cons (- u) u (inj-l (ℝ-bounds->ℚ< x (- u) u xl--u xu-u)))

      mmu≤u : (- (- u)) ≤ u
      mmu≤u = subst ((- (- u)) ≤_) minus-double-inverse refl-≤

      b⊆a : b i⊆ a
      b⊆a = i⊆-cons l≤-u refl-≤



ℝ∈Iℚ-absℝ⁻ : (x : ℝ) (a : Iℚ) -> ℝ∈Iℚ (absℝ x) a -> ∥ ℝ∈Iℚ x a ⊎ ℝ∈Iℚ x (i- a) ∥
ℝ∈Iℚ-absℝ⁻ x a@(Iℚ-cons l u l≤u) (axl-l , (xl--u , xu-u)) = ∥-map handle axl-l
  where
  module x = Real x

  handle : (x.L l) ⊎ (x.U (- l)) -> ℝ∈Iℚ x a ⊎ ℝ∈Iℚ x (i- a)
  handle (inj-l xl-l) = inj-l (xl-l , xu-u)
  handle (inj-r xu--l) = inj-r (xl--u , xu--l)



module _ (x y : ℝ) where
  private
    xy = (x ℝ* y)
    mx = (ℝ- x)
    my = (ℝ- y)
    ax = absℝ x
    ay = absℝ y
    axy = absℝ xy
    axay = ax ℝ* ay
    module x = Real x
    module y = Real y
    module xy = Real xy
    module axy = Real axy
    module axay = Real axay

    ℝ∈Iℚ--' : (z : ℝ) (a : Iℚ) -> ℝ∈Iℚ z (i- a) -> ℝ∈Iℚ (ℝ- z) a
    ℝ∈Iℚ--' z a z∈-a = subst (ℝ∈Iℚ (ℝ- z)) (i--double-inverse {a}) (ℝ∈Iℚ-- z (i- a) z∈-a)

    f : (b : Iℚ) -> ImbalancedI b -> ℝ∈Iℚ axay b -> ℝ∈Iℚ axy b
    f b imb-b axay∈b = unsquash (isProp-ℝ∈Iℚ axy b) (∥-bind handle (ℝ∈Iℚ-*⁻ ax ay b axay∈b))
      where
      ∈b : ℝ -> Type₀
      ∈b z = ℝ∈Iℚ z b

      handle : Σ[ c ∈ Iℚ ] Σ[ d ∈ Iℚ ] (ℝ∈Iℚ ax c × ℝ∈Iℚ ay d × (c i* d) i⊆ b) ->
               ∥ ℝ∈Iℚ axy b ∥
      handle (c , d , ax∈c , ay∈d , cd⊆b) =
        ∥-map2 handle2 (ℝ∈Iℚ-absℝ⁻ x c ax∈c) (ℝ∈Iℚ-absℝ⁻ y d ay∈d)
        where
        handle2 : (ℝ∈Iℚ x c ⊎ ℝ∈Iℚ x (i- c)) -> (ℝ∈Iℚ y d ⊎ ℝ∈Iℚ y (i- d)) ->
                  ℝ∈Iℚ axy b
        handle2 (inj-l x∈c) (inj-l y∈d) = ℝ∈Iℚ-absℝ-ImbalancedI xy b imb-b xy∈b
          where
          xy∈b : ℝ∈Iℚ xy b
          xy∈b = ℝ∈Iℚ-⊆ xy cd⊆b (ℝ∈Iℚ-* x y c d x∈c y∈d)
        handle2 (inj-l x∈c) (inj-r y∈-d) =
          subst ∈b (absℝ-- xy) (ℝ∈Iℚ-absℝ-ImbalancedI m-xy b imb-b m-xy∈b)
          where
          xmy = (x ℝ* (ℝ- y))
          xmy∈b : ℝ∈Iℚ xmy b
          xmy∈b = ℝ∈Iℚ-⊆ xmy cd⊆b (ℝ∈Iℚ-* x my c d x∈c (ℝ∈Iℚ--' y d y∈-d))

          m-xy = ℝ- xy

          m-path : xmy == m-xy
          m-path = minus-extract-right

          m-xy∈b : ℝ∈Iℚ m-xy b
          m-xy∈b = subst ∈b m-path xmy∈b

        handle2 (inj-r x∈-c) (inj-l y∈d) =
          subst ∈b (absℝ-- xy) (ℝ∈Iℚ-absℝ-ImbalancedI m-xy b imb-b m-xy∈b)
          where
          mxy = ((ℝ- x) ℝ* y)
          mxy∈b : ℝ∈Iℚ mxy b
          mxy∈b = ℝ∈Iℚ-⊆ mxy cd⊆b (ℝ∈Iℚ-* mx y c d (ℝ∈Iℚ--' x c x∈-c) y∈d)

          m-xy = ℝ- xy

          m-path : mxy == m-xy
          m-path = minus-extract-left

          m-xy∈b : ℝ∈Iℚ m-xy b
          m-xy∈b = subst ∈b m-path mxy∈b
        handle2 (inj-r x∈-c) (inj-r y∈-d) = (ℝ∈Iℚ-absℝ-ImbalancedI xy b imb-b xy∈b)
          where
          mxmy = ((ℝ- x) ℝ* (ℝ- y))
          mxmy∈b : ℝ∈Iℚ mxmy b
          mxmy∈b = ℝ∈Iℚ-⊆ mxmy cd⊆b (ℝ∈Iℚ-* mx my c d (ℝ∈Iℚ--' x c x∈-c) (ℝ∈Iℚ--' y d y∈-d))

          m-path : mxmy == xy
          m-path = minus-extract-left >=> cong ℝ-_ minus-extract-right >=> minus-double-inverse

          xy∈b : ℝ∈Iℚ xy b
          xy∈b = subst ∈b m-path mxmy∈b


    f' : (b : Iℚ) -> ℝ∈Iℚ axay b -> ℝ∈Iℚ axy b
    f' b axay∈b = unsquash (isProp-ℝ∈Iℚ axy b) (∥-map handle (ℝ∈Iℚ-*⁻ ax ay b axay∈b))
      where
      handle : Σ[ c ∈ Iℚ ] Σ[ d ∈ Iℚ ] (ℝ∈Iℚ ax c × ℝ∈Iℚ ay d × (c i* d) i⊆ b) ->
               ℝ∈Iℚ axy b
      handle (c , d , ax∈c , ay∈d , cd⊆b) = axy∈b
        where
        Σic = ℝ∈Iℚ-absℝ-ΣImbalancedI x c ax∈c
        ic = fst Σic
        ax∈ic = fst (snd Σic)
        imb-ic = fst (snd (snd Σic))
        ic⊆c = snd (snd (snd Σic))

        Σid = ℝ∈Iℚ-absℝ-ΣImbalancedI y d ay∈d
        id = fst Σid
        ay∈id = fst (snd Σid)
        imb-id = fst (snd (snd Σid))
        id⊆d = snd (snd (snd Σid))

        icid = ic i* id
        imb-icid = i*-preserves-ImbalancedI ic id imb-ic imb-id
        axy∈icid = f icid imb-icid (ℝ∈Iℚ-* ax ay ic id ax∈ic ay∈id)
        icid⊆b = trans-i⊆ (i*-preserves-⊆ ic⊆c id⊆d) cd⊆b
        axy∈b = ℝ∈Iℚ-⊆ axy icid⊆b axy∈icid


  abstract
    absℝ-distrib-* : absℝ (x ℝ* y) == absℝ x ℝ* absℝ y
    absℝ-distrib-* = sym (ℝ∈Iℚ->path axay axy f')

 --   absℝ-distrib-* : absℝ (x * y) == absℝ x * absℝ y
 --   absℝ-distrib-* = p1 >=> p2 >=> p3
 --     where
 --     p1 : absℝ (x ℝ* y) == absℝ (x ℝ*ᵉ y)
 --     p1 = cong absℝ (ℝ*-eval {x} {y})
 --     p2 : absℝ (x ℝ*ᵉ y) == absℝ x ℝ*ᵉ absℝ y
 --     p2 = absℝ-distrib-*ᵉ
 --     p3 : absℝ x ℝ*ᵉ absℝ y == absℝ x ℝ* absℝ y
 --     p3 = sym (ℝ*-eval {absℝ x} {absℝ y})
