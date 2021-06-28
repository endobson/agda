{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.minmax
open import relation hiding (_⊆_)
open import ring.implementations.rational
open import sign
open import sign.instances.rational
open import truncation

private
  variable
    ℓ : Level

record Iℚ : Type₀ where
  constructor Iℚ-cons
  field
    l : ℚ
    u : ℚ
    l≤u : l ℚ≤ u


_i+_ : Iℚ -> Iℚ -> Iℚ
_i+_ (Iℚ-cons l1 u1 l1≤u1) (Iℚ-cons l2 u2 l2≤u2 ) =
  Iℚ-cons (l1 r+ l2) (u1 r+ u2) (r+-both-preserves-≤ l1 u1 l2 u2 l1≤u1 l2≤u2)

Iℚ-bounds-path : {a b : Iℚ} -> (Iℚ.l a == Iℚ.l b) -> (Iℚ.u a == Iℚ.u b) -> a == b
Iℚ-bounds-path {a} {b} pl pu = \i -> Iℚ-cons (pl i) (pu i) (p≤ i)
  where
  p≤ : PathP (\i -> (pl i) ℚ≤ (pu i)) (Iℚ.l≤u a) (Iℚ.l≤u b)
  p≤ = isProp->PathP (\i -> isProp-ℚ≤ {pl i} {pu i}) (Iℚ.l≤u a) (Iℚ.l≤u b)

i-_ : Iℚ -> Iℚ
i-_ (Iℚ-cons l u l≤u) = Iℚ-cons (r- u) (r- l) (r--flips-≤ l u l≤u)


ℚ->Iℚ : ℚ -> Iℚ
ℚ->Iℚ q = Iℚ-cons q q (refl-ℚ≤ {q})

0i : Iℚ
0i = ℚ->Iℚ 0r

1i : Iℚ
1i = ℚ->Iℚ 1r

NonNegI : Pred Iℚ ℓ-zero
NonNegI (Iℚ-cons l _ _) = NonNeg l
NonPosI : Pred Iℚ ℓ-zero
NonPosI (Iℚ-cons _ u _) = NonPos u
CrossZeroI : Pred Iℚ ℓ-zero
CrossZeroI (Iℚ-cons l u _) = NonPos l × NonNeg u

PosI : Pred Iℚ ℓ-zero
PosI (Iℚ-cons l _ _) = Pos l
NegI : Pred Iℚ ℓ-zero
NegI (Iℚ-cons _ u _) = Neg u
StrictCrossZeroI : Pred Iℚ ℓ-zero
StrictCrossZeroI (Iℚ-cons l u _) = Neg l × Pos u

ConstantI : Pred Iℚ ℓ-zero
ConstantI (Iℚ-cons l u _) = l == u

ZeroEndedI : Pred Iℚ ℓ-zero
ZeroEndedI (Iℚ-cons l u _) = Zero l ⊎ Zero u



i+-commute : (a b : Iℚ) -> a i+ b == b i+ a
i+-commute (Iℚ-cons l1 u1 _) (Iℚ-cons l2 u2 _) = Iℚ-bounds-path (r+-commute l1 l2) (r+-commute u1 u2)

i+-assoc : (a b c : Iℚ) -> (a i+ b) i+ c == a i+ (b i+ c)
i+-assoc (Iℚ-cons l1 u1 _) (Iℚ-cons l2 u2 _) (Iℚ-cons l3 u3 _) =
  Iℚ-bounds-path (r+-assoc l1 l2 l3) (r+-assoc u1 u2 u3)

i+-right-zero : (a : Iℚ) -> a i+ 0i == a
i+-right-zero (Iℚ-cons l u _) = Iℚ-bounds-path (r+-right-zero l) (r+-right-zero u)

_i∪_ : Iℚ -> Iℚ -> Iℚ
_i∪_ (Iℚ-cons l1 u1 l1≤u1) (Iℚ-cons l2 u2 l2≤u2) =
  (Iℚ-cons (minℚ l1 l2) (maxℚ u1 u2)
           (trans-ℚ≤ {minℚ l1 l2} {u1} {maxℚ u1 u2}
                     (trans-ℚ≤ {minℚ l1 l2} {l1} {u1} (minℚ-≤-left l1 l2) l1≤u1)
                     (maxℚ-≤-left u1 u2)))

i∪-commute : (a b : Iℚ) -> a i∪ b == b i∪ a
i∪-commute a b = Iℚ-bounds-path minℚ-commute maxℚ-commute

i∪-same : (a : Iℚ) -> a i∪ a == a
i∪-same a = Iℚ-bounds-path minℚ-same maxℚ-same

i-scale : ℚ -> Iℚ -> Iℚ
i-scale k (Iℚ-cons l u l≤u) =
  Iℚ-cons min max (trans-ℚ≤ {min} {k r* l} {max} (minℚ-≤-left (k r* l) (k r* u))
                                                 (maxℚ-≤-left (k r* l) (k r* u)))
  where
  min = minℚ (k r* l) (k r* u)
  max = maxℚ (k r* l) (k r* u)

i-scale-NN : ℚ⁰⁺ -> Iℚ -> Iℚ
i-scale-NN (k , nn-k) (Iℚ-cons l u l≤u) =
  Iℚ-cons (k r* l) (k r* u) (r*₁-preserves-≤ (k , nn-k) l u l≤u)

i-scale-NP : ℚ⁰⁻ -> Iℚ -> Iℚ
i-scale-NP (k , np-k) (Iℚ-cons l u l≤u) =
  Iℚ-cons (k r* u) (k r* l) (r*₁-flips-≤ (k , np-k) l u l≤u)

i-scale-NN-path : (k : ℚ⁰⁺) -> (a : Iℚ) -> i-scale-NN k a == i-scale ⟨ k ⟩ a
i-scale-NN-path (k , nn-k) (Iℚ-cons l u l≤u) = Iℚ-bounds-path (sym lp) (sym up)
  where
  lp : minℚ (k r* l) (k r* u) == k r* l
  lp = minℚ-left _ _ (r*₁-preserves-≤ (k , nn-k) l u l≤u)
  up : maxℚ (k r* l) (k r* u) == k r* u
  up = maxℚ-right _ _ (r*₁-preserves-≤ (k , nn-k) l u l≤u)

i-scale-NP-path : (k : ℚ⁰⁻) -> (a : Iℚ) -> i-scale-NP k a == i-scale ⟨ k ⟩ a
i-scale-NP-path (k , np-k) (Iℚ-cons l u l≤u) = Iℚ-bounds-path (sym lp) (sym up)
  where
  lp : minℚ (k r* l) (k r* u) == k r* u
  lp = minℚ-right _ _ (r*₁-flips-≤ (k , np-k) l u l≤u)
  up : maxℚ (k r* l) (k r* u) == k r* l
  up = maxℚ-left _ _ (r*₁-flips-≤ (k , np-k) l u l≤u)

i-scale-1 : (a : Iℚ) -> i-scale 1r a == a
i-scale-1 a = sym (i-scale-NN-path (1r , inj-l Pos-1r) a) >=>
              Iℚ-bounds-path (r*-left-one _) (r*-left-one _)

_i*_ : Iℚ -> Iℚ -> Iℚ
_i*_ (Iℚ-cons l1 u1 _) i2 = (i-scale l1 i2) i∪ (i-scale u1 i2)


i*-commute : (a b : Iℚ) -> a i* b == b i* a
i*-commute (Iℚ-cons al au _) (Iℚ-cons bl bu _) = Iℚ-bounds-path l-path u-path
  where
  l-path : minℚ (minℚ (al r* bl) (al r* bu)) (minℚ (au r* bl) (au r* bu)) ==
           minℚ (minℚ (bl r* al) (bl r* au)) (minℚ (bu r* al) (bu r* au))
  l-path = minℚ-assoc _ _ _ >=>
           cong (minℚ _) (sym (minℚ-assoc _ _ _) >=>
                          cong (\x -> minℚ x _) minℚ-commute >=>
                          minℚ-assoc _ _ _) >=>
           sym (minℚ-assoc _ _ _) >=>
           cong2 minℚ (cong2 minℚ (r*-commute _ _) (r*-commute _ _))
                      (cong2 minℚ (r*-commute _ _) (r*-commute _ _))
  u-path : maxℚ (maxℚ (al r* bl) (al r* bu)) (maxℚ (au r* bl) (au r* bu)) ==
           maxℚ (maxℚ (bl r* al) (bl r* au)) (maxℚ (bu r* al) (bu r* au))
  u-path = maxℚ-assoc _ _ _ >=>
           cong (maxℚ _) (sym (maxℚ-assoc _ _ _) >=>
                          cong (\x -> maxℚ x _) maxℚ-commute >=>
                          maxℚ-assoc _ _ _) >=>
           sym (maxℚ-assoc _ _ _) >=>
           cong2 maxℚ (cong2 maxℚ (r*-commute _ _) (r*-commute _ _))
                      (cong2 maxℚ (r*-commute _ _) (r*-commute _ _))

i--scale : (a : Iℚ) -> i- a == i-scale (r- 1r) a
i--scale a@(Iℚ-cons l u l≤u) = Iℚ-bounds-path lp up
  where
  mu≤ml : ((r- 1r) r* u) ℚ≤ ((r- 1r) r* l)
  mu≤ml = r*₁-flips-≤ ((r- 1r) , inj-l (r--flips-sign _ _ Pos-1r)) l u l≤u


  lp : (r- u) == minℚ ((r- 1r) r* l) ((r- 1r) r* u)
  lp = cong r-_ (sym (r*-left-one u)) >=>
       sym (r*-minus-extract-left 1r u) >=>
       sym (minℚ-right ((r- 1r) r* l) ((r- 1r) r* u) mu≤ml)
  up : (r- l) == maxℚ ((r- 1r) r* l) ((r- 1r) r* u)
  up = cong r-_ (sym (r*-left-one l)) >=>
       sym (r*-minus-extract-left 1r l) >=>
       sym (maxℚ-left ((r- 1r) r* l) ((r- 1r) r* u) mu≤ml)


i-scale-distrib-∪ : (k : ℚ) (a b : Iℚ) ->
                    i-scale k (a i∪ b) == (i-scale k a) i∪ (i-scale k b)
i-scale-distrib-∪ k a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) =
  handle _ (isSign-self k)
  where
  nn-case : NonNeg k -> i-scale k (a i∪ b) == (i-scale k a) i∪ (i-scale k b)
  nn-case nn-k =
    sym (i-scale-NN-path k⁺ (a i∪ b)) >=>
    Iℚ-bounds-path lp up >=>
    cong2 _i∪_ (i-scale-NN-path k⁺ a) (i-scale-NN-path k⁺ b)
    where
    k⁺ : ℚ⁰⁺
    k⁺ = k , nn-k
    lp : k r* (minℚ al bl) == minℚ (k r* al) (k r* bl)
    lp = r*₁-distrib-min k⁺ al bl
    up : k r* (maxℚ au bu) == maxℚ (k r* au) (k r* bu)
    up = r*₁-distrib-max k⁺ au bu

  np-case : NonPos k -> i-scale k (a i∪ b) == (i-scale k a) i∪ (i-scale k b)
  np-case np-k =
    sym (i-scale-NP-path k⁻ (a i∪ b)) >=>
    Iℚ-bounds-path up lp >=>
    cong2 _i∪_ (i-scale-NP-path k⁻ a) (i-scale-NP-path k⁻ b)
    where
    k⁻ : ℚ⁰⁻
    k⁻ = k , np-k
    lp : k r* (minℚ al bl) == maxℚ (k r* al) (k r* bl)
    lp = r*₁-flip-distrib-min k⁻ al bl
    up : k r* (maxℚ au bu) == minℚ (k r* au) (k r* bu)
    up = r*₁-flip-distrib-max k⁻ au bu

  handle : (s : Sign) -> isSign s k ->
           i-scale k (a i∪ b) == (i-scale k a) i∪ (i-scale k b)
  handle pos-sign pk = nn-case (inj-l pk)
  handle zero-sign zk = nn-case (inj-r zk)
  handle neg-sign nk = np-case (inj-l nk)

i-scale-twice : (k1 k2 : ℚ) (a : Iℚ) -> i-scale k1 (i-scale k2 a) == i-scale (k1 r* k2) a
i-scale-twice k1 k2 a = handle _ _ (isSign-self k1) (isSign-self k2)
  where
  Ans = i-scale k1 (i-scale k2 a) == i-scale (k1 r* k2) a

  nnnn-case : NonNeg k1 -> NonNeg k2 -> Ans
  nnnn-case nn-k1 nn-k2 =
    cong (i-scale k1) (sym (i-scale-NN-path (k2 , nn-k2) a)) >=>
    sym (i-scale-NN-path (k1 , nn-k1) (i-scale-NN (k2 , nn-k2) a)) >=>
    Iℚ-bounds-path (sym (r*-assoc _ _ _)) (sym (r*-assoc _ _ _)) >=>
    i-scale-NN-path (_ , r*-NonNeg-NonNeg nn-k1 nn-k2) a

  nnnp-case : NonNeg k1 -> NonPos k2 -> Ans
  nnnp-case nn-k1 np-k2 =
    cong (i-scale k1) (sym (i-scale-NP-path (k2 , np-k2) a)) >=>
    sym (i-scale-NN-path (k1 , nn-k1) (i-scale-NP (k2 , np-k2) a)) >=>
    Iℚ-bounds-path (sym (r*-assoc _ _ _)) (sym (r*-assoc _ _ _)) >=>
    i-scale-NP-path (_ , r*-NonNeg-NonPos nn-k1 np-k2) a

  npnn-case : NonPos k1 -> NonNeg k2 -> Ans
  npnn-case np-k1 nn-k2 =
    cong (i-scale k1) (sym (i-scale-NN-path (k2 , nn-k2) a)) >=>
    sym (i-scale-NP-path (k1 , np-k1) (i-scale-NN (k2 , nn-k2) a)) >=>
    Iℚ-bounds-path (sym (r*-assoc _ _ _)) (sym (r*-assoc _ _ _)) >=>
    i-scale-NP-path (_ , r*-NonPos-NonNeg np-k1 nn-k2) a

  npnp-case : NonPos k1 -> NonPos k2 -> Ans
  npnp-case np-k1 np-k2 =
    cong (i-scale k1) (sym (i-scale-NP-path (k2 , np-k2) a)) >=>
    sym (i-scale-NP-path (k1 , np-k1) (i-scale-NP (k2 , np-k2) a)) >=>
    Iℚ-bounds-path (sym (r*-assoc _ _ _)) (sym (r*-assoc _ _ _)) >=>
    i-scale-NN-path (_ , r*-NonPos-NonPos np-k1 np-k2) a

  handle : (s1 s2 : Sign) -> (isSign s1 k1) -> (isSign s2 k2) -> Ans
  handle pos-sign  pos-sign  p1 p2 = nnnn-case (inj-l p1) (inj-l p2)
  handle pos-sign  zero-sign p1 p2 = nnnn-case (inj-l p1) (inj-r p2)
  handle pos-sign  neg-sign  p1 p2 = nnnp-case (inj-l p1) (inj-l p2)
  handle zero-sign pos-sign  p1 p2 = nnnn-case (inj-r p1) (inj-l p2)
  handle zero-sign zero-sign p1 p2 = nnnn-case (inj-r p1) (inj-r p2)
  handle zero-sign neg-sign  p1 p2 = nnnp-case (inj-r p1) (inj-l p2)
  handle neg-sign  pos-sign  p1 p2 = npnn-case (inj-l p1) (inj-l p2)
  handle neg-sign  zero-sign p1 p2 = npnp-case (inj-l p1) (inj-r p2)
  handle neg-sign  neg-sign  p1 p2 = npnp-case (inj-l p1) (inj-l p2)



i-Lower : Iℚ -> Pred ℚ ℓ-zero
i-Lower (Iℚ-cons l _ _) q = q ℚ≤ l

i-Upper : Iℚ -> Pred ℚ ℓ-zero
i-Upper (Iℚ-cons _ u _) q = u ℚ≤ q

i∪-Lower : {q : ℚ} -> (a b : Iℚ) -> i-Lower a q -> i-Lower b q -> i-Lower (a i∪ b) q
i∪-Lower a b q≤al q≤bl = minℚ-property (Iℚ.l a) (Iℚ.l b) q≤al q≤bl

i∪-Upper : {q : ℚ} -> (a b : Iℚ) -> i-Upper a q -> i-Upper b q -> i-Upper (a i∪ b) q
i∪-Upper a b au≤q bu≤q = maxℚ-property (Iℚ.u a) (Iℚ.u b) au≤q bu≤q

LowerUpper->Constant : {q : ℚ} -> (a : Iℚ) -> i-Lower a q -> i-Upper a q -> ConstantI a
LowerUpper->Constant {q} (Iℚ-cons l u l≤u)  q≤l u≤q = antisym-ℚ≤ l≤u (trans-ℚ≤ {u} {q} {l} u≤q q≤l)

i-width : Iℚ -> ℚ
i-width (Iℚ-cons l u _) = diffℚ l u

NonNeg-i-width : (a : Iℚ) -> NonNeg (i-width a)
NonNeg-i-width = Iℚ.l≤u

i-scale-width : (k : ℚ) (a : Iℚ) -> i-width (i-scale k a) == absℚ k r* (i-width a)
i-scale-width k a@(Iℚ-cons l u l≤u)  = handle (isSign-self k)
  where
  nn-case : NonNeg k -> i-width (i-scale k a) == absℚ k r* (i-width a)
  nn-case nn-k =
    cong2 diffℚ (minℚ-left _ _ kl≤ku) (maxℚ-right _ _ kl≤ku) >=>
    sym (r*-distrib-diffℚ k l u) >=>
    cong (_r* (diffℚ l u)) (sym (absℚ-NonNeg nn-k))

    where
    kl≤ku : (k r* l) ℚ≤ (k r* u)
    kl≤ku = r*₁-preserves-≤ (k , nn-k) l u l≤u

  n-case : Neg k -> i-width (i-scale k a) == absℚ k r* (i-width a)
  n-case n-k =
    cong2 diffℚ (minℚ-right _ _ ku≤kl) (maxℚ-left _ _ ku≤kl) >=>
    sym (r*-distrib-diffℚ k u l) >=>
    sym RationalRing.minus-double-inverse >=>
    cong r-_ (sym (r*-minus-extract-right _ _)) >=>
    (sym (r*-minus-extract-left _ _)) >=>
    cong2 _r*_ (sym (absℚ-NonPos (inj-l n-k)))
               (sym (diffℚ-anticommute l u))

    where
    ku≤kl : (k r* u) ℚ≤ (k r* l)
    ku≤kl = r*₁-flips-≤ (k , inj-l n-k) l u l≤u


  handle : {s : Sign} -> isSign s k -> i-width (i-scale k a) == absℚ k r* (i-width a)
  handle {pos-sign}  pos-k  = nn-case (inj-l pos-k)
  handle {zero-sign} zero-k = nn-case (inj-r zero-k)
  handle {neg-sign}  neg-k  = n-case neg-k

i∪₁-width-≤ : (a b : Iℚ) -> i-width a ℚ≤ i-width (a i∪ b)
i∪₁-width-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) =
  r+-both-preserves-≤ au (maxℚ au bu) (r- al) (r- (minℚ al bl)) lt1 lt2
  where
  lt1 : au ℚ≤ (maxℚ au bu)
  lt1 = maxℚ-≤-left au bu
  lt2 : (r- al) ℚ≤ (r- (minℚ al bl))
  lt2 = r--flips-≤ (minℚ al bl) al (minℚ-≤-left al bl)

i∪₂-width-≤ : (a b : Iℚ) -> i-width b ℚ≤ i-width (a i∪ b)
i∪₂-width-≤ a b = subst (\x -> i-width b ℚ≤ i-width x) (i∪-commute b a) (i∪₁-width-≤ b a)

i-maxabs : Iℚ -> ℚ
i-maxabs (Iℚ-cons l u _) = maxℚ (absℚ l) (absℚ u)

private
  NonNeg-≤ : (a b : ℚ) -> NonNeg a -> a ℚ≤ b -> NonNeg b
  NonNeg-≤ a b nn-a a≤b = subst NonNeg (diffℚ-step a b) (r+-NonNeg-NonNeg nn-a a≤b)
  NonPos-≤ : (a b : ℚ) -> NonPos b -> a ℚ≤ b -> NonPos a
  NonPos-≤ a b np-b a≤b =
    subst NonPos (diffℚ-step b a)
                 (r+-preserves-NonPos np-b (subst NonPos (sym (diffℚ-anticommute b a))
                                                         (r--NonNeg a≤b)))
  Pos-≤ : (a b : ℚ) -> Pos a -> a ℚ≤ b -> Pos b
  Pos-≤ a b p-a a≤b = subst Pos (diffℚ-step a b) (r+-Pos-NonNeg p-a a≤b)
  Neg-≤ : (a b : ℚ) -> Neg b -> a ℚ≤ b -> Neg a
  Neg-≤ a b n-b a≤b =
   subst Neg (RationalRing.minus-double-inverse {a})
             (r--flips-sign _ _ (Pos-≤ (r- b) (r- a) (r--flips-sign _ _ n-b) (r--flips-≤ a b a≤b)))

  Pos-< : (a b : ℚ) -> NonNeg a -> a < b -> Pos b
  Pos-< a b nn-a a<b = subst Pos (diffℚ-step a b) (r+-NonNeg-Pos nn-a a<b)

  Neg-< : (a b : ℚ) -> NonPos b -> a < b -> Neg a
  Neg-< a b np-b a<b =
   subst Neg (RationalRing.minus-double-inverse {a})
             (r--flips-sign _ _ (Pos-< (r- b) (r- a) (r--NonPos np-b) (r--flips-order a b a<b)))



i-maxabs-NonNeg : (a : Iℚ) -> NonNegI a -> i-maxabs a == Iℚ.u a
i-maxabs-NonNeg (Iℚ-cons l u l≤u) nn-l =
  cong2 maxℚ (absℚ-NonNeg nn-l) (absℚ-NonNeg nn-u) >=>
  maxℚ-right l u l≤u
  where
  nn-u = NonNeg-≤ l u nn-l l≤u

i-maxabs-NonPos : (a : Iℚ) -> NonPosI a -> i-maxabs a == (r- (Iℚ.l a))
i-maxabs-NonPos (Iℚ-cons l u l≤u) np-u =
  cong2 maxℚ (absℚ-NonPos np-l) (absℚ-NonPos np-u) >=>
  maxℚ-left (r- l) (r- u) (r--flips-≤ l u l≤u)
  where
  np-l = NonPos-≤ l u np-u l≤u

i-maxabs-CrossZero : (a : Iℚ) -> CrossZeroI a -> i-maxabs a ℚ≤ i-width a
i-maxabs-CrossZero a@(Iℚ-cons l u l≤u) (np-l , nn-u) =
  subst (_ℚ≤ w) (sym pm) (maxℚ-property {P = (_ℚ≤ w)} (r- l) u l-lt u-lt)
  where
  m = i-maxabs a
  w = i-width a
  pm : m == maxℚ (r- l) u
  pm = cong2 maxℚ (absℚ-NonPos np-l) (absℚ-NonNeg nn-u)

  l-lt : (r- l) ℚ≤ w
  l-lt = subst (_ℚ≤ w) (r+-left-zero (r- l)) (r+₂-preserves-≤ _ _ (r- l) (NonNeg-0≤ _ nn-u))

  u-lt : u ℚ≤ w
  u-lt = subst (_ℚ≤ w) (r+-right-zero u) (r+₁-preserves-≤ u _ _ (NonNeg-0≤ _ (r--NonPos np-l)))


i-maxabs-Zero : (a : Iℚ) -> Zero (i-maxabs a) -> a == 0i
i-maxabs-Zero a@(Iℚ-cons al au _) zm = Iℚ-bounds-path zl zu
  where
  np-aal : NonPos (absℚ al)
  np-aal =
    ≤0-NonPos _ ((subst ((absℚ al) ℚ≤_) (Zero-path _ zm) (maxℚ-≤-left (absℚ al) (absℚ au))))

  np-aau : NonPos (absℚ au)
  np-aau =
    ≤0-NonPos _ ((subst ((absℚ au) ℚ≤_) (Zero-path _ zm) (maxℚ-≤-right (absℚ al) (absℚ au))))

  zl : al == 0r
  zl = Zero-path al (absℚ-Zero (NonNeg-NonPos->Zero (NonNeg-absℚ al) np-aal))
  zu : au == 0r
  zu = Zero-path au (absℚ-Zero (NonNeg-NonPos->Zero (NonNeg-absℚ au) np-aau))




NonNeg-i-maxabs : (a : Iℚ) -> NonNeg (i-maxabs a)
NonNeg-i-maxabs (Iℚ-cons l u _) =
  maxℚ-property {P = NonNeg} (absℚ l) (absℚ u) (NonNeg-absℚ l) (NonNeg-absℚ u)


i-width-bound : (a : Iℚ) -> i-width a ℚ≤ (2r r* (i-maxabs a))
i-width-bound a@(Iℚ-cons l u l≤u) =
  subst2 _ℚ≤_ (diffℚ-trans l 0r u) (2r-path (i-maxabs a)) lt1
  where
  dl≤absl : diffℚ l 0r ℚ≤ absℚ l
  dl≤absl = subst (_ℚ≤ absℚ l) (sym (r+-left-zero (r- l))) (maxℚ-≤-right l (r- l))
  absl≤maxabs : absℚ l ℚ≤ i-maxabs a
  absl≤maxabs = maxℚ-≤-left _ _
  dl≤maxabs = trans-ℚ≤ {diffℚ l 0r} {absℚ l} {i-maxabs a} dl≤absl absl≤maxabs

  du≤absu : diffℚ 0r u ℚ≤ absℚ u
  du≤absu = subst (_ℚ≤ absℚ u) (sym (r+-right-zero u)) (maxℚ-≤-left u (r- u))
  absu≤maxabs : absℚ u ℚ≤ i-maxabs a
  absu≤maxabs = maxℚ-≤-right _ _
  du≤maxabs = trans-ℚ≤ {diffℚ 0r u} {absℚ u} {i-maxabs a} du≤absu absu≤maxabs

  dp : diffℚ l 0r r+ diffℚ 0r u == diffℚ l u
  dp = (diffℚ-trans l 0r u)

  lt1 : (diffℚ l 0r r+ diffℚ 0r u) ℚ≤ (i-maxabs a r+ i-maxabs a)
  lt1 = r+-both-preserves-≤ (diffℚ l 0r) (i-maxabs a) (diffℚ 0r u) (i-maxabs a)
                            dl≤maxabs du≤maxabs


i*-width-NNNN : (a b : Iℚ) -> NonNegI a -> NonNegI b ->
                i-width (a i* b) ==
                (i-width a r* (Iℚ.l b)) r+ (Iℚ.u a r* (i-width b))
i*-width-NNNN a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) nn-al nn-bl =
  wp2 >=> delta-p
  where
  nn-au : NonNeg au
  nn-au = subst NonNeg (diffℚ-step al au) (r+-NonNeg-NonNeg nn-al al≤au)
  nn-bu : NonNeg bu
  nn-bu = subst NonNeg (diffℚ-step bl bu) (r+-NonNeg-NonNeg nn-bl bl≤bu)
  wa = i-width a
  wb = i-width b

  albl≤albu : (al r* bl) ℚ≤ (al r* bu)
  albl≤albu = r*₁-preserves-≤ (al , nn-al) bl bu bl≤bu
  aubl≤aubu : (au r* bl) ℚ≤ (au r* bu)
  aubl≤aubu = r*₁-preserves-≤ (au , nn-au) bl bu bl≤bu

  albl≤aubl : (al r* bl) ℚ≤ (au r* bl)
  albl≤aubl = r*₂-preserves-≤ al au (bl , nn-bl) al≤au
  albu≤aubu : (al r* bu) ℚ≤ (au r* bu)
  albu≤aubu = r*₂-preserves-≤ al au (bu , nn-bu) al≤au

  i1 = i-scale al b
  i1lp : Iℚ.l i1 == al r* bl
  i1lp = minℚ-left _ _ albl≤albu
  i1up : Iℚ.u i1 == al r* bu
  i1up = maxℚ-right _ _ albl≤albu
  i2 = i-scale au b
  i2lp : Iℚ.l i2 == au r* bl
  i2lp = minℚ-left _ _ aubl≤aubu
  i2up : Iℚ.u i2 == au r* bu
  i2up = maxℚ-right _ _ aubl≤aubu


  l = Iℚ.l (a i* b)
  lp : l == al r* bl
  lp = cong2 minℚ i1lp i2lp >=> minℚ-left _ _ albl≤aubl

  u = Iℚ.u (a i* b)
  up : u == au r* bu
  up = cong2 maxℚ i1up i2up >=> maxℚ-right _ _ albu≤aubu

  wp : i-width (a i* b) == (au r* bu) r+ (r- (al r* bl))
  wp = cong2 diffℚ lp up

  delta = ((wa r* bl) r+ ((al r* wb) r+ (wa r* wb)))

  abup : (au r* bu) == delta r+ (al r* bl)
  abup = cong2 _r*_ (sym (diffℚ-step al au)) (sym (diffℚ-step bl bu)) >=>
         RationalSemiring.*-distrib-+-left {al r+ wa} {bl} {wb} >=>
         cong2 _r+_ (RationalSemiring.*-distrib-+-right {al} {wa} {bl})
                    (RationalSemiring.*-distrib-+-right {al} {wa} {wb}) >=>
         r+-assoc (al r* bl) (wa r* bl) ((al r* wb) r+ (wa r* wb)) >=>
         r+-commute (al r* bl) ((wa r* bl) r+ ((al r* wb) r+ (wa r* wb)))

  wp2 : i-width (a i* b) == delta
  wp2 = wp >=> (cong (_r+ (r- (al r* bl))) abup) >=>
        r+-assoc delta (al r* bl) (r- (al r* bl)) >=>
        cong (delta r+_) (r+-inverse (al r* bl)) >=>
        r+-right-zero delta

  delta-p : delta == (wa r* bl) r+ (au r* wb)
  delta-p =
    cong ((wa r* bl) r+_) (sym (RationalSemiring.*-distrib-+-right) >=>
                           cong (_r* wb) (diffℚ-step al au))

i*-width-NNNP : (a b : Iℚ) -> NonNegI a -> NonPosI b ->
                i-width (a i* b) ==
                (i-width a r* (r- (Iℚ.l b))) r+ (Iℚ.l a r* (i-width b))
i*-width-NNNP a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) nn-al np-bu =
  wp >=> path
  where
  nn-au : NonNeg au
  nn-au = subst NonNeg (diffℚ-step al au) (r+-NonNeg-NonNeg nn-al al≤au)
  np-bl : NonPos bl
  np-bl = subst NonPos (diffℚ-step bu bl)
                       (r+-preserves-NonPos np-bu (subst NonPos (sym (diffℚ-anticommute bu bl))
                                                                (r--NonNeg bl≤bu)))
  wa = i-width a
  wb = i-width b

  albl≤albu : (al r* bl) ℚ≤ (al r* bu)
  albl≤albu = r*₁-preserves-≤ (al , nn-al) bl bu bl≤bu
  aubl≤aubu : (au r* bl) ℚ≤ (au r* bu)
  aubl≤aubu = r*₁-preserves-≤ (au , nn-au) bl bu bl≤bu

  aubl≤albl : (au r* bl) ℚ≤ (al r* bl)
  aubl≤albl = r*₂-flips-≤ al au (bl , np-bl) al≤au
  aubu≤albu : (au r* bu) ℚ≤ (al r* bu)
  aubu≤albu = r*₂-flips-≤ al au (bu , np-bu) al≤au

  i1 = i-scale al b
  i1lp : Iℚ.l i1 == al r* bl
  i1lp = minℚ-left _ _ albl≤albu
  i1up : Iℚ.u i1 == al r* bu
  i1up = maxℚ-right _ _ albl≤albu
  i2 = i-scale au b
  i2lp : Iℚ.l i2 == au r* bl
  i2lp = minℚ-left _ _ aubl≤aubu
  i2up : Iℚ.u i2 == au r* bu
  i2up = maxℚ-right _ _ aubl≤aubu


  l = Iℚ.l (a i* b)
  lp : l == au r* bl
  lp = cong2 minℚ i1lp i2lp >=> minℚ-right _ _ aubl≤albl

  u = Iℚ.u (a i* b)
  up : u == al r* bu
  up = cong2 maxℚ i1up i2up >=> maxℚ-left _ _ aubu≤albu

  wp : i-width (a i* b) == (al r* bu) r+ (r- (au r* bl))
  wp = cong2 diffℚ lp up

  path : (al r* bu) r+ (r- (au r* bl)) == (wa r* (r- bl)) r+ (al r* wb)
  path = cong2 _r+_ (cong (al r*_) (sym (diffℚ-step bl bu)) >=>
                     RationalSemiring.*-distrib-+-left {al} {bl} {wb} >=>
                     r+-commute (al r* bl) (al r* wb))
                    (sym (r*-minus-extract-right au bl) >=>
                     cong (_r* (r- bl)) (sym (diffℚ-step al au)) >=>
                     RationalSemiring.*-distrib-+-right {al} {wa} {r- bl}) >=>
         r+-assoc (al r* wb) (al r* bl) ((al r* (r- bl)) r+ (wa r* (r- bl))) >=>
         cong ((al r* wb) r+_) (sym (r+-assoc (al r* bl) (al r* (r- bl)) (wa r* (r- bl))) >=>
                                cong (_r+ (wa r* (r- bl)))
                                     (cong ((al r* bl) r+_) (r*-minus-extract-right al bl) >=>
                                      r+-inverse (al r* bl)) >=>
                                r+-left-zero (wa r* (r- bl))) >=>
         r+-commute (al r* wb) (wa r* (r- bl))

i*-width-NNCZ : (a b : Iℚ) -> NonNegI a -> CrossZeroI b ->
                i-width (a i* b) == (Iℚ.u a r* (i-width b))
i*-width-NNCZ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) nn-al (np-bl , nn-bu) = wp
  where
  nn-au : NonNeg au
  nn-au = subst NonNeg (diffℚ-step al au) (r+-NonNeg-NonNeg nn-al al≤au)

  wa = i-width a
  wb = i-width b

  albl≤albu : (al r* bl) ℚ≤ (al r* bu)
  albl≤albu = r*₁-preserves-≤ (al , nn-al) bl bu bl≤bu
  aubl≤aubu : (au r* bl) ℚ≤ (au r* bu)
  aubl≤aubu = r*₁-preserves-≤ (au , nn-au) bl bu bl≤bu

  aubl≤albl : (au r* bl) ℚ≤ (al r* bl)
  aubl≤albl = r*₂-flips-≤ al au (bl , np-bl) al≤au
  albu≤aubu : (al r* bu) ℚ≤ (au r* bu)
  albu≤aubu = r*₂-preserves-≤ al au (bu , nn-bu) al≤au

  i1 = i-scale al b
  i1lp : Iℚ.l i1 == al r* bl
  i1lp = minℚ-left _ _ albl≤albu
  i1up : Iℚ.u i1 == al r* bu
  i1up = maxℚ-right _ _ albl≤albu
  i2 = i-scale au b
  i2lp : Iℚ.l i2 == au r* bl
  i2lp = minℚ-left _ _ aubl≤aubu
  i2up : Iℚ.u i2 == au r* bu
  i2up = maxℚ-right _ _ aubl≤aubu


  l = Iℚ.l (a i* b)
  lp : l == au r* bl
  lp = cong2 minℚ i1lp i2lp >=> minℚ-right _ _ aubl≤albl

  u = Iℚ.u (a i* b)
  up : u == au r* bu
  up = cong2 maxℚ i1up i2up >=> maxℚ-right _ _ albu≤aubu

  wp : i-width (a i* b) == au r* (diffℚ bl bu)
  wp = cong2 diffℚ lp up >=> sym (r*-distrib-diffℚ au bl bu)


i*-width-NPNP : (a b : Iℚ) -> NonPosI a -> NonPosI b ->
                i-width (a i* b) ==
                (i-width a r* (r- (Iℚ.l b))) r+ ((r- (Iℚ.u a)) r* (i-width b))
i*-width-NPNP a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) np-au np-bu =
  wp2 >=> delta-p
  where
  np-al : NonPos al
  np-al = subst NonPos (diffℚ-step au al)
                       (r+-preserves-NonPos np-au (subst NonPos (sym (diffℚ-anticommute au al))
                                                                (r--NonNeg al≤au)))
  np-bl : NonPos bl
  np-bl = subst NonPos (diffℚ-step bu bl)
                       (r+-preserves-NonPos np-bu (subst NonPos (sym (diffℚ-anticommute bu bl))
                                                                (r--NonNeg bl≤bu)))

  wa = i-width a
  wb = i-width b

  albu≤albl : (al r* bu) ℚ≤ (al r* bl)
  albu≤albl = r*₁-flips-≤ (al , np-al) bl bu bl≤bu
  aubu≤aubl : (au r* bu) ℚ≤ (au r* bl)
  aubu≤aubl = r*₁-flips-≤ (au , np-au) bl bu bl≤bu

  aubl≤albl : (au r* bl) ℚ≤ (al r* bl)
  aubl≤albl = r*₂-flips-≤ al au (bl , np-bl) al≤au
  aubu≤albu : (au r* bu) ℚ≤ (al r* bu)
  aubu≤albu = r*₂-flips-≤ al au (bu , np-bu) al≤au

  i1 = i-scale al b
  i1lp : Iℚ.l i1 == al r* bu
  i1lp = minℚ-right _ _ albu≤albl
  i1up : Iℚ.u i1 == al r* bl
  i1up = maxℚ-left _ _ albu≤albl
  i2 = i-scale au b
  i2lp : Iℚ.l i2 == au r* bu
  i2lp = minℚ-right _ _ aubu≤aubl
  i2up : Iℚ.u i2 == au r* bl
  i2up = maxℚ-left _ _ aubu≤aubl


  l = Iℚ.l (a i* b)
  lp : l == au r* bu
  lp = cong2 minℚ i1lp i2lp >=> minℚ-right _ _ aubu≤albu

  u = Iℚ.u (a i* b)
  up : u == al r* bl
  up = cong2 maxℚ i1up i2up >=> maxℚ-left _ _ aubl≤albl

  wp : i-width (a i* b) == (al r* bl) r+ (r- (au r* bu))
  wp = cong2 diffℚ lp up

  delta = ((wa r* bl) r+ ((al r* wb) r+ (wa r* wb)))

  abup : (au r* bu) == (al r* bl) r+ delta
  abup = cong2 _r*_ (sym (diffℚ-step al au)) (sym (diffℚ-step bl bu)) >=>
         RationalSemiring.*-distrib-+-left {al r+ wa} {bl} {wb} >=>
         cong2 _r+_ (RationalSemiring.*-distrib-+-right {al} {wa} {bl})
                    (RationalSemiring.*-distrib-+-right {al} {wa} {wb}) >=>
         r+-assoc (al r* bl) (wa r* bl) ((al r* wb) r+ (wa r* wb))

  wp2 : i-width (a i* b) == (r- delta)
  wp2 = wp >=> (cong ((al r* bl) r+_)
                     (cong r-_ abup >=>
                      RationalRing.minus-distrib-plus {al r* bl} {delta})) >=>
        sym (r+-assoc (al r* bl) (r- (al r* bl)) (r- delta)) >=>
        cong (_r+ (r- delta)) (r+-inverse (al r* bl)) >=>
        r+-left-zero (r- delta)

  delta-p : (r- delta) == (wa r* (r- bl)) r+ ((r- au) r* wb)
  delta-p =
    cong r-_
      (cong ((wa r* bl) r+_) (sym (RationalSemiring.*-distrib-+-right) >=>
                              cong (_r* wb) (diffℚ-step al au))) >=>
    RationalRing.minus-distrib-plus {wa r* bl} {au r* wb} >=>
    cong2 _r+_ (sym (r*-minus-extract-right wa bl)) (sym (r*-minus-extract-left au wb))

i*-width-NPCZ : (a b : Iℚ) -> NonPosI a -> CrossZeroI b ->
                i-width (a i* b) == (r- (Iℚ.l a)) r* (i-width b)
i*-width-NPCZ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) np-au (np-bl , nn-bu) = wp
  where
  np-al : NonPos al
  np-al = subst NonPos (diffℚ-step au al)
                       (r+-preserves-NonPos np-au (subst NonPos (sym (diffℚ-anticommute au al))
                                                                (r--NonNeg al≤au)))
  wa = i-width a
  wb = i-width b

  albu≤albl : (al r* bu) ℚ≤ (al r* bl)
  albu≤albl = r*₁-flips-≤ (al , np-al) bl bu bl≤bu
  aubu≤aubl : (au r* bu) ℚ≤ (au r* bl)
  aubu≤aubl = r*₁-flips-≤ (au , np-au) bl bu bl≤bu

  aubl≤albl : (au r* bl) ℚ≤ (al r* bl)
  aubl≤albl = r*₂-flips-≤ al au (bl , np-bl) al≤au
  albu≤aubu : (al r* bu) ℚ≤ (au r* bu)
  albu≤aubu = r*₂-preserves-≤ al au (bu , nn-bu) al≤au

  i1 = i-scale al b
  i1lp : Iℚ.l i1 == al r* bu
  i1lp = minℚ-right _ _ albu≤albl
  i1up : Iℚ.u i1 == al r* bl
  i1up = maxℚ-left _ _ albu≤albl
  i2 = i-scale au b
  i2lp : Iℚ.l i2 == au r* bu
  i2lp = minℚ-right _ _ aubu≤aubl
  i2up : Iℚ.u i2 == au r* bl
  i2up = maxℚ-left _ _ aubu≤aubl


  l = Iℚ.l (a i* b)
  lp : l == al r* bu
  lp = cong2 minℚ i1lp i2lp >=> minℚ-left _ _ albu≤aubu

  u = Iℚ.u (a i* b)
  up : u == al r* bl
  up = cong2 maxℚ i1up i2up >=> maxℚ-left _ _ aubl≤albl

  wp : i-width (a i* b) == (r- al) r* wb
  wp = cong2 diffℚ lp up >=> sym (r*-distrib-diffℚ al bu bl) >=>
       cong (al r*_) (diffℚ-anticommute bu bl) >=>
       r*-minus-extract-right al wb >=>
       sym (r*-minus-extract-left al wb)


i*-width-CZCZ-≤ : (a b : Iℚ) -> CrossZeroI a -> CrossZeroI b ->
                  (i-width (a i* b)) ℚ≤ (((i-width a) r* (i-maxabs b)) r+ ((i-maxabs a) r* (i-width b)))
i*-width-CZCZ-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) (np-al , nn-au) (np-bl , nn-bu) =
  d≤wmmw
  where
  wa = i-width a
  wb = i-width b
  ma = i-maxabs a
  mb = i-maxabs b

  nn-wa : NonNeg wa
  nn-wa = NonNeg-i-width a
  nn-wb : NonNeg wb
  nn-wb = NonNeg-i-width b
  nn-ma : NonNeg ma
  nn-ma = NonNeg-i-maxabs a
  nn-mb : NonNeg mb
  nn-mb = NonNeg-i-maxabs b

  ma≤wa : ma ℚ≤ wa
  ma≤wa = i-maxabs-CrossZero a (np-al , nn-au)
  mb≤wb : mb ℚ≤ wb
  mb≤wb = i-maxabs-CrossZero b (np-bl , nn-bu)

  albu≤albl : (al r* bu) ℚ≤ (al r* bl)
  albu≤albl = r*₁-flips-≤ (al , np-al) bl bu bl≤bu
  aubl≤aubu : (au r* bl) ℚ≤ (au r* bu)
  aubl≤aubu = r*₁-preserves-≤ (au , nn-au) bl bu bl≤bu

  aubl≤albl : (au r* bl) ℚ≤ (al r* bl)
  aubl≤albl = r*₂-flips-≤ al au (bl , np-bl) al≤au
  albu≤aubu : (al r* bu) ℚ≤ (au r* bu)
  albu≤aubu = r*₂-preserves-≤ al au (bu , nn-bu) al≤au

  i1 = i-scale al b
  i1lp : Iℚ.l i1 == al r* bu
  i1lp = minℚ-right _ _ albu≤albl
  i1up : Iℚ.u i1 == al r* bl
  i1up = maxℚ-left _ _ albu≤albl
  i2 = i-scale au b
  i2lp : Iℚ.l i2 == au r* bl
  i2lp = minℚ-left _ _ aubl≤aubu
  i2up : Iℚ.u i2 == au r* bu
  i2up = maxℚ-right _ _ aubl≤aubu

  mal≤m : (r- al) ℚ≤ ma
  mal≤m = subst (_ℚ≤ ma) (absℚ-NonPos np-al) (maxℚ-≤-left (absℚ al) (absℚ au))

  mbl≤m : (r- bl) ℚ≤ mb
  mbl≤m = subst (_ℚ≤ mb) (absℚ-NonPos np-bl) (maxℚ-≤-left (absℚ bl) (absℚ bu))

  m≤al : (r- ma) ℚ≤ al
  m≤al = subst ((r- ma) ℚ≤_) (RationalRing.minus-double-inverse {al})
               (r--flips-≤ (r- al) ma mal≤m)

  m≤bl : (r- mb) ℚ≤ bl
  m≤bl = subst ((r- mb) ℚ≤_) (RationalRing.minus-double-inverse {bl})
               (r--flips-≤ (r- bl) mb mbl≤m)

  au≤m : au ℚ≤ ma
  au≤m = subst (_ℚ≤ ma) (absℚ-NonNeg nn-au) (maxℚ-≤-right (absℚ al) (absℚ au))

  bu≤m : bu ℚ≤ mb
  bu≤m = subst (_ℚ≤ mb) (absℚ-NonNeg nn-bu) (maxℚ-≤-right (absℚ bl) (absℚ bu))

  mm≤albu : (r- (ma r* mb)) ℚ≤ (al r* bu)
  mm≤albu =
    subst (_ℚ≤ (al r* bu)) (r*-minus-extract-left ma mb)
    (trans-ℚ≤ {(r- ma) r* mb} {al r* mb} {al r* bu}
              (r*₂-preserves-≤ (r- ma) al (mb , nn-mb) m≤al)
              (r*₁-flips-≤ (al , np-al) bu mb bu≤m))

  mm≤aubl : (r- (ma r* mb)) ℚ≤ (au r* bl)
  mm≤aubl =
    subst (_ℚ≤ (au r* bl)) (r*-minus-extract-right ma mb)
    (trans-ℚ≤ {ma r* (r- mb)} {ma r* bl} {au r* bl}
              (r*₁-preserves-≤ (ma , nn-ma) (r- mb) bl m≤bl)
              (r*₂-flips-≤ au ma (bl , np-bl) au≤m))

  albl≤mm : (al r* bl) ℚ≤ (ma r* mb)
  albl≤mm =
    subst ((al r* bl) ℚ≤_) (r*-minus-extract-right (r- ma) mb >=>
                            cong r-_ (r*-minus-extract-left ma mb) >=>
                            RationalRing.minus-double-inverse {ma r* mb})
    (trans-ℚ≤ {al r* bl} {(r- ma) r* bl} {(r- ma) r* (r- mb)}
              (r*₂-flips-≤ (r- ma) al (bl , np-bl) m≤al)
              (r*₁-flips-≤ ((r- ma) , (r--NonNeg nn-ma)) (r- mb) bl m≤bl))

  aubu≤mm : (au r* bu) ℚ≤ (ma r* mb)
  aubu≤mm =
    (trans-ℚ≤ {au r* bu} {ma r* bu} {ma r* mb}
              (r*₂-preserves-≤ au ma (bu , nn-bu) au≤m)
              (r*₁-preserves-≤ (ma , nn-ma) bu mb bu≤m))


  l = Iℚ.l (a i* b)
  lp : l == minℚ (al r* bu) (au r* bl)
  lp = cong2 minℚ i1lp i2lp

  mm≤l : (r- (ma r* mb)) ℚ≤ l
  mm≤l = subst ((r- (ma r* mb)) ℚ≤_) (sym lp)
         (minℚ-property {P = ((r- (ma r* mb)) ℚ≤_)} (al r* bu) (au r* bl) mm≤albu mm≤aubl)

  ml≤mm : (r- l) ℚ≤ (ma r* mb)
  ml≤mm = subst ((r- l) ℚ≤_) (RationalRing.minus-double-inverse {ma r* mb})
                (r--flips-≤ (r- (ma r* mb)) l mm≤l)


  u = Iℚ.u (a i* b)
  up : u == maxℚ (al r* bl) (au r* bu)
  up = cong2 maxℚ i1up i2up

  u≤mm : u ℚ≤ (ma r* mb)
  u≤mm = subst (_ℚ≤ (ma r* mb)) (sym up)
         (maxℚ-property {P = (_ℚ≤ (ma r* mb))} (al r* bl) (au r* bu) albl≤mm aubu≤mm)

  mm≤wm : (ma r* mb) ℚ≤ (wa r* mb)
  mm≤wm = r*₂-preserves-≤ ma wa (mb , nn-mb) ma≤wa

  mm≤mw : (ma r* mb) ℚ≤ (ma r* wb)
  mm≤mw = r*₁-preserves-≤ (ma , nn-ma) mb wb mb≤wb

  d≤wmmw : (diffℚ l u) ℚ≤ ((wa r* mb) r+ (ma r* wb))
  d≤wmmw = r+-both-preserves-≤ u (wa r* mb) (r- l) (ma r* wb)
                               (trans-ℚ≤ {u}    {ma r* mb} {wa r* mb} u≤mm mm≤wm)
                               (trans-ℚ≤ {r- l} {ma r* mb} {ma r* wb} ml≤mm mm≤mw)


i*-width-NNNN-≤ : (a b : Iℚ) -> NonNegI a -> NonNegI b ->
                  (i-width (a i* b)) ℚ≤ (((i-width a) r* (i-maxabs b)) r+ ((i-maxabs a) r* (i-width b)))
i*-width-NNNN-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) nn-al nn-bl =
  subst2 _ℚ≤_ (sym (i*-width-NNNN a b nn-al nn-bl)) p lt

  where
  wa = i-width a
  wb = i-width b

  nn-wa : NonNeg wa
  nn-wa = NonNeg-i-width a

  lt : ((wa r* bl) r+ (au r* wb)) ℚ≤ ((wa r* bu) r+ (au r* wb))
  lt = r+₂-preserves-≤ _ _ (au r* wb) (r*₁-preserves-≤ (wa , nn-wa) bl bu bl≤bu)

  p : ((wa r* bu) r+ (au r* wb)) == ((wa r* (i-maxabs b)) r+ ((i-maxabs a) r* wb))
  p i = (wa r* (i-maxabs-NonNeg b nn-bl (~ i))) r+ ((i-maxabs-NonNeg a nn-al (~ i)) r* wb)


i*-width-NNNP-≤ : (a b : Iℚ) -> NonNegI a -> NonPosI b ->
                  (i-width (a i* b)) ℚ≤ (((i-width a) r* (i-maxabs b)) r+ ((i-maxabs a) r* (i-width b)))
i*-width-NNNP-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) nn-al np-bu =
  subst2 _ℚ≤_ (sym (i*-width-NNNP a b nn-al np-bu)) p lt
  where
  wa = i-width a
  wb = i-width b

  nn-wb : NonNeg wb
  nn-wb = NonNeg-i-width b

  lt : ((wa r* (r- bl)) r+ (al r* wb)) ℚ≤ ((wa r* (r- bl)) r+ (au r* wb))
  lt = r+₁-preserves-≤ (wa r* (r- bl)) _ _ (r*₂-preserves-≤ al au (wb , nn-wb) al≤au)

  p : ((wa r* (r- bl)) r+ (au r* wb)) == ((wa r* (i-maxabs b)) r+ ((i-maxabs a) r* wb))
  p i = (wa r* (i-maxabs-NonPos b np-bu (~ i))) r+ ((i-maxabs-NonNeg a nn-al (~ i)) r* wb)


i*-width-NPNN-≤ : (a b : Iℚ) -> NonPosI a -> NonNegI b ->
                  (i-width (a i* b)) ℚ≤ (((i-width a) r* (i-maxabs b)) r+ ((i-maxabs a) r* (i-width b)))
i*-width-NPNN-≤ a b np-a nn-b =
  subst2 _ℚ≤_ (cong i-width (i*-commute b a))
              (\i -> r+-commute (r*-commute (i-width b) (i-maxabs a) i)
                                (r*-commute (i-maxabs b) (i-width a) i) i)
         (i*-width-NNNP-≤ b a nn-b np-a)


i*-width-NPNP-≤ : (a b : Iℚ) -> NonPosI a -> NonPosI b ->
                  (i-width (a i* b)) ℚ≤ (((i-width a) r* (i-maxabs b)) r+ ((i-maxabs a) r* (i-width b)))
i*-width-NPNP-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) np-au np-bu =
  subst2 _ℚ≤_ (sym (i*-width-NPNP a b np-au np-bu)) p lt
  where
  wa = i-width a
  wb = i-width b

  nn-wb : NonNeg wb
  nn-wb = NonNeg-i-width b

  lt : ((wa r* (r- bl)) r+ ((r- au) r* wb)) ℚ≤ ((wa r* (r- bl)) r+ ((r- al) r* wb))
  lt = r+₁-preserves-≤ (wa r* (r- bl)) _ _ (r*₂-preserves-≤ (r- au) (r- al) (wb , nn-wb)
                                                            (r--flips-≤ al au al≤au))

  p : ((wa r* (r- bl)) r+ ((r- al) r* wb)) == ((wa r* (i-maxabs b)) r+ ((i-maxabs a) r* wb))
  p i = (wa r* (i-maxabs-NonPos b np-bu (~ i))) r+ ((i-maxabs-NonPos a np-au (~ i)) r* wb)


i*-width-NNCZ-≤ : (a b : Iℚ) -> NonNegI a -> CrossZeroI b ->
                  (i-width (a i* b)) ℚ≤ (((i-width a) r* (i-maxabs b)) r+ ((i-maxabs a) r* (i-width b)))
i*-width-NNCZ-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) nn-al (np-bl , nn-bu) =
  subst2 _ℚ≤_ (sym (i*-width-NNCZ a b nn-al (np-bl , nn-bu))) p lt

  where
  wa = i-width a
  wb = i-width b
  ma = i-maxabs a
  mb = i-maxabs b

  nn-wa : NonNeg wa
  nn-wa = NonNeg-i-width a
  nn-mb : NonNeg mb
  nn-mb = NonNeg-i-maxabs b

  lt : (au r* wb) ℚ≤ ((wa r* mb) r+ (au r* wb))
  lt = subst (_ℚ≤ ((wa r* mb) r+ (au r* wb)))
             (r+-left-zero (au r* wb))
             (r+₂-preserves-≤ _ _ (au r* wb) (NonNeg-0≤ _ (r*-NonNeg-NonNeg nn-wa nn-mb)))

  p : ((wa r* mb) r+ (au r* wb)) == ((wa r* mb) r+ (ma r* wb))
  p i = (wa r* mb) r+ ((i-maxabs-NonNeg a nn-al (~ i)) r* wb)


i*-width-CZNN-≤ : (a b : Iℚ) -> CrossZeroI a -> NonNegI b ->
                  (i-width (a i* b)) ℚ≤ (((i-width a) r* (i-maxabs b)) r+ ((i-maxabs a) r* (i-width b)))
i*-width-CZNN-≤ a b cz-a nn-b =
  subst2 _ℚ≤_ (cong i-width (i*-commute b a))
              (\i -> r+-commute (r*-commute (i-width b) (i-maxabs a) i)
                                (r*-commute (i-maxabs b) (i-width a) i) i)
         (i*-width-NNCZ-≤ b a nn-b cz-a)

i*-width-NPCZ-≤ : (a b : Iℚ) -> NonPosI a -> CrossZeroI b ->
                  (i-width (a i* b)) ℚ≤ (((i-width a) r* (i-maxabs b)) r+ ((i-maxabs a) r* (i-width b)))
i*-width-NPCZ-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) np-au (np-bl , nn-bu) =
  subst2 _ℚ≤_ (sym (i*-width-NPCZ a b np-au (np-bl , nn-bu))) p lt

  where
  wa = i-width a
  wb = i-width b
  ma = i-maxabs a
  mb = i-maxabs b

  nn-wa : NonNeg wa
  nn-wa = NonNeg-i-width a
  nn-mb : NonNeg mb
  nn-mb = NonNeg-i-maxabs b

  lt : ((r- al) r* wb) ℚ≤ ((wa r* mb) r+ ((r- al) r* wb))
  lt = subst (_ℚ≤ ((wa r* mb) r+ ((r- al) r* wb)))
             (r+-left-zero ((r- al) r* wb))
             (r+₂-preserves-≤ _ _ ((r- al) r* wb) (NonNeg-0≤ _ (r*-NonNeg-NonNeg nn-wa nn-mb)))

  p : ((wa r* mb) r+ ((r- al) r* wb)) == ((wa r* mb) r+ (ma r* wb))
  p i = (wa r* mb) r+ ((i-maxabs-NonPos a np-au (~ i)) r* wb)


i*-width-CZNP-≤ : (a b : Iℚ) -> CrossZeroI a -> NonPosI b ->
                  (i-width (a i* b)) ℚ≤ (((i-width a) r* (i-maxabs b)) r+ ((i-maxabs a) r* (i-width b)))
i*-width-CZNP-≤ a b cz-a np-b =
  subst2 _ℚ≤_ (cong i-width (i*-commute b a))
              (\i -> r+-commute (r*-commute (i-width b) (i-maxabs a) i)
                                (r*-commute (i-maxabs b) (i-width a) i) i)
         (i*-width-NPCZ-≤ b a np-b cz-a)

private
  data Class (i : Iℚ) : Type₀ where
    nn-c : NonNegI i    -> Class i
    np-c : NonPosI i    -> Class i
    cz-c : CrossZeroI i -> Class i

  data StrictClass (i : Iℚ) : Type₀ where
    p-c  : PosI i       -> StrictClass i
    n-c  : NegI i       -> StrictClass i
    cz-c : CrossZeroI i -> StrictClass i

  data StrictClass' (i : Iℚ) : Type₀ where
    nn-c : NonNegI i          -> StrictClass' i
    np-c : NonPosI i          -> StrictClass' i
    cz-c : StrictCrossZeroI i -> StrictClass' i

  classify : (i : Iℚ) -> Class i
  classify i@(Iℚ-cons l u _) = handle _ _ (isSign-self l) (isSign-self u)
    where
    handle : (s1 s2 : Sign) -> (isSign s1 l) -> (isSign s2 u) -> Class i
    handle pos-sign  _  pl _ = nn-c (inj-l pl)
    handle zero-sign _  zl _ = nn-c (inj-r zl)
    handle neg-sign  pos-sign  nl pu = cz-c (inj-l nl , inj-l pu)
    handle neg-sign  zero-sign nl zu = np-c (inj-r zu)
    handle neg-sign  neg-sign  nl nu = np-c (inj-l nu)

  strict-classify : (i : Iℚ) -> StrictClass i
  strict-classify i@(Iℚ-cons l u _) = handle _ _ (isSign-self l) (isSign-self u)
    where
    handle : (s1 s2 : Sign) -> (isSign s1 l) -> (isSign s2 u) -> StrictClass i
    handle pos-sign   _         pl _  = p-c pl
    handle zero-sign  pos-sign  zl pu = cz-c (inj-r zl , inj-l pu)
    handle zero-sign  zero-sign zl zu = cz-c (inj-r zl , inj-r zu)
    handle zero-sign  neg-sign  zl nu = n-c nu
    handle neg-sign   pos-sign  nl pu = cz-c (inj-l nl , inj-l pu)
    handle neg-sign   zero-sign nl zu = cz-c (inj-l nl , inj-r zu)
    handle neg-sign   neg-sign  nl nu = n-c nu

  strict-classify' : (i : Iℚ) -> StrictClass' i
  strict-classify' i@(Iℚ-cons l u _) = handle _ _ (isSign-self l) (isSign-self u)
    where
    handle : (s1 s2 : Sign) -> (isSign s1 l) -> (isSign s2 u) -> StrictClass' i
    handle pos-sign  _  pl _ = nn-c (inj-l pl)
    handle zero-sign _  zl _ = nn-c (inj-r zl)
    handle neg-sign  pos-sign  nl pu = cz-c (nl , pu)
    handle neg-sign  zero-sign nl zu = np-c (inj-r zu)
    handle neg-sign  neg-sign  nl nu = np-c (inj-l nu)



i*-width-≤ : (a b : Iℚ) ->
             (i-width (a i* b)) ℚ≤ (((i-width a) r* (i-maxabs b)) r+ ((i-maxabs a) r* (i-width b)))
i*-width-≤ a b = handle (classify a) (classify b)
  where
  handle : Class a -> Class b ->
           (i-width (a i* b)) ℚ≤ (((i-width a) r* (i-maxabs b)) r+ ((i-maxabs a) r* (i-width b)))
  handle (nn-c pa) (nn-c pb) = i*-width-NNNN-≤ a b pa pb
  handle (nn-c pa) (np-c pb) = i*-width-NNNP-≤ a b pa pb
  handle (nn-c pa) (cz-c pb) = i*-width-NNCZ-≤ a b pa pb
  handle (np-c pa) (nn-c pb) = i*-width-NPNN-≤ a b pa pb
  handle (np-c pa) (np-c pb) = i*-width-NPNP-≤ a b pa pb
  handle (np-c pa) (cz-c pb) = i*-width-NPCZ-≤ a b pa pb
  handle (cz-c pa) (nn-c pb) = i*-width-CZNN-≤ a b pa pb
  handle (cz-c pa) (np-c pb) = i*-width-CZNP-≤ a b pa pb
  handle (cz-c pa) (cz-c pb) = i*-width-CZCZ-≤ a b pa pb

Constant->zero-width : (a : Iℚ) -> ConstantI a -> i-width a == 0r
Constant->zero-width (Iℚ-cons l u _) p = (cong (_r+ (r- l)) (sym p)) >=> (r+-inverse l)

zero-width->Constant : (a : Iℚ) -> i-width a == 0r -> ConstantI a
zero-width->Constant (Iℚ-cons l u _) p =
  sym (r+-right-zero l) >=> (cong (l r+_) (sym p)) >=> diffℚ-step l u


i∪₁-Constant : (a b : Iℚ) -> ConstantI (a i∪ b) -> ConstantI a
i∪₁-Constant a@(Iℚ-cons l u l≤u) b const = (antisym-ℚ≤ l≤u u≤l)
  where

  0w : i-width (a i∪ b) == 0r
  0w = Constant->zero-width (a i∪ b) const

  np-w : NonPos (i-width a)
  np-w = ≤0-NonPos (i-width a) (subst (i-width a ℚ≤_) 0w (i∪₁-width-≤ a b))

  z-w : Zero (i-width a)
  z-w = NonNeg-NonPos->Zero (NonNeg-i-width a) np-w

  u≤l : NonNeg (diffℚ u l)
  u≤l = subst NonNeg (sym (diffℚ-anticommute u l)) (inj-r (r--flips-sign _ _ z-w))

i∪₂-Constant : (a b : Iℚ) -> ConstantI (a i∪ b) -> ConstantI b
i∪₂-Constant a b const = i∪₁-Constant b a (subst ConstantI (i∪-commute a b) const)

i*-Constant : (a b : Iℚ) -> ConstantI (a i* b) -> ConstantI a ⊎ ConstantI b
i*-Constant a@(Iℚ-cons al au _) b const =
  handle (r*-ZeroFactor z1) (r*-ZeroFactor z2)
  where
  c1 : ConstantI (i-scale al b)
  c1 = i∪₁-Constant (i-scale al b) (i-scale au b) const
  c2 : ConstantI (i-scale au b)
  c2 = i∪₂-Constant (i-scale al b) (i-scale au b) const

  z1 : Zero (absℚ al r* (i-width b))
  z1 = subst Zero (sym (Constant->zero-width (i-scale al b) c1) >=> i-scale-width al b) Zero-0r
  z2 : Zero (absℚ au r* (i-width b))
  z2 = subst Zero (sym (Constant->zero-width (i-scale au b) c2) >=> i-scale-width au b) Zero-0r

  handle : (Zero (absℚ al) ⊎ Zero (i-width b)) -> (Zero (absℚ au) ⊎ Zero (i-width b)) -> _
  handle (inj-r zw) _         = inj-r (zero-width->Constant b (Zero-path _ zw))
  handle (inj-l _) (inj-r zw) = inj-r (zero-width->Constant b (Zero-path _ zw))
  handle (inj-l zal) (inj-l zau) = inj-l (pl >=> sym pu)
    where
    pl : al == 0r
    pl = Zero-path _ (absℚ-Zero zal)
    pu : au == 0r
    pu = Zero-path _ (absℚ-Zero zau)

i*-left-one : (a : Iℚ) -> 1i i* a == a
i*-left-one a = cong2 _i∪_ (i-scale-1 a) (i-scale-1 a) >=> (i∪-same a)


-- Inclusion

record _i⊆_ (a : Iℚ) (b : Iℚ) : Type₀ where
  constructor i⊆-cons
  field
    l : Iℚ.l b ℚ≤ Iℚ.l a
    u : Iℚ.u a ℚ≤ Iℚ.u b

OrderedOverlap : (a b : Iℚ) -> Type₀
OrderedOverlap (Iℚ-cons al au _) (Iℚ-cons bl bu _) = bl ℚ≤ au

Overlap : (a b : Iℚ) -> Type₀
Overlap a b = OrderedOverlap a b × OrderedOverlap b a

i-intersect : (a b : Iℚ) -> Overlap a b -> Iℚ
i-intersect a@(Iℚ-cons l1 u1 l1≤u1) b@(Iℚ-cons l2 u2 l2≤u2) (l2≤u1 , l1≤u2) =
  Iℚ-cons (maxℚ l1 l2) (minℚ u1 u2) ls≤us
  where
  ls = maxℚ l1 l2
  us = minℚ u1 u2
  ls≤u1 : ls ℚ≤ u1
  ls≤u1 = maxℚ-property l1 l2 l1≤u1 l2≤u1

  ls≤u2 : ls ℚ≤ u2
  ls≤u2 = maxℚ-property l1 l2 l1≤u2 l2≤u2

  ls≤us : ls ℚ≤ us
  ls≤us = minℚ-property {P = ls ℚ≤_} u1 u2 ls≤u1 ls≤u2

i⊆-Lower : {a b : Iℚ} -> a i⊆ b -> (q : ℚ) -> i-Lower b q -> i-Lower a q
i⊆-Lower {a} {b} (i⊆-cons bl≤al _) q q≤bl = trans-ℚ≤ {q} {Iℚ.l b} {Iℚ.l a} q≤bl bl≤al

i⊆-Upper : {a b : Iℚ} -> a i⊆ b -> (q : ℚ) -> i-Upper b q -> i-Upper a q
i⊆-Upper {a} {b} (i⊆-cons _ au≤bu) q bu≤q = trans-ℚ≤ {Iℚ.u a} {Iℚ.u b} {q} au≤bu bu≤q

trans-i⊆ : {a b c : Iℚ} -> a i⊆ b -> b i⊆ c -> a i⊆ c
trans-i⊆ {Iℚ-cons al au _} {Iℚ-cons bl bu _} {Iℚ-cons cl cu _} a⊆b b⊆c = record
  { l = trans-ℚ≤ {cl} {bl} {al} (_i⊆_.l b⊆c) (_i⊆_.l a⊆b)
  ; u = trans-ℚ≤ {au} {bu} {cu} (_i⊆_.u a⊆b) (_i⊆_.u b⊆c)
  }

i-intersect-⊆₁ : (a b : Iℚ) -> (o : Overlap a b) -> i-intersect a b o i⊆ a
i-intersect-⊆₁ a b _ = i⊆-cons (maxℚ-≤-left _ _) (minℚ-≤-left (Iℚ.u a) _)

i-intersect-⊆₂ : (a b : Iℚ) -> (o : Overlap a b) -> i-intersect a b o i⊆ b
i-intersect-⊆₂ a b _ = i⊆-cons (maxℚ-≤-right _ _) (minℚ-≤-right _ (Iℚ.u b))

i-scale-preserves-⊆ : (k : ℚ) {a b : Iℚ} -> a i⊆ b -> (i-scale k a) i⊆ (i-scale k b)
i-scale-preserves-⊆ k {a@(Iℚ-cons al au al≤au)} {b@(Iℚ-cons bl bu bl≤bu)} (i⊆-cons l u) =
  handle (isSign-self k)
  where
  nn-case : NonNeg k -> (i-scale k a) i⊆ (i-scale k b)
  nn-case nn = i⊆-cons (subst2 _ℚ≤_ (sym minb-path) (sym mina-path) (r*₁-preserves-≤ (k , nn) bl al l))
                       (subst2 _ℚ≤_ (sym maxa-path) (sym maxb-path) (r*₁-preserves-≤ (k , nn) au bu u))
    where
    minb-path : minℚ (k r* bl) (k r* bu) == k r* bl
    minb-path = minℚ-left _ _ (r*₁-preserves-≤ (k , nn) bl bu bl≤bu)

    mina-path : minℚ (k r* al) (k r* au) == k r* al
    mina-path = minℚ-left _ _ (r*₁-preserves-≤ (k , nn) al au al≤au)

    maxb-path : maxℚ (k r* bl) (k r* bu) == k r* bu
    maxb-path = maxℚ-right _ _ (r*₁-preserves-≤ (k , nn) bl bu bl≤bu)

    maxa-path : maxℚ (k r* al) (k r* au) == k r* au
    maxa-path = maxℚ-right _ _ (r*₁-preserves-≤ (k , nn) al au al≤au)

  np-case : NonPos k -> (i-scale k a) i⊆ (i-scale k b)
  np-case np = i⊆-cons (subst2 _ℚ≤_ (sym minb-path) (sym mina-path) (r*₁-flips-≤ (k , np) au bu u))
                       (subst2 _ℚ≤_ (sym maxa-path) (sym maxb-path) (r*₁-flips-≤ (k , np) bl al l))
    where
    minb-path : minℚ (k r* bl) (k r* bu) == k r* bu
    minb-path = minℚ-right _ _ (r*₁-flips-≤ (k , np) bl bu bl≤bu)

    mina-path : minℚ (k r* al) (k r* au) == k r* au
    mina-path = minℚ-right _ _ (r*₁-flips-≤ (k , np) al au al≤au)

    maxb-path : maxℚ (k r* bl) (k r* bu) == k r* bl
    maxb-path = maxℚ-left _ _ (r*₁-flips-≤ (k , np) bl bu bl≤bu)

    maxa-path : maxℚ (k r* al) (k r* au) == k r* al
    maxa-path = maxℚ-left _ _ (r*₁-flips-≤ (k , np) al au al≤au)

  handle : {s : Sign} -> isSign s k -> (i-scale k a) i⊆ (i-scale k b)
  handle {pos-sign}  pk = nn-case (inj-l pk)
  handle {zero-sign} zk = nn-case (inj-r zk)
  handle {neg-sign}  nk = np-case (inj-l nk)


i∪₁-preserves-⊆ : (a : Iℚ) {b c : Iℚ} -> b i⊆ c -> (a i∪ b) i⊆ (a i∪ c)
i∪₁-preserves-⊆ a {b} {c} (i⊆-cons l u) =
  i⊆-cons (minℚ₁-preserves-≤ (Iℚ.l a) (Iℚ.l c) (Iℚ.l b) l)
          (maxℚ₁-preserves-≤ (Iℚ.u a) (Iℚ.u b) (Iℚ.u c) u)

i∪₂-preserves-⊆ : {a b : Iℚ} -> a i⊆ b -> (c : Iℚ) -> (a i∪ c) i⊆ (b i∪ c)
i∪₂-preserves-⊆ {a} {b} a⊆b c =
  subst2 _i⊆_ (i∪-commute c a) (i∪-commute c b) (i∪₁-preserves-⊆ c a⊆b)

i∪-preserves-⊆ : {a b c d : Iℚ} -> a i⊆ b -> c i⊆ d  -> (a i∪ c) i⊆ (b i∪ d)
i∪-preserves-⊆ {a} {b} {c} {d} a⊆b c⊆d =
  trans-i⊆ (i∪₁-preserves-⊆ a c⊆d) (i∪₂-preserves-⊆ a⊆b d)


i*₁-preserves-⊆ : (a : Iℚ) {b c : Iℚ} -> b i⊆ c -> (a i* b) i⊆ (a i* c)
i*₁-preserves-⊆ (Iℚ-cons al au _) b⊆c =
  i∪-preserves-⊆ (i-scale-preserves-⊆ al b⊆c) (i-scale-preserves-⊆ au b⊆c)

i*₂-preserves-⊆ : {a b : Iℚ} -> a i⊆ b -> (c : Iℚ) -> (a i* c) i⊆ (b i* c)
i*₂-preserves-⊆ {a} {b} a⊆b c = subst2 _i⊆_ (i*-commute c a) (i*-commute c b) (i*₁-preserves-⊆ c a⊆b)

i-width-⊆ : {a b : Iℚ} -> a i⊆ b -> i-width a ℚ≤ i-width b
i-width-⊆ {Iℚ-cons al au _} {Iℚ-cons bl bu _} (i⊆-cons l u) =
  r+-both-preserves-≤ au bu (r- al) (r- bl) u (r--flips-≤ bl al l)

i-maxabs-⊆ : {a b : Iℚ} -> a i⊆ b -> i-maxabs a ℚ≤ i-maxabs b
i-maxabs-⊆ {a@(Iℚ-cons al au al≤au)} {b@(Iℚ-cons bl bu bl≤bu)} (i⊆-cons bl≤al au≤bu) =
  maxℚ-property {P = _ℚ≤ i-maxabs b} (absℚ al) (absℚ au) aal≤mb aau≤mb
  where
  abs≤ : (q : ℚ) -> q ℚ≤ absℚ q
  abs≤ q = maxℚ-≤-left q (r- q)
  mabs≤ : (q : ℚ) -> (r- q) ℚ≤ absℚ q
  mabs≤ q = maxℚ-≤-right q (r- q)

  point : (q : ℚ) -> (bl ℚ≤ q) -> (q ℚ≤ bu) -> absℚ q ℚ≤ i-maxabs b
  point q bl≤q q≤bu = handle (split-maxℚ q (r- q))
    where
    handle : (absℚ q == q ⊎ absℚ q == (r- q)) -> absℚ q ℚ≤ i-maxabs b
    handle (inj-l p) =
      subst (_ℚ≤ i-maxabs b) (sym p)
            (trans-ℚ≤ {q} {bu} {i-maxabs b}
                      q≤bu (trans-ℚ≤ {bu} {absℚ bu} {i-maxabs b}
                                     (abs≤ bu) (maxℚ-≤-right (absℚ bl) (absℚ bu))))
    handle (inj-r p) =
      subst (_ℚ≤ i-maxabs b) (sym p)
            (trans-ℚ≤ {(r- q)} {(r- bl)} {i-maxabs b}
                      (r--flips-≤ bl q bl≤q)
                      (trans-ℚ≤ {(r- bl)} {absℚ bl} {i-maxabs b}
                                (mabs≤ bl) (maxℚ-≤-left (absℚ bl) (absℚ bu))))

  al≤bu = trans-ℚ≤ {al} {au} {bu} al≤au au≤bu
  bl≤au = trans-ℚ≤ {bl} {al} {au} bl≤al al≤au

  aal≤mb = point al bl≤al al≤bu
  aau≤mb = point au bl≤au au≤bu




-- Strict Inclusion
record _i⊂_ (a : Iℚ) (b : Iℚ) : Type₀ where
  constructor i⊂-cons
  field
    l : Iℚ.l b < Iℚ.l a
    u : Iℚ.u a < Iℚ.u b

trans-i⊂ : {a b c : Iℚ} -> a i⊂ b -> b i⊂ c -> a i⊂ c
trans-i⊂ {Iℚ-cons al au _} {Iℚ-cons bl bu _} {Iℚ-cons cl cu _} a⊂b b⊂c = record
  { l = trans-< {_} {_} {_} {cl} {bl} {al} (_i⊂_.l b⊂c) (_i⊂_.l a⊂b)
  ; u = trans-< {_} {_} {_} {au} {bu} {cu} (_i⊂_.u a⊂b) (_i⊂_.u b⊂c)
  }

trans-i⊂-i⊆ : {a b c : Iℚ} -> a i⊂ b -> b i⊆ c -> a i⊂ c
trans-i⊂-i⊆ {Iℚ-cons al au _} {Iℚ-cons bl bu _} {Iℚ-cons cl cu _} a⊂b b⊆c = record
  { l = trans-≤-< {cl} {bl} {al} (_i⊆_.l b⊆c) (_i⊂_.l a⊂b)
  ; u = trans-<-≤ {au} {bu} {cu} (_i⊂_.u a⊂b) (_i⊆_.u b⊆c)
  }

weaken-i⊂ : {a b : Iℚ} -> a i⊂ b -> a i⊆ b
weaken-i⊂ (i⊂-cons l u) = (i⊆-cons (inj-l l) (inj-l u))



i∪-preserves-⊂ : {a b c d : Iℚ} -> a i⊂ b -> c i⊂ d -> (a i∪ c) i⊂ (b i∪ d)
i∪-preserves-⊂ {a@(Iℚ-cons al au _)} {b@(Iℚ-cons bl bu _)} {c@(Iℚ-cons cl cu _)} {d@(Iℚ-cons dl du _)}
               (i⊂-cons bl<al au<bu) (i⊂-cons dl<cl cu<du) =
  i⊂-cons (minℚ-preserves-< bl al dl cl bl<al dl<cl) (maxℚ-preserves-< au bu cu du au<bu cu<du)

i-scale-preserves-⊂ : {k : ℚ} {a b : Iℚ} -> NonZero k -> a i⊂ b -> (i-scale k a) i⊂ (i-scale k b)
i-scale-preserves-⊂ {k} {(Iℚ-cons al au al≤au)} {(Iℚ-cons bl bu bl≤bu)} (inj-l pk) (i⊂-cons bl<al au<bu) =
  i⊂-cons (subst2 _<_ (sym minb-path) (sym mina-path) (r*₁-preserves-order (k , pk) bl al bl<al))
          (subst2 _<_ (sym maxa-path) (sym maxb-path) (r*₁-preserves-order (k , pk) au bu au<bu))
  where
  minb-path : minℚ (k r* bl) (k r* bu) == k r* bl
  minb-path = minℚ-left _ _ (r*₁-preserves-≤ (k , inj-l pk) bl bu bl≤bu)

  mina-path : minℚ (k r* al) (k r* au) == k r* al
  mina-path = minℚ-left _ _ (r*₁-preserves-≤ (k , inj-l pk) al au al≤au)

  maxb-path : maxℚ (k r* bl) (k r* bu) == k r* bu
  maxb-path = maxℚ-right _ _ (r*₁-preserves-≤ (k , inj-l pk) bl bu bl≤bu)

  maxa-path : maxℚ (k r* al) (k r* au) == k r* au
  maxa-path = maxℚ-right _ _ (r*₁-preserves-≤ (k , inj-l pk) al au al≤au)
i-scale-preserves-⊂ {k} {(Iℚ-cons al au al≤au)} {(Iℚ-cons bl bu bl≤bu)} (inj-r nk) (i⊂-cons bl<al au<bu) =
  i⊂-cons (subst2 _<_ (sym minb-path) (sym mina-path) (r*₁-flips-order (k , nk) au bu au<bu))
          (subst2 _<_ (sym maxa-path) (sym maxb-path) (r*₁-flips-order (k , nk) bl al bl<al))
  where
  minb-path : minℚ (k r* bl) (k r* bu) == k r* bu
  minb-path = minℚ-right _ _ (r*₁-flips-≤ (k , inj-l nk) bl bu bl≤bu)

  mina-path : minℚ (k r* al) (k r* au) == k r* au
  mina-path = minℚ-right _ _ (r*₁-flips-≤ (k , inj-l nk) al au al≤au)

  maxb-path : maxℚ (k r* bl) (k r* bu) == k r* bl
  maxb-path = maxℚ-left _ _ (r*₁-flips-≤ (k , inj-l nk) bl bu bl≤bu)

  maxa-path : maxℚ (k r* al) (k r* au) == k r* al
  maxa-path = maxℚ-left _ _ (r*₁-flips-≤ (k , inj-l nk) al au al≤au)

i*₁-preserves-⊂ : (a : Iℚ) -> (¬ (ZeroEndedI a)) -> {b c : Iℚ} -> b i⊂ c -> (a i* b) i⊂ (a i* c)
i*₁-preserves-⊂ a@(Iℚ-cons al au _) ¬za {b} {c} b⊂c = handle _ _ (isSign-self al) (isSign-self au)
  where
  handle : (s1 s2 : Sign) -> isSign s1 al -> isSign s2 au -> (a i* b) i⊂ (a i* c)
  handle pos-sign pos-sign pal pau =
    i∪-preserves-⊂ (i-scale-preserves-⊂ (inj-l pal) b⊂c) (i-scale-preserves-⊂ (inj-l pau) b⊂c)
  handle pos-sign neg-sign pal nau =
    i∪-preserves-⊂ (i-scale-preserves-⊂ (inj-l pal) b⊂c) (i-scale-preserves-⊂ (inj-r nau) b⊂c)
  handle neg-sign pos-sign nal pau =
    i∪-preserves-⊂ (i-scale-preserves-⊂ (inj-r nal) b⊂c) (i-scale-preserves-⊂ (inj-l pau) b⊂c)
  handle neg-sign neg-sign nal nau =
    i∪-preserves-⊂ (i-scale-preserves-⊂ (inj-r nal) b⊂c) (i-scale-preserves-⊂ (inj-r nau) b⊂c)
  handle zero-sign _         zal _   = bot-elim (¬za (inj-l zal))
  handle pos-sign  zero-sign _   zau = bot-elim (¬za (inj-r zau))
  handle neg-sign  zero-sign _   zau = bot-elim (¬za (inj-r zau))


i*₂-preserves-⊂ : {a b : Iℚ} -> a i⊂ b -> (c : Iℚ) -> (¬ (ZeroEndedI c)) -> (a i* c) i⊂ (b i* c)
i*₂-preserves-⊂ {a} {b} a⊂b c ¬zc =
  subst2 _i⊂_ (i*-commute c a) (i*-commute c b) (i*₁-preserves-⊂ c ¬zc a⊂b)

i*-preserves-⊂ : {a b c d : Iℚ} -> a i⊂ b -> c i⊂ d ->
                 (¬ (ZeroEndedI a)) -> (a i* c) i⊂ (b i* d)
i*-preserves-⊂ {a} {b} {c} {d} a⊂b c⊂d ¬za =
  trans-i⊂-i⊆ (i*₁-preserves-⊂ a ¬za c⊂d) (i*₂-preserves-⊆ (weaken-i⊂ a⊂b) d)


find-shrink-factor : {a b : Iℚ} -> a i⊂ b -> Σ[ k ∈ ℚ ] (Pos k × k < 1r × i-scale k a i⊆ b)
find-shrink-factor {a@(Iℚ-cons al au al≤au)} {b@(Iℚ-cons bl bu bl≤bu)} (i⊂-cons bl<al au<bu) =
  handle (strict-classify b)
  where
  Ans = Σ[ k ∈ ℚ ] (Pos k × k < 1r × i-scale k a i⊆ b)
  p-case : PosI b -> Ans
  p-case p-bl = k , p-k , k<1 , subst (_i⊆ b) p-path (i⊆-cons bl≤pl pu≤bu)
    where
    al-pos : Pos al
    al-pos = subst Pos (diffℚ-step bl al) (r+-preserves-Pos _ _ p-bl bl<al)

    al-inv : ℚInv al
    al-inv = Pos->Inv al-pos

    1/al = (r1/ al al-inv)
    pos-1/al = (r1/-preserves-Pos al al-inv al-pos)

    k = bl r* 1/al

    k<1 : k < 1r
    k<1 = subst (k <_) (r*-commute al 1/al >=> r1/-inverse al al-inv)
                (r*₂-preserves-order bl al (1/al , pos-1/al) bl<al)

    p-k = r*₁-preserves-sign (bl , p-bl) _ pos-1/al
    nn-k : NonNeg k
    nn-k = inj-l p-k


    nn-au : NonNeg au
    nn-au = NonNeg-≤ al au (inj-l al-pos) al≤au

    p = i-scale-NN (k , nn-k) a
    pl = Iℚ.l p
    pu = Iℚ.u p
    p' = i-scale k a

    p-path : p == p'
    p-path = i-scale-NN-path (k , nn-k) a

    pl-path : pl == bl
    pl-path = r*-assoc bl 1/al al
              >=> (cong (bl r*_) (r1/-inverse al al-inv))
              >=> r*-right-one bl

    bl≤pl : bl ℚ≤ pl
    bl≤pl = subst (_ℚ≤ pl) pl-path (refl-ℚ≤ {pl})

    pu≤au : pu ℚ≤ au
    pu≤au = subst (pu ℚ≤_) (r*-left-one au) (r*₂-preserves-≤ k 1r (au , nn-au) (inj-l k<1))

    pu≤bu : pu ℚ≤ bu
    pu≤bu = trans-ℚ≤ {pu} {au} {bu} pu≤au (inj-l au<bu)

  n-case : NegI b -> Ans
  n-case n-bu =
    k , p-k , k<1 , subst (_i⊆ b) p-path (i⊆-cons bl≤pl pu≤bu)
    where
    n-au : Neg au
    n-au = subst Neg (cong (bu r+_) (sym (diffℚ-anticommute bu au)) >=> diffℚ-step bu au)
                 (r+-preserves-Neg _ _ n-bu (r--flips-sign _ _ au<bu))

    au-inv : ℚInv au
    au-inv = Neg->Inv n-au

    1/au = (r1/ au au-inv)
    neg-1/au = (r1/-preserves-Neg au au-inv n-au)

    k = bu r* 1/au

    k<1 : k < 1r
    k<1 = subst (k <_) (r*-commute au 1/au >=> r1/-inverse au au-inv)
                (r*₂-flips-order au bu (1/au , neg-1/au) au<bu)

    p-k = r*₁-flips-sign (bu , n-bu) _ neg-1/au
    nn-k : NonNeg k
    nn-k = inj-l p-k


    np-al : NonPos al
    np-al = NonPos-≤ al au (inj-l n-au) al≤au

    p = i-scale-NN (k , nn-k) a
    pl = Iℚ.l p
    pu = Iℚ.u p
    p' = i-scale k a

    p-path : p == p'
    p-path = i-scale-NN-path (k , nn-k) a

    pu-path : pu == bu
    pu-path = r*-assoc bu 1/au au
              >=> (cong (bu r*_) (r1/-inverse au au-inv))
              >=> r*-right-one bu

    pu≤bu : pu ℚ≤ bu
    pu≤bu = subst (pu ℚ≤_) pu-path (refl-ℚ≤ {pu})

    al≤pl : al ℚ≤ pl
    al≤pl = subst (_ℚ≤ pl) (r*-left-one al) (r*₂-flips-≤ k 1r (al , np-al) (inj-l k<1))

    bl≤pl : bl ℚ≤ pl
    bl≤pl = trans-ℚ≤ {bl} {al} {pl} (inj-l bl<al) al≤pl

  cz-case : CrossZeroI b -> Ans
  cz-case (np-bl , nn-bu) =
    1/2r , Pos-1/ℕ (2 , _) , 1/2r<1r , subst (_i⊆ b) p-path (i⊆-cons bl≤pl pu≤bu)
    where


    p = i-scale-NN (1/2r , (inj-l (Pos-1/ℕ (2 , _)))) a
    pl = Iℚ.l p
    pu = Iℚ.u p
    p' = i-scale 1/2r a

    p-path : p == p'
    p-path = i-scale-NN-path (1/2r , (inj-l (Pos-1/ℕ (2 , _)))) a

    1/2bu≤bu : (1/2r r* bu) ℚ≤ bu
    1/2bu≤bu = subst ((1/2r r* bu) ℚ≤_) (r*-left-one bu)
                     (r*₂-preserves-≤ 1/2r 1r (bu , nn-bu) (inj-l 1/2r<1r))

    pu≤1/2bu : pu ℚ≤ (1/2r r* bu)
    pu≤1/2bu = r*₁-preserves-≤ (1/2r , inj-l (Pos-1/ℕ (2 , _))) au bu (inj-l au<bu)

    pu≤bu : pu ℚ≤ bu
    pu≤bu = trans-ℚ≤ {pu} {1/2r r* bu} {bu} pu≤1/2bu 1/2bu≤bu

    bl≤1/2bl : bl ℚ≤ (1/2r r* bl)
    bl≤1/2bl = subst (_ℚ≤ (1/2r r* bl)) (r*-left-one bl)
                     (r*₂-flips-≤ 1/2r 1r (bl , np-bl) (inj-l 1/2r<1r))

    1/2bl≤pl : (1/2r r* bl) ℚ≤ pl
    1/2bl≤pl = r*₁-preserves-≤ (1/2r , inj-l (Pos-1/ℕ (2 , _))) bl al (inj-l bl<al)

    bl≤pl : bl ℚ≤ pl
    bl≤pl = trans-ℚ≤ {bl} {1/2r r* bl} {pl} bl≤1/2bl 1/2bl≤pl


  handle : StrictClass b -> Ans
  handle (p-c p) = p-case p
  handle (n-c p) = n-case p
  handle (cz-c p) = cz-case p


find-growth-factor : {a b : Iℚ} -> a i⊂ b -> Σ[ k ∈ ℚ ] (Pos k × 1r < k × i-scale k a i⊆ b)
find-growth-factor {a@(Iℚ-cons al au al≤au)} {b@(Iℚ-cons bl bu bl≤bu)} (i⊂-cons bl<al au<bu) =
  handle (strict-classify' b)
  where
  Ans = Σ[ k ∈ ℚ ] (Pos k × 1r < k × i-scale k a i⊆ b)
  nn-case : NonNegI b -> Ans
  nn-case nn-bl = k , p-k , 1<k , subst (_i⊆ b) p-path (i⊆-cons bl≤pl pu≤bu)
    where
    p-au : Pos au
    p-au = Pos-< bl au nn-bl (trans-<-≤ {bl} {al} {au} bl<al al≤au)

    au-inv : ℚInv au
    au-inv = Pos->Inv p-au

    1/au = (r1/ au au-inv)
    pos-1/au = (r1/-preserves-Pos au au-inv p-au)

    k = bu r* 1/au

    1<k : 1r < k
    1<k = subst (_< k) (r*-commute au 1/au >=> r1/-inverse au au-inv)
                (r*₂-preserves-order au bu (1/au , pos-1/au) au<bu)

    p-bu = Pos-≤ au bu p-au (inj-l au<bu)

    p-k = r*₁-preserves-sign (bu , p-bu) _ pos-1/au
    nn-k : NonNeg k
    nn-k = inj-l p-k


    nn-al : NonNeg al
    nn-al = NonNeg-≤ bl al nn-bl (inj-l bl<al)

    p = i-scale-NN (k , nn-k) a
    pl = Iℚ.l p
    pu = Iℚ.u p
    p' = i-scale k a

    p-path : p == p'
    p-path = i-scale-NN-path (k , nn-k) a

    pu-path : pu == bu
    pu-path = r*-assoc bu 1/au au
              >=> (cong (bu r*_) (r1/-inverse au au-inv))
              >=> r*-right-one bu

    pu≤bu : pu ℚ≤ bu
    pu≤bu = subst (pu ℚ≤_) pu-path (refl-ℚ≤ {pu})

    al≤pl : al ℚ≤ pl
    al≤pl = subst (_ℚ≤ pl) (r*-left-one al) (r*₂-preserves-≤ 1r k (al , nn-al) (inj-l 1<k))

    bl≤pl : bl ℚ≤ pl
    bl≤pl = trans-ℚ≤ {bl} {al} {pl} (inj-l bl<al) al≤pl

  np-case : NonPosI b -> Ans
  np-case np-bu = k , p-k , 1<k , subst (_i⊆ b) p-path (i⊆-cons bl≤pl pu≤bu)
    where
    n-al : Neg al
    n-al = Neg-< al bu np-bu (trans-≤-< {al} {au} {bu} al≤au au<bu)

    al-inv : ℚInv al
    al-inv = Neg->Inv n-al

    1/al = (r1/ al al-inv)
    neg-1/al = (r1/-preserves-Neg al al-inv n-al)

    k = bl r* 1/al

    1<k : 1r < k
    1<k = subst (_< k) (r*-commute al 1/al >=> r1/-inverse al al-inv)
                (r*₂-flips-order bl al (1/al , neg-1/al) bl<al)

    n-bl = Neg-≤ bl al n-al (inj-l bl<al)

    p-k = r*₁-flips-sign (bl , n-bl) _ neg-1/al
    nn-k : NonNeg k
    nn-k = inj-l p-k


    np-au : NonPos au
    np-au = NonPos-≤ au bu np-bu (inj-l au<bu)

    p = i-scale-NN (k , nn-k) a
    pl = Iℚ.l p
    pu = Iℚ.u p
    p' = i-scale k a

    p-path : p == p'
    p-path = i-scale-NN-path (k , nn-k) a

    pl-path : pl == bl
    pl-path = r*-assoc bl 1/al al
              >=> (cong (bl r*_) (r1/-inverse al al-inv))
              >=> r*-right-one bl

    bl≤pl : bl ℚ≤ pl
    bl≤pl = subst (_ℚ≤ pl) pl-path (refl-ℚ≤ {pl})

    pu≤au : pu ℚ≤ au
    pu≤au = subst (pu ℚ≤_) (r*-left-one au) (r*₂-flips-≤ 1r k (au , np-au) (inj-l 1<k))

    pu≤bu : pu ℚ≤ bu
    pu≤bu = trans-ℚ≤ {pu} {au} {bu} pu≤au (inj-l au<bu)



  cz-case : StrictCrossZeroI b -> Ans
  cz-case (n-bl , p-bu) = k , p-k , 1<k  , subst (_i⊆ b) p-path (i⊆-cons bl≤pl pu≤bu)
    where
    hbl = 1/2r r* bl
    hbu = 1/2r r* bu

    al' = minℚ al hbl
    au' = maxℚ au hbu

    n-al' : Neg al'
    n-al' = Neg-≤ al' hbl (r*₁-preserves-sign (1/2r , Pos-1/ℕ (2 , _)) _ n-bl) (minℚ-≤-right al hbl)

    p-au' : Pos au'
    p-au' = Pos-≤ hbu au' (r*₁-preserves-sign (1/2r , Pos-1/ℕ (2 , _)) _ p-bu) (maxℚ-≤-right au hbu)

    bl<al' : bl < al'
    bl<al' = minℚ-property {P = bl <_} al hbl bl<al
                           (subst (_< hbl) (r*-left-one bl)
                                  (r*₂-flips-order 1/2r 1r (bl , n-bl) 1/2r<1r))
    au'<bu : au' < bu
    au'<bu = maxℚ-property {P = _< bu} au hbu au<bu
                           (subst (hbu <_) (r*-left-one bu)
                                  (r*₂-preserves-order 1/2r 1r (bu , p-bu) 1/2r<1r))

    al'-inv : ℚInv al'
    al'-inv = Neg->Inv n-al'

    au'-inv : ℚInv au'
    au'-inv = Pos->Inv p-au'

    1/al' = (r1/ al' al'-inv)
    1/au' = (r1/ au' au'-inv)

    kl = bl r* 1/al'
    ku = bu r* 1/au'

    n-1/al' = r1/-preserves-Neg al' al'-inv n-al'
    p-1/au' = r1/-preserves-Pos au' au'-inv p-au'

    p-kl : Pos kl
    p-kl = r*₁-flips-sign (bl , n-bl) _ n-1/al'
    p-ku : Pos ku
    p-ku = r*₁-preserves-sign (bu , p-bu) _ p-1/au'

    1<kl : 1r < kl
    1<kl = subst (_< kl) (r*-commute al' 1/al' >=> r1/-inverse al' al'-inv)
                 (r*₂-flips-order bl al' (1/al' , n-1/al') bl<al')
    1<ku : 1r < ku
    1<ku = subst (_< ku) (r*-commute au' 1/au' >=> r1/-inverse au' au'-inv)
                 (r*₂-preserves-order au' bu (1/au' , p-1/au') au'<bu)

    k = minℚ kl ku

    p-k : Pos k
    p-k = minℚ-property {P = Pos} kl ku p-kl p-ku

    1<k : 1r < k
    1<k = minℚ-property {P = 1r <_} kl ku 1<kl 1<ku

    p = i-scale-NN (k , inj-l p-k) a
    pl = Iℚ.l p
    pu = Iℚ.u p
    p' = i-scale k a

    p-path : p == p'
    p-path = i-scale-NN-path (k , inj-l p-k) a

    l-path : kl r* al' == bl
    l-path = r*-assoc bl 1/al' al'
             >=> (cong (bl r*_) (r1/-inverse al' al'-inv))
             >=> r*-right-one bl

    u-path : ku r* au' == bu
    u-path = r*-assoc bu 1/au' au'
             >=> (cong (bu r*_) (r1/-inverse au' au'-inv))
             >=> r*-right-one bu

    al'≤al : al' ℚ≤ al
    al'≤al = minℚ-≤-left al hbl
    au≤au' : au  ℚ≤ au'
    au≤au' = maxℚ-≤-left au hbu

    k≤kl : k ℚ≤ kl
    k≤kl = minℚ-≤-left kl ku
    k≤ku : k ℚ≤ ku
    k≤ku = minℚ-≤-right kl ku


    bl≤pl : bl ℚ≤ pl
    bl≤pl = subst (_ℚ≤ pl) l-path
                  (trans-ℚ≤ {kl r* al'} {k r* al'} {k r* al}
                            (r*₂-flips-≤ k kl (al' , inj-l n-al') k≤kl)
                            (r*₁-preserves-≤ (k , inj-l p-k) al' al al'≤al))

    pu≤bu : pu ℚ≤ bu
    pu≤bu = subst (pu ℚ≤_) u-path
                  (trans-ℚ≤ {k r* au} {k r* au'} {ku r* au'}
                            (r*₁-preserves-≤ (k , inj-l p-k) au au' au≤au')
                            (r*₂-preserves-≤ k ku (au' , inj-l p-au') k≤ku))

  handle : StrictClass' b -> Ans
  handle (nn-c p) = nn-case p
  handle (np-c p) = np-case p
  handle (cz-c p) = cz-case p
