{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval where

open import additive-group
open import base
open import equality
open import equivalence
open import functions
open import hlevel
open import order
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.minmax
open import rational
open import rational.order
open import rational.proper-interval.classify
open import relation
open import ring
open import ring.implementations.rational
open import semiring
open import sign
open import sign.instances.rational
open import sum

open import rational.proper-interval.base public

_i+_ : Iℚ -> Iℚ -> Iℚ
_i+_ a b = Iℚ-cons (a.l + b.l) (a.u + b.u) abs.lt
  where
  module a = Iℚ a
  module b = Iℚ b
  module abs where
    LT = _≤_
    abstract
      lt : LT (a.l + b.l) (a.u + b.u)
      lt = (+-preserves-≤ a.l≤u b.l≤u)


i-_ : Iℚ -> Iℚ
i-_ a = Iℚ-cons (- a.u) (- a.l) (minus-flips-≤ a.l≤u)
  where
  module a = Iℚ a

i--double-inverse : {a : Iℚ} -> (i- (i- a)) == a
i--double-inverse {Iℚ-cons l u l≤u} = Iℚ-bounds-path minus-double-inverse minus-double-inverse

ℚ->Iℚ : ℚ -> Iℚ
ℚ->Iℚ q = Iℚ-cons q q refl-≤

0i : Iℚ
0i = ℚ->Iℚ 0r

1i : Iℚ
1i = ℚ->Iℚ 1r

i+-commute : (a b : Iℚ) -> a i+ b == b i+ a
i+-commute _ _ = Iℚ-bounds-path +-commute +-commute

i+-assoc : (a b c : Iℚ) -> (a i+ b) i+ c == a i+ (b i+ c)
i+-assoc _ _ _ = Iℚ-bounds-path +-assoc +-assoc

i+-right-zero : (a : Iℚ) -> a i+ 0i == a
i+-right-zero _ = Iℚ-bounds-path +-right-zero +-right-zero

_i∪_ : Iℚ -> Iℚ -> Iℚ
_i∪_ a b = (Iℚ-cons (min a.l b.l) (max a.u b.u) abs.lt)
  where
  module a = Iℚ a
  module b = Iℚ b
  module abs where
    LT = _≤_
    abstract
      lt : LT (min a.l b.l) (max a.u b.u)
      lt = (trans-≤ (trans-≤ min-≤-left a.l≤u) max-≤-left)

i∪-commute : (a b : Iℚ) -> a i∪ b == b i∪ a
i∪-commute a b = Iℚ-bounds-path min-commute max-commute

i∪-assoc : (a b c : Iℚ) -> (a i∪ b) i∪ c == a i∪ (b i∪ c)
i∪-assoc a b c = Iℚ-bounds-path min-assoc max-assoc

i∪-same : (a : Iℚ) -> a i∪ a == a
i∪-same a = Iℚ-bounds-path min-idempotent max-idempotent

i-scale : ℚ -> Iℚ -> Iℚ
i-scale k a =
  Iℚ-cons min' max' abs.lt
  where
  module a = Iℚ a
  min' = min (k * a.l) (k * a.u)
  max' = max (k * a.l) (k * a.u)
  module abs where
    LT = _≤_
    abstract
      lt : LT min' max'
      lt = trans-≤ min-≤-left max-≤-left

i-scale-0≤ : ℚ⁰⁺ -> Iℚ -> Iℚ
i-scale-0≤ (k , 0≤k) a =
  Iℚ-cons (k * a.l) (k * a.u) (*₁-preserves-≤ 0≤k a.l≤u)
   where
   module a = Iℚ a

i-scale-≤0 : ℚ⁰⁻ -> Iℚ -> Iℚ
i-scale-≤0 (k , k≤0) a =
  Iℚ-cons (k * a.u) (k * a.l) (*₁-flips-≤ k≤0 a.l≤u)
   where
   module a = Iℚ a

i-scale-0≤-path : (k : ℚ⁰⁺) -> (a : Iℚ) -> i-scale-0≤ k a == i-scale ⟨ k ⟩ a
i-scale-0≤-path (k , 0≤k) (Iℚ-cons l u l≤u) = Iℚ-bounds-path (sym lp) (sym up)
  where
  kl≤ku : (k * l) ≤ (k * u)
  kl≤ku = (*₁-preserves-≤ 0≤k l≤u)
  lp : min (k * l) (k * u) == k * l
  lp = min-≤-path kl≤ku
  up : max (k * l) (k * u) == k * u
  up = max-≤-path kl≤ku

i-scale-≤0-path : (k : ℚ⁰⁻) -> (a : Iℚ) -> i-scale-≤0 k a == i-scale ⟨ k ⟩ a
i-scale-≤0-path (k , k≤0) (Iℚ-cons l u l≤u) = Iℚ-bounds-path (sym lp) (sym up)
  where
  lp : min (k * l) (k * u) == k * u
  lp = min-≥-path (*₁-flips-≤ k≤0 l≤u)
  up : max (k * l) (k * u) == k * l
  up = max-≥-path (*₁-flips-≤ k≤0 l≤u)


i-scale-1 : (a : Iℚ) -> i-scale 1r a == a
i-scale-1 a = sym (i-scale-0≤-path (1r , weaken-< Pos-1r) a) >=>
              Iℚ-bounds-path *-left-one *-left-one

i-scale-SymI : (k : ℚ) -> (a : Iℚ) -> SymI a -> i-scale (- k) a == i-scale k a
i-scale-SymI k (Iℚ-cons l u l≤u) l=-u =
  Iℚ-bounds-path p1 p2
  where
  -kl=ku = (*-right l=-u >=> minus-extract-both)
  -ku=kl = (minus-extract-left >=>
            sym minus-extract-right >=>
            *-right (sym l=-u))
  p1 : min (- k * l) (- k * u) == min (k * l) (k * u)
  p1 = cong2 min -kl=ku -ku=kl >=> min-commute

  p2 : max (- k * l) (- k * u) == max (k * l) (k * u)
  p2 = cong2 max -kl=ku -ku=kl >=> max-commute



_i*_ : Iℚ -> Iℚ -> Iℚ
_i*_ (Iℚ-cons l1 u1 _) i2 = (i-scale l1 i2) i∪ (i-scale u1 i2)

i*-NN : (a b : Iℚ) -> (NonNegI a) -> (NonNegI b) -> Iℚ
i*-NN a b 0≤al 0≤bl = Iℚ-cons (a.l * b.l) (a.u * b.u) lt
  where
  module a = Iℚ a
  module b = Iℚ b
  opaque
    lt : (a.l * b.l) ≤ (a.u * b.u)
    lt = trans-≤
           (*₁-preserves-≤ 0≤al b.l≤u)
           (*₂-preserves-≤ a.l≤u (trans-≤ 0≤bl b.l≤u))

i*-NN-path : (a b : Iℚ) -> (nn-a : (NonNegI a)) -> (nn-b : (NonNegI b)) ->
             i*-NN a b nn-a nn-b == (a i* b)
i*-NN-path a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) 0≤al 0≤bl =
  Iℚ-bounds-path (sym (min-≤-path (*₂-preserves-≤ al≤au 0≤bl)))
                 (sym (max-≤-path (*₂-preserves-≤ al≤au 0≤bu))) >=>
  cong2 _i∪_ (i-scale-0≤-path (al , 0≤al) b) (i-scale-0≤-path (au , 0≤au) b)
  where
  0≤au = trans-≤ 0≤al al≤au
  0≤bu = trans-≤ 0≤bl bl≤bu

i*-SymI : (a b : Iℚ) -> (SymI a) -> (SymI b) -> Iℚ
i*-SymI a b al=-au bl=-bu = Iℚ-cons (- (a.u * b.u)) (a.u * b.u) abs.lt
  where
  module a = Iℚ a
  module b = Iℚ b
  0≤au : 0# ≤ a.u
  0≤au = convert-≮ au≮0
    where
    au≮0 : a.u ≮ 0#
    au≮0 au<0 = asym-< au<0 (trans-<-≤ 0<al a.l≤u)
      where
      0<al = trans-<-= (minus-flips-<0 au<0) (sym al=-au)

  module abs where
    LT = _≤_
    abstract
      lt : LT (- (a.u * b.u)) (a.u * b.u)
      lt = trans-=-≤ (sym minus-extract-right >=> *-right (sym bl=-bu))
                     (*₁-preserves-≤ 0≤au b.l≤u)

i*-SymI-path : (a b : Iℚ) -> (sym-a : (SymI a)) -> (sym-b : (SymI b)) ->
               i*-SymI a b sym-a sym-b == (a i* b)
i*-SymI-path a@(Iℚ-cons _ _ _) b al=-au bl=-bu = Iℚ-bounds-path (sym p1) (sym p2)
  where
  module a = Iℚ a
  module b = Iℚ b

  0≤au : 0# ≤ a.u
  0≤au = convert-≮ au≮0
    where
    au≮0 : a.u ≮ 0#
    au≮0 au<0 = asym-< au<0 (trans-<-≤ 0<al a.l≤u)
      where
      0<al = trans-<-= (minus-flips-<0 au<0) (sym al=-au)


  p0 : a i* b == i-scale a.u b
  p0 = (cong (_i∪ (i-scale a.u b))
                       ((\ i -> i-scale (al=-au i) b) >=>
                        i-scale-SymI a.u b bl=-bu) >=>
                  i∪-same (i-scale a.u b))

  p15 : Iℚ.l (i-scale a.u b) == a.u * b.l
  p15 = sym (*-distrib-min-left 0≤au) >=>
        *-right (min-≤-path b.l≤u)

  p1 : Iℚ.l ((i-scale a.l b) i∪ (i-scale a.u b)) == - (a.u * b.u)
  p1 = cong Iℚ.l p0 >=> p15 >=> *-right bl=-bu >=> minus-extract-right

  p25 : Iℚ.u (i-scale a.u b) == a.u * b.u
  p25 = sym (*-distrib-max-left 0≤au) >=>
        *-right (max-≤-path b.l≤u)

  p2 : Iℚ.u ((i-scale a.l b) i∪ (i-scale a.u b)) == (a.u * b.u)
  p2 = cong Iℚ.u p0 >=> p25

i*-commute : (a b : Iℚ) -> a i* b == b i* a
i*-commute (Iℚ-cons al au _) (Iℚ-cons bl bu _) = Iℚ-bounds-path l-path u-path
  where
  l-path : min (min (al * bl) (al * bu)) (min (au * bl) (au * bu)) ==
           min (min (bl * al) (bl * au)) (min (bu * al) (bu * au))
  l-path = min-assoc >=>
           cong (min _) (sym min-assoc >=>
                          cong (\x -> min x _) min-commute >=>
                          min-assoc) >=>
           sym min-assoc >=>
           cong2 min (cong2 min *-commute *-commute)
                     (cong2 min *-commute *-commute)
  u-path : max (max (al * bl) (al * bu)) (max (au * bl) (au * bu)) ==
           max (max (bl * al) (bl * au)) (max (bu * al) (bu * au))
  u-path = max-assoc >=>
           cong (max _) (sym max-assoc >=>
                          cong (\x -> max x _) max-commute >=>
                          max-assoc) >=>
           sym max-assoc >=>
           cong2 max (cong2 max *-commute *-commute)
                     (cong2 max *-commute *-commute)

i--scale : (a : Iℚ) -> i- a == i-scale (- 1r) a
i--scale a@(Iℚ-cons l u l≤u) = Iℚ-bounds-path lp up
  where
  mu≤ml : ((- 1r) * u) ≤ ((- 1r) * l)
  mu≤ml = *₁-flips-≤ (weaken-< (r--flips-sign _ pos-sign Pos-1r)) l≤u


  lp : (- u) == min ((- 1r) * l) ((- 1r) * u)
  lp = cong -_ (sym *-left-one) >=>
       sym minus-extract-left >=>
       sym (min-≥-path mu≤ml)
  up : (- l) == max ((- 1r) * l) ((- 1r) * u)
  up = cong -_ (sym *-left-one) >=>
       sym minus-extract-left >=>
       sym (max-≥-path mu≤ml)


i-scale-distrib-∪ : (k : ℚ) (a b : Iℚ) ->
                    i-scale k (a i∪ b) == (i-scale k a) i∪ (i-scale k b)
i-scale-distrib-∪ k a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) = a.path
  where
  module a where
    abstract
      nn-case : 0# ≤ k -> i-scale k (a i∪ b) == (i-scale k a) i∪ (i-scale k b)
      nn-case 0≤k =
        sym (i-scale-0≤-path k⁺ (a i∪ b)) >=>
        Iℚ-bounds-path lp up >=>
        cong2 _i∪_ (i-scale-0≤-path k⁺ a) (i-scale-0≤-path k⁺ b)
        where
        k⁺ : ℚ⁰⁺
        k⁺ = k , 0≤k
        lp : k * (min al bl) == min (k * al) (k * bl)
        lp = *-distrib-min-left 0≤k
        up : k * (max au bu) == max (k * au) (k * bu)
        up = *-distrib-max-left 0≤k

      np-case : k ≤ 0# -> i-scale k (a i∪ b) == (i-scale k a) i∪ (i-scale k b)
      np-case k≤0 =
        sym (i-scale-≤0-path k⁻ (a i∪ b)) >=>
        Iℚ-bounds-path up lp >=>
        cong2 _i∪_ (i-scale-≤0-path k⁻ a) (i-scale-≤0-path k⁻ b)
        where
        k⁻ : ℚ⁰⁻
        k⁻ = k , k≤0
        lp : k * (min al bl) == max (k * al) (k * bl)
        lp = *-distrib-flip-min-left k≤0
        up : k * (max au bu) == min (k * au) (k * bu)
        up = *-distrib-flip-max-left k≤0

      path : i-scale k (a i∪ b) == (i-scale k a) i∪ (i-scale k b)
      path = either (np-case ∘ weaken-<) nn-case (split-< k 0#)

i-scale-twice : (k1 k2 : ℚ) (a : Iℚ) -> i-scale k1 (i-scale k2 a) == i-scale (k1 * k2) a
i-scale-twice k1 k2 a = handle (split-< k1 0#) (split-< k2 0#)
  where
  Ans = i-scale k1 (i-scale k2 a) == i-scale (k1 * k2) a

  nnnn-case : 0# ≤ k1 -> 0# ≤ k2 -> Ans
  nnnn-case 0≤k1 0≤k2 =
    cong (i-scale k1) (sym (i-scale-0≤-path (k2 , 0≤k2) a)) >=>
    sym (i-scale-0≤-path (k1 , 0≤k1) (i-scale-0≤ (k2 , 0≤k2) a)) >=>
    Iℚ-bounds-path (sym *-assoc) (sym *-assoc) >=>
    i-scale-0≤-path (_ , *-preserves-0≤ 0≤k1 0≤k2) a

  nnnp-case : 0# ≤ k1 -> k2 ≤ 0# -> Ans
  nnnp-case 0≤k1 k2≤0 =
    cong (i-scale k1) (sym (i-scale-≤0-path (k2 , k2≤0) a)) >=>
    sym (i-scale-0≤-path (k1 , 0≤k1) (i-scale-≤0 (k2 , k2≤0) a)) >=>
    Iℚ-bounds-path (sym *-assoc) (sym *-assoc) >=>
    i-scale-≤0-path (_ , *₁-preserves-≤0 0≤k1 k2≤0) a

  npnn-case : k1 ≤ 0# -> 0# ≤ k2 -> Ans
  npnn-case k1≤0 0≤k2 =
    cong (i-scale k1) (sym (i-scale-0≤-path (k2 , 0≤k2) a)) >=>
    sym (i-scale-≤0-path (k1 , k1≤0) (i-scale-0≤ (k2 , 0≤k2) a)) >=>
    Iℚ-bounds-path (sym *-assoc) (sym *-assoc) >=>
    i-scale-≤0-path (_ , *₂-preserves-≤0 k1≤0 0≤k2) a

  npnp-case : k1 ≤ 0# -> k2 ≤ 0# -> Ans
  npnp-case k1≤0 k2≤0 =
    cong (i-scale k1) (sym (i-scale-≤0-path (k2 , k2≤0) a)) >=>
    sym (i-scale-≤0-path (k1 , k1≤0) (i-scale-≤0 (k2 , k2≤0) a)) >=>
    Iℚ-bounds-path (sym *-assoc) (sym *-assoc) >=>
    i-scale-0≤-path (_ , *-flips-≤0 k1≤0 k2≤0) a

  handle : (k1 < 0# ⊎ 0# ≤ k1) -> (k2 < 0# ⊎ 0# ≤ k2) -> Ans
  handle (inj-l k1<0) (inj-l k2<0) = npnp-case (weaken-< k1<0) (weaken-< k2<0)
  handle (inj-l k1<0) (inj-r 0≤k2) = npnn-case (weaken-< k1<0) 0≤k2
  handle (inj-r 0≤k1) (inj-l k2<0) = nnnp-case 0≤k1 (weaken-< k2<0)
  handle (inj-r 0≤k1) (inj-r 0≤k2) = nnnn-case 0≤k1 0≤k2


i-scale-distrib-i+ : (k : ℚ) (a b : Iℚ) -> i-scale k (a i+ b) == i-scale k a i+ i-scale k b
i-scale-distrib-i+ k a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) =
  either (np-case ∘ weaken-<) nn-case (split-< k 0#)
  where
  nn-case : 0# ≤ k -> i-scale k (a i+ b) == (i-scale k a) i+ (i-scale k b)
  nn-case 0≤k =
    sym (i-scale-0≤-path k⁺ (a i+ b)) >=>
    Iℚ-bounds-path *-distrib-+-left *-distrib-+-left >=>
    cong2 _i+_ (i-scale-0≤-path k⁺ a) (i-scale-0≤-path k⁺ b)
    where
    k⁺ : ℚ⁰⁺
    k⁺ = k , 0≤k

  np-case : k ≤ 0# -> i-scale k (a i+ b) == (i-scale k a) i+ (i-scale k b)
  np-case k≤0 =
    sym (i-scale-≤0-path k⁻ (a i+ b)) >=>
    Iℚ-bounds-path *-distrib-+-left *-distrib-+-left >=>
    cong2 _i+_ (i-scale-≤0-path k⁻ a) (i-scale-≤0-path k⁻ b)
    where
    k⁻ : ℚ⁰⁻
    k⁻ = k , k≤0


i-scale-i*₂ : (k : ℚ) (a b : Iℚ) -> i-scale k (a i* b) == a i* (i-scale k b)
i-scale-i*₂ k a@(Iℚ-cons al au al≤au) b =
  i-scale-distrib-∪ k (i-scale al b) (i-scale au b) >=>
  cong2 _i∪_ (i-scale-twice k al b >=>
              (cong (\x -> i-scale x b) *-commute) >=>
              sym (i-scale-twice al k b))
             (i-scale-twice k au b >=>
              (cong (\x -> i-scale x b) *-commute) >=>
              sym (i-scale-twice au k b))

i--extract-right : (a b : Iℚ) -> a i* (i- b) == i- (a i* b)
i--extract-right a b =
  cong (a i*_) (i--scale b) >=>
  sym (i-scale-i*₂ (- 1r) a b) >=>
  sym (i--scale (a i* b))

i--extract-left : (a b : Iℚ) -> (i- a) i* b == i- (a i* b)
i--extract-left a b =
  i*-commute (i- a) b >=> (i--extract-right b a) >=> cong i-_ (i*-commute b a)

i--extract-both : (a b : Iℚ) -> (i- a) i* (i- b) == (a i* b)
i--extract-both a b = i--extract-left a (i- b) >=> cong i-_ (i--extract-right a b) >=>
                      i--double-inverse


i-Lower : Iℚ -> Pred ℚ ℓ-zero
i-Lower a q = q ≤ (Iℚ.l a)

i-Upper : Iℚ -> Pred ℚ ℓ-zero
i-Upper a q = (Iℚ.u a) ≤ q

i∪-Lower : {q : ℚ} -> (a b : Iℚ) -> i-Lower a q -> i-Lower b q -> i-Lower (a i∪ b) q
i∪-Lower {q} a b q≤al q≤bl = min-property {P = q ≤_} (Iℚ.l a) (Iℚ.l b) q≤al q≤bl

i∪-Upper : {q : ℚ} -> (a b : Iℚ) -> i-Upper a q -> i-Upper b q -> i-Upper (a i∪ b) q
i∪-Upper {q} a b au≤q bu≤q = max-property {P = _≤ q} (Iℚ.u a) (Iℚ.u b) au≤q bu≤q

LowerUpper->Constant : {q : ℚ} -> (a : Iℚ) -> i-Lower a q -> i-Upper a q -> ConstantI a
LowerUpper->Constant {q} (Iℚ-cons l u l≤u) q≤l u≤q = antisym-≤ l≤u (trans-≤ u≤q q≤l)

i-width : Iℚ -> ℚ
i-width (Iℚ-cons l u _) = diff l u

0≤i-width : (a : Iℚ) -> 0# ≤ (i-width a)
0≤i-width (Iℚ-cons l u l≤u) = diff-0≤⁺ l≤u

i-scale-width : (k : ℚ) (a : Iℚ) -> i-width (i-scale k a) == abs k * (i-width a)
i-scale-width k a@(Iℚ-cons l u l≤u) =
  either (np-case ∘ weaken-<) nn-case (split-< k 0#)
  where
  nn-case : 0# ≤ k -> i-width (i-scale k a) == abs k * (i-width a)
  nn-case 0≤k =
    cong2 diff (min-≤-path kl≤ku) (max-≤-path kl≤ku) >=>
    sym *-distrib-diff-left >=>
    cong (_* (diff l u)) (sym (abs-0≤-path 0≤k))

    where
    kl≤ku : (k * l) ≤ (k * u)
    kl≤ku = *₁-preserves-≤ 0≤k l≤u

  np-case : k ≤ 0# -> i-width (i-scale k a) == abs k * (i-width a)
  np-case k≤0 =
    cong2 diff (min-≥-path ku≤kl) (max-≥-path ku≤kl) >=>
    sym *-distrib-diff-left >=>
    sym minus-double-inverse >=>
    cong -_ (sym minus-extract-right) >=>
    (sym minus-extract-left) >=>
    cong2 _*_ (sym (abs-≤0-path k≤0))
              (sym diff-anticommute)

    where
    ku≤kl : (k * u) ≤ (k * l)
    ku≤kl = *₁-flips-≤ k≤0 l≤u

i∪₁-width-≤ : (a b : Iℚ) -> i-width a ≤ i-width (a i∪ b)
i∪₁-width-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) =
  +-preserves-≤ lt1 lt2
  where
  lt1 : au ≤ (max au bu)
  lt1 = max-≤-left
  lt2 : (- al) ≤ (- (min al bl))
  lt2 = minus-flips-≤ min-≤-left

i∪₂-width-≤ : (a b : Iℚ) -> i-width b ≤ i-width (a i∪ b)
i∪₂-width-≤ a b = trans-≤-= (i∪₁-width-≤ b a) (cong i-width (i∪-commute b a))

i-maxabs : Iℚ -> ℚ
i-maxabs a = max (- (Iℚ.l a)) (Iℚ.u a)

i-maxabs' : Iℚ -> ℚ
i-maxabs' a = max (abs (Iℚ.l a)) (abs (Iℚ.u a))

i-maxabs'-path : (a : Iℚ) -> i-maxabs' a == i-maxabs a
i-maxabs'-path (Iℚ-cons l u l≤u) =
  max-swap >=> max-commute >=> cong2 max (max-≥-path (minus-flips-≤ l≤u)) (max-≤-path l≤u)



i-maxabs-NonNeg : (a : Iℚ) -> NonNegI a -> i-maxabs a == Iℚ.u a
i-maxabs-NonNeg (Iℚ-cons l u l≤u) 0≤l =
  max-≤-path (trans-≤ (trans-≤ (minus-flips-0≤ 0≤l) 0≤l) l≤u)

i-maxabs-NonPos : (a : Iℚ) -> NonPosI a -> i-maxabs a == (- (Iℚ.l a))
i-maxabs-NonPos (Iℚ-cons l u l≤u) u≤0 =
  max-≥-path (trans-≤ (trans-≤ u≤0 (minus-flips-≤0 u≤0)) (minus-flips-≤ l≤u))

i-maxabs-CrossZero : (a : Iℚ) -> CrossZeroI a -> i-maxabs a ≤ i-width a
i-maxabs-CrossZero a@(Iℚ-cons l u l≤u) (l≤0 , 0≤u) =
  max-property {P = (_≤ w)} (- l) u l-lt u-lt
  where
  m = i-maxabs a
  w = i-width a

  l-lt : (- l) ≤ w
  l-lt = trans-=-≤ (sym +-left-zero) (+₂-preserves-≤ 0≤u)

  u-lt : u ≤ w
  u-lt = trans-=-≤ (sym +-right-zero) (+₁-preserves-≤ (minus-flips-≤0 l≤0))


i-maxabs-Zero : (a : Iℚ) -> Zero (i-maxabs a) -> a == 0i
i-maxabs-Zero a@(Iℚ-cons al au al≤au) zm = Iℚ-bounds-path zl zu
  where
  0≤al : 0# ≤ al
  0≤al = trans-≤-= (minus-flips-≤0 (trans-≤-= max-≤-left zm)) minus-double-inverse

  au≤0 : au ≤ 0#
  au≤0 = trans-≤-= max-≤-right zm

  zl : al == 0r
  zl = antisym-≤ (trans-≤ al≤au au≤0) 0≤al
  zu : au == 0r
  zu = antisym-≤ au≤0 (trans-≤ 0≤al al≤au)



0≤i-maxabs : (a : Iℚ) -> 0# ≤ (i-maxabs a)
0≤i-maxabs a@(Iℚ-cons l u _) =
  trans-≤-=
    (max-property {P = 0# ≤_} (abs l) (abs u) abs-0≤ abs-0≤)
    (i-maxabs'-path  a)

i-width-bound : (a : Iℚ) -> i-width a ≤ (2r * (i-maxabs a))
i-width-bound a@(Iℚ-cons l u l≤u) =
  subst2 _≤_ diff-trans (2r-path (i-maxabs a)) lt1
  where
  dl≤maxabs : diff l 0# ≤ i-maxabs a
  dl≤maxabs = trans-=-≤ +-left-zero max-≤-left
  du≤maxabs : diff 0# u ≤ i-maxabs a
  du≤maxabs = trans-=-≤ (+-right minus-zero >=> +-right-zero) max-≤-right


  lt1 : (diff l 0r + diff 0r u) ≤ (i-maxabs a + i-maxabs a)
  lt1 = +-preserves-≤ dl≤maxabs du≤maxabs


i*-width-NNNN : (a b : Iℚ) -> NonNegI a -> NonNegI b ->
                i-width (a i* b) ==
                (i-width a * (Iℚ.l b)) + (Iℚ.u a * (i-width b))
i*-width-NNNN a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) 0≤al 0≤bl =
  wp2 >=> delta-p
  where
  0≤au : 0# ≤ au
  0≤au = trans-≤ 0≤al al≤au
  0≤bu : 0# ≤ bu
  0≤bu = trans-≤ 0≤bl bl≤bu
  wa = i-width a
  wb = i-width b

  albl≤albu : (al * bl) ≤ (al * bu)
  albl≤albu = *₁-preserves-≤ 0≤al bl≤bu
  aubl≤aubu : (au * bl) ≤ (au * bu)
  aubl≤aubu = *₁-preserves-≤ 0≤au bl≤bu

  albl≤aubl : (al * bl) ≤ (au * bl)
  albl≤aubl = *₂-preserves-≤ al≤au 0≤bl
  albu≤aubu : (al * bu) ≤ (au * bu)
  albu≤aubu = *₂-preserves-≤ al≤au 0≤bu

  i1 = i-scale al b
  i1lp : Iℚ.l i1 == al * bl
  i1lp = min-≤-path albl≤albu
  i1up : Iℚ.u i1 == al * bu
  i1up = max-≤-path albl≤albu
  i2 = i-scale au b
  i2lp : Iℚ.l i2 == au * bl
  i2lp = min-≤-path aubl≤aubu
  i2up : Iℚ.u i2 == au * bu
  i2up = max-≤-path aubl≤aubu


  l = Iℚ.l (a i* b)
  lp : l == al * bl
  lp = cong2 min i1lp i2lp >=> min-≤-path albl≤aubl

  u = Iℚ.u (a i* b)
  up : u == au * bu
  up = cong2 max i1up i2up >=> max-≤-path albu≤aubu

  wp : i-width (a i* b) == (au * bu) + (- (al * bl))
  wp = cong2 diff lp up

  delta = ((wa * bl) + ((al * wb) + (wa * wb)))

  abup : (au * bu) == delta + (al * bl)
  abup = *-cong (sym diff-step) (sym diff-step) >=>
         *-distrib-+-left >=>
         +-cong *-distrib-+-right *-distrib-+-right >=>
         +-assoc >=>
         +-commute

  wp2 : i-width (a i* b) == delta
  wp2 = wp >=> (+-left abup) >=>
        +-assoc >=>
        +-right +-inverse >=>
        +-right-zero

  delta-p : delta == (wa * bl) + (au * wb)
  delta-p =
    cong ((wa * bl) +_) (sym *-distrib-+-right >=>
                         cong (_* wb) diff-step)



i*-width-NNNP : (a b : Iℚ) -> NonNegI a -> NonPosI b ->
                i-width (a i* b) ==
                (i-width a * (- (Iℚ.l b))) + (Iℚ.l a * (i-width b))
i*-width-NNNP a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) 0≤al bu≤0 =
  wp >=> path
  where
  0≤au : 0# ≤ au
  0≤au = trans-≤ 0≤al al≤au
  bl≤0 : bl ≤ 0#
  bl≤0 = trans-≤ bl≤bu bu≤0

  wa = i-width a
  wb = i-width b

  albl≤albu : (al * bl) ≤ (al * bu)
  albl≤albu = *₁-preserves-≤ 0≤al bl≤bu
  aubl≤aubu : (au * bl) ≤ (au * bu)
  aubl≤aubu = *₁-preserves-≤ 0≤au bl≤bu

  aubl≤albl : (au * bl) ≤ (al * bl)
  aubl≤albl = *₂-flips-≤ al≤au bl≤0
  aubu≤albu : (au * bu) ≤ (al * bu)
  aubu≤albu = *₂-flips-≤ al≤au bu≤0

  i1 = i-scale al b
  i1lp : Iℚ.l i1 == al * bl
  i1lp = min-≤-path albl≤albu
  i1up : Iℚ.u i1 == al * bu
  i1up = max-≤-path albl≤albu
  i2 = i-scale au b
  i2lp : Iℚ.l i2 == au * bl
  i2lp = min-≤-path aubl≤aubu
  i2up : Iℚ.u i2 == au * bu
  i2up = max-≤-path aubl≤aubu


  l = Iℚ.l (a i* b)
  lp : l == au * bl
  lp = cong2 min i1lp i2lp >=> min-≥-path aubl≤albl

  u = Iℚ.u (a i* b)
  up : u == al * bu
  up = cong2 max i1up i2up >=> max-≥-path aubu≤albu

  wp : i-width (a i* b) == (al * bu) + (- (au * bl))
  wp = cong2 diff lp up

  path : (al * bu) + (- (au * bl)) == (wa * (- bl)) + (al * wb)
  path = +-cong (*-right (sym diff-step) >=>
                 *-distrib-+-left >=>
                 +-commute)
                (sym minus-extract-right >=>
                 *-left (sym diff-step) >=>
                 *-distrib-+-right) >=>
         +-assoc >=>
         +-right (sym +-assoc >=>
                  +-left (+-right minus-extract-right >=> +-inverse) >=>
                  +-left-zero) >=>
         +-commute

i*-width-NNCZ : (a b : Iℚ) -> NonNegI a -> CrossZeroI b ->
                i-width (a i* b) == (Iℚ.u a * (i-width b))
i*-width-NNCZ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) 0≤al (bl≤0 , 0≤bu) = wp
  where
  0≤au : 0# ≤ au
  0≤au = trans-≤ 0≤al al≤au

  wa = i-width a
  wb = i-width b

  albl≤albu : (al * bl) ≤ (al * bu)
  albl≤albu = *₁-preserves-≤ 0≤al bl≤bu
  aubl≤aubu : (au * bl) ≤ (au * bu)
  aubl≤aubu = *₁-preserves-≤ 0≤au bl≤bu

  aubl≤albl : (au * bl) ≤ (al * bl)
  aubl≤albl = *₂-flips-≤ al≤au bl≤0
  albu≤aubu : (al * bu) ≤ (au * bu)
  albu≤aubu = *₂-preserves-≤ al≤au 0≤bu

  i1 = i-scale al b
  i1lp : Iℚ.l i1 == al * bl
  i1lp = min-≤-path albl≤albu
  i1up : Iℚ.u i1 == al * bu
  i1up = max-≤-path albl≤albu
  i2 = i-scale au b
  i2lp : Iℚ.l i2 == au * bl
  i2lp = min-≤-path aubl≤aubu
  i2up : Iℚ.u i2 == au * bu
  i2up = max-≤-path aubl≤aubu


  l = Iℚ.l (a i* b)
  lp : l == au * bl
  lp = cong2 min i1lp i2lp >=> min-≥-path aubl≤albl

  u = Iℚ.u (a i* b)
  up : u == au * bu
  up = cong2 max i1up i2up >=> max-≤-path albu≤aubu

  wp : i-width (a i* b) == au * (diff bl bu)
  wp = cong2 diff lp up >=> sym *-distrib-diff-left


i*-width-NPNP : (a b : Iℚ) -> NonPosI a -> NonPosI b ->
                i-width (a i* b) ==
                (i-width a * (- (Iℚ.l b))) + ((- (Iℚ.u a)) * (i-width b))
i*-width-NPNP a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) au≤0 bu≤0 =
  wp2 >=> delta-p
  where
  al≤0 : al ≤ 0#
  al≤0 = trans-≤ al≤au au≤0
  bl≤0 : bl ≤ 0#
  bl≤0 = trans-≤ bl≤bu bu≤0

  wa = i-width a
  wb = i-width b

  albu≤albl : (al * bu) ≤ (al * bl)
  albu≤albl = *₁-flips-≤ al≤0 bl≤bu
  aubu≤aubl : (au * bu) ≤ (au * bl)
  aubu≤aubl = *₁-flips-≤ au≤0 bl≤bu

  aubl≤albl : (au * bl) ≤ (al * bl)
  aubl≤albl = *₂-flips-≤ al≤au bl≤0
  aubu≤albu : (au * bu) ≤ (al * bu)
  aubu≤albu = *₂-flips-≤ al≤au bu≤0

  i1 = i-scale al b
  i1lp : Iℚ.l i1 == al * bu
  i1lp = min-≥-path albu≤albl
  i1up : Iℚ.u i1 == al * bl
  i1up = max-≥-path albu≤albl
  i2 = i-scale au b
  i2lp : Iℚ.l i2 == au * bu
  i2lp = min-≥-path aubu≤aubl
  i2up : Iℚ.u i2 == au * bl
  i2up = max-≥-path aubu≤aubl


  l = Iℚ.l (a i* b)
  lp : l == au * bu
  lp = cong2 min i1lp i2lp >=> min-≥-path aubu≤albu

  u = Iℚ.u (a i* b)
  up : u == al * bl
  up = cong2 max i1up i2up >=> max-≥-path aubl≤albl

  wp : i-width (a i* b) == (al * bl) + (- (au * bu))
  wp = cong2 diff lp up

  delta = ((wa * bl) + ((al * wb) + (wa * wb)))

  abup : (au * bu) == (al * bl) + delta
  abup = *-cong (sym diff-step) (sym diff-step) >=>
         *-distrib-+-left >=>
         +-cong *-distrib-+-right *-distrib-+-right >=>
         +-assoc

  wp2 : i-width (a i* b) == (- delta)
  wp2 = wp >=> (+-right (cong -_ abup >=> minus-distrib-plus)) >=>
        sym +-assoc >=>
        +-left +-inverse >=>
        +-left-zero

  delta-p : (- delta) == (wa * (- bl)) + ((- au) * wb)
  delta-p =
    cong -_ (+-right (sym *-distrib-+-right >=> cong (_* wb) diff-step)) >=>
    minus-distrib-plus >=>
    +-cong (sym minus-extract-right) (sym minus-extract-left)

i*-width-NPCZ : (a b : Iℚ) -> NonPosI a -> CrossZeroI b ->
                i-width (a i* b) == (- (Iℚ.l a)) * (i-width b)
i*-width-NPCZ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) au≤0 (bl≤0 , 0≤bu) = wp
  where
  al≤0 : al ≤ 0#
  al≤0 = trans-≤ al≤au au≤0

  wa = i-width a
  wb = i-width b

  albu≤albl : (al * bu) ≤ (al * bl)
  albu≤albl = *₁-flips-≤ al≤0 bl≤bu
  aubu≤aubl : (au * bu) ≤ (au * bl)
  aubu≤aubl = *₁-flips-≤ au≤0 bl≤bu

  aubl≤albl : (au * bl) ≤ (al * bl)
  aubl≤albl = *₂-flips-≤ al≤au bl≤0
  albu≤aubu : (al * bu) ≤ (au * bu)
  albu≤aubu = *₂-preserves-≤ al≤au 0≤bu

  i1 = i-scale al b
  i1lp : Iℚ.l i1 == al * bu
  i1lp = min-≥-path albu≤albl
  i1up : Iℚ.u i1 == al * bl
  i1up = max-≥-path albu≤albl
  i2 = i-scale au b
  i2lp : Iℚ.l i2 == au * bu
  i2lp = min-≥-path aubu≤aubl
  i2up : Iℚ.u i2 == au * bl
  i2up = max-≥-path aubu≤aubl


  l = Iℚ.l (a i* b)
  lp : l == al * bu
  lp = cong2 min i1lp i2lp >=> min-≤-path albu≤aubu

  u = Iℚ.u (a i* b)
  up : u == al * bl
  up = cong2 max i1up i2up >=> max-≥-path aubl≤albl

  wp : i-width (a i* b) == (- al) * wb
  wp = cong2 diff lp up >=> sym *-distrib-diff-left >=>
       cong (al *_) diff-anticommute >=>
       minus-extract-right >=>
       sym minus-extract-left


i*-width-CZCZ-≤ : (a b : Iℚ) -> CrossZeroI a -> CrossZeroI b ->
                  (i-width (a i* b)) ≤ (((i-width a) * (i-maxabs b)) + ((i-maxabs a) * (i-width b)))
i*-width-CZCZ-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) (al≤0 , 0≤au) (bl≤0 , 0≤bu) =
  d≤wmmw
  where
  wa = i-width a
  wb = i-width b
  ma = i-maxabs a
  mb = i-maxabs b

  0≤wa : 0# ≤ wa
  0≤wa = 0≤i-width a
  0≤wb : 0# ≤ wb
  0≤wb = 0≤i-width b
  0≤ma : 0# ≤ ma
  0≤ma = 0≤i-maxabs a
  0≤mb : 0# ≤ mb
  0≤mb = 0≤i-maxabs b

  ma≤wa : ma ≤ wa
  ma≤wa = i-maxabs-CrossZero a (al≤0 , 0≤au)
  mb≤wb : mb ≤ wb
  mb≤wb = i-maxabs-CrossZero b (bl≤0 , 0≤bu)

  albu≤albl : (al * bu) ≤ (al * bl)
  albu≤albl = *₁-flips-≤ al≤0 bl≤bu
  aubl≤aubu : (au * bl) ≤ (au * bu)
  aubl≤aubu = *₁-preserves-≤ 0≤au bl≤bu

  aubl≤albl : (au * bl) ≤ (al * bl)
  aubl≤albl = *₂-flips-≤ al≤au bl≤0
  albu≤aubu : (al * bu) ≤ (au * bu)
  albu≤aubu = *₂-preserves-≤ al≤au 0≤bu

  i1 = i-scale al b
  i1lp : Iℚ.l i1 == al * bu
  i1lp = min-≥-path albu≤albl
  i1up : Iℚ.u i1 == al * bl
  i1up = max-≥-path albu≤albl
  i2 = i-scale au b
  i2lp : Iℚ.l i2 == au * bl
  i2lp = min-≤-path aubl≤aubu
  i2up : Iℚ.u i2 == au * bu
  i2up = max-≤-path aubl≤aubu

  mal≤m : (- al) ≤ ma
  mal≤m = max-≤-left

  mbl≤m : (- bl) ≤ mb
  mbl≤m = max-≤-left

  m≤al : (- ma) ≤ al
  m≤al = trans-≤-= (minus-flips-≤ mal≤m) minus-double-inverse

  m≤bl : (- mb) ≤ bl
  m≤bl = trans-≤-= (minus-flips-≤ mbl≤m) minus-double-inverse

  au≤m : au ≤ ma
  au≤m = max-≤-right

  bu≤m : bu ≤ mb
  bu≤m = max-≤-right

  mm≤albu : (- (ma * mb)) ≤ (al * bu)
  mm≤albu =
    trans-=-≤ (sym minus-extract-left)
      (trans-≤ (*₂-preserves-≤ m≤al 0≤mb)
               (*₁-flips-≤ al≤0 bu≤m))

  mm≤aubl : (- (ma * mb)) ≤ (au * bl)
  mm≤aubl =
    trans-=-≤ (sym minus-extract-right)
      (trans-≤ (*₁-preserves-≤ 0≤ma m≤bl)
               (*₂-flips-≤ au≤m bl≤0))

  albl≤mm : (al * bl) ≤ (ma * mb)
  albl≤mm =
    trans-≤-=
      (trans-≤ (*₂-flips-≤ m≤al bl≤0)
               (*₁-flips-≤ (minus-flips-0≤ 0≤ma) m≤bl))
      minus-extract-both

  aubu≤mm : (au * bu) ≤ (ma * mb)
  aubu≤mm = trans-≤ (*₂-preserves-≤ au≤m 0≤bu) (*₁-preserves-≤ 0≤ma bu≤m)


  l = Iℚ.l (a i* b)
  lp : l == min (al * bu) (au * bl)
  lp = cong2 min i1lp i2lp

  mm≤l : (- (ma * mb)) ≤ l
  mm≤l = trans-≤-= (min-property {P = ((- (ma * mb)) ≤_)} (al * bu) (au * bl) mm≤albu mm≤aubl)
                   (sym lp)

  ml≤mm : (- l) ≤ (ma * mb)
  ml≤mm = trans-≤-= (minus-flips-≤ mm≤l) minus-double-inverse


  u = Iℚ.u (a i* b)
  up : u == max (al * bl) (au * bu)
  up = cong2 max i1up i2up

  u≤mm : u ≤ (ma * mb)
  u≤mm = trans-=-≤ up (max-property {P = (_≤ (ma * mb))} (al * bl) (au * bu) albl≤mm aubu≤mm)

  mm≤wm : (ma * mb) ≤ (wa * mb)
  mm≤wm = *₂-preserves-≤ ma≤wa 0≤mb

  mm≤mw : (ma * mb) ≤ (ma * wb)
  mm≤mw = *₁-preserves-≤ 0≤ma mb≤wb

  d≤wmmw : (diff l u) ≤ ((wa * mb) + (ma * wb))
  d≤wmmw = +-preserves-≤ (trans-≤ u≤mm mm≤wm) (trans-≤ ml≤mm mm≤mw)


i*-width-NNNN-≤ : (a b : Iℚ) -> NonNegI a -> NonNegI b ->
                  (i-width (a i* b)) ≤ (((i-width a) * (i-maxabs b)) + ((i-maxabs a) * (i-width b)))
i*-width-NNNN-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) 0≤al 0≤bl =
  subst2 _≤_ (sym (i*-width-NNNN a b 0≤al 0≤bl)) p lt

  where
  wa = i-width a
  wb = i-width b

  0≤wa : 0# ≤ wa
  0≤wa = 0≤i-width a

  lt : ((wa * bl) + (au * wb)) ≤ ((wa * bu) + (au * wb))
  lt = +₂-preserves-≤ (*₁-preserves-≤ 0≤wa bl≤bu)

  p : ((wa * bu) + (au * wb)) == ((wa * (i-maxabs b)) + ((i-maxabs a) * wb))
  p i = (wa * (i-maxabs-NonNeg b 0≤bl (~ i))) + ((i-maxabs-NonNeg a 0≤al (~ i)) * wb)


i*-width-NNNP-≤ : (a b : Iℚ) -> NonNegI a -> NonPosI b ->
                  (i-width (a i* b)) ≤ (((i-width a) * (i-maxabs b)) + ((i-maxabs a) * (i-width b)))
i*-width-NNNP-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) 0≤al bu≤0 =
  subst2 _≤_ (sym (i*-width-NNNP a b 0≤al bu≤0)) p lt
  where
  wa = i-width a
  wb = i-width b

  0≤wb : 0# ≤ wb
  0≤wb = 0≤i-width b

  lt : ((wa * (- bl)) + (al * wb)) ≤ ((wa * (- bl)) + (au * wb))
  lt = +₁-preserves-≤ (*₂-preserves-≤ al≤au 0≤wb)

  p : ((wa * (- bl)) + (au * wb)) == ((wa * (i-maxabs b)) + ((i-maxabs a) * wb))
  p i = (wa * (i-maxabs-NonPos b bu≤0 (~ i))) + ((i-maxabs-NonNeg a 0≤al (~ i)) * wb)


i*-width-NPNN-≤ : (a b : Iℚ) -> NonPosI a -> NonNegI b ->
                  (i-width (a i* b)) ≤ (((i-width a) * (i-maxabs b)) + ((i-maxabs a) * (i-width b)))
i*-width-NPNN-≤ a b a≤0 0≤b =
  subst2 _≤_ (cong i-width (i*-commute b a))
             (+-cong *-commute *-commute >=> +-commute)
         (i*-width-NNNP-≤ b a 0≤b a≤0)


i*-width-NPNP-≤ : (a b : Iℚ) -> NonPosI a -> NonPosI b ->
                  (i-width (a i* b)) ≤ (((i-width a) * (i-maxabs b)) + ((i-maxabs a) * (i-width b)))
i*-width-NPNP-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) au≤0 bu≤0 =
  subst2 _≤_ (sym (i*-width-NPNP a b au≤0 bu≤0)) p lt
  where
  wa = i-width a
  wb = i-width b

  0≤wb : 0# ≤ wb
  0≤wb = 0≤i-width b

  lt : ((wa * (- bl)) + ((- au) * wb)) ≤ ((wa * (- bl)) + ((- al) * wb))
  lt = +₁-preserves-≤ (*₂-preserves-≤ (minus-flips-≤ al≤au) 0≤wb)

  p : ((wa * (- bl)) + ((- al) * wb)) == ((wa * (i-maxabs b)) + ((i-maxabs a) * wb))
  p i = (wa * (i-maxabs-NonPos b bu≤0 (~ i))) + ((i-maxabs-NonPos a au≤0 (~ i)) * wb)


i*-width-NNCZ-≤ : (a b : Iℚ) -> NonNegI a -> CrossZeroI b ->
                  (i-width (a i* b)) ≤ (((i-width a) * (i-maxabs b)) + ((i-maxabs a) * (i-width b)))
i*-width-NNCZ-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) 0≤al (bl≤0 , 0≤bu) =
  subst2 _≤_ (sym (i*-width-NNCZ a b 0≤al (bl≤0 , 0≤bu))) p lt
  where
  wa = i-width a
  wb = i-width b
  ma = i-maxabs a
  mb = i-maxabs b

  0≤wa : 0# ≤ wa
  0≤wa = 0≤i-width a
  0≤mb : 0# ≤ mb
  0≤mb = 0≤i-maxabs b

  lt : (au * wb) ≤ ((wa * mb) + (au * wb))
  lt = trans-=-≤ (sym +-left-zero) (+₂-preserves-≤ (*-preserves-0≤ 0≤wa 0≤mb))

  p : ((wa * mb) + (au * wb)) == ((wa * mb) + (ma * wb))
  p i = (wa * mb) + ((i-maxabs-NonNeg a 0≤al (~ i)) * wb)


i*-width-CZNN-≤ : (a b : Iℚ) -> CrossZeroI a -> NonNegI b ->
                  (i-width (a i* b)) ≤ (((i-width a) * (i-maxabs b)) + ((i-maxabs a) * (i-width b)))
i*-width-CZNN-≤ a b cz-a nn-b =
  subst2 _≤_ (cong i-width (i*-commute b a))
             (+-cong *-commute *-commute >=> +-commute)
         (i*-width-NNCZ-≤ b a nn-b cz-a)

i*-width-NPCZ-≤ : (a b : Iℚ) -> NonPosI a -> CrossZeroI b ->
                  (i-width (a i* b)) ≤ (((i-width a) * (i-maxabs b)) + ((i-maxabs a) * (i-width b)))
i*-width-NPCZ-≤ a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) au≤0 (bl≤0 , 0≤bu) =
  subst2 _≤_ (sym (i*-width-NPCZ a b au≤0 (bl≤0 , 0≤bu))) p lt
  where
  wa = i-width a
  wb = i-width b
  ma = i-maxabs a
  mb = i-maxabs b

  0≤wa : 0# ≤ wa
  0≤wa = 0≤i-width a
  0≤mb : 0# ≤ mb
  0≤mb = 0≤i-maxabs b

  lt : ((- al) * wb) ≤ ((wa * mb) + ((- al) * wb))
  lt = trans-=-≤ (sym +-left-zero) (+₂-preserves-≤ (*-preserves-0≤ 0≤wa 0≤mb))

  p : ((wa * mb) + ((- al) * wb)) == ((wa * mb) + (ma * wb))
  p i = (wa * mb) + ((i-maxabs-NonPos a au≤0 (~ i)) * wb)


i*-width-CZNP-≤ : (a b : Iℚ) -> CrossZeroI a -> NonPosI b ->
                  (i-width (a i* b)) ≤ (((i-width a) * (i-maxabs b)) + ((i-maxabs a) * (i-width b)))
i*-width-CZNP-≤ a b cz-a np-b =
  subst2 _≤_ (cong i-width (i*-commute b a))
             (+-cong *-commute *-commute >=> +-commute)
         (i*-width-NPCZ-≤ b a np-b cz-a)



i*-width-≤ : (a b : Iℚ) ->
             (i-width (a i* b)) ≤ (((i-width a) * (i-maxabs b)) + ((i-maxabs a) * (i-width b)))
i*-width-≤ a b = handle (classify a) (classify b)
  where
  handle : Class a -> Class b ->
           (i-width (a i* b)) ≤ (((i-width a) * (i-maxabs b)) + ((i-maxabs a) * (i-width b)))
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
Constant->zero-width (Iℚ-cons _ _ _) p = (+-left (sym p)) >=> +-inverse

zero-width->Constant : (a : Iℚ) -> i-width a == 0r -> ConstantI a
zero-width->Constant (Iℚ-cons _ _ _) = diff-zero


i∪₁-Constant : (a b : Iℚ) -> ConstantI (a i∪ b) -> ConstantI a
i∪₁-Constant a@(Iℚ-cons l u l≤u) b const = (antisym-≤ l≤u u≤l)
  where

  0w : i-width (a i∪ b) == 0r
  0w = Constant->zero-width (a i∪ b) const

  np-w : NonPos (i-width a)
  np-w = ≤0-NonPos (i-width a) (trans-≤-= (i∪₁-width-≤ a b) 0w)

  z-w : Zero (i-width a)
  z-w = NonNeg-NonPos->Zero (0≤-NonNeg _ (0≤i-width a)) np-w

  u≤l : u ≤ l
  u≤l = NonNeg-diffℚ⁻ u l (subst NonNeg (sym diff-anticommute)
                                        (inj-r (r--flips-sign _ zero-sign z-w)))

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

  z1 : Zero (abs al * (i-width b))
  z1 = subst Zero (sym (Constant->zero-width (i-scale al b) c1) >=> i-scale-width al b) Zero-0r
  z2 : Zero (abs au * (i-width b))
  z2 = subst Zero (sym (Constant->zero-width (i-scale au b) c2) >=> i-scale-width au b) Zero-0r

  handle : (Zero (abs al) ⊎ Zero (i-width b)) -> (Zero (abs au) ⊎ Zero (i-width b)) -> _
  handle (inj-r zw) _         = inj-r (zero-width->Constant b (Zero-path _ zw))
  handle (inj-l _) (inj-r zw) = inj-r (zero-width->Constant b (Zero-path _ zw))
  handle (inj-l zal) (inj-l zau) = inj-l (pl >=> sym pu)
    where
    pl : al == 0r
    pl = eqInv abs-zero-eq zal
    pu : au == 0r
    pu = eqInv abs-zero-eq zau

i*-left-one : (a : Iℚ) -> 1i i* a == a
i*-left-one a = cong2 _i∪_ (i-scale-1 a) (i-scale-1 a) >=> (i∪-same a)


-- Inclusion

record _i⊆_ (a : Iℚ) (b : Iℚ) : Type₀ where
  constructor i⊆-cons
  field
    l : Iℚ.l b ≤ Iℚ.l a
    u : Iℚ.u a ≤ Iℚ.u b

OrderedOverlap : (a b : Iℚ) -> Type₀
OrderedOverlap a b = (Iℚ.l b) ≤ (Iℚ.u a)

Overlap : (a b : Iℚ) -> Type₀
Overlap a b = OrderedOverlap a b × OrderedOverlap b a

isProp-Overlap : (a b : Iℚ) -> isProp (Overlap a b)
isProp-Overlap a b = isProp× isProp-≤ isProp-≤

sym-Overlap : (a b : Iℚ) -> Overlap a b -> Overlap b a
sym-Overlap _ _ (o1 , o2) = (o2 , o1)

NonOverlap : (a b : Iℚ) -> Type₀
NonOverlap a b = (Iℚ.u a < Iℚ.l b) ⊎ (Iℚ.u b < Iℚ.l a)

decidable-Overlap : Decidable2 Overlap
decidable-Overlap a@(Iℚ-cons al au _) b@(Iℚ-cons bl bu _) =
  handle (split-< au bl) (split-< bu al)
  where
  handle : ((au < bl) ⊎ (bl ≤ au)) -> ((bu < al) ⊎ (al ≤ bu)) -> Dec (Overlap a b)
  handle (inj-l au<bl) _             = no (\{ (bl≤au , al≤bu) -> irrefl-< (trans-<-≤ au<bl bl≤au) })
  handle (inj-r bl≤au) (inj-l bu<al) = no (\{ (bl≤au , al≤bu) -> irrefl-< (trans-<-≤ bu<al al≤bu) })
  handle (inj-r bl≤au) (inj-r al≤bu) = yes (bl≤au , al≤bu)

split-Overlap : (a b : Iℚ) -> (Overlap a b ⊎ NonOverlap a b)
split-Overlap a@(Iℚ-cons al au _) b@(Iℚ-cons bl bu _) =
  handle (split-< au bl) (split-< bu al)
  where
  handle : ((au < bl) ⊎ (bl ≤ au)) -> ((bu < al) ⊎ (al ≤ bu)) -> (Overlap a b ⊎ NonOverlap a b)
  handle (inj-l au<bl) _             = inj-r (inj-l au<bl)
  handle (inj-r bl≤au) (inj-l bu<al) = inj-r (inj-r bu<al)
  handle (inj-r bl≤au) (inj-r al≤bu) = inj-l (bl≤au , al≤bu)


i-intersect : (a b : Iℚ) -> Overlap a b -> Iℚ
i-intersect a b (bl≤au , al≤bu) =
  Iℚ-cons (max a.l b.l) (min a.u b.u) ls≤us
  where
  module a = Iℚ a
  module b = Iℚ b

  ls = max a.l b.l
  us = min a.u b.u
  ls≤au : ls ≤ a.u
  ls≤au = max-property {P = _≤ a.u} a.l b.l a.l≤u bl≤au

  ls≤bu : ls ≤ b.u
  ls≤bu = max-property {P = _≤ b.u} a.l b.l al≤bu b.l≤u

  ls≤us : ls ≤ us
  ls≤us = min-property {P = ls ≤_} a.u b.u ls≤au ls≤bu

i⊆-Lower : {a b : Iℚ} -> a i⊆ b -> (q : ℚ) -> i-Lower b q -> i-Lower a q
i⊆-Lower (i⊆-cons bl≤al _) _ q≤bl = trans-≤ q≤bl bl≤al

i⊆-Upper : {a b : Iℚ} -> a i⊆ b -> (q : ℚ) -> i-Upper b q -> i-Upper a q
i⊆-Upper (i⊆-cons _ au≤bu) _ bu≤q = trans-≤ au≤bu bu≤q

trans-i⊆ : {a b c : Iℚ} -> a i⊆ b -> b i⊆ c -> a i⊆ c
trans-i⊆  a⊆b b⊆c = record
  { l = trans-≤ (_i⊆_.l b⊆c) (_i⊆_.l a⊆b)
  ; u = trans-≤ (_i⊆_.u a⊆b) (_i⊆_.u b⊆c)
  }

i-intersect-⊆₁ : (a b : Iℚ) -> (o : Overlap a b) -> i-intersect a b o i⊆ a
i-intersect-⊆₁ a b _ = i⊆-cons max-≤-left min-≤-left

i-intersect-⊆₂ : (a b : Iℚ) -> (o : Overlap a b) -> i-intersect a b o i⊆ b
i-intersect-⊆₂ a b _ = i⊆-cons max-≤-right min-≤-right

i-scale-preserves-⊆ : (k : ℚ) {a b : Iℚ} -> a i⊆ b -> (i-scale k a) i⊆ (i-scale k b)
i-scale-preserves-⊆ k {a@(Iℚ-cons al au al≤au)} {b@(Iℚ-cons bl bu bl≤bu)} (i⊆-cons l u) =
  handle (decide-sign k)
  where
  nn-case : NonNeg k -> (i-scale k a) i⊆ (i-scale k b)
  nn-case nn = i⊆-cons (subst2 _≤_ (sym minb-path) (sym mina-path)
                                   (*₁-preserves-≤ (NonNeg-0≤ _ nn) l))
                       (subst2 _≤_ (sym maxa-path) (sym maxb-path)
                                   (*₁-preserves-≤ (NonNeg-0≤ _ nn) u))
    where
    minb-path : min (k * bl) (k * bu) == k * bl
    minb-path = min-≤-path (*₁-preserves-≤ (NonNeg-0≤ _ nn) bl≤bu)

    mina-path : min (k * al) (k * au) == k * al
    mina-path = min-≤-path (*₁-preserves-≤ (NonNeg-0≤ _ nn) al≤au)

    maxb-path : max (k * bl) (k * bu) == k * bu
    maxb-path = max-≤-path (*₁-preserves-≤ (NonNeg-0≤ _ nn) bl≤bu)

    maxa-path : max (k * al) (k * au) == k * au
    maxa-path = max-≤-path (*₁-preserves-≤ (NonNeg-0≤ _ nn) al≤au)

  np-case : NonPos k -> (i-scale k a) i⊆ (i-scale k b)
  np-case np = i⊆-cons (subst2 _≤_ (sym minb-path) (sym mina-path)
                                   (*₁-flips-≤ (NonPos-≤0 _ np) u))
                       (subst2 _≤_ (sym maxa-path) (sym maxb-path)
                                   (*₁-flips-≤ (NonPos-≤0 _ np) l))
    where
    minb-path : min (k * bl) (k * bu) == k * bu
    minb-path = min-≥-path (*₁-flips-≤ (NonPos-≤0 _ np) bl≤bu)

    mina-path : min (k * al) (k * au) == k * au
    mina-path = min-≥-path (*₁-flips-≤ (NonPos-≤0 _ np) al≤au)

    maxb-path : max (k * bl) (k * bu) == k * bl
    maxb-path = max-≥-path (*₁-flips-≤ (NonPos-≤0 _ np) bl≤bu)

    maxa-path : max (k * al) (k * au) == k * al
    maxa-path = max-≥-path (*₁-flips-≤ (NonPos-≤0 _ np) al≤au)

  handle : Σ[ s ∈ Sign ] isSign s k -> (i-scale k a) i⊆ (i-scale k b)
  handle (pos-sign  , pk) = nn-case (inj-l pk)
  handle (zero-sign , zk) = nn-case (inj-r zk)
  handle (neg-sign  , nk) = np-case (inj-l nk)


i∪₁-preserves-⊆ : (a : Iℚ) {b c : Iℚ} -> b i⊆ c -> (a i∪ b) i⊆ (a i∪ c)
i∪₁-preserves-⊆ a (i⊆-cons l u) = i⊆-cons (min₁-preserves-≤ l) (max₁-preserves-≤ u)

i∪₂-preserves-⊆ : {a b : Iℚ} -> a i⊆ b -> (c : Iℚ) -> (a i∪ c) i⊆ (b i∪ c)
i∪₂-preserves-⊆ {a} {b} a⊆b c =
  subst2 _i⊆_ (i∪-commute c a) (i∪-commute c b) (i∪₁-preserves-⊆ c a⊆b)

i∪-preserves-⊆ : {a b c d : Iℚ} -> a i⊆ b -> c i⊆ d  -> (a i∪ c) i⊆ (b i∪ d)
i∪-preserves-⊆ {a} {b} {c} {d} a⊆b c⊆d =
  trans-i⊆ (i∪₁-preserves-⊆ a c⊆d) (i∪₂-preserves-⊆ a⊆b d)

i∪₁-⊆ : (a b : Iℚ) -> a i⊆ (a i∪ b)
i∪₁-⊆ (Iℚ-cons al au _) (Iℚ-cons bl bu _) = i⊆-cons min-≤-left max-≤-left

i∪₂-⊆ : (a b : Iℚ) -> b i⊆ (a i∪ b)
i∪₂-⊆ (Iℚ-cons al au _) (Iℚ-cons bl bu _) = i⊆-cons min-≤-right max-≤-right

i*₁-preserves-⊆ : (a : Iℚ) {b c : Iℚ} -> b i⊆ c -> (a i* b) i⊆ (a i* c)
i*₁-preserves-⊆ (Iℚ-cons al au _) b⊆c =
  i∪-preserves-⊆ (i-scale-preserves-⊆ al b⊆c) (i-scale-preserves-⊆ au b⊆c)

i*₂-preserves-⊆ : {a b : Iℚ} -> a i⊆ b -> (c : Iℚ) -> (a i* c) i⊆ (b i* c)
i*₂-preserves-⊆ {a} {b} a⊆b c = subst2 _i⊆_ (i*-commute c a) (i*-commute c b) (i*₁-preserves-⊆ c a⊆b)

i*-preserves-⊆ : {a b c d : Iℚ} -> a i⊆ b -> c i⊆ d  -> (a i* c) i⊆ (b i* d)
i*-preserves-⊆ {a} {b} {c} {d} a⊆b c⊆d =
  trans-i⊆ (i*₁-preserves-⊆ a c⊆d) (i*₂-preserves-⊆ a⊆b d)

i+₁-preserves-⊆ : (a : Iℚ) {b c : Iℚ} -> b i⊆ c -> (a i+ b) i⊆ (a i+ c)
i+₁-preserves-⊆ (Iℚ-cons al au _) (i⊆-cons cl≤bl bu≤cu) =
  i⊆-cons (+₁-preserves-≤ cl≤bl) (+₁-preserves-≤ bu≤cu)

i+₂-preserves-⊆ : {a b : Iℚ} -> a i⊆ b -> (c : Iℚ) -> (a i+ c) i⊆ (b i+ c)
i+₂-preserves-⊆ (i⊆-cons bl≤al au≤bu) (Iℚ-cons cl cu _) =
  i⊆-cons (+₂-preserves-≤ bl≤al) (+₂-preserves-≤ au≤bu)

i+-preserves-⊆ : {a b c d : Iℚ} -> a i⊆ b -> c i⊆ d  -> (a i+ c) i⊆ (b i+ d)
i+-preserves-⊆ {a} {b} {c} {d} a⊆b c⊆d =
  trans-i⊆ (i+₁-preserves-⊆ a c⊆d) (i+₂-preserves-⊆ a⊆b d)

i-width-⊆ : {a b : Iℚ} -> a i⊆ b -> i-width a ≤ i-width b
i-width-⊆ {Iℚ-cons al au _} {Iℚ-cons bl bu _} (i⊆-cons l u) = +-preserves-≤ u (minus-flips-≤ l)

i-maxabs-⊆ : {a b : Iℚ} -> a i⊆ b -> i-maxabs a ≤ i-maxabs b
i-maxabs-⊆ {a@(Iℚ-cons al au al≤au)} {b@(Iℚ-cons bl bu bl≤bu)} (i⊆-cons bl≤al au≤bu) =
  max-preserves-≤ (minus-flips-≤ bl≤al) au≤bu

i⊆-preserves-PosI : {a b : Iℚ} -> a i⊆ b -> PosI b -> PosI a
i⊆-preserves-PosI (i⊆-cons bl≤al _) pos-bl = Pos-≤ _ _ pos-bl bl≤al




-- Strict Inclusion
record _i⊂_ (a : Iℚ) (b : Iℚ) : Type₀ where
  no-eta-equality ; pattern
  constructor i⊂-cons
  field
    l : Iℚ.l b < Iℚ.l a
    u : Iℚ.u a < Iℚ.u b

trans-i⊂ : {a b c : Iℚ} -> a i⊂ b -> b i⊂ c -> a i⊂ c
trans-i⊂ (i⊂-cons ab-l ab-u) (i⊂-cons bc-l bc-u) =
  i⊂-cons (trans-< bc-l ab-l) (trans-< ab-u bc-u)

trans-i⊂-i⊆ : {a b c : Iℚ} -> a i⊂ b -> b i⊆ c -> a i⊂ c
trans-i⊂-i⊆ {Iℚ-cons al au _} {Iℚ-cons bl bu _} {Iℚ-cons cl cu _} a⊂b b⊆c = record
  { l = trans-≤-< {d1 = cl} {bl} {al} (_i⊆_.l b⊆c) (_i⊂_.l a⊂b)
  ; u = trans-<-≤ {d1 = au} {bu} {cu} (_i⊂_.u a⊂b) (_i⊆_.u b⊆c)
  }

trans-i⊆-i⊂ : {a b c : Iℚ} -> a i⊆ b -> b i⊂ c -> a i⊂ c
trans-i⊆-i⊂ {Iℚ-cons al au _} {Iℚ-cons bl bu _} {Iℚ-cons cl cu _} a⊆b b⊂c = record
  { l = trans-<-≤ (_i⊂_.l b⊂c) (_i⊆_.l a⊆b)
  ; u = trans-≤-< (_i⊆_.u a⊆b) (_i⊂_.u b⊂c)
  }

weaken-i⊂ : {a b : Iℚ} -> a i⊂ b -> a i⊆ b
weaken-i⊂ {a} {b} (i⊂-cons l u) = (i⊆-cons (weaken-< l) (weaken-< u))



i∪-preserves-⊂ : {a b c d : Iℚ} -> a i⊂ b -> c i⊂ d -> (a i∪ c) i⊂ (b i∪ d)
i∪-preserves-⊂ (i⊂-cons bl<al au<bu) (i⊂-cons dl<cl cu<du) =
  i⊂-cons (min-preserves-< bl<al dl<cl) (max-preserves-< au<bu cu<du)

i-scale-preserves-⊂ : {k : ℚ} {a b : Iℚ} -> NonZero k -> a i⊂ b -> (i-scale k a) i⊂ (i-scale k b)
i-scale-preserves-⊂ {k} {(Iℚ-cons al au al≤au)} {(Iℚ-cons bl bu bl≤bu)} (inj-l pk) (i⊂-cons bl<al au<bu) =
  i⊂-cons (subst2 _<_ (sym minb-path) (sym mina-path) (*₁-preserves-< pk bl<al))
          (subst2 _<_ (sym maxa-path) (sym maxb-path) (*₁-preserves-< pk au<bu))
  where
  minb-path : min (k * bl) (k * bu) == k * bl
  minb-path = min-≤-path (*₁-preserves-≤ (weaken-< pk) bl≤bu)

  mina-path : min (k * al) (k * au) == k * al
  mina-path = min-≤-path (*₁-preserves-≤ (weaken-< pk) al≤au)

  maxb-path : max (k * bl) (k * bu) == k * bu
  maxb-path = max-≤-path (*₁-preserves-≤ (weaken-< pk) bl≤bu)

  maxa-path : max (k * al) (k * au) == k * au
  maxa-path = max-≤-path (*₁-preserves-≤ (weaken-< pk) al≤au)
i-scale-preserves-⊂ {k} {(Iℚ-cons al au al≤au)} {(Iℚ-cons bl bu bl≤bu)} (inj-r nk) (i⊂-cons bl<al au<bu) =
  i⊂-cons (subst2 _<_ (sym minb-path) (sym mina-path) (*₁-flips-< nk au<bu))
          (subst2 _<_ (sym maxa-path) (sym maxb-path) (*₁-flips-< nk bl<al))
  where
  minb-path : min (k * bl) (k * bu) == k * bu
  minb-path = min-≥-path (*₁-flips-≤ (weaken-< nk) bl≤bu)

  mina-path : min (k * al) (k * au) == k * au
  mina-path = min-≥-path (*₁-flips-≤ (weaken-< nk) al≤au)

  maxb-path : max (k * bl) (k * bu) == k * bl
  maxb-path = max-≥-path (*₁-flips-≤ (weaken-< nk) bl≤bu)

  maxa-path : max (k * al) (k * au) == k * al
  maxa-path = max-≥-path (*₁-flips-≤ (weaken-< nk) al≤au)

i*₁-preserves-⊂ : (a : Iℚ) -> (¬ (ZeroEndedI a)) -> {b c : Iℚ} -> b i⊂ c -> (a i* b) i⊂ (a i* c)
i*₁-preserves-⊂ a@(Iℚ-cons al au _) ¬za {b} {c} b⊂c =
  handle (fst (decide-sign al)) (fst (decide-sign au)) (snd (decide-sign al)) (snd (decide-sign au))
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


find-shrink-factor : {a b : Iℚ} -> a i⊂ b -> Σ[ k ∈ ℚ ] (Pos k × k < 1r × i-scale k a i⊆ b)
find-shrink-factor {a@(Iℚ-cons al au al≤au)} {b@(Iℚ-cons bl bu bl≤bu)} (i⊂-cons bl<al au<bu) =
  handle (strict-classify b)
  where
  Ans = Σ[ k ∈ ℚ ] (0# < k × k < 1# × i-scale k a i⊆ b)
  p-case : PosI b -> Ans
  p-case 0<bl = k , 0<k , k<1 , subst (_i⊆ b) p-path (i⊆-cons bl≤pl pu≤bu)
    where
    0<al : 0# < al
    0<al = trans-< 0<bl bl<al

    al-inv : ℚInv al
    al-inv = Pos->Inv 0<al

    1/al = (r1/ al al-inv)
    0<1/al = (r1/-preserves-Pos al al-inv 0<al)

    k = bl * 1/al
    k<1 : k < 1r
    k<1 = trans-<-= (*₂-preserves-< bl<al 0<1/al)
                    (*-commute >=> r1/-inverse al al-inv)

    0<k : 0# < k
    0<k = *-preserves-0< 0<bl 0<1/al
    0≤k : 0# ≤ k
    0≤k = weaken-< 0<k


    0≤au : 0# ≤ au
    0≤au = trans-≤ (weaken-< 0<al) al≤au

    p = i-scale-0≤ (k , 0≤k) a
    pl = Iℚ.l p
    pu = Iℚ.u p
    p' = i-scale k a

    p-path : p == p'
    p-path = i-scale-0≤-path (k , 0≤k) a

    pl-path : pl == bl
    pl-path = *-assoc >=> *-right (r1/-inverse al al-inv) >=> *-right-one

    bl≤pl : bl ≤ pl
    bl≤pl = path-≤ (sym pl-path)

    pu≤au : pu ≤ au
    pu≤au = trans-≤-= (*₂-preserves-≤ (weaken-< k<1) 0≤au) *-left-one

    pu≤bu : pu ≤ bu
    pu≤bu = trans-≤ pu≤au (weaken-< au<bu)

  n-case : NegI b -> Ans
  n-case bu<0 = k , 0<k , k<1 , subst (_i⊆ b) p-path (i⊆-cons bl≤pl pu≤bu)
    where
    au<0 : au < 0#
    au<0 = trans-< au<bu bu<0

    au-inv : ℚInv au
    au-inv = Neg->Inv au<0

    1/au = (r1/ au au-inv)
    1/au<0 = (r1/-preserves-Neg au au-inv au<0)

    k = bu * 1/au

    k<1 : k < 1r
    k<1 = trans-<-= (*₂-flips-< au<bu 1/au<0)
                    (*-commute >=> r1/-inverse au au-inv)

    0<k = *-flips-<0 bu<0 1/au<0
    0≤k : 0# ≤ k
    0≤k = weaken-< 0<k


    al≤0 : al ≤ 0#
    al≤0 = trans-≤ al≤au (weaken-< au<0)

    p = i-scale-0≤ (k , 0≤k) a
    pl = Iℚ.l p
    pu = Iℚ.u p
    p' = i-scale k a

    p-path : p == p'
    p-path = i-scale-0≤-path (k , 0≤k) a

    pu-path : pu == bu
    pu-path = *-assoc >=> *-right (r1/-inverse au au-inv) >=> *-right-one

    pu≤bu : pu ≤ bu
    pu≤bu = path-≤ pu-path

    al≤pl : al ≤ pl
    al≤pl = trans-=-≤ (sym *-left-one) (*₂-flips-≤ (weaken-< k<1) al≤0)

    bl≤pl : bl ≤ pl
    bl≤pl = trans-≤ (weaken-< bl<al) al≤pl

  cz-case : CrossZeroI b -> Ans
  cz-case (bl≤0 , 0≤bu) =
    1/2r , Pos-1/ℕ (2 , _) , 1/2r<1r , subst (_i⊆ b) p-path (i⊆-cons bl≤pl pu≤bu)
    where
    0≤1/2 : 0# ≤ 1/2r
    0≤1/2 = weaken-< (Pos-1/ℕ (2 , _))

    p = i-scale-0≤ (1/2r , 0≤1/2) a
    pl = Iℚ.l p
    pu = Iℚ.u p
    p' = i-scale 1/2r a

    p-path : p == p'
    p-path = i-scale-0≤-path (1/2r , 0≤1/2) a

    1/2bu≤bu : (1/2r * bu) ≤ bu
    1/2bu≤bu = trans-≤-= (*₂-preserves-≤ (weaken-< 1/2r<1r) 0≤bu) *-left-one

    pu≤1/2bu : pu ≤ (1/2r * bu)
    pu≤1/2bu = *₁-preserves-≤ 0≤1/2 (weaken-< au<bu)

    pu≤bu : pu ≤ bu
    pu≤bu = trans-≤ pu≤1/2bu 1/2bu≤bu

    bl≤1/2bl : bl ≤ (1/2r * bl)
    bl≤1/2bl = trans-=-≤ (sym *-left-one) (*₂-flips-≤ (weaken-< 1/2r<1r) bl≤0)

    1/2bl≤pl : (1/2r * bl) ≤ pl
    1/2bl≤pl = *₁-preserves-≤ 0≤1/2 (weaken-< bl<al)

    bl≤pl : bl ≤ pl
    bl≤pl = trans-≤ bl≤1/2bl 1/2bl≤pl


  handle : StrictClass b -> Ans
  handle (p-c p) = p-case p
  handle (n-c p) = n-case p
  handle (cz-c p) = cz-case p


find-growth-factor : {a b : Iℚ} -> a i⊂ b -> Σ[ k ∈ ℚ ] (0# < k × 1# < k × i-scale k a i⊆ b)
find-growth-factor {a@(Iℚ-cons al au al≤au)} {b@(Iℚ-cons bl bu bl≤bu)} (i⊂-cons bl<al au<bu) =
  handle (strict-classify' b)
  where
  Ans = Σ[ k ∈ ℚ ] (0# < k × 1# < k × i-scale k a i⊆ b)
  nn-case : NonNegI b -> Ans
  nn-case 0≤bl = k , 0<k , 1<k , subst (_i⊆ b) p-path (i⊆-cons bl≤pl pu≤bu)
    where
    0<au : 0# < au
    0<au = trans-≤-< 0≤bl (trans-<-≤ bl<al al≤au)

    au-inv : ℚInv au
    au-inv = Pos->Inv 0<au

    1/au = (r1/ au au-inv)
    0<1/au = (r1/-preserves-Pos au au-inv 0<au)

    k = bu * 1/au

    1<k : 1r < k
    1<k = trans-=-< (sym (*-commute >=> r1/-inverse au au-inv))
                    (*₂-preserves-< au<bu 0<1/au)

    0<bu = trans-< 0<au au<bu

    0<k = *-preserves-0< 0<bu 0<1/au
    0≤k : 0# ≤ k
    0≤k = weaken-< 0<k

    0≤al : 0# ≤ al
    0≤al = trans-≤ 0≤bl (weaken-< bl<al)

    p = i-scale-0≤ (k , 0≤k) a
    pl = Iℚ.l p
    pu = Iℚ.u p
    p' = i-scale k a

    p-path : p == p'
    p-path = i-scale-0≤-path (k , 0≤k) a

    pu-path : pu == bu
    pu-path = *-assoc >=> *-right (r1/-inverse au au-inv) >=> *-right-one

    pu≤bu : pu ≤ bu
    pu≤bu = path-≤ pu-path

    al≤pl : al ≤ pl
    al≤pl = trans-=-≤ (sym *-left-one) (*₂-preserves-≤ (weaken-< 1<k) 0≤al)

    bl≤pl : bl ≤ pl
    bl≤pl = trans-≤ (weaken-< bl<al) al≤pl

  np-case : NonPosI b -> Ans
  np-case bu≤0 = k , 0<k , 1<k , subst (_i⊆ b) p-path (i⊆-cons bl≤pl pu≤bu)
    where
    al<0 : al < 0#
    al<0 = trans-≤-< al≤au (trans-<-≤ au<bu bu≤0)

    al-inv : ℚInv al
    al-inv = Neg->Inv al<0

    1/al = r1/ al al-inv
    1/al<0 = r1/-preserves-Neg al al-inv al<0

    k = bl * 1/al

    1<k : 1r < k
    1<k = trans-=-< (sym (*-commute >=> r1/-inverse al al-inv))
                    (*₂-flips-< bl<al 1/al<0)

    n-bl = Neg-≤ bl al al<0 (weaken-< bl<al)

    0<k = *-flips-<0 (trans-< bl<al al<0) 1/al<0
    0≤k : 0# ≤ k
    0≤k = weaken-< 0<k


    au≤0 : au ≤ 0#
    au≤0 = trans-≤ (weaken-< au<bu) bu≤0

    p = i-scale-0≤ (k , 0≤k) a
    pl = Iℚ.l p
    pu = Iℚ.u p
    p' = i-scale k a

    p-path : p == p'
    p-path = i-scale-0≤-path (k , 0≤k) a

    pl-path : pl == bl
    pl-path = *-assoc >=> *-right (r1/-inverse al al-inv) >=> *-right-one

    bl≤pl : bl ≤ pl
    bl≤pl = path-≤ (sym pl-path)

    pu≤au : pu ≤ au
    pu≤au = trans-≤-= (*₂-flips-≤ (weaken-< 1<k) au≤0)  *-left-one

    pu≤bu : pu ≤ bu
    pu≤bu = trans-≤ pu≤au (weaken-< au<bu)



  cz-case : StrictCrossZeroI b -> Ans
  cz-case (n-bl , p-bu) = k , p-k , 1<k  , subst (_i⊆ b) p-path (i⊆-cons bl≤pl pu≤bu)
    where
    hbl = 1/2r * bl
    hbu = 1/2r * bu

    al' = min al hbl
    au' = max au hbu

    n-al' : Neg al'
    n-al' = Neg-≤ al' hbl (r*₁-preserves-sign (1/2r , Pos-1/ℕ (2 , _)) _ {neg-sign} n-bl)
                          min-≤-right

    p-au' : Pos au'
    p-au' = Pos-≤ hbu au' (r*₁-preserves-sign (1/2r , Pos-1/ℕ (2 , _)) _ {pos-sign} p-bu)
                          max-≤-right

    bl<al' : bl < al'
    bl<al' = min-property {P = bl <_} al hbl bl<al
                          (trans-=-< (sym *-left-one) (*₂-flips-< 1/2r<1r n-bl))
    au'<bu : au' < bu
    au'<bu = max-property {P = _< bu} au hbu au<bu
                          (trans-<-= (*₂-preserves-< 1/2r<1r p-bu) *-left-one)

    al'-inv : ℚInv al'
    al'-inv = Neg->Inv n-al'

    au'-inv : ℚInv au'
    au'-inv = Pos->Inv p-au'

    1/al' = (r1/ al' al'-inv)
    1/au' = (r1/ au' au'-inv)

    kl = bl * 1/al'
    ku = bu * 1/au'

    n-1/al' = r1/-preserves-Neg al' al'-inv n-al'
    p-1/au' = r1/-preserves-Pos au' au'-inv p-au'

    p-kl : Pos kl
    p-kl = r*₁-flips-sign (bl , n-bl) _ {neg-sign} n-1/al'
    p-ku : Pos ku
    p-ku = r*₁-preserves-sign (bu , p-bu) _ {pos-sign} p-1/au'

    1<kl : 1r < kl
    1<kl = trans-=-< (sym (*-commute >=> r1/-inverse al' al'-inv))
                     (*₂-flips-< bl<al' n-1/al')
    1<ku : 1r < ku
    1<ku = trans-=-< (sym (*-commute >=> r1/-inverse au' au'-inv))
                     (*₂-preserves-< au'<bu p-1/au')

    k = min kl ku

    p-k : Pos k
    p-k = min-property {P = Pos} kl ku p-kl p-ku

    1<k : 1r < k
    1<k = min-property {P = 1r <_} kl ku 1<kl 1<ku

    p = i-scale-0≤ (k , weaken-< p-k) a
    pl = Iℚ.l p
    pu = Iℚ.u p
    p' = i-scale k a

    p-path : p == p'
    p-path = i-scale-0≤-path (k , weaken-< p-k) a

    l-path : kl * al' == bl
    l-path = *-assoc >=> *-right (r1/-inverse al' al'-inv) >=> *-right-one

    u-path : ku * au' == bu
    u-path = *-assoc >=> *-right (r1/-inverse au' au'-inv) >=> *-right-one

    al'≤al : al' ≤ al
    al'≤al = min-≤-left
    au≤au' : au  ≤ au'
    au≤au' = max-≤-left

    k≤kl : k ≤ kl
    k≤kl = min-≤-left
    k≤ku : k ≤ ku
    k≤ku = min-≤-right


    bl≤pl : bl ≤ pl
    bl≤pl = trans-=-≤ (sym l-path)
              (trans-≤ (*₂-flips-≤ k≤kl (weaken-< n-al'))
                       (*₁-preserves-≤ (weaken-< p-k) al'≤al))

    pu≤bu : pu ≤ bu
    pu≤bu = trans-≤-= (trans-≤ (*₁-preserves-≤ (weaken-< p-k) au≤au')
                               (*₂-preserves-≤ k≤ku (weaken-< p-au')))
                      u-path

  handle : StrictClass' b -> Ans
  handle (nn-c p) = nn-case p
  handle (np-c p) = np-case p
  handle (cz-c p) = cz-case p
