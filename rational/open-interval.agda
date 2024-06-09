{-# OPTIONS --cubical --safe --exact-split #-}

module rational.open-interval where

open import additive-group
open import base
open import equality
open import hlevel
open import heyting-field.instances.rational
open import order
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-field
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.minmax
open import rational
open import rational.order
open import relation
open import semiring
open import ring
open import sum
open import sign
open import sign.instances.rational
open import truncation

import rational.proper-interval as closed

private
  variable
    ℓ : Level

record Iℚ : Type₀ where
  no-eta-equality ; pattern
  constructor Iℚ-cons
  field
    l : ℚ
    u : ℚ
    l<u : l ℚ< u

opaque
  Iℚ-bounds-path : {a b : Iℚ} -> (Iℚ.l a == Iℚ.l b) -> (Iℚ.u a == Iℚ.u b) -> a == b
  Iℚ-bounds-path {a@(Iℚ-cons _ _ _)} {b@(Iℚ-cons _ _ _)} pl pu i = Iℚ-cons (pl i) (pu i) (p< i)
    where
    p< : PathP (\i -> (pl i) < (pu i)) (Iℚ.l<u a) (Iℚ.l<u b)
    p< = isProp->PathP (\i -> isProp-<)

Overlap : (a b : Iℚ) -> Type₀
Overlap a b = (Iℚ.l b < Iℚ.u a) × (Iℚ.l a < Iℚ.u b)

isProp-Overlap : (a b : Iℚ) -> isProp (Overlap a b)
isProp-Overlap a b = isProp× isProp-< isProp-<

sym-Overlap : (a b : Iℚ) -> Overlap a b -> Overlap b a
sym-Overlap _ _ (o1 , o2) = (o2 , o1)

NonOverlap : (a b : Iℚ) -> Type₀
NonOverlap a b = (Iℚ.u a ≤ Iℚ.l b) ⊎ (Iℚ.u b ≤ Iℚ.l a)

split-Overlap : (a b : Iℚ) -> (Overlap a b ⊎ NonOverlap a b)
split-Overlap a@(Iℚ-cons al au _) b@(Iℚ-cons bl bu _) =
  handle (split-< bl au) (split-< al bu)
  where
  handle : ((bl < au) ⊎ (au ≤ bl)) -> ((al < bu) ⊎ (bu ≤ al)) -> (Overlap a b ⊎ NonOverlap a b)
  handle (inj-r au≤bl) _             = inj-r (inj-l au≤bl)
  handle (inj-l bl<au) (inj-r bu≤al) = inj-r (inj-r bu≤al)
  handle (inj-l bl<au) (inj-l al<bu) = inj-l (bl<au , al<bu)

Separated : (a b : Iℚ) -> Type₀
Separated a b = (Iℚ.u a < Iℚ.l b) ⊎ (Iℚ.u b < Iℚ.l a)

Touching : (a b : Iℚ) -> Type₀
Touching a b = (Iℚ.l b ≤ Iℚ.u a) × (Iℚ.l a ≤ Iℚ.u b)

isProp-Touching : (a b : Iℚ) -> isProp (Touching a b)
isProp-Touching a b = isProp× isProp-≤ isProp-≤

sym-Touching : (a b : Iℚ) -> Touching a b -> Touching b a
sym-Touching _ _ (t1 , t2) = (t2 , t1)

split-Separated : (a b : Iℚ) -> (Touching a b ⊎ Separated a b)
split-Separated a@(Iℚ-cons al au _) b@(Iℚ-cons bl bu _) =
  handle (split-< au bl) (split-< bu al)
  where
  handle : ((au < bl) ⊎ (bl ≤ au)) -> ((bu < al) ⊎ (al ≤ bu)) -> (Touching a b ⊎ Separated a b)
  handle (inj-l au<bl) _             = inj-r (inj-l au<bl)
  handle (inj-r bl≤au) (inj-l bu<al) = inj-r (inj-r bu<al)
  handle (inj-r bl≤au) (inj-r al≤bu) = inj-l (bl≤au , al≤bu)



SymI : Pred Iℚ ℓ-zero
SymI a = (Iℚ.l a) == (- (Iℚ.u a))

PosI : Pred Iℚ ℓ-zero
PosI a = 0# < (Iℚ.l a)
NegI : Pred Iℚ ℓ-zero
NegI a = (Iℚ.u a) < 0#
NonNegI : Pred Iℚ ℓ-zero
NonNegI a = 0# ≤ Iℚ.l a
NonPosI : Pred Iℚ ℓ-zero
NonPosI a = Iℚ.u a ≤ 0#

ZeroEndedI : Pred Iℚ ℓ-zero
ZeroEndedI a = Zero (Iℚ.l a) ⊎ Zero (Iℚ.u a)

i-Lower : Iℚ -> Pred ℚ ℓ-zero
i-Lower a q = q ≤ (Iℚ.l a)

i-Upper : Iℚ -> Pred ℚ ℓ-zero
i-Upper a q = (Iℚ.u a) ≤ q

¬LowerUpper : {q : ℚ} -> (i : Iℚ) -> i-Lower i q -> i-Upper i q -> Bot
¬LowerUpper (Iℚ-cons l u l<u) q≤l u≤q = irrefl-< (trans-<-≤ l<u (trans-≤ u≤q q≤l))

-- Interval operations

i-_ : Iℚ -> Iℚ
i-_ a = Iℚ-cons (- a.u) (- a.l) (minus-flips-< a.l<u)
  where
  module a = Iℚ a

i--double-inverse : {a : Iℚ} -> (i- (i- a)) == a
i--double-inverse = Iℚ-bounds-path minus-double-inverse minus-double-inverse


_i+_ : Iℚ -> Iℚ -> Iℚ
_i+_ a b = Iℚ-cons (a.l + b.l) (a.u + b.u) lt
  where
  module a = Iℚ a
  module b = Iℚ b
  opaque
    lt : (a.l + b.l) < (a.u + b.u)
    lt = (+-preserves-< a.l<u b.l<u)

i+-commute : (a b : Iℚ) -> a i+ b == b i+ a
i+-commute _ _ = Iℚ-bounds-path +-commute +-commute

i+-assoc : (a b c : Iℚ) -> (a i+ b) i+ c == a i+ (b i+ c)
i+-assoc _ _ _ = Iℚ-bounds-path +-assoc +-assoc

_i∪_ : Iℚ -> Iℚ -> Iℚ
_i∪_ a b = (Iℚ-cons (min a.l b.l) (max a.u b.u) lt)
  where
  module a = Iℚ a
  module b = Iℚ b
  opaque
    lt : (min a.l b.l) < (max a.u b.u)
    lt = (trans-<-≤ (trans-≤-< min-≤-left a.l<u) max-≤-left)

i∪-commute : (a b : Iℚ) -> a i∪ b == b i∪ a
i∪-commute a b = Iℚ-bounds-path min-commute max-commute

i∪-assoc : (a b c : Iℚ) -> (a i∪ b) i∪ c == a i∪ (b i∪ c)
i∪-assoc a b c = Iℚ-bounds-path min-assoc max-assoc

i∪-same : (a : Iℚ) -> a i∪ a == a
i∪-same a = Iℚ-bounds-path min-idempotent max-idempotent

i-width : Iℚ -> ℚ
i-width a = diff (Iℚ.l a) (Iℚ.u a)

0<i-width : (a : Iℚ) -> 0# < (i-width a)
0<i-width a = diff-0<⁺ (Iℚ.l<u a)

i-maxabs : Iℚ -> ℚ
i-maxabs (Iℚ-cons l u _) = max (- l) u

0<i-maxabs : (a : Iℚ) -> 0# < (i-maxabs a)
0<i-maxabs a@(Iℚ-cons l u l<u) =
  unsquash isProp-< (∥-map handle (comparison-< l 0# u l<u))
  where
  handle : (l < 0# ⊎ 0# < u) -> 0# < (i-maxabs a)
  handle (inj-l l<0) = trans-<-≤ (minus-flips-<0 l<0) max-≤-left
  handle (inj-r 0<u) = trans-<-≤ 0<u max-≤-right


i-scale⁺ : (k : ℚ⁺) -> Iℚ -> Iℚ
i-scale⁺ (k , 0<k) a =
  Iℚ-cons (k * a.l) (k * a.u) (*₁-preserves-< 0<k a.l<u)
  where
  module a = Iℚ a

i-scale⁻ : (k : ℚ⁻) -> Iℚ -> Iℚ
i-scale⁻ (k , k<0) a =
  Iℚ-cons (k * a.u) (k * a.l) (*₁-flips-< k<0 a.l<u)
  where
  module a = Iℚ a

i-scale : (k : ℚ) -> (k <> 0#)-> Iℚ -> Iℚ
i-scale k k<>0 a = Iℚ-cons min' max' lt
  where
  module a = Iℚ a
  min' = min (k * a.l) (k * a.u)
  max' = max (k * a.l) (k * a.u)
  handle⁺ : (0# < k) -> min' < max'
  handle⁺ 0<k =
    trans-=-< (sym (*-distrib-min-left (weaken-< 0<k)))
      (trans-<-=
        (*₁-preserves-< 0<k (trans-≤-< min-≤-left (trans-<-≤ a.l<u max-≤-right)))
        (*-distrib-max-left (weaken-< 0<k)))

  handle⁻ : (k < 0#) -> min' < max'
  handle⁻ k<0 =
    trans-=-< (sym (*-distrib-flip-max-left (weaken-< k<0)))
      (trans-<-=
        (*₁-flips-< k<0 (trans-≤-< min-≤-left (trans-<-≤ a.l<u max-≤-right)))
        (*-distrib-flip-min-left (weaken-< k<0)))

  opaque
    lt : min' < max'
    lt = either handle⁻ handle⁺ k<>0

i-scale⁺-path : (k⁺@(k , 0<k) : ℚ⁺) (a : Iℚ) -> i-scale⁺ k⁺ a == i-scale k (inj-r 0<k) a
i-scale⁺-path (k , 0<k) a =
  Iℚ-bounds-path (sym (min-≤-path (weaken-< (*₁-preserves-< 0<k (Iℚ.l<u a)))))
                 (sym (max-≤-path (weaken-< (*₁-preserves-< 0<k (Iℚ.l<u a)))))


i-intersect : (a b : Iℚ) -> Overlap a b -> Iℚ
i-intersect a b (bl<au , al<bu) =
  Iℚ-cons (max a.l b.l) (min a.u b.u) ls<us
  where
  module a = Iℚ a
  module b = Iℚ b
  ls = max a.l b.l
  us = min a.u b.u
  opaque
    ls<au : ls < a.u
    ls<au = max-property {P = _< a.u} a.l b.l a.l<u bl<au

    ls<bu : ls < b.u
    ls<bu = max-property {P = _< b.u} a.l b.l al<bu b.l<u

    ls<us : ls < us
    ls<us = min-property {P = ls <_} a.u b.u ls<au ls<bu

i*-SymI : (a b : Iℚ) -> (SymI a) -> (SymI b) -> Iℚ
i*-SymI a b al=-au bl=-bu = Iℚ-cons (- (a.u * b.u)) (a.u * b.u) lt
  where
  module a = Iℚ a
  module b = Iℚ b

  opaque
    0<au : 0# < a.u
    0<au = unsquash isProp-< (∥-map handle (comparison-< a.l 0# a.u a.l<u))
      where
      handle : (a.l < 0# ⊎ 0# < a.u) -> 0# < a.u
      handle (inj-l al<0) = trans-<-= (minus-flips-<0 al<0) (cong -_ al=-au >=> minus-double-inverse)
      handle (inj-r 0<au) = 0<au

    0<bu : 0# < b.u
    0<bu = unsquash isProp-< (∥-map handle (comparison-< b.l 0# b.u b.l<u))
      where
      handle : (b.l < 0# ⊎ 0# < b.u) -> 0# < b.u
      handle (inj-l bl<0) = trans-<-= (minus-flips-<0 bl<0) (cong -_ bl=-bu >=> minus-double-inverse)
      handle (inj-r 0<bu) = 0<bu

    0<us : 0# < (a.u * b.u)
    0<us = *-preserves-0< 0<au 0<bu


    lt : (- (a.u * b.u)) < (a.u * b.u)
    lt = trans-< (minus-flips-0< 0<us) 0<us


ΣCI->OI : (Σ closed.Iℚ closed.NonConstantI) -> Iℚ
ΣCI->OI (i , l<u) = Iℚ-cons i.l i.u l<u
  where
  module i = closed.Iℚ i

OI->ΣCI : Iℚ -> Σ closed.Iℚ closed.NonConstantI
OI->ΣCI i = (closed.Iℚ-cons i.l i.u (weaken-< i.l<u)) , i.l<u
  where
  module i = Iℚ i

OI->CI : Iℚ -> closed.Iℚ
OI->CI i = fst (OI->ΣCI i)

_i*_ : Iℚ -> Iℚ -> Iℚ
i1 i* i2 =
  let (c1 , nc1) = OI->ΣCI i1 ; (c2 , nc2) = OI->ΣCI i2 in
  ΣCI->OI (c1 closed.i* c2 , closed.i*-NonConstant c1 c2 nc1 nc2)

i*-NN : (a b : Iℚ) -> (NonNegI a) -> (NonNegI b) -> Iℚ
i*-NN a b 0≤al 0≤bl = Iℚ-cons (a.l * b.l) (a.u * b.u) lt
  where
  module a = Iℚ a
  module b = Iℚ b
  opaque
    lt : (a.l * b.l) < (a.u * b.u)
    lt = trans-≤-<
           (*₁-preserves-≤ 0≤al (weaken-< b.l<u))
           (*₂-preserves-< a.l<u (trans-≤-< 0≤bl b.l<u))


opaque
  i*-NN-path : (a b : Iℚ) -> (nn-a : (NonNegI a)) -> (nn-b : (NonNegI b)) ->
               i*-NN a b nn-a nn-b == (a i* b)
  i*-NN-path a b nn-a nn-b =
    Iℚ-bounds-path (cong closed.Iℚ.l cp) (cong closed.Iℚ.u cp)
    where
    cp : closed.i*-NN (OI->CI a) (OI->CI b) nn-a nn-b ==
         (OI->CI a) closed.i* (OI->CI b)
    cp = closed.i*-NN-path (OI->CI a) (OI->CI b) nn-a nn-b



i*-SymI-path : (a b : Iℚ) -> (sym-a : (SymI a)) -> (sym-b : (SymI b)) ->
               i*-SymI a b sym-a sym-b == (a i* b)
i*-SymI-path a b al=-au bl=-bu = Iℚ-bounds-path (sym pl) (sym pu)
  where
  module a = Iℚ a
  module b = Iℚ b

  0<au : 0# < a.u
  0<au = unsquash isProp-< (∥-map handle (comparison-< a.l 0# a.u a.l<u))
    where
    handle : (a.l < 0# ⊎ 0# < a.u) -> 0# < a.u
    handle (inj-l al<0) = trans-<-= (minus-flips-<0 al<0) (cong -_ al=-au >=> minus-double-inverse)
    handle (inj-r 0<au) = 0<au

  al<0 : a.l < 0#
  al<0 = trans-=-< al=-au (minus-flips-0< 0<au)

  0<bu : 0# < b.u
  0<bu = unsquash isProp-< (∥-map handle (comparison-< b.l 0# b.u b.l<u))
    where
    handle : (b.l < 0# ⊎ 0# < b.u) -> 0# < b.u
    handle (inj-l bl<0) = trans-<-= (minus-flips-<0 bl<0) (cong -_ bl=-bu >=> minus-double-inverse)
    handle (inj-r 0<bu) = 0<bu

  bl<0 : b.l < 0#
  bl<0 = trans-=-< bl=-bu (minus-flips-0< 0<bu)

  min-bs : min b.l b.u == b.l
  min-bs = min-≤-path (weaken-< (trans-< bl<0 0<bu))
  max-bs : max b.l b.u == b.u
  max-bs = max-≤-path (weaken-< (trans-< bl<0 0<bu))

  opaque
    pl : min (min (a.l * b.l) (a.l * b.u)) (min (a.u * b.l) (a.u * b.u)) == - (a.u * b.u)
    pl =
      cong2 min (sym (*-distrib-flip-max-left (weaken-< al<0)) >=>
                 cong (a.l *_) max-bs >=>
                 cong (_* b.u) al=-au >=>
                 minus-extract-left)
                (sym (*-distrib-min-left (weaken-< 0<au)) >=>
                 cong (a.u *_) (min-bs >=> bl=-bu) >=>
                 minus-extract-right) >=>
      min-idempotent

    pu : max (max (a.l * b.l) (a.l * b.u)) (max (a.u * b.l) (a.u * b.u)) == (a.u * b.u)
    pu =
      cong2 max (sym (*-distrib-flip-min-left (weaken-< al<0)) >=>
                 cong (a.l *_) (min-bs >=> bl=-bu) >=>
                 cong (_* (- b.u)) al=-au >=>
                 minus-extract-both)
                (sym (*-distrib-max-left (weaken-< 0<au)) >=>
                 cong (a.u *_) max-bs) >=>
      max-idempotent

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

i*-width-≤ : (a b : Iℚ) ->
             (i-width (a i* b)) ≤ (((i-width a) * (i-maxabs b)) + ((i-maxabs a) * (i-width b)))
i*-width-≤ a@(Iℚ-cons _ _ _) b@(Iℚ-cons _ _ _) =
  closed.i*-width-≤ (fst (OI->ΣCI a)) (fst (OI->ΣCI b))



-- Inclusion
record _i⊆_ (a : Iℚ) (b : Iℚ) : Type₀ where
  constructor i⊆-cons
  field
    l : Iℚ.l b ≤ Iℚ.l a
    u : Iℚ.u a ≤ Iℚ.u b

i⊆-Lower : {a b : Iℚ} -> a i⊆ b -> (q : ℚ) -> i-Lower b q -> i-Lower a q
i⊆-Lower (i⊆-cons bl≤al _) q q≤bl = trans-≤ q≤bl bl≤al

i⊆-Upper : {a b : Iℚ} -> a i⊆ b -> (q : ℚ) -> i-Upper b q -> i-Upper a q
i⊆-Upper (i⊆-cons _ au≤bu) q bu≤q = trans-≤ au≤bu bu≤q

trans-i⊆ : {a b c : Iℚ} -> a i⊆ b -> b i⊆ c -> a i⊆ c
trans-i⊆ {Iℚ-cons al au _} {Iℚ-cons bl bu _} {Iℚ-cons cl cu _} a⊆b b⊆c = record
  { l = trans-≤ (_i⊆_.l b⊆c) (_i⊆_.l a⊆b)
  ; u = trans-≤ (_i⊆_.u a⊆b) (_i⊆_.u b⊆c)
  }


i-intersect-⊆₁ : (a b : Iℚ) -> (o : Overlap a b) -> i-intersect a b o i⊆ a
i-intersect-⊆₁ a b _ = i⊆-cons max-≤-left min-≤-left

i-intersect-⊆₂ : (a b : Iℚ) -> (o : Overlap a b) -> i-intersect a b o i⊆ b
i-intersect-⊆₂ a b _ = i⊆-cons max-≤-right min-≤-right


i∪₁-preserves-⊆ : (a : Iℚ) {b c : Iℚ} -> b i⊆ c -> (a i∪ b) i⊆ (a i∪ c)
i∪₁-preserves-⊆ a (i⊆-cons l u) = i⊆-cons (min₁-preserves-≤ l) (max₁-preserves-≤ u)

i∪₂-preserves-⊆ : {a b : Iℚ} -> a i⊆ b -> (c : Iℚ) -> (a i∪ c) i⊆ (b i∪ c)
i∪₂-preserves-⊆ {a} {b} a⊆b c =
  subst2 _i⊆_ (i∪-commute c a) (i∪-commute c b) (i∪₁-preserves-⊆ c a⊆b)

i∪-preserves-⊆ : {a b c d : Iℚ} -> a i⊆ b -> c i⊆ d  -> (a i∪ c) i⊆ (b i∪ d)
i∪-preserves-⊆ {a} {b} {c} {d} a⊆b c⊆d =
  trans-i⊆ (i∪₁-preserves-⊆ a c⊆d) (i∪₂-preserves-⊆ a⊆b d)

i*₁-preserves-⊆ : (a : Iℚ) {b c : Iℚ} -> b i⊆ c -> (a i* b) i⊆ (a i* c)
i*₁-preserves-⊆ a {b} {c} b⊆c =
  i⊆-cons (closed._i⊆_.l inner) (closed._i⊆_.u inner)
  where
  a' : closed.Iℚ
  a' = fst (OI->ΣCI a)
  b' : closed.Iℚ
  b' = fst (OI->ΣCI b)
  c' : closed.Iℚ
  c' = fst (OI->ΣCI c)
  b'⊆c' : b' closed.i⊆ c'
  b'⊆c' = closed.i⊆-cons (_i⊆_.l b⊆c) (_i⊆_.u b⊆c)
  inner : (a' closed.i* b') closed.i⊆ (a' closed.i* c')
  inner = closed.i*₁-preserves-⊆ a' b'⊆c'

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
i-width-⊆ (i⊆-cons l u) = +-preserves-≤ u (minus-flips-≤ l)

i-maxabs-⊆ : {a b : Iℚ} -> a i⊆ b -> i-maxabs a ≤ i-maxabs b
i-maxabs-⊆ {a@(Iℚ-cons al au al≤au)} {b@(Iℚ-cons bl bu bl≤bu)} (i⊆-cons bl≤al au≤bu) =
  max-least-≤ (trans-≤ (minus-flips-≤ bl≤al) max-≤-left)
              (trans-≤ au≤bu max-≤-right)

i⊆-preserves-PosI : {a b : Iℚ} -> a i⊆ b -> PosI b -> PosI a
i⊆-preserves-PosI (i⊆-cons bl≤al _) 0<bl = trans-<-≤ 0<bl bl≤al

OI->CI-reflects-⊆ : {a b : Iℚ} -> (OI->CI a closed.i⊆ OI->CI b) -> a i⊆ b
OI->CI-reflects-⊆ (closed.i⊆-cons l u) = (i⊆-cons l u)


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
weaken-i⊂ {a} {b} (i⊂-cons l u) = (i⊆-cons (weaken-< {d1 = Iℚ.l b} l) (weaken-< {d1 = Iℚ.u a} u))


i∪-preserves-⊂ : {a b c d : Iℚ} -> a i⊂ b -> c i⊂ d -> (a i∪ c) i⊂ (b i∪ d)
i∪-preserves-⊂ (i⊂-cons bl<al au<bu) (i⊂-cons dl<cl cu<du) =
  i⊂-cons (min-preserves-< bl<al dl<cl) (max-preserves-< au<bu cu<du)

i*₁-preserves-⊂ : (a : Iℚ) -> (¬ (ZeroEndedI a)) -> {b c : Iℚ} -> b i⊂ c -> (a i* b) i⊂ (a i* c)
i*₁-preserves-⊂ a ¬za {b} {c} b⊂c =
  i⊂-cons (closed._i⊂_.l inner) (closed._i⊂_.u inner)
  where
  a' : closed.Iℚ
  a' = fst (OI->ΣCI a)
  b' : closed.Iℚ
  b' = fst (OI->ΣCI b)
  c' : closed.Iℚ
  c' = fst (OI->ΣCI c)
  b'⊂c' : b' closed.i⊂ c'
  b'⊂c' = closed.i⊂-cons (_i⊂_.l b⊂c) (_i⊂_.u b⊂c)
  inner : (a' closed.i* b') closed.i⊂ (a' closed.i* c')
  inner = closed.i*₁-preserves-⊂ a' ¬za b'⊂c'

i*₂-preserves-⊂ : {a b : Iℚ} -> a i⊂ b -> (c : Iℚ) -> (¬ (ZeroEndedI c)) -> (a i* c) i⊂ (b i* c)
i*₂-preserves-⊂ {a} {b} a⊂b c ¬zc =
  subst2 _i⊂_ (i*-commute c a) (i*-commute c b) (i*₁-preserves-⊂ c ¬zc a⊂b)

OI->CI-preserves-⊂ : {a b : Iℚ} -> a i⊂ b -> (OI->CI a closed.i⊂ OI->CI b)
OI->CI-preserves-⊂ (i⊂-cons l u) = (closed.i⊂-cons l u)


OI->CI-reflects-⊂ : {a b : Iℚ} -> (OI->CI a closed.i⊂ OI->CI b) -> a i⊂ b
OI->CI-reflects-⊂ (closed.i⊂-cons l u) = (i⊂-cons l u)


-- Growth/Shrink
module _ where
  private
    CrossZeroI : Pred Iℚ ℓ-zero
    CrossZeroI a = (Iℚ.l a) ≤ 0# × 0# ≤ (Iℚ.u a)

    data StrictClass (i : Iℚ) : Type₀ where
      p-c  : PosI i       -> StrictClass i
      n-c  : NegI i       -> StrictClass i
      cz-c : CrossZeroI i -> StrictClass i

    strict-classify : (i : Iℚ) -> StrictClass i
    strict-classify i@(Iℚ-cons l u _) =
      handle (split-< 0# l) (split-< u 0#)
      where
      handle : (0# < l ⊎ l ≤ 0#) -> (u < 0# ⊎ 0# ≤ u) -> StrictClass i
      handle (inj-l 0<l) _           = p-c 0<l
      handle (inj-r l≤0) (inj-l u<0) = n-c u<0
      handle (inj-r l≤0) (inj-r 0≤u) = cz-c (l≤0 , 0≤u)


  find-shrink-factor : {a b : Iℚ} -> a i⊂ b -> Σ[ k⁺@(k , _) ∈ ℚ⁺ ] (k < 1r × i-scale⁺ k⁺ a i⊆ b)
  find-shrink-factor {a@(Iℚ-cons al au al<au)} {b@(Iℚ-cons bl bu bl<bu)} (i⊂-cons bl<al au<bu) =
    handle (strict-classify b)
    where
    Ans = Σ[ k⁺@(k , _) ∈ ℚ⁺ ] (k < 1# × i-scale⁺ k⁺ a i⊆ b)
    p-case : PosI b -> Ans
    p-case 0<bl = (k , 0<k) , k<1 , i⊆-cons bl≤pl pu≤bu
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
      0≤au = weaken-< (trans-< 0<al al<au)

      p = i-scale⁺ (k , 0<k) a
      pl = Iℚ.l p
      pu = Iℚ.u p

      pl-path : pl == bl
      pl-path = *-assoc >=> *-right (r1/-inverse al al-inv) >=> *-right-one

      bl≤pl : bl ≤ pl
      bl≤pl = path-≤ (sym pl-path)

      pu≤au : pu ≤ au
      pu≤au = trans-≤-= (*₂-preserves-≤ (weaken-< k<1) 0≤au) *-left-one

      pu≤bu : pu ≤ bu
      pu≤bu = trans-≤ pu≤au (weaken-< au<bu)

    n-case : NegI b -> Ans
    n-case bu<0 = (k , 0<k) , k<1 , i⊆-cons bl≤pl pu≤bu
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
      al≤0 = weaken-< (trans-< al<au au<0)

      p = i-scale⁺ (k , 0<k) a
      pl = Iℚ.l p
      pu = Iℚ.u p

      pu-path : pu == bu
      pu-path = *-assoc >=> *-right (r1/-inverse au au-inv) >=> *-right-one

      pu≤bu : pu ≤ bu
      pu≤bu = path-≤ pu-path

      al≤pl : al ≤ pl
      al≤pl = trans-=-≤ (sym *-left-one) (*₂-flips-≤ (weaken-< k<1) al≤0)

      bl≤pl : bl ≤ pl
      bl≤pl = trans-≤ (weaken-< bl<al) al≤pl

    cz-case : CrossZeroI b -> Ans
    cz-case (bl≤0 , 0≤bu) = (1/2 , 0<1/2) , 1/2<1 , i⊆-cons bl≤pl pu≤bu
      where
      0≤1/2 : 0# ≤ 1/2
      0≤1/2 = weaken-< 0<1/2

      p = i-scale⁺ (1/2 , 0<1/2) a
      pl = Iℚ.l p
      pu = Iℚ.u p

      1/2bu≤bu : (1/2 * bu) ≤ bu
      1/2bu≤bu = trans-≤-= (*₂-preserves-≤ (weaken-< 1/2<1) 0≤bu) *-left-one

      pu≤1/2bu : pu ≤ (1/2 * bu)
      pu≤1/2bu = *₁-preserves-≤ 0≤1/2 (weaken-< au<bu)

      pu≤bu : pu ≤ bu
      pu≤bu = trans-≤ pu≤1/2bu 1/2bu≤bu

      bl≤1/2bl : bl ≤ (1/2 * bl)
      bl≤1/2bl = trans-=-≤ (sym *-left-one) (*₂-flips-≤ (weaken-< 1/2<1) bl≤0)

      1/2bl≤pl : (1/2 * bl) ≤ pl
      1/2bl≤pl = *₁-preserves-≤ 0≤1/2 (weaken-< bl<al)

      bl≤pl : bl ≤ pl
      bl≤pl = trans-≤ bl≤1/2bl 1/2bl≤pl


    handle : StrictClass b -> Ans
    handle (p-c p) = p-case p
    handle (n-c p) = n-case p
    handle (cz-c p) = cz-case p


module _ where
  private
    StrictCrossZeroI : Pred Iℚ ℓ-zero
    StrictCrossZeroI a = Neg (Iℚ.l a) × Pos (Iℚ.u a)

    data StrictClass' (i : Iℚ) : Type₀ where
      nn-c : NonNegI i         -> StrictClass' i
      np-c : NonPosI i         -> StrictClass' i
      cz-c : StrictCrossZeroI i -> StrictClass' i

    strict-classify' : (i : Iℚ) -> StrictClass' i
    strict-classify' i@(Iℚ-cons l u _) =
      handle (split-< l 0#) (split-< 0# u)
      where
      handle : (l < 0# ⊎ 0# ≤ l) -> (0# < u ⊎ u ≤ 0#) -> StrictClass' i
      handle (inj-r 0≤l) _           = nn-c 0≤l
      handle (inj-l l<0) (inj-r u≤0) = np-c u≤0
      handle (inj-l l<0) (inj-l 0<u) = cz-c (l<0 , 0<u)

  find-growth-factor : {a b : Iℚ} -> a i⊂ b -> Σ[ k⁺@(k , _) ∈ ℚ⁺ ] (1# < k × i-scale⁺ k⁺ a i⊆ b)
  find-growth-factor {a@(Iℚ-cons al au al<au)} {b@(Iℚ-cons bl bu bl<bu)} (i⊂-cons bl<al au<bu) =
    handle (strict-classify' b)
    where
    Ans = Σ[ k⁺@(k , _) ∈ ℚ⁺ ] (1# < k × i-scale⁺ k⁺ a i⊆ b)
    nn-case : NonNegI b -> Ans
    nn-case 0≤bl = (k , 0<k) , 1<k , i⊆-cons bl≤pl pu≤bu
      where
      0<au : 0# < au
      0<au = trans-≤-< 0≤bl (trans-< bl<al al<au)

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

      p = i-scale⁺ (k , 0<k) a
      pl = Iℚ.l p
      pu = Iℚ.u p


      pu-path : pu == bu
      pu-path = *-assoc >=> *-right (r1/-inverse au au-inv) >=> *-right-one

      pu≤bu : pu ≤ bu
      pu≤bu = path-≤ pu-path

      al≤pl : al ≤ pl
      al≤pl = trans-=-≤ (sym *-left-one) (*₂-preserves-≤ (weaken-< 1<k) 0≤al)

      bl≤pl : bl ≤ pl
      bl≤pl = trans-≤ (weaken-< bl<al) al≤pl

    np-case : NonPosI b -> Ans
    np-case bu≤0 = (k , 0<k) , 1<k , i⊆-cons bl≤pl pu≤bu
      where
      al<0 : al < 0#
      al<0 = trans-< al<au (trans-<-≤ au<bu bu≤0)

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

      p = i-scale⁺ (k , 0<k) a
      pl = Iℚ.l p
      pu = Iℚ.u p

      pl-path : pl == bl
      pl-path = *-assoc >=> *-right (r1/-inverse al al-inv) >=> *-right-one

      bl≤pl : bl ≤ pl
      bl≤pl = path-≤ (sym pl-path)

      pu≤au : pu ≤ au
      pu≤au = trans-≤-= (*₂-flips-≤ (weaken-< 1<k) au≤0)  *-left-one

      pu≤bu : pu ≤ bu
      pu≤bu = trans-≤ pu≤au (weaken-< au<bu)



    cz-case : StrictCrossZeroI b -> Ans
    cz-case (n-bl , p-bu) = (k , 0<k) , 1<k  , i⊆-cons bl≤pl pu≤bu
      where
      hbl = 1/2 * bl
      hbu = 1/2 * bu

      al' = min al hbl
      au' = max au hbu

      n-al' : Neg al'
      n-al' = Neg-≤ al' hbl (r*₁-preserves-sign (1/2 , 0<1/2) _ {neg-sign} n-bl)
                            min-≤-right

      p-au' : Pos au'
      p-au' = Pos-≤ hbu au' (r*₁-preserves-sign (1/2 , 0<1/2) _ {pos-sign} p-bu)
                            max-≤-right

      bl<al' : bl < al'
      bl<al' = min-property {P = bl <_} al hbl bl<al
                            (trans-=-< (sym *-left-one) (*₂-flips-< 1/2<1 n-bl))
      au'<bu : au' < bu
      au'<bu = max-property {P = _< bu} au hbu au<bu
                            (trans-<-= (*₂-preserves-< 1/2<1 p-bu) *-left-one)

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

      0<k : Pos k
      0<k = min-property {P = 0# <_} kl ku p-kl p-ku
      0≤k = weaken-< 0<k

      1<k : 1r < k
      1<k = min-property {P = 1# <_} kl ku 1<kl 1<ku

      p = i-scale⁺ (k , 0<k) a
      pl = Iℚ.l p
      pu = Iℚ.u p


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
                         (*₁-preserves-≤ 0≤k al'≤al))

      pu≤bu : pu ≤ bu
      pu≤bu = trans-≤-= (trans-≤ (*₁-preserves-≤ 0≤k au≤au')
                                 (*₂-preserves-≤ k≤ku (weaken-< p-au')))
                        u-path

    handle : StrictClass' b -> Ans
    handle (nn-c p) = nn-case p
    handle (np-c p) = np-case p
    handle (cz-c p) = cz-case p
