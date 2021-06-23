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

NonNegI : Pred Iℚ ℓ-zero
NonNegI (Iℚ-cons l _ _) = NonNeg l
NonPosI : Pred Iℚ ℓ-zero
NonPosI (Iℚ-cons _ u _) = NonPos u
CrossZeroI : Pred Iℚ ℓ-zero
CrossZeroI (Iℚ-cons l u _) = NonPos l × NonNeg u

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

i-scale : ℚ -> Iℚ -> Iℚ
i-scale k (Iℚ-cons l u l≤u) =
  Iℚ-cons min max (trans-ℚ≤ {min} {k r* l} {max} (minℚ-≤-left (k r* l) (k r* u))
                                                 (maxℚ-≤-left (k r* l) (k r* u)))
  where
  min = minℚ (k r* l) (k r* u)
  max = maxℚ (k r* l) (k r* u)

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
