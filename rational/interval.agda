{-# OPTIONS --cubical --safe --exact-split #-}

module rational.interval where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order-switch
open import rational.minmax
open import relation hiding (_⊆_)
open import sign
open import sign.instances.rational

private
  variable
    ℓ : Level

Iℚ : Type₀
Iℚ = ℚ × ℚ

Iℚ-l : Iℚ -> ℚ
Iℚ-l (l , _) = l

Iℚ-u : Iℚ -> ℚ
Iℚ-u (_ , u) = u

_i+_ : Iℚ -> Iℚ -> Iℚ
_i+_ (l1 , u1) (l2 , u2) = (l1 r+ l2 , u1 r+ u2)

_i≤_ : Rel Iℚ ℓ-zero
_i≤_ (l1 , u1) (l2 , u2) = l1 ℚ≤ l2 × u1 ℚ≤ u2

i-_ : Iℚ -> Iℚ
i-_ (l1 , u1) = (r- u1 , r- l1)

i-conj : Iℚ -> Iℚ
i-conj (l1 , u1) = (u1 , l1)

ℚ->Iℚ : ℚ -> Iℚ
ℚ->Iℚ q = q , q

0i : Iℚ
0i = ℚ->Iℚ 0r

_i∙_ : Iℚ -> Iℚ -> Iℚ
_i∙_ (l1 , u1) (l2 , u2) = (l1 r* l2 , u1 r* u2)

i-cross : Iℚ -> Iℚ -> Iℚ
i-cross (l1 , u1) (l2 , u2) = minℚ (l1 r* u2) (l2 r* u1) , maxℚ (l1 r* l2) (u1 r* u2)


NonNegI : Pred Iℚ ℓ-zero
NonNegI (l , u) = NonNeg l × NonNeg u
NonPosI : Pred Iℚ ℓ-zero
NonPosI (l , u) = NonPos l × NonPos u
ForwardZeroI : Pred Iℚ ℓ-zero
ForwardZeroI (l , u) = NonPos l × NonNeg u
BackwardZeroI : Pred Iℚ ℓ-zero
BackwardZeroI (l , u) = NonNeg l × NonPos u

ForwardI : Pred Iℚ ℓ-zero
ForwardI (l , u) = l ℚ≤ u

BackwardI : Pred Iℚ ℓ-zero
BackwardI (l , u) = u ℚ≤ l

private
  NonNegℚ-NonPosℚ-path : {q : ℚ} -> NonNeg q -> NonPos q -> q == 0r
  NonNegℚ-NonPosℚ-path nn np = antisym-≤ (NonPos-≤0 _ np) (NonNeg-0≤ _ nn)

NonNeg-ForwardZero-path : {a : Iℚ} -> NonNegI a -> ForwardZeroI a -> (Iℚ-l a) == 0r
NonNeg-ForwardZero-path (nn-l , _) (np-l , _) = NonNegℚ-NonPosℚ-path nn-l np-l

NonNeg-BackwardZero-path : {a : Iℚ} -> NonNegI a -> BackwardZeroI a -> (Iℚ-u a) == 0r
NonNeg-BackwardZero-path (_ , nn-u) (_ , np-u) = NonNegℚ-NonPosℚ-path nn-u np-u


NonNeg-NonPos-path₁ : {a : Iℚ} -> NonNegI a -> NonPosI a -> (Iℚ-l a) == 0r
NonNeg-NonPos-path₁ (nn-l , _) (np-l , _) = NonNegℚ-NonPosℚ-path nn-l np-l

NonNeg-NonPos-path₂ : {a : Iℚ} -> NonNegI a -> NonPosI a -> (Iℚ-u a) == 0r
NonNeg-NonPos-path₂ (_ , nn-u) (_ , np-u) = NonNegℚ-NonPosℚ-path nn-u np-u

NonNeg-NonPos-path : {a : Iℚ} -> NonNegI a -> NonPosI a -> a == 0i
NonNeg-NonPos-path nn np = cong2 _,_ (NonNeg-NonPos-path₁ nn np) (NonNeg-NonPos-path₂ nn np)

NonPos-ForwardZero-path : {a : Iℚ} -> NonPosI a -> ForwardZeroI a -> (Iℚ-u a) == 0r
NonPos-ForwardZero-path (_ , np-u) (_ , nn-u) = NonNegℚ-NonPosℚ-path nn-u np-u

NonPos-BackwardZero-path : {a : Iℚ} -> NonPosI a -> BackwardZeroI a -> (Iℚ-l a) == 0r
NonPos-BackwardZero-path (np-l , _) (nn-l , _) = NonNegℚ-NonPosℚ-path nn-l np-l

ForwardZero-BackwardZero-path₁ : {a : Iℚ} -> ForwardZeroI a -> BackwardZeroI a -> (Iℚ-l a) == 0r
ForwardZero-BackwardZero-path₁ (np-l , _) (nn-l , _) = NonNegℚ-NonPosℚ-path nn-l np-l

ForwardZero-BackwardZero-path₂ : {a : Iℚ} -> ForwardZeroI a -> BackwardZeroI a -> (Iℚ-u a) == 0r
ForwardZero-BackwardZero-path₂ (_ , nn-u) (_ , np-u) = NonNegℚ-NonPosℚ-path nn-u np-u

ForwardZero-BackwardZero-path : {a : Iℚ} -> ForwardZeroI a -> BackwardZeroI a -> a == 0i
ForwardZero-BackwardZero-path nn np =
  cong2 _,_ (ForwardZero-BackwardZero-path₁ nn np) (ForwardZero-BackwardZero-path₂ nn np)

-- Inclusion

_⊆_ : Iℚ -> Iℚ -> Type₀
_⊆_ (al , au) (bl , bu) = bl ℚ≤ al × au ℚ≤ bu

data ΣI (a : Iℚ) (P : Pred ℚ ℓ) : Type (ℓ-suc ℓ) where
  ΣI-∃ : (x : ℚ) -> (Iℚ-l a) ℚ≤ x -> x ℚ≤ (Iℚ-u a) -> P x -> ΣI a P
  ΣI-∀ : (Iℚ-u a ℚ≤ Iℚ-l a) -> (f : (x : ℚ) -> (Iℚ-u a) ℚ≤ x -> x ℚ≤ (Iℚ-l a) -> P x) -> ΣI a P

data ∀I (a : Iℚ) (P : Pred ℚ ℓ) : Type (ℓ-suc ℓ) where
  ∀I-∀ : (Iℚ-l a ℚ≤ Iℚ-u a) -> (f : (x : ℚ) -> (Iℚ-l a) ℚ≤ x -> x ℚ≤ (Iℚ-u a) -> P x) -> ∀I a P
  ∀I-∃ : (x : ℚ) -> (Iℚ-u a) ℚ≤ x -> x ℚ≤ (Iℚ-l a) -> P x -> ∀I a P

weaken-ΣI : {P : Pred ℚ ℓ} {a b : Iℚ} -> a ⊆ b -> ΣI a P -> ΣI b P
weaken-ΣI {P = P} {al , au} {bl , bu} (bl≤al , au≤bu) (ΣI-∃ x al≤x x≤au px) =
  (ΣI-∃ x (trans-ℚ≤ {bl} {al} {x} bl≤al al≤x) (trans-ℚ≤ {x} {au} {bu} x≤au au≤bu) px)
weaken-ΣI {P = P} {al , au} {bl , bu} (bl≤al , au≤bu) (ΣI-∀ au≤al f) =
  handle (split-< bl bu) (split-< bl au)
  where
  handle : (bl < bu) ⊎ (bu ℚ≤ bl) -> (bl < au) ⊎ (au ℚ≤ bl) -> _
  handle (inj-l bl<bu) (inj-l bl<au) = ΣI-∃ au (weaken-< bl<au) au≤bu (f au (refl-ℚ≤ {au}) au≤al)
  handle (inj-l bl<bu) (inj-r au≤bl) = ΣI-∃ bl (refl-ℚ≤ {bl}) (weaken-< bl<bu) (f bl au≤bl bl≤al)
  handle (inj-r bu≤bl) _ =
    ΣI-∀ bu≤bl (\ x bu≤x x≤bl -> f x (trans-ℚ≤ {au} {bu} {x} au≤bu bu≤x)
                                     (trans-ℚ≤ {x} {bl} {al} x≤bl bl≤al))


weaken-∀I : {P : Pred ℚ ℓ} {a b : Iℚ} -> a ⊆ b -> ∀I b P -> ∀I a P
weaken-∀I {P = P} {al , au} {bl , bu} (bl≤al , au≤bu) (∀I-∃ x bu≤x x≤bl px) =
 (∀I-∃ x (trans-ℚ≤ {au} {bu} {x} au≤bu bu≤x) (trans-ℚ≤ {x} {bl} {al} x≤bl bl≤al) px)
weaken-∀I {P = P} {al , au} {bl , bu} (bl≤al , au≤bu) (∀I-∀ bl≤bu f) =
  handle (split-< al au) (split-< bl au)
  where
  handle : (al < au) ⊎ (au ℚ≤ al) -> (bl < au) ⊎ (au ℚ≤ bl) -> _
  handle (inj-r au≤al) (inj-l bl<au) = ∀I-∃ au (refl-ℚ≤ {au}) au≤al (f au (weaken-< bl<au) au≤bu)
  handle (inj-r au≤al) (inj-r au≤bl) = ∀I-∃ bl au≤bl bl≤al (f bl (refl-ℚ≤ {bl}) bl≤bu)
  handle (inj-l al<au) _ =
    ∀I-∀ (weaken-< al<au) (\ x al≤x x≤au -> f x (trans-ℚ≤ {bl} {al} {x} bl≤al al≤x)
                                                (trans-ℚ≤ {x} {au} {bu} x≤au au≤bu))



-- Properties

i+-commute : (a b : Iℚ) -> a i+ b == b i+ a
i+-commute (l1 , u1) (l2 , u2) = cong2 _,_ (r+-commute l1 l2) (r+-commute u1 u2)

i+-assoc : (a b c : Iℚ) -> (a i+ b) i+ c == a i+ (b i+ c)
i+-assoc (l1 , u1) (l2 , u2) (l3 , u3) = cong2 _,_ (r+-assoc l1 l2 l3) (r+-assoc u1 u2 u3)

i+-inverse : (a : Iℚ) -> (a i+ (i- (i-conj a))) == 0i
i+-inverse (l , u) = cong2 _,_ (r+-inverse l) (r+-inverse u)

i+-right-zero : (a : Iℚ) -> a i+ 0i == a
i+-right-zero (l , u) = cong2 _,_ (r+-right-zero l) (r+-right-zero u)

i∙-commute : (a b : Iℚ) -> a i∙ b == b i∙ a
i∙-commute (l1 , u1) (l2 , u2) = cong2 _,_ (r*-commute l1 l2) (r*-commute u1 u2)

i∙-assoc : (a b c : Iℚ) -> (a i∙ b) i∙ c == a i∙ (b i∙ c)
i∙-assoc (l1 , u1) (l2 , u2) (l3 , u3) = cong2 _,_ (r*-assoc l1 l2 l3) (r*-assoc u1 u2 u3)

i∙-right-zero : (a : Iℚ) -> (a i∙ 0i) == 0i
i∙-right-zero (l , u) = cong2 _,_ (r*-right-zero l) (r*-right-zero u)

i∙-left-zero : (a : Iℚ) -> (0i i∙ a) == 0i
i∙-left-zero (l , u) = cong2 _,_ (r*-left-zero l) (r*-left-zero u)


i-cross-commute : (a b : Iℚ) -> i-cross a b == i-cross b a
i-cross-commute a b = cong2 _,_ minℚ-commute (cong2 maxℚ (r*-commute _ _) (r*-commute _ _))

-- Interval properties

i-conj-Forward : (a : Iℚ) -> ForwardI a -> BackwardI (i-conj a)
i-conj-Forward a f = f
i-conj-Backward : (a : Iℚ) -> BackwardI a -> ForwardI (i-conj a)
i-conj-Backward a b = b
i-conj-ForwardZero : (a : Iℚ) -> ForwardZeroI a -> BackwardZeroI (i-conj a)
i-conj-ForwardZero a (np , nn) = (nn , np)
i-conj-BackwardZero : (a : Iℚ) -> BackwardZeroI a -> ForwardZeroI (i-conj a)
i-conj-BackwardZero a (nn , np) = (np , nn)
i-conj-NonNeg : (a : Iℚ) -> NonNegI a -> NonNegI (i-conj a)
i-conj-NonNeg a (nn1 , nn2) = (nn2 , nn1)
i-conj-NonPos : (a : Iℚ) -> NonPosI a -> NonPosI (i-conj a)
i-conj-NonPos a (np1 , np2) = (np2 , np1)

i∙-NonNeg-NonNeg : (a b : Iℚ) -> NonNegI a -> NonNegI b -> NonNegI (a i∙ b)
i∙-NonNeg-NonNeg a b (nn-al , nn-au) (nn-bl , nn-bu) =
  r*-NonNeg-NonNeg nn-al nn-bl , r*-NonNeg-NonNeg nn-au nn-bu

i∙-NonPos-NonPos : (a b : Iℚ) -> NonPosI a -> NonPosI b -> NonNegI (a i∙ b)
i∙-NonPos-NonPos a b (np-al , np-au) (np-bl , np-bu) =
  r*-NonPos-NonPos np-al np-bl , r*-NonPos-NonPos np-au np-bu

i∙-NonNeg-NonPos : (a b : Iℚ) -> NonNegI a -> NonPosI b -> NonPosI (a i∙ b)
i∙-NonNeg-NonPos a b (nn-al , nn-au) (np-bl , np-bu) =
  r*-NonNeg-NonPos nn-al np-bl , r*-NonNeg-NonPos nn-au np-bu

i∙-NonPos-NonNeg : (a b : Iℚ) -> NonPosI a -> NonNegI b -> NonPosI (a i∙ b)
i∙-NonPos-NonNeg a b (np-al , np-au) (nn-bl , nn-bu) =
  r*-NonPos-NonNeg np-al nn-bl , r*-NonPos-NonNeg np-au nn-bu

i∙-NonNeg-ForwardZero : (a b : Iℚ) -> NonNegI a -> ForwardZeroI b -> ForwardZeroI (a i∙ b)
i∙-NonNeg-ForwardZero a b (nn-al , nn-au) (np-bl , nn-bu) =
  r*-NonNeg-NonPos nn-al np-bl , r*-NonNeg-NonNeg nn-au nn-bu

i∙-NonNeg-BackwardZero : (a b : Iℚ) -> NonNegI a -> BackwardZeroI b -> BackwardZeroI (a i∙ b)
i∙-NonNeg-BackwardZero a b (nn-al , nn-au) (nn-bl , np-bu) =
  r*-NonNeg-NonNeg nn-al nn-bl , r*-NonNeg-NonPos nn-au np-bu


--
