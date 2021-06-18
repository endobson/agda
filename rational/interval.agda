{-# OPTIONS --cubical --safe --exact-split #-}

module rational.interval where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.minmax
open import relation
open import sign
open import sign.instances.rational


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

private
  NonNegℚ-NonPosℚ-path : {q : ℚ} -> NonNeg q -> NonPos q -> q == 0r
  NonNegℚ-NonPosℚ-path (inj-r zq) _ = (Zero-path _ zq)
  NonNegℚ-NonPosℚ-path (inj-l pq) npq = bot-elim (NonPos->¬Pos npq pq)

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
