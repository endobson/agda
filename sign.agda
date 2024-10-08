{-# OPTIONS --cubical --safe --exact-split #-}

module sign where

open import base
open import discrete
open import equality
open import hlevel
open import relation

data Sign : Type₀ where
  pos-sign : Sign
  zero-sign : Sign
  neg-sign : Sign

isNonZeroSign : Pred Sign ℓ-zero
isNonZeroSign pos-sign = Top
isNonZeroSign zero-sign = Bot
isNonZeroSign neg-sign = Top

isPosSign : Pred Sign ℓ-zero
isPosSign pos-sign = Top
isPosSign zero-sign = Bot
isPosSign neg-sign = Bot

isZeroSign : Pred Sign ℓ-zero
isZeroSign pos-sign = Bot
isZeroSign zero-sign = Top
isZeroSign neg-sign = Bot

isNegSign : Pred Sign ℓ-zero
isNegSign pos-sign = Bot
isNegSign zero-sign = Bot
isNegSign neg-sign = Top

_s*_ : Sign -> Sign -> Sign
_s*_ pos-sign  pos-sign  = pos-sign
_s*_ zero-sign pos-sign  = zero-sign
_s*_ neg-sign  pos-sign  = neg-sign
_s*_ pos-sign  zero-sign = zero-sign
_s*_ zero-sign zero-sign = zero-sign
_s*_ neg-sign  zero-sign = zero-sign
_s*_ pos-sign  neg-sign  = neg-sign
_s*_ zero-sign neg-sign  = zero-sign
_s*_ neg-sign  neg-sign  = pos-sign


s*-commute : {s1 s2 : Sign} -> (s1 s* s2) == (s2 s* s1)
s*-commute {pos-sign}  {pos-sign}  = refl
s*-commute {zero-sign} {pos-sign}  = refl
s*-commute {neg-sign}  {pos-sign}  = refl
s*-commute {pos-sign}  {zero-sign} = refl
s*-commute {zero-sign} {zero-sign} = refl
s*-commute {neg-sign}  {zero-sign} = refl
s*-commute {pos-sign}  {neg-sign}  = refl
s*-commute {zero-sign} {neg-sign}  = refl
s*-commute {neg-sign}  {neg-sign}  = refl


s*-pos-left-identity : {s : Sign} -> (pos-sign s* s) == s
s*-pos-left-identity {pos-sign} = refl
s*-pos-left-identity {zero-sign} = refl
s*-pos-left-identity {neg-sign} = refl

s*-pos-right-identity : {s : Sign} -> (s s* pos-sign) == s
s*-pos-right-identity = s*-commute >=> s*-pos-left-identity

s*-left-zero : {s : Sign} -> (zero-sign s* s) == zero-sign
s*-left-zero {pos-sign}  = refl
s*-left-zero {zero-sign} = refl
s*-left-zero {neg-sign}  = refl

s*-right-zero : {s : Sign} -> (s s* zero-sign) == zero-sign
s*-right-zero = s*-commute >=> s*-left-zero


s⁻¹_ : Sign -> Sign
s⁻¹_ = neg-sign s*_

s⁻¹-twice : {s : Sign} -> s⁻¹ (s⁻¹ s) == s
s⁻¹-twice {pos-sign} = refl
s⁻¹-twice {zero-sign} = refl
s⁻¹-twice {neg-sign} = refl

s⁻¹-injective : {s1 s2 : Sign} -> s⁻¹ s1 == s⁻¹ s2 -> s1 == s2
s⁻¹-injective {pos-sign}  {pos-sign}  p = refl
s⁻¹-injective {pos-sign}  {zero-sign} p = bot-elim (subst isNonZeroSign p tt)
s⁻¹-injective {pos-sign}  {neg-sign}  p = sym p
s⁻¹-injective {zero-sign} {pos-sign}  p = bot-elim (subst isNonZeroSign (sym p) tt)
s⁻¹-injective {zero-sign} {zero-sign} p = refl
s⁻¹-injective {zero-sign} {neg-sign}  p = bot-elim (subst isNonZeroSign (sym p) tt)
s⁻¹-injective {neg-sign}  {pos-sign}  p = sym p
s⁻¹-injective {neg-sign}  {zero-sign} p = bot-elim (subst isNonZeroSign p tt)
s⁻¹-injective {neg-sign}  {neg-sign}  p = refl


s⁻¹-extract-left : {s1 s2 : Sign} -> (s⁻¹ s1) s* s2 == s⁻¹ (s1 s* s2)
s⁻¹-extract-left {pos-sign} = cong s⁻¹_ (sym s*-pos-left-identity)
s⁻¹-extract-left {zero-sign} = s*-left-zero >=> cong s⁻¹_ (sym s*-left-zero)
s⁻¹-extract-left {neg-sign} = s*-pos-left-identity >=> sym s⁻¹-twice


s*₁-NonZero-Injective : {s1 s2 s3 : Sign} -> isNonZeroSign s1 -> (s1 s* s2) == (s1 s* s3) -> (s2 == s3)
s*₁-NonZero-Injective {pos-sign} _ p = sym s*-pos-left-identity >=> p >=> s*-pos-left-identity
s*₁-NonZero-Injective {neg-sign} _ p = s⁻¹-injective p

s*₂-NonZero-Injective : {s1 s2 s3 : Sign} -> isNonZeroSign s1 -> (s2 s* s1) == (s3 s* s1) -> (s2 == s3)
s*₂-NonZero-Injective nz path = s*₁-NonZero-Injective nz (s*-commute >=> path >=> s*-commute)

s*₁-NonZero-order2 : {s1 s2 : Sign} -> isNonZeroSign s1 -> (s1 s* (s1 s* s2)) == s2
s*₁-NonZero-order2 {pos-sign} _ = s*-pos-left-identity >=> s*-pos-left-identity
s*₁-NonZero-order2 {neg-sign} _ = s⁻¹-twice

s*₂-NonZero-order2 : {s1 s2 : Sign} -> isNonZeroSign s1 -> ((s2 s* s1) s* s1) == s2
s*₂-NonZero-order2 nz = cong (_s* _) s*-commute >=> s*-commute >=> s*₁-NonZero-order2 nz

s*-assoc : {s1 s2 s3 : Sign} -> (s1 s* s2) s* s3 == s1 s* (s2 s* s3)
s*-assoc {pos-sign} {s2} {s3} = cong (_s* s3) s*-pos-left-identity >=> sym s*-pos-left-identity
s*-assoc {zero-sign} {s2} {s3} = cong (_s* s3) s*-left-zero >=> s*-left-zero >=> sym s*-left-zero
s*-assoc {neg-sign}  = s⁻¹-extract-left

-- hlevel of Sign

Discrete-Sign : Discrete Sign
Discrete-Sign pos-sign  pos-sign  = yes refl
Discrete-Sign pos-sign  zero-sign = no (\p -> subst isPosSign p tt)
Discrete-Sign pos-sign  neg-sign  = no (\p -> subst isPosSign p tt)
Discrete-Sign zero-sign pos-sign  = no (\p -> subst isPosSign (sym p) tt)
Discrete-Sign zero-sign zero-sign = yes refl
Discrete-Sign zero-sign neg-sign  = no (\p -> subst isNegSign (sym p) tt)
Discrete-Sign neg-sign  pos-sign  = no (\p -> subst isNegSign p tt)
Discrete-Sign neg-sign  zero-sign = no (\p -> subst isNegSign p tt)
Discrete-Sign neg-sign  neg-sign  = yes refl

isSet-Sign : isSet Sign
isSet-Sign = Discrete->isSet Discrete-Sign


-- Sign structure on a type

record SignStr {ℓD : Level} (D : Type ℓD) (ℓS : Level) : Type (ℓ-max ℓD (ℓ-suc ℓS)) where
  field
    isSign : Sign -> Pred D ℓS
    isProp-isSign : (s : Sign) (x : D) -> isProp (isSign s x)
    isSign-unique : (x : D) -> (s1 s2 : Sign) -> (p1 : isSign s1 x) -> (p2 : isSign s2 x) -> s1 == s2

  Pos : Pred D ℓS
  Pos = isSign pos-sign

  Neg : Pred D ℓS
  Neg = isSign neg-sign

  Zero : Pred D ℓS
  Zero = isSign zero-sign

  NonPos : Pred D ℓS
  NonPos = Neg ∪ Zero

  NonNeg : Pred D ℓS
  NonNeg = Pos ∪ Zero

  NonZero : Pred D ℓS
  NonZero = Pos ∪ Neg


  isProp-Pos : (x : D) -> isProp (Pos x)
  isProp-Pos x = isProp-isSign pos-sign x
  isProp-Neg : (x : D) -> isProp (Neg x)
  isProp-Neg x = isProp-isSign neg-sign x
  isProp-Zero : (x : D) -> isProp (Zero x)
  isProp-Zero x = isProp-isSign zero-sign x

  isProp-NonNeg : (x : D) -> isProp (NonNeg x)
  isProp-NonNeg x =
    isProp⊎ (isProp-Pos x) (isProp-Zero x)
            (\px zx -> (subst isPosSign (isSign-unique x pos-sign zero-sign px zx) tt))

  isProp-NonPos : (x : D) -> isProp (NonPos x)
  isProp-NonPos x =
    isProp⊎ (isProp-Neg x) (isProp-Zero x)
            (\nx zx -> (subst isNegSign (isSign-unique x neg-sign zero-sign nx zx) tt))

  Pos->NonNeg : {x : D} -> Pos x -> NonNeg x
  Pos->NonNeg = inj-l

  Zero->NonNeg : {x : D} -> Zero x -> NonNeg x
  Zero->NonNeg = inj-r

  Pos->NonZero : {x : D} -> Pos x -> NonZero x
  Pos->NonZero = inj-l

  Neg->NonZero : {x : D} -> Neg x -> NonZero x
  Neg->NonZero = inj-r

  Neg->NonPos : {x : D} -> Neg x -> NonPos x
  Neg->NonPos = inj-l

  Zero->NonPos : {x : D} -> Zero x -> NonPos x
  Zero->NonPos = inj-r


  NonPos->¬Pos : {x : D} -> NonPos x -> ¬ (Pos x)
  NonPos->¬Pos {x} (inj-l nx) px =
    (subst isPosSign (isSign-unique x pos-sign neg-sign px nx) tt)
  NonPos->¬Pos {x} (inj-r zx) px =
    (subst isZeroSign (isSign-unique x zero-sign pos-sign zx px) tt)

  NonNeg->¬Neg : {x : D} -> NonNeg x -> ¬ (Neg x)
  NonNeg->¬Neg {x} (inj-l px) nx =
    (subst isPosSign (isSign-unique x pos-sign neg-sign px nx) tt)
  NonNeg->¬Neg {x} (inj-r zx) nx =
    (subst isZeroSign (isSign-unique x zero-sign neg-sign zx nx) tt)

  NonZero->¬Zero : {x : D} -> NonZero x -> ¬ (Zero x)
  NonZero->¬Zero {x} (inj-l px) zx =
    (subst isPosSign (isSign-unique x pos-sign zero-sign px zx) tt)
  NonZero->¬Zero {x} (inj-r nx) zx =
    (subst isNegSign (isSign-unique x neg-sign zero-sign nx zx) tt)

  NonNeg-NonPos->Zero : {x : D} -> NonNeg x -> NonPos x -> Zero x
  NonNeg-NonPos->Zero (inj-l p) np = bot-elim (NonPos->¬Pos np p)
  NonNeg-NonPos->Zero (inj-r z) _ = z


module _ {ℓD ℓS : Level} {D : Type ℓD} {{S : SignStr D ℓS}} where
  open SignStr S public


record DecidableSignStr {ℓD ℓS : Level} {D : Type ℓD} (S : SignStr D ℓS)
  : Type (ℓ-max ℓD (ℓ-suc ℓS)) where
  private
    module S = SignStr S

  field
    decide-sign : (x : D) -> Σ[ s ∈ Sign ] (S.isSign s x)

  sign : D -> Sign
  sign x = fst (decide-sign x)

module _ {ℓD ℓS : Level} {D : Type ℓD} {S : SignStr D ℓS} {{DS : DecidableSignStr S}} where
  open DecidableSignStr DS public
