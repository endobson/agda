{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.unit where

open import additive-group
open import base
open import commutative-monoid
open import equality-path
open import group
open import hlevel.base
open import hlevel.sigma
open import monoid
open import semiring
open import sigma.base

module _ {ℓ : Level} {D : Type ℓ} {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}} where

  record isUnit (x : D) : Type ℓ where
    constructor is-unit
    field
      inv : D
      path : (x * inv) == 1#

  opaque
    isProp-isUnit : {x : D} -> isProp (isUnit x)
    isProp-isUnit {x} (is-unit inv₁ p₁) (is-unit inv₂ p₂) = (\i -> record
      { inv = inv-path i
      ; path = path-path i
      })
      where

      inv-path : inv₁ == inv₂
      inv-path =
        sym (*-left-one) >=>
        (cong (_* inv₁) (sym p₂ >=> *-commute)) >=>
        *-assoc >=> *-commute >=>
        (cong (_* inv₂) p₁) >=>
        *-left-one

      path-path : PathP (\i -> x * (inv-path i) == 1#) p₁ p₂
      path-path = isProp->PathP (\_ -> Semiring.isSet-Domain S _ _)

  isUnit-1# : isUnit 1#
  isUnit-1# = is-unit 1# *-left-one


module _ {ℓ : Level} {D : Type ℓ} {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}} where

  u*-closed : {x y : D} -> isUnit x -> isUnit y -> isUnit (x * y)
  u*-closed {x} {y} (is-unit 1/x px) (is-unit 1/y py) = is-unit (1/x * 1/y) p
    where
    opaque
      p : (x * y) * (1/x * 1/y) == 1#
      p = cong (_* (1/x * 1/y)) (*-commute) >=>
          *-assoc >=> (cong (y *_) (sym *-assoc)) >=>
          cong (y *_) (cong (_* 1/y) px >=> *-left-one) >=> py

  *-isUnit-split : {x y : D} -> isUnit (x * y) -> (isUnit x) × (isUnit y)
  *-isUnit-split {x} {y} (is-unit inv path) =
    (is-unit (y * inv) p₁) , (is-unit (x * inv) p₂)
    where
    opaque
      p₁ : x * (y * inv) == 1#
      p₁ = sym *-assoc >=> path
      p₂ : y * (x * inv) == 1#
      p₂ = sym *-assoc >=> *-left *-commute >=> path


module _ {ℓ : Level} (D : Type ℓ) {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}} where

  Unit : Type ℓ
  Unit = Σ D isUnit


module _ {ℓ : Level} {D : Type ℓ} {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}} where

  unit-path : {x y : Unit D} -> ⟨ x ⟩ == ⟨ y ⟩ -> x == y
  unit-path p = ΣProp-path isProp-isUnit p


module _ {ℓ : Level} {D : Type ℓ} {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}} where

  isSet-Unit : isSet (Unit D)
  isSet-Unit = isSetΣ (Semiring.isSet-Domain S) (\_ -> (isProp->isSet isProp-isUnit))

  1u : Unit D
  1u = 1# , isUnit-1#

  _u*_ : Unit D -> Unit D -> Unit D
  (x , ux) u* (y , uy) = x * y , u*-closed ux uy

  opaque
    u*-assoc : {x y z : Unit D} -> (x u* y) u* z == x u* (y u* z)
    u*-assoc = unit-path *-assoc
    u*-commute : {x y : Unit D} -> x u* y == y u* x
    u*-commute = unit-path *-commute

    u*-left-one : {x : Unit D} -> 1u u* x == x
    u*-left-one = unit-path *-left-one
    u*-right-one : {x : Unit D} -> x u* 1u == x
    u*-right-one = unit-path *-right-one

  u1/ : Unit D -> Unit D
  u1/ (x , (is-unit inv p)) = inv , (is-unit x p')
    where
    opaque
      p' : inv * x == 1#
      p' = *-commute >=> p

  opaque
    u*-left-inverse : {x : Unit D} -> (u1/ x) u* x == 1u
    u*-left-inverse {x , (is-unit inv p)} = unit-path (*-commute >=> p)
    u*-right-inverse : {x : Unit D} -> x u* (u1/ x) == 1u
    u*-right-inverse {x , (is-unit inv p)} = unit-path p

    u*-left-inverseᵉ : (x : Unit D) -> (u1/ x) u* x == 1u
    u*-left-inverseᵉ _ = u*-left-inverse
    u*-right-inverseᵉ : (x : Unit D) -> x u* (u1/ x) == 1u
    u*-right-inverseᵉ _ = u*-right-inverse


    u1/-distrib-u* : {x y : Unit D} -> u1/ (x u* y) == (u1/ x) u* (u1/ y)
    u1/-distrib-u* {x , ux} {y , uy} = unit-path refl


module _ {ℓ : Level} (D : Type ℓ) {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}} where

  Monoid-u* : Monoid (Unit D)
  Monoid-u* = record
    { ε = 1u
    ; _∙_ = _u*_
    ; ∙-assoc = u*-assoc
    ; ∙-left-ε = u*-left-one
    ; ∙-right-ε = u*-right-one
    ; isSet-Domain = isSet-Unit
    }


  CommMonoid-u* : CommMonoid (Unit D)
  CommMonoid-u* = record
    { monoid = Monoid-u*
    ; ∙-commute = u*-commute
    }

  GroupStr-u* : GroupStr (Unit D)
  GroupStr-u* = record
    { monoid = Monoid-u*
    ; inverse = u1/
    ; ∙-left-inverse = u*-left-inverse
    ; ∙-right-inverse = u*-right-inverse
    }
