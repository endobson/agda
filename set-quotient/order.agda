{-# OPTIONS --cubical --safe --exact-split #-}

module set-quotient.order where

open import base
open import equivalence
open import hlevel
open import hlevel.htype
open import isomorphism
open import order
open import relation
open import set-quotient
open import sigma.base
open import univalence

private
  module _ {ℓD ℓ~ ℓ≼ : Level} {D : Type ℓD} {D~ : Rel D ℓ~} {D≼ : Rel D ℓ≼}
    {{PO : isPreOrder D≼}}
    (sym-D~ : Symmetric D~)
    (trans-~-≼ : ∀ {x} {y} {z} -> D~ x y -> y ≼ z -> x ≼ z)
    (trans-≼-~ : ∀ {x} {y} {z} -> x ≼ y -> D~ y z -> x ≼ z)
    (antisym-≼-~ : ∀ {x} {y} -> x ≼ y -> y ≼ x -> D~ x y)
    where
    private
      SetQuotient≤'Σ : (D / D~) -> (D / D~) -> hProp ℓ≼
      SetQuotient≤'Σ = SetQuotientElim.rec2 isSet-hProp val case1 case2
        where
        val : (x y : D) -> hProp ℓ≼
        val x y = x ≼ y , isProp-≼

        opaque
          case1 : (x y z : D) -> D~ x y -> val x z == val y z
          case1 x y z x~y = ΣProp-path isProp-isProp (isoToPath ≼-iso)
            where
            ≼-iso : Iso (x ≼ z) (y ≼ z)
            ≼-iso .Iso.fun x≼z = trans-~-≼ (sym-D~ x~y) x≼z
            ≼-iso .Iso.inv y≼z = trans-~-≼ x~y y≼z
            ≼-iso .Iso.rightInv _ = isProp-≼ _ _
            ≼-iso .Iso.leftInv _ = isProp-≼ _ _

          case2 : (x y z : D) -> D~ y z -> val x y == val x z
          case2 x y z y~z = ΣProp-path isProp-isProp (isoToPath ≼-iso)
            where
            ≼-iso : Iso (x ≼ y) (x ≼ z)
            ≼-iso .Iso.fun x≼y = trans-≼-~ x≼y y~z
            ≼-iso .Iso.inv x≼z = trans-≼-~ x≼z (sym-D~ y~z)
            ≼-iso .Iso.rightInv _ = isProp-≼ _ _
            ≼-iso .Iso.leftInv _ = isProp-≼ _ _


    SetQuotient≤' : Rel (D / D~) ℓ≼
    SetQuotient≤' x y = fst (SetQuotient≤'Σ x y)

    private
      trans-SetQuotient≤' : ∀ x y z -> SetQuotient≤' x y -> SetQuotient≤' y z -> SetQuotient≤' x z
      trans-SetQuotient≤' =
        SetQuotientElim.elimProp3
          (\x y z -> isPropΠ2 (\_ _ -> snd (SetQuotient≤'Σ x z)))
          (\x y z -> trans-≼)

      refl-SetQuotient≤' : ∀ x -> SetQuotient≤' x x
      refl-SetQuotient≤' =
        SetQuotientElim.elimProp
          (\x -> snd (SetQuotient≤'Σ x x))
          (\x -> refl-≼)


      antisym-SetQuotient≤' : ∀ x y -> SetQuotient≤' x y -> SetQuotient≤' y x -> x == y
      antisym-SetQuotient≤' =
        SetQuotientElim.elimProp2
          (\x y -> isPropΠ2 (\_ _ -> squash/ x y))
          (\x y x≼y y≼x -> eq/ x y (antisym-≼-~ x≼y y≼x))

    opaque
      isPartialOrder-SetQuotient≤' : isPartialOrder SetQuotient≤'
      isPartialOrder-SetQuotient≤' = record
        { isProp-≤ = \{x} {y} -> snd (SetQuotient≤'Σ x y)
        ; trans-≤ = \{x} {y} {z} -> trans-SetQuotient≤' x y z
        ; refl-≤ = \{x} -> refl-SetQuotient≤' x
        ; antisym-≤ = \{x} {y} -> antisym-SetQuotient≤' x y
        }


module _ {ℓD ℓ~ ℓ≼ : Level} {D : Type ℓD} {D~ : Rel D ℓ~} {D≼ : Rel D ℓ≼}
  {{PO : isPreOrder D≼}}
  (eq : ∀ x y -> D~ x y ≃ ((x ≼ y) × (y ≼ x)))
  where

  private
    opaque
      sym-~ : Symmetric D~
      sym-~ {x} {y} x~y = eqInv (eq y x) ((\ ((a , b) : ((x ≼ y) × (y ≼ x))) -> (b , a))
                                          (eqFun (eq x y) x~y))

      trans-~-≼ : ∀ {x} {y} {z} -> D~ x y -> y ≼ z -> x ≼ z
      trans-~-≼ {x} {y} {z} x~y y≼z = trans-≼ (proj₁ (eqFun (eq x y) x~y)) y≼z
      trans-≼-~ : ∀ {x} {y} {z} -> x ≼ y -> D~ y z -> x ≼ z
      trans-≼-~ {x} {y} {z} x≼y y~z = trans-≼ x≼y (proj₁ (eqFun (eq y z) y~z))

      antisym-≼-~ : ∀ {x} {y} -> x ≼ y -> y ≼ x -> D~ x y
      antisym-≼-~ {x} {y} x≼y y≼x = eqInv (eq x y) (x≼y , y≼x)

  SetQuotient≤ : Rel (D / D~) ℓ≼
  SetQuotient≤ = SetQuotient≤' sym-~ trans-~-≼ trans-≼-~ antisym-≼-~

  isPartialOrder-SetQuotient≤ : isPartialOrder SetQuotient≤
  isPartialOrder-SetQuotient≤ = isPartialOrder-SetQuotient≤' sym-~ trans-~-≼ trans-≼-~ antisym-≼-~
