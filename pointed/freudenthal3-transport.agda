{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.freudenthal3-transport where


open import base
open import pointed.base
open import cubical
open import equality-path
open import equality.square
open import equality.dependent-path
open import base
open import funext
open import isomorphism
open import sigma
open import univalence

open import additive-group
open import order
open import functions
open import nat.order
open import order.instances.nat
open import additive-group.instances.nat
open import cubical
open import equality-path
open import equality.square
open import equality.square-compose
open import equality.square-compose2
open import equality.path-composition-equivalence
open import connected
open import hlevel.base
open import hlevel.pi
open import pointed.base
open import pointed.loop-space
open import truncation.generic
open import truncation.generic.path
open import truncation.generic.map
open import equivalence.base
open import equivalence
open import connected.wedge
open import connected.reduce

open import pointed.suspension
open import pointed.freudenthal2
open import pointed.freudenthal2-transport

{-

module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) {n : Nat} (cA : isConnectedₙ n A) (a₁ : A) where
  open freudenthal A∙ cA
  open encode₂ a₁


  tencode : (p : north == south) -> encode₂ north (p >=> sym (meridian a₁)) -> encode₂ south (p >=> refl)
  tencode p = transport (\i -> encode₂ (meridian a₁ i) (ans i))
    where
    ans : ∀ (i : I) -> north == meridian a₁ i
    ans i = p >=> (\j -> meridian a₁ (~ j ∨ i))

  tencode₂ : (p₁ : north == north) (p₂ : north == south) (sq : Square p₁ p₂ refl (meridian a₁))
             -> encode₂ north p₁ -> encode₂ south p₂
  tencode₂ p₁ p₂ sq = transport (\i -> encode₂ (meridian a₁ i) (sq i))


  v₀ : encode₂ north refl
  v₀ = (∣ ★A , compPath-sym (meridian ★A) ∣)

  tencode₂-path₁ :
    tencode₂ refl (meridian a₁) (\i j -> meridian a₁ (i ∧ j)) v₀ ==
    transport (\i -> right-edge i (meridian a₁))
     (transport (\i -> base i (\j -> meridian a₁ (i ∧ j)))
       (transport (\i -> left-edge (~ i) refl) v₀))
  tencode₂-path₁ =
    transport-transP-mid (sym left-edge) base right-edge (\i t -> t (\j -> meridian a₁ (i ∧ j))) v₀

  le-rpath : (refl >=> meridian a₁ >=> sym (meridian a₁)) == refl
  le-rpath = ((\i -> refl >=> (\j -> meridian a₁ (j ∧ ~ i)) >=> (\j -> meridian a₁ (~ j ∧ ~ i))) >=>
              compPath-refl-right (refl >=> refl) >=>
              compPath-refl-right refl)

  v₁ : encode₂ north (refl >=> meridian a₁ >=> sym (meridian a₁))
  v₁ = transport (\k -> cong north-code le-rpath (~ k)) v₀


  tleft-edge-path₁ : (transport (\i -> left-edge (~ i) refl) v₀) ==
    from-north₂ (refl >=> meridian a₁) a₁ v₁
  tleft-edge-path₁ =
    (sym (transport-twice
           (ua (from-north₂ (refl >=> meridian a₁) a₁ , isEquiv-from-north₂ (refl >=> meridian a₁) a₁))
           (cong north-code (sym le-rpath))
           v₀)) >=>
    (\i -> transport-ua
             (from-north₂ (refl >=> meridian a₁) a₁ , isEquiv-from-north₂ (refl >=> meridian a₁) a₁)
             i v₁)
-}
