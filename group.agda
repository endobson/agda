{-# OPTIONS --cubical --safe --exact-split #-}

module group where

open import base
open import cubical
open import commutative-monoid
open import equality
open import equivalence
open import functions
open import hlevel.base
open import hlevel.pi
open import monoid
open import isomorphism
open import funext
open import sigma.base
open import univalence

private
  record hasInverse {ℓ : Level} {D : Type ℓ} (M : Monoid D) : Type ℓ where
    open Monoid M

    field
      inverse : D -> D
      ∙-left-inverse : {x : D} -> (inverse x) ∙ x == ε
      ∙-right-inverse : {x : D} -> x ∙ (inverse x) == ε

  isProp-hasInverse : {ℓ : Level} {D : Type ℓ} {M : Monoid D} ->
    isProp (hasInverse M)
  isProp-hasInverse {D = D} {M = M} I₁ I₂ = \i -> record
    { inverse = \x -> inv-p x i
    ; ∙-left-inverse = lp i
    ; ∙-right-inverse = rp i
    }
    where
    open Monoid M
    module I₁ = hasInverse I₁
    module I₂ = hasInverse I₂

    inv-p : ∀ x -> I₁.inverse x == I₂.inverse x
    inv-p x =
      sym ∙-right-ε >=>
      ∙-right (sym I₂.∙-right-inverse) >=>
      sym ∙-assoc >=>
      ∙-left I₁.∙-left-inverse >=>
      ∙-left-ε

    lp : PathP (\i -> ∀ {x : D} -> inv-p x i ∙ x == ε) I₁.∙-left-inverse I₂.∙-left-inverse
    lp = isProp->PathP (\i -> isPropΠⁱ (\i -> isSet-Domain _ _))
    rp : PathP (\i -> ∀ {x : D} -> x ∙ inv-p x i == ε) I₁.∙-right-inverse I₂.∙-right-inverse
    rp = isProp->PathP (\i -> isPropΠⁱ (\i -> isSet-Domain _ _))


record GroupStr {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  field
    monoid : Monoid Domain
  open Monoid monoid public

  field
    inverse : Domain -> Domain
    ∙-left-inverse : {x : Domain} -> (inverse x) ∙ x == ε
    ∙-right-inverse : {x : Domain} -> x ∙ (inverse x) == ε

  hasInverse-monoid : hasInverse monoid
  hasInverse-monoid = record
    { inverse = inverse
    ; ∙-left-inverse = ∙-left-inverse
    ; ∙-right-inverse = ∙-right-inverse
    }



record AbGroupStr {ℓ : Level} (Domain : Type ℓ) : Type ℓ where
  field
    comm-monoid : CommMonoid Domain
  open CommMonoid comm-monoid public

  field
    inverse : Domain -> Domain
    ∙-left-inverse : {x : Domain} -> (inverse x) ∙ x == ε
    ∙-right-inverse : {x : Domain} -> x ∙ (inverse x) == ε

  abstract
    inverse-CMʰ : CommMonoidʰᵉ comm-monoid comm-monoid inverse
    inverse-CMʰ = record
      { monoidʰ = record
        { preserves-ε = sym ∙-right-ε >=> ∙-left-inverse
        ; preserves-∙ = preserves-∙
        }
      }
      where
      preserves-∙ : (x y : Domain) -> inverse (x ∙ y) == (inverse x) ∙ (inverse y)
      preserves-∙ x y =
        sym ∙-right-ε >=>
        ∙-right (sym ∙-right-ε >=>
                 cong2 _∙_ (sym ∙-right-inverse) (sym ∙-right-inverse) >=>
                 ∙-assoc >=>
                 ∙-right (sym ∙-assoc >=> ∙-left ∙-commute >=> ∙-assoc) >=>
                 sym ∙-assoc) >=>
        sym ∙-assoc >=>
        ∙-left ∙-left-inverse >=>
        ∙-left-ε

Group : (ℓ : Level) -> Type (ℓ-suc ℓ)
Group ℓ = Σ[ D ∈ Type ℓ ] (GroupStr D)

module Group {ℓ : Level} (G : Group ℓ) where
  open GroupStr (snd G) public

  Domain : Type ℓ
  Domain = ⟨ G ⟩

  D : Type ℓ
  D = Domain

  Str : GroupStr D
  Str = snd G

module _ {ℓ₁ ℓ₂ : Level}
         (G₁@(D₁ , GS₁) : Group ℓ₁)
         (G₂@(D₂ , GS₂) : Group ℓ₂)
  where
  private
    module G₁ = Group G₁
    module G₂ = Group G₂

  record isGroupʰ (f : G₁.D -> G₂.D) : Type (ℓ-max ℓ₁ ℓ₂) where
    field
      preserves-ε : f G₁.ε == G₂.ε
      preserves-∙ : ∀ x y -> f (x G₁.∙ y) == (f x) G₂.∙ (f y)
      preserves-inverse : ∀ x -> f (G₁.inverse x) == (G₂.inverse (f x))


  Groupʰ : Type (ℓ-max ℓ₁ ℓ₂)
  Groupʰ = Σ (G₁.D -> G₂.D) isGroupʰ


module Groupʰ {ℓ₁ ℓ₂ : Level} {G₁ : Group ℓ₁} {G₂ : Group ℓ₂}
              (h : Groupʰ G₁ G₂) where
  private
    module G₁ = Group G₁
    module G₂ = Group G₂

  open isGroupʰ (snd h) public

  f : G₁.D -> G₂.D
  f = fst h


module _ {ℓ₁ ℓ₂ : Level} {G₁ : Group ℓ₁} {G₂ : Group ℓ₂} where
  private
    module G₁ = Group G₁
    module G₂ = Group G₂

  opaque
    isProp-isGroupʰ : {f : G₁.D -> G₂.D} -> isProp (isGroupʰ G₁ G₂ f)
    isProp-isGroupʰ h₁ h₂ i = record
      { preserves-ε = isSet-D₂ _ _ h₁.preserves-ε h₂.preserves-ε i
      ; preserves-∙ = \x y -> isSet-D₂ _ _ (h₁.preserves-∙ x y) (h₂.preserves-∙ x y) i
      ; preserves-inverse = \x -> isSet-D₂ _ _ (h₁.preserves-inverse x) (h₂.preserves-inverse x) i
      }
      where
      module h₁ = isGroupʰ h₁
      module h₂ = isGroupʰ h₂

      isSet-D₂ : isSet G₂.D
      isSet-D₂ = G₂.isSet-Domain


module _ {ℓ₁ ℓ₂ : Level} {G₁ : Group ℓ₁} {G₂ : Group ℓ₂}
         (f : Groupʰ G₁ G₂) where

  record isGroupIso : Type (ℓ-max ℓ₁ ℓ₂) where
    field
      inv : Groupʰ G₂ G₁
      rightInv : ∀ x -> ⟨ f ⟩ (⟨ inv ⟩ x) == x
      leftInv : ∀ x -> ⟨ inv ⟩ (⟨ f ⟩ x) == x


module _ {ℓ₁ ℓ₂ : Level} {G₁ : Group ℓ₁} {G₂ : Group ℓ₂}
         {h@(f , fʰ) : Groupʰ G₁ G₂} where

  opaque
    isProp-isGroupIso : isProp (isGroupIso h)
    isProp-isGroupIso i₁ i₂ = \j -> record
      { inv = inv-p j
      ; rightInv = rightInv-p j
      ; leftInv = leftInv-p j
      }
      where
      module i₁ = isGroupIso i₁
      module i₂ = isGroupIso i₂

      inv-p : i₁.inv == i₂.inv
      inv-p = ΣProp-path isProp-isGroupʰ (funExt ip)
        where
        ip : ∀ x -> ⟨ i₁.inv ⟩ x == ⟨ i₂.inv ⟩ x
        ip x =
          cong ⟨ i₁.inv ⟩ (sym (i₂.rightInv x)) >=>
          i₁.leftInv (⟨ i₂.inv ⟩ x)

      rightInv-p : PathP (\i -> ∀ x -> ⟨ h ⟩ (⟨ inv-p i ⟩ x) == x) i₁.rightInv i₂.rightInv
      rightInv-p = isProp->PathP (\i -> isPropΠ (\x -> Group.isSet-Domain G₂ _ _))

      leftInv-p : PathP (\i -> ∀ x -> ⟨ inv-p i ⟩ (⟨ h ⟩ x) == x) i₁.leftInv i₂.leftInv
      leftInv-p = isProp->PathP (\i -> isPropΠ (\x -> Group.isSet-Domain G₁ _ _))



GroupIso : {ℓ₁ ℓ₂ : Level} -> (Group ℓ₁) -> (Group ℓ₂) -> Type (ℓ-max ℓ₁ ℓ₂)
GroupIso G₁ G₂ = Σ (Groupʰ G₁ G₂) isGroupIso

module GroupIso {ℓ₁ ℓ₂ : Level} {G₁ : Group ℓ₁} {G₂ : Group ℓ₂}
                (i : GroupIso G₁ G₂) where
  open isGroupIso (snd i) public

  fun : Groupʰ G₁ G₂
  fun = fst i


module _ {ℓ₁ ℓ₂ : Level} {G₁ : Group ℓ₁} {G₂ : Group ℓ₂} where

  GroupIso⁻¹ : GroupIso G₁ G₂ -> GroupIso G₂ G₁
  GroupIso⁻¹ I = I.inv , record
    { inv = I.fun
    ; rightInv = I.leftInv
    ; leftInv = I.rightInv
    }
    where
    module I = GroupIso I


module _ {ℓ : Level} {G₁ G₂ : Group ℓ} (I : GroupIso G₁ G₂)
  where
  private
    module G₁ = Group G₁
    module G₂ = Group G₂
    module I = GroupIso I

  GroupExt : G₁ == G₂
  GroupExt = Σ-path dp gs-p
    where
    d-eq : G₁.D ≃ G₂.D
    d-eq = isoToEquiv (iso ⟨ I.fun ⟩ ⟨ I.inv ⟩ I.rightInv I.leftInv)

    dp : G₁.D == G₂.D
    dp = ua d-eq

    ∙p : PathP (\i -> dp i -> dp i -> dp i) G₁._∙_ G₂._∙_
    ∙p i x y = ua-glue d-eq i (\{ (i = i0) -> x G₁.∙ y }) (inS shift)
      where
      shift : G₂.D
      shift = hcomp (\j -> \{ (i = i0) -> Groupʰ.preserves-∙ I.fun x y (~ j)
                            ; (i = i1) -> x G₂.∙ y
                            })
                    ((ua-unglue d-eq i x) G₂.∙ (ua-unglue d-eq i y))

    op-p : (G₁.D , G₁._∙_) == (G₂.D , G₂._∙_)
    op-p i = dp i , ∙p i

    monoid-p : PathP (\i -> Monoid (dp i)) G₁.monoid G₂.monoid
    monoid-p = MonoidExt op-p

    inv-p : PathP (\i -> hasInverse (monoid-p i))
              G₁.hasInverse-monoid G₂.hasInverse-monoid
    inv-p = isProp->PathP (\i -> isProp-hasInverse)


    gs-p : PathP (\i -> GroupStr (dp i)) G₁.Str G₂.Str
    gs-p i = record
      { monoid = monoid-p i
      ; inverse = hasInverse.inverse (inv-p i)
      ; ∙-left-inverse = \{x} -> hasInverse.∙-left-inverse (inv-p i) {x}
      ; ∙-right-inverse = \{x} -> hasInverse.∙-right-inverse (inv-p i) {x}
      }



module _ {ℓ₁ ℓ₂ ℓ₃ : Level} {G₁ : Group ℓ₁} {G₂ : Group ℓ₂} {G₃ : Group ℓ₃} where
  private
    module G₁ = Group G₁
    module G₂ = Group G₂
    module G₃ = Group G₃

  ∘-isGroupʰ :
    {f : G₂.D -> G₃.D} {g : G₁.D -> G₂.D} ->
    (isGroupʰ G₂ G₃ f) -> (isGroupʰ G₁ G₂ g) -> (isGroupʰ G₁ G₃ (f ∘ g))
  ∘-isGroupʰ {f = f} {g = g} fʰ gʰ = record
    { preserves-ε = (cong f gʰ.preserves-ε) >=> fʰ.preserves-ε
    ; preserves-∙ = \x y -> (cong f (gʰ.preserves-∙ x y)) >=> fʰ.preserves-∙ (g x) (g y)
    ; preserves-inverse = \x -> cong f (gʰ.preserves-inverse x) >=> fʰ.preserves-inverse (g x)
    }
    where
    module fʰ = isGroupʰ fʰ
    module gʰ = isGroupʰ gʰ

  ∘-Groupʰ : (Groupʰ G₂ G₃) -> (Groupʰ G₁ G₂) -> (Groupʰ G₁ G₃)
  ∘-Groupʰ (f , fʰ) (g , gʰ) = f ∘ g , ∘-isGroupʰ fʰ gʰ

  _>Groupʰ>_ : (Groupʰ G₁ G₂) -> (Groupʰ G₂ G₃) -> (Groupʰ G₁ G₃)
  f >Groupʰ> g = ∘-Groupʰ g f


module _ {ℓ : Level} (G : Group ℓ) where
  private
    module G = Group G

  record isAbelian  : Type ℓ where
    field
      ∙-commute : ∀ (a b : G.D) -> a G.∙ b == b G.∙ a
