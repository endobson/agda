{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.grid-aligned where

open import apartness.instances.rational
open import base
open import equality-path
open import hlevel.base
open import hlevel.sigma
open import int.base
open import order
open import rational
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.point
open import rational.integer
open import rational.order
open import semidomain
open import semidomain.instances.rational
open import semiring
open import sigma.base

record isGridAligned-Rel {ℓ : Level} (A : Type ℓ) (ℓR : Level) : Type (ℓ-max ℓ (ℓ-suc ℓR)) where
  field
    R : ℚ⁺ -> A -> Type ℓR
    isProp-R : ∀ q a -> isProp (R q a)

isGridAligned : {ℓA ℓR : Level} {A : Type ℓA} -> {{isGridAligned-Rel A ℓR}} -> ℚ⁺ -> A -> Type ℓR
isGridAligned {{GA}} = isGridAligned-Rel.R GA

isProp-isGridAligned : {ℓA ℓR : Level} {A : Type ℓA} -> {{_ : isGridAligned-Rel A ℓR}} ->
                       ∀ q a -> isProp (isGridAligned q a)
isProp-isGridAligned {{GA}} = isGridAligned-Rel.isProp-R GA


record isGridAligned₂-Rel {ℓ : Level} (A : Type ℓ) (ℓR : Level) : Type (ℓ-max ℓ (ℓ-suc ℓR)) where
  field
    R : ℚ⁺ -> ℚ⁺ -> A -> Type ℓR
    isProp-R : ∀ q₁ q₂ a -> isProp (R q₁ q₂ a)

isGridAligned₂ : {ℓA ℓR : Level} {A : Type ℓA} -> {{isGridAligned₂-Rel A ℓR}} -> ℚ⁺ -> ℚ⁺ -> A -> Type ℓR
isGridAligned₂ {{GA}} = isGridAligned₂-Rel.R GA

isProp-isGridAligned₂ : {ℓA ℓR : Level} {A : Type ℓA} -> {{_ : isGridAligned₂-Rel A ℓR}} ->
                        ∀ q₁ q₂ a -> isProp (isGridAligned₂ q₁ q₂ a)
isProp-isGridAligned₂ {{GA}} = isGridAligned₂-Rel.isProp-R GA


private
  isGridAligned-Rel-GA₂ : {ℓ ℓR : Level} {A : Type ℓ} {{_ : isGridAligned₂-Rel A ℓR}} ->
                          isGridAligned-Rel A ℓR
  isGridAligned-Rel-GA₂ {{GA₂}} = record
    { R = \q a -> isGridAligned₂ q q a
    ; isProp-R = \q a -> isProp-isGridAligned₂ q q a
    }


instance
  isGridAligned-Rel-ℚ : isGridAligned-Rel ℚ ℓ-zero
  isGridAligned-Rel-ℚ = record
    { R = isGridAlignedℚ
    ; isProp-R = isProp-isGridAlignedℚ
    }
    where
    isGridAlignedℚ : ℚ⁺ -> ℚ -> Type₀
    isGridAlignedℚ (u , _) q = Σ[ n ∈ ℤ ] (ℤ->ℚ n * u == q)

    opaque
      isProp-isGridAlignedℚ : (u : ℚ⁺) (q : ℚ) -> isProp (isGridAlignedℚ u q)
      isProp-isGridAlignedℚ (_ , 0<u) q (n₁ , p₁) (n₂ , p₂) =
        ΣProp-path (isSetℚ _ _) n₁=n₂
        where
        n₁=n₂ : n₁ == n₂
        n₁=n₂ =
          isInjective-ℤ->ℚ
            (*₂-reflects-=
              (\p -> irrefl-path-< (sym p) 0<u)
              (p₁ >=> (sym p₂)))


  isGridAligned₂-Rel-Point : isGridAligned₂-Rel Point ℓ-zero
  isGridAligned₂-Rel-Point = record
    { R = isGridAligned₂Point
    ; isProp-R = \ux uy (x , y) -> isProp× (isProp-isGridAligned ux x) (isProp-isGridAligned uy y)
    }
    where
    isGridAligned₂Point : ℚ⁺ -> ℚ⁺ -> Point -> Type₀
    isGridAligned₂Point ux uy (x , y) = isGridAligned ux x × isGridAligned uy y
  isGridAligned-Rel-Point : isGridAligned-Rel Point ℓ-zero
  isGridAligned-Rel-Point = isGridAligned-Rel-GA₂

  isGridAligned₂-Rel-Box : isGridAligned₂-Rel Box ℓ-zero
  isGridAligned₂-Rel-Box = record
    { R = isGridAligned₂Box
    ; isProp-R = isProp-isGridAligned₂Box
    }
    where
    isGridAligned₂Box : ℚ⁺ -> ℚ⁺ -> Box -> Type₀
    isGridAligned₂Box ux uy B =
      isGridAligned ux B.left ×
      isGridAligned ux B.right ×
      isGridAligned uy B.bottom ×
      isGridAligned uy B.top
      where
      module B = Box B
    isProp-isGridAligned₂Box : ∀ ux uy B -> isProp (isGridAligned₂Box ux uy B)
    isProp-isGridAligned₂Box ux uy B =
      isProp× (isProp-isGridAligned ux B.left)
       (isProp× (isProp-isGridAligned ux B.right)
        (isProp× (isProp-isGridAligned uy B.bottom)
                 (isProp-isGridAligned uy B.top)))
      where
      module B = Box B
  isGridAligned-Rel-Box : isGridAligned-Rel Box ℓ-zero
  isGridAligned-Rel-Box = isGridAligned-Rel-GA₂

  isGridAligned₂-Rel-Boxes : {ℓ : Level} -> isGridAligned₂-Rel (Boxes ℓ) ℓ
  isGridAligned₂-Rel-Boxes = record
    { R = isGridAligned₂Boxes
    ; isProp-R = isProp-isGridAligned₂Boxes
    }
    where
    isGridAligned₂Boxes : {ℓ : Level} -> ℚ⁺ -> ℚ⁺ -> Boxes ℓ -> Type ℓ
    isGridAligned₂Boxes ux uy B =
      ∀ (i : B.I) -> isGridAligned₂ ux uy (B.box i)
      where
      module B = Boxes B
    opaque
      isProp-isGridAligned₂Boxes : {ℓ : Level} -> (ux uy : ℚ⁺) -> (B : Boxes ℓ) ->
                                   isProp (isGridAligned₂Boxes ux uy B)
      isProp-isGridAligned₂Boxes ux uy B =
        isPropΠ (\i -> isProp-isGridAligned₂ ux uy (Boxes.box B i))
  isGridAligned-Rel-Boxes : {ℓ : Level} -> isGridAligned-Rel (Boxes ℓ) ℓ
  isGridAligned-Rel-Boxes = isGridAligned-Rel-GA₂
