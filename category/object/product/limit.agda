{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import boolean
open import category.base
open import category.constructions.cone
open import category.constructions.cone.univalent
open import category.instances.free
open import category.instances.quiver
open import category.limits2
open import category.object.product
open import category.object.terminal
open import category.univalent
open import equality-path
open import hlevel
open import isomorphism

module category.object.product.limit where

-- Two Objects; no morphisms.
BinaryProductQ : Quiver ℓ-zero
BinaryProductQ = cons-Quiver (Boolean , isSet-Boolean) (Bot , isProp->isSet isPropBot) (\()) (\())

module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) where
  private
    module C = PreCategory C

  BinaryProductDiagram : (x y : Obj C) -> Diagram (FreeCat BinaryProductQ) C
  BinaryProductDiagram x y =
    free-diagram-on-Quiver BinaryProductQ C
      (\s -> bool-choice x y s)
      (\())

  module _ (x y : Obj C) where
    private
      D : Diagram (FreeCat BinaryProductQ) C
      D = BinaryProductDiagram x y

      bp-cone-path : {c1 c2 : Cone D} ->
                     (op : fst c1 == fst c2) ->
                     PathP (\i -> C [ op i , x ]) (ConeStr.component (snd c1) true)
                                                  (ConeStr.component (snd c2) true) ->
                     PathP (\i -> C [ op i , y ]) (ConeStr.component (snd c1) false)
                                                  (ConeStr.component (snd c2) false) ->
                     c1 == c2
      bp-cone-path op px py =
        cone-path D op \{ true -> px ; false -> py }


      raw->cone : {c : Obj C} -> (f : C [ c , x ]) -> (g : C [ c , y ]) -> Cone D
      raw->cone f g = _ , record
        { component = \{ true -> f ; false -> g }
        ; component-compose =
          \{ (edge-path (edge ()) _)
           ; (empty-path) -> C.⋆-right-id _
           }
        }

      module _ {c1 c2 : Cone D} where
        private
          o1 = fst c1
          o2 = fst c2
          module s1 = ConeStr (snd c1)
          module s2 = ConeStr (snd c2)
        ConeMor-iso : Iso (Σ[ h ∈ C [ o2 , o1 ] ] ((h ⋆⟨ C ⟩ s1.component true == s2.component true) ×
                                            (h ⋆⟨ C ⟩ s1.component false == s2.component false)))
                   (ConeMor D c2 c1)
        ConeMor-iso .Iso.fun (h , p1 , p2) = record
          { f = h
          ; component = \{ true -> sym p1 ; false -> sym p2 }
          }
        ConeMor-iso .Iso.inv cm =
          ConeMor.f cm , sym (ConeMor.component cm true) , sym (ConeMor.component cm false)
        ConeMor-iso .Iso.leftInv _ = refl
        ConeMor-iso .Iso.rightInv cm ii .ConeMor.f = ConeMor.f cm
        ConeMor-iso .Iso.rightInv cm ii .ConeMor.component true = ConeMor.component cm true
        ConeMor-iso .Iso.rightInv cm ii .ConeMor.component false = ConeMor.component cm false

      module _ (p : Product C x y) where
        private
          module p = Product p

        product->limit : Limit D
        product->limit .Terminal.obj = raw->cone p.π₁ p.π₂
        product->limit .Terminal.universal (_ , s2) =
          iso-isContr ConeMor-iso (p.universal (s2.component true) (s2.component false))
          where
          module s2 = ConeStr s2

      module _ (l : Limit D) where
        private
          obj = fst (Terminal.obj l)
          module str = ConeStr (snd (Terminal.obj l))

        limit->product : Product C x y
        limit->product .Product.obj = obj
        limit->product .Product.π₁ = str.component true
        limit->product .Product.π₂ = str.component false
        limit->product .Product.universal f g =
          iso-isContr (iso⁻¹ ConeMor-iso) (Terminal.universal l (raw->cone f g))


    limit<->product : Iso (Limit D) (Product C x y)
    limit<->product .Iso.fun = limit->product
    limit<->product .Iso.inv = product->limit
    limit<->product .Iso.rightInv _ = product-path refl refl refl
    limit<->product .Iso.leftInv _ = terminal-path (bp-cone-path refl refl refl)

  abstract
    isProp-Product : isUnivalent C -> {x y : Obj C} -> isProp (Product C x y)
    isProp-Product univ =
      iso-isProp (limit<->product _ _) (isProp-Terminal (isUnivalent-ConeC _ univ))
