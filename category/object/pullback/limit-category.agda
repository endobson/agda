{-# OPTIONS --cubical --safe --exact-split #-}

module category.object.pullback.limit-category where

open import base
open import category.base
open import equality.identity-system
open import equality.prop-identity-system
open import hlevel
open import isomorphism
open import relation

-- This is the category the pullback is a limit over.

data PullbackC-Obj : Type ℓ-zero where
  nodeA : PullbackC-Obj
  nodeB : PullbackC-Obj
  nodeC : PullbackC-Obj

private
  PObj : Type ℓ-zero
  PObj = PullbackC-Obj

  ObjCover : PullbackC-Obj -> PullbackC-Obj -> hProp ℓ-zero
  ObjCover nodeA nodeA = Top , isPropTop
  ObjCover nodeA nodeB = Bot , isPropBot
  ObjCover nodeA nodeC = Bot , isPropBot
  ObjCover nodeB nodeA = Bot , isPropBot
  ObjCover nodeB nodeB = Top , isPropTop
  ObjCover nodeB nodeC = Bot , isPropBot
  ObjCover nodeC nodeA = Bot , isPropBot
  ObjCover nodeC nodeB = Bot , isPropBot
  ObjCover nodeC nodeC = Top , isPropTop

  ObjCover' : PullbackC-Obj -> PullbackC-Obj -> Type ℓ-zero
  ObjCover' x y = fst (ObjCover x y)


data PullbackC-Mor : Type ℓ-zero where
  pathAA : PullbackC-Mor
  pathAC : PullbackC-Mor
  pathBB : PullbackC-Mor
  pathBC : PullbackC-Mor
  pathCC : PullbackC-Mor

private
  mor-source : PullbackC-Mor -> PObj
  mor-source pathAA = nodeA
  mor-source pathAC = nodeA
  mor-source pathBB = nodeB
  mor-source pathBC = nodeB
  mor-source pathCC = nodeC

  mor-target : PullbackC-Mor -> PObj
  mor-target pathAA = nodeA
  mor-target pathAC = nodeC
  mor-target pathBB = nodeB
  mor-target pathBC = nodeC
  mor-target pathCC = nodeC

opaque
  isSet-PullbackC-Mor : isSet PullbackC-Mor
  isSet-PullbackC-Mor = PropIdentitySystem.isSet-A (record
    { R' = PCover
    ; r = reflCover
    ; to-path = cover->path _ _
    })
    where

    PCover : (e1 e2 : PullbackC-Mor) -> hProp ℓ-zero
    PCover pathAA pathAA = Top , isPropTop
    PCover pathAA pathAC = Bot , isPropBot
    PCover pathAA pathBB = Bot , isPropBot
    PCover pathAA pathBC = Bot , isPropBot
    PCover pathAA pathCC = Bot , isPropBot
    PCover pathAC pathAA = Bot , isPropBot
    PCover pathAC pathAC = Top , isPropTop
    PCover pathAC pathBB = Bot , isPropBot
    PCover pathAC pathBC = Bot , isPropBot
    PCover pathAC pathCC = Bot , isPropBot
    PCover pathBB pathAA = Bot , isPropBot
    PCover pathBB pathAC = Bot , isPropBot
    PCover pathBB pathBB = Top , isPropTop
    PCover pathBB pathBC = Bot , isPropBot
    PCover pathBB pathCC = Bot , isPropBot
    PCover pathBC pathAA = Bot , isPropBot
    PCover pathBC pathAC = Bot , isPropBot
    PCover pathBC pathBB = Bot , isPropBot
    PCover pathBC pathBC = Top , isPropTop
    PCover pathBC pathCC = Bot , isPropBot
    PCover pathCC pathAA = Bot , isPropBot
    PCover pathCC pathAC = Bot , isPropBot
    PCover pathCC pathBB = Bot , isPropBot
    PCover pathCC pathBC = Bot , isPropBot
    PCover pathCC pathCC = Top , isPropTop

    reflCover : (x : PullbackC-Mor) -> ⟨ PCover x x ⟩
    reflCover pathAA = tt
    reflCover pathAC = tt
    reflCover pathBB = tt
    reflCover pathBC = tt
    reflCover pathCC = tt

    cover->path : (x y : PullbackC-Mor) -> ⟨ PCover x y ⟩ -> x == y
    cover->path pathAA pathAA _ = refl
    cover->path pathAC pathAC _ = refl
    cover->path pathBB pathBB _ = refl
    cover->path pathBC pathBC _ = refl
    cover->path pathCC pathCC _ = refl


data PMor (x y : PObj) : Type ℓ-zero where
  pmor : (m : PullbackC-Mor) -> { ObjCover' x (mor-source m) } ->
         { ObjCover' (mor-target m) y } ->
         PMor x y

private
  isSet-PMor : {x y : PObj} -> isSet (PMor x y)
  isSet-PMor {x} {y} =
    iso-isSet
      (iso⁻¹ isoPMor)
      (isSetΣ isSet-PullbackC-Mor
        (\m -> (isProp->isSet (isProp× (snd (ObjCover x (mor-source m)))
                                       (snd (ObjCover (mor-target m) y))))))
    where
    isoPMor : Iso (PMor x y) (Σ[ m ∈ PullbackC-Mor ]
                              (ObjCover' x (mor-source m) × ObjCover' (mor-target m) y))
    isoPMor .Iso.fun (pmor m {c1} {c2}) = m , c1 , c2
    isoPMor .Iso.inv (m , c1 , c2) = (pmor m {c1} {c2})
    isoPMor .Iso.rightInv _ = refl
    isoPMor .Iso.leftInv (pmor _) = refl

  mor-compose : (x y z : PObj) -> PMor x y -> PMor y z -> PMor x z
  mor-compose nodeA nodeA nodeA (pmor pathAA) (pmor pathAA) = pmor pathAA
  mor-compose nodeA nodeA nodeC (pmor pathAA) (pmor pathAC) = pmor pathAC
  mor-compose nodeA nodeC nodeC (pmor pathAC) (pmor pathCC) = pmor pathAC
  mor-compose nodeB nodeB nodeB (pmor pathBB) (pmor pathBB) = pmor pathBB
  mor-compose nodeB nodeB nodeC (pmor pathBB) (pmor pathBC) = pmor pathBC
  mor-compose nodeB nodeC nodeC (pmor pathBC) (pmor pathCC) = pmor pathBC
  mor-compose nodeC nodeC nodeC (pmor pathCC) (pmor pathCC) = pmor pathCC



private
  PullbackC-Sorts : CategorySorts ℓ-zero ℓ-zero
  PullbackC-Sorts = record { Obj = PObj ; Mor = PMor }

  PullbackC-Ops : CategoryOps PullbackC-Sorts
  PullbackC-Ops = record
    { id = \{ {nodeA} -> pmor pathAA
            ; {nodeB} -> pmor pathBB
            ; {nodeC} -> pmor pathCC
            }
    ; _⋆_ = \{x} {y} {z} -> mor-compose x y z
    }

  module O = CategoryOps PullbackC-Ops

  mor-assoc : (w x y z : PObj) ->
              (f : PMor w x) -> (g : PMor x y) -> (h : PMor y z) ->
              (f O.⋆ g) O.⋆ h == f O.⋆ (g O.⋆ h)
  mor-assoc nodeA nodeA nodeA nodeA (pmor pathAA) (pmor pathAA) (pmor pathAA) = refl
  mor-assoc nodeA nodeA nodeA nodeC (pmor pathAA) (pmor pathAA) (pmor pathAC) = refl
  mor-assoc nodeA nodeA nodeC nodeC (pmor pathAA) (pmor pathAC) (pmor pathCC) = refl
  mor-assoc nodeA nodeC nodeC nodeC (pmor pathAC) (pmor pathCC) (pmor pathCC) = refl
  mor-assoc nodeB nodeB nodeB nodeB (pmor pathBB) (pmor pathBB) (pmor pathBB) = refl
  mor-assoc nodeB nodeB nodeB nodeC (pmor pathBB) (pmor pathBB) (pmor pathBC) = refl
  mor-assoc nodeB nodeB nodeC nodeC (pmor pathBB) (pmor pathBC) (pmor pathCC) = refl
  mor-assoc nodeB nodeC nodeC nodeC (pmor pathBC) (pmor pathCC) (pmor pathCC) = refl
  mor-assoc nodeC nodeC nodeC nodeC (pmor pathCC) (pmor pathCC) (pmor pathCC) = refl


  PullbackC-Laws : CategoryLaws PullbackC-Ops
  PullbackC-Laws = record
    { ⋆-left-id = \{ {nodeA} {nodeA} (pmor pathAA) -> refl
                   ; {nodeA} {nodeC} (pmor pathAC) -> refl
                   ; {nodeB} {nodeB} (pmor pathBB) -> refl
                   ; {nodeB} {nodeC} (pmor pathBC) -> refl
                   ; {nodeC} {nodeC} (pmor pathCC) -> refl
                   }
    ; ⋆-right-id = \{ {nodeA} {nodeA} (pmor pathAA) -> refl
                    ; {nodeA} {nodeC} (pmor pathAC) -> refl
                    ; {nodeB} {nodeB} (pmor pathBB) -> refl
                    ; {nodeB} {nodeC} (pmor pathBC) -> refl
                    ; {nodeC} {nodeC} (pmor pathCC) -> refl
                    }
    ; ⋆-assoc = mor-assoc _ _ _ _
    ; isSet-Mor = isSet-PMor
    }

PullbackC : PreCategory ℓ-zero ℓ-zero
PullbackC = Laws->Category PullbackC-Laws
