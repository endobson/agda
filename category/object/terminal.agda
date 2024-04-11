{-# OPTIONS --cubical --safe --exact-split #-}

module category.object.terminal where

open import base
open import equality.identity-system
open import category.base
open import category.univalent
open import equivalence.base
open import hlevel
open import relation
open import truncation

module _ {ℓO ℓM} (C : PreCategory ℓO ℓM) where
  isTerminal : Pred (Obj C) _
  isTerminal obj = (c : Obj C) -> isContr (C [ c , obj ])

  record Terminal : Type (ℓ-max ℓO ℓM) where
    field
      obj : Obj C
      universal : isTerminal obj

    mor : {c : Obj C} -> C [ c , obj ]
    mor = fst (universal _)

    unique : {c : Obj C} {f : C [ c , obj ]} -> mor == f
    unique = snd (universal _) _

    unique₂ : {c : Obj C} -> isProp (C [ c , obj ])
    unique₂ = isContr->isProp (universal _)

module TerminalHelpers {ℓO ℓM : Level} {C : PreCategory ℓO ℓM}
                       (T : Terminal C) where
  open Terminal T
    renaming ( obj to 1C
             ; mor to !
             ; unique₂ to !-uniqueᵉ )
    public

  !-unique : {c : Obj C} -> {f g : C [ c , 1C ]} -> f == g
  !-unique = !-uniqueᵉ _ _


module _ {ℓO ℓM} (C : PreCategory ℓO ℓM) where
  isProp-isTerminal : {o : Obj C} -> isProp (isTerminal C o)
  isProp-isTerminal = isPropΠ (\_ -> isProp-isContr)

module _ {ℓO ℓM} {C : PreCategory ℓO ℓM} where
  private
    terminals->iso : (t1 t2 : Terminal C) -> CatIso C (Terminal.obj t1) (Terminal.obj t2)
    terminals->iso t1 t2 .CatIso.mor = Terminal.mor t2
    terminals->iso t1 t2 .CatIso.inv = Terminal.mor t1
    terminals->iso t1 t2 .CatIso.sec = Terminal.unique₂ t2 _ _
    terminals->iso t1 t2 .CatIso.ret = Terminal.unique₂ t1 _ _

    terminals->isProp-iso : (t1 t2 : Terminal C) ->
      isProp (CatIso C (Terminal.obj t1) (Terminal.obj t2))
    terminals->isProp-iso t1 t2 ia ib =
      cat-iso-path (Terminal.unique₂ t2 (CatIso.mor ia) (CatIso.mor ib))

  terminals->unique-iso : (t1 t2 : Terminal C) -> isContr (CatIso C (Terminal.obj t1) (Terminal.obj t2))
  terminals->unique-iso t1 t2 = terminals->iso t1 t2 , terminals->isProp-iso t1 t2 _


  terminal-path : {t1 t2 : Terminal C} ->
                  (Terminal.obj t1 == Terminal.obj t2) ->
                  t1 == t2
  terminal-path op i .Terminal.obj = op i
  terminal-path {t1} {t2} op i .Terminal.universal c =
    isProp->PathPᵉ (\i -> isProp-isContr {A = C [ c , op i ]})
    (Terminal.universal t1 c) (Terminal.universal t2 c) i

  isProp-Terminal : isUnivalent' C -> isProp (Terminal C)
  isProp-Terminal univ t1 t2 = terminal-path (univ .isIdentitySystem.to-path (terminals->iso t1 t2))
