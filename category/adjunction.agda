{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.base
open import category.constructions.functor-cat
open import category.functor
open import category.isomorphism
open import category.natural-isomorphism
open import category.natural-transformation
open import equality-path

module category.adjunction where

module _ {ℓOC ℓMC ℓOD ℓMD : Level} {C : PreCategory ℓOC ℓMC} {D : PreCategory ℓOD ℓMD} where

  record Adjunction (L : Functor C D) (R : Functor D C) : Type (ℓ-max* 4 ℓOC ℓMC ℓOD ℓMD) where
    field
      unit : NaturalTransformation (idF C) (L ⋆F R)
      counit : NaturalTransformation (R ⋆F L) (idF D)

      tri-L : ∀ (c : Obj C) -> (NT-obj (unit NT▶ L) c) ⋆⟨ D ⟩ (NT-obj (L NT◀ counit) c) == id D
      tri-R : ∀ (d : Obj D) -> (NT-obj (R NT◀ unit) d) ⋆⟨ C ⟩ (NT-obj (counit NT▶ R) d) == id C

    module unit = NaturalTransformation unit
    module counit = NaturalTransformation counit

  AdjointEquiv : (L : Functor C D) (R : Functor D C) -> Type _
  AdjointEquiv L R = Σ (Adjunction L R) AdjunctionEquiv
    where
    AdjunctionEquiv : Adjunction L R -> Type _
    AdjunctionEquiv adj = isNaturalIso _ _ unit × isNaturalIso _ _ counit
      where
      open Adjunction adj

  isEquivC : (Functor C D) -> Type _
  isEquivC L = Σ[ R ∈ Functor D C ] (AdjointEquiv L R)

_≃C_ : {ℓOC ℓMC ℓOD ℓMD : Level} -> (PreCategory ℓOC ℓMC) -> (PreCategory ℓOD ℓMD) -> Type _
C ≃C D = Σ (Functor C D) isEquivC

private
  module _ {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
           {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD} where

    _⋆NI_ : {F G H : Functor C D} ->
            NaturalIsomorphism F G ->
            NaturalIsomorphism G H ->
            NaturalIsomorphism F H
    (nt1 , ni1) ⋆NI (nt2 , ni2) = nt1 ⋆NT nt2 , isIso'
      where
      isIso' : (c : Obj C) -> isIso D (NT-obj (nt1 ⋆NT nt2) c)
      isIso' c = record
        { inv = i2.inv ⋆⟨ D ⟩ i1.inv
        ; sec = ⋆-assoc >=> (⋆-right (sym ⋆-assoc >=> ⋆-left i1.sec >=> ⋆-left-id)) >=> i2.sec
        ; ret = ⋆-assoc >=> (⋆-right (sym ⋆-assoc >=> ⋆-left i2.ret >=> ⋆-left-id)) >=> i1.ret
        }
        where
        module i1 = isIso (ni1 c)
        module i2 = isIso (ni2 c)
        open CategoryHelpers D

    infixl 15 _⋆NI_


module _ {ℓOC ℓMC ℓOD ℓMD ℓOE ℓME : Level}
         {C : PreCategory ℓOC ℓMC}
         {D : PreCategory ℓOD ℓMD}
         {E : PreCategory ℓOE ℓME}
         {f1 : Functor C D}
         {f2 : Functor C D}
         {f3 : Functor D E}
         {f4 : Functor D E} where
  composeʰ-NT : NaturalTransformation f1 f2 ->
                NaturalTransformation f3 f4 ->
                NaturalTransformation (f1 ⋆F f3) (f2 ⋆F f4)
  composeʰ-NT nt12 nt34 = record
    { obj = \ c -> nt34.obj (F-obj f1 c) ⋆⟨ E ⟩ (F-mor f4 (nt12.obj c))
    ; mor = \ m ->
      E.⋆-left (nt34.mor (nt12.obj _)) >=>
      E.⋆-assoc >=>
      E.⋆-right (nt34.mor _) >=>
      sym E.⋆-assoc >=>
      E.⋆-left (sym (f3.⋆ _ _) >=> cong f3.mor (nt12.mor _) >=>
                 f3.⋆ _ _) >=>
      E.⋆-assoc >=>
      E.⋆-right (sym (nt34.mor _))
    }
    where
    module f3 = Functor f3
    module E = CategoryHelpers E
    module nt12 = NaturalTransformation nt12
    module nt34 = NaturalTransformation nt34

module _ {ℓOC ℓMC ℓOD ℓMD : Level}
         {C : PreCategory ℓOC ℓMC}
         {D : PreCategory ℓOD ℓMD} where

  NT-λ⇒ : {F : Functor C D} -> NaturalTransformation (idF C ⋆F F) F
  NT-λ⇒ = record
    { obj = \c -> id D
    ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
    }
    where
    open CategoryHelpers D

  NT-λ⇐ : {F : Functor C D} -> NaturalTransformation F (idF C ⋆F F)
  NT-λ⇐ = record
    { obj = \c -> id D
    ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
    }
    where
    open CategoryHelpers D

  NT-ρ⇒ : {F : Functor C D} -> NaturalTransformation (F ⋆F idF D) F
  NT-ρ⇒ = record
    { obj = \c -> id D
    ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
    }
    where
    open CategoryHelpers D

  NT-ρ⇐ : {F : Functor C D} -> NaturalTransformation F (F ⋆F idF D)
  NT-ρ⇐ = record
    { obj = \c -> id D
    ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
    }
    where
    open CategoryHelpers D

  NI-λ⇒ : {F : Functor C D} -> NaturalIsomorphism (idF C ⋆F F) F
  NI-λ⇒ = NT-λ⇒ , \_ -> isIso-id _
  NI-λ⇐ : {F : Functor C D} -> NaturalIsomorphism F (idF C ⋆F F)
  NI-λ⇐ = NT-λ⇐ , \_ -> isIso-id _

  NI-ρ⇒ : {F : Functor C D} -> NaturalIsomorphism (F ⋆F idF D) F
  NI-ρ⇒ = NT-ρ⇒ , \_ -> isIso-id _
  NI-ρ⇐ : {F : Functor C D} -> NaturalIsomorphism F (F ⋆F idF D)
  NI-ρ⇐ = NT-ρ⇐ , \_ -> isIso-id _


module _ {ℓOC ℓMC ℓOD ℓMD ℓOE ℓME : Level}
         {C : PreCategory ℓOC ℓMC}
         {D : PreCategory ℓOD ℓMD}
         {E : PreCategory ℓOE ℓME} where
--   _NT▶_ : {f1 f2 : Functor C D} -> NaturalTransformation f1 f2 -> (f3 : Functor D E) ->
--           NaturalTransformation (f1 ⋆F f3) (f2 ⋆F f3)
--   _NT▶_ nt f3 = record
--     { obj = \c -> F-mor f3 (NT-obj nt c)
--     ; mor = \m -> sym (F-⋆ f3 _ _) >=> cong (F-mor f3) (NT-mor nt _) >=> (F-⋆ f3 _ _)
--     }
-- 
--   _NT◀_ : (f1 : Functor C D) -> {f2 f3 : Functor D E} -> NaturalTransformation f2 f3 ->
--           NaturalTransformation (f1 ⋆F f2) (f1 ⋆F f3)
--   _NT◀_ f1 nt = record
--     { obj = \c -> (NT-obj nt (F-obj f1 c))
--     ; mor = \m -> (NT-mor nt _)
--     }

  _NI▶_ : {f1 f2 : Functor C D} -> NaturalIsomorphism f1 f2 -> (f3 : Functor D E) ->
          NaturalIsomorphism (f1 ⋆F f3) (f2 ⋆F f3)
  _NI▶_ (nt , ni) f3 = (nt NT▶ f3) , \c -> functor-preserves-isIso f3 (ni c)

  _NI◀_ : (f1 : Functor C D) {f2 f3 : Functor D E} -> NaturalIsomorphism f2 f3 ->
          NaturalIsomorphism (f1 ⋆F f2) (f1 ⋆F f3)
  _NI◀_ f3 (nt , ni) = (f3 NT◀ nt) , \c -> (ni (F-obj f3 c))


module _ {ℓOC1 ℓMC1 ℓOC2 ℓMC2 ℓOC3 ℓMC3 ℓOC4 ℓMC4 : Level}
         {C1 : PreCategory ℓOC1 ℓMC1}
         {C2 : PreCategory ℓOC2 ℓMC2}
         {C3 : PreCategory ℓOC3 ℓMC3}
         {C4 : PreCategory ℓOC4 ℓMC4}
         where

  NT-α⇒ᵉ : (F : Functor C1 C2) (G : Functor C2 C3) (H : Functor C3 C4) ->
           NaturalTransformation ((F ⋆F G) ⋆F H) (F ⋆F (G ⋆F H))
  NT-α⇒ᵉ F G H = record
    { obj = \c -> id C4
    ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
    }
    where
    open CategoryHelpers C4

  NT-α⇐ᵉ : (F : Functor C1 C2) (G : Functor C2 C3) (H : Functor C3 C4) ->
           NaturalTransformation (F ⋆F (G ⋆F H)) ((F ⋆F G) ⋆F H)
  NT-α⇐ᵉ F G H = record
    { obj = \c -> id C4
    ; mor = \m -> ⋆-left-id >=> sym ⋆-right-id
    }
    where
    open CategoryHelpers C4

  NI-α⇒ᵉ : (F : Functor C1 C2) (G : Functor C2 C3) (H : Functor C3 C4) ->
           NaturalIsomorphism ((F ⋆F G) ⋆F H) (F ⋆F (G ⋆F H))
  NI-α⇒ᵉ F G H = NT-α⇒ᵉ F G H , \_ -> isIso-id _


  NI-α⇐ᵉ : (F : Functor C1 C2) (G : Functor C2 C3) (H : Functor C3 C4) ->
           NaturalIsomorphism (F ⋆F (G ⋆F H)) ((F ⋆F G) ⋆F H)
  NI-α⇐ᵉ F G H = NT-α⇐ᵉ F G H , \_ -> isIso-id _


module _ {ℓOC ℓMC ℓOD ℓMD ℓOE ℓME : Level}
         {C : PreCategory ℓOC ℓMC}
         {D : PreCategory ℓOD ℓMD}
         {E : PreCategory ℓOE ℓME}
         {f1 : Functor C D}
         {f2 : Functor D C}
         {f3 : Functor D E}
         {f4 : Functor E D}
         (ae1 : AdjointEquiv f1 f2) (ae2 : AdjointEquiv f3 f4)
  where
  private
    module a1 = Adjunction (fst ae1)
    module a2 = Adjunction (fst ae2)

  private
    ni-unit1 = (fst (snd ae1))
    ni-unit2 = (fst (snd ae2))
    ni-counit1 = (snd (snd ae1))
    ni-counit2 = (snd (snd ae2))

    unit-iso : NaturalIsomorphism (idF C) ((f1 ⋆F f3) ⋆F (f4 ⋆F f2))
    unit-iso = (a1.unit , ni-unit1) ⋆NI (f1 NI◀ inner) ⋆NI (NI-α⇐ᵉ f1 f3 (f4 ⋆F f2))
      where
      inner : NaturalIsomorphism f2 (f3 ⋆F (f4 ⋆F f2))
      inner = NI-λ⇐ ⋆NI ((a2.unit , ni-unit2) NI▶ f2) ⋆NI (NI-α⇒ᵉ f3 f4 f2)

    counit-iso : NaturalIsomorphism ((f4 ⋆F f2) ⋆F (f1 ⋆F f3)) (idF E)
    counit-iso =
      (NI-α⇒ᵉ f4 f2 (f1 ⋆F f3)) ⋆NI
      (f4 NI◀ inner) ⋆NI
      (a2.counit , ni-counit2)
      where
      inner : NaturalIsomorphism (f2 ⋆F (f1 ⋆F f3)) f3
      inner = (NI-α⇐ᵉ f2 f1 f3) ⋆NI ((a1.counit , ni-counit1) NI▶ f3) ⋆NI NI-λ⇒

    unit = fst unit-iso
    counit = fst counit-iso

    unit-obj : (c : Obj C) -> (NT-obj unit c) == (NT-obj a1.unit c ⋆⟨ C ⟩
                                                  F-mor f2 (NT-obj a2.unit (F-obj f1 c)))
    unit-obj c = ⋆-right-id >=> ⋆-right (⋆-right-id >=> ⋆-left-id)
      where
      open CategoryHelpers C

    counit-obj : (e : Obj E) -> (NT-obj counit e) ==
                                (F-mor f3 (NT-obj a1.counit (F-obj f4 e))) ⋆⟨ E ⟩
                                (NT-obj a2.counit e)
    counit-obj e = ⋆-left (⋆-left-id >=> ⋆-right-id >=> ⋆-left-id)
      where
      open CategoryHelpers E

    tri-L : (c : Obj C) -> (F-mor (f1 ⋆F f3) (NT-obj unit c)) ⋆⟨ E ⟩
                           (NT-obj counit (F-obj (f1 ⋆F f3) c)) == id E
    tri-L c = outer
      where
      module f1 = Functor f1
      module f2 = Functor f2
      module f3 = Functor f3
      module f4 = Functor f4

      inner : f1.mor (NT-obj a1.unit c ⋆⟨ C ⟩ (f2.mor (NT-obj a2.unit (f1.obj c)))) ⋆⟨ D ⟩
              (NT-obj a1.counit (f4.obj (f3.obj (f1.obj c)))) ==
              (NT-obj a2.unit (f1.obj c))
      inner = ⋆-left (F-⋆ f1 _ _) >=>
              ⋆-assoc >=>
              ⋆-right (sym (NT-mor a1.counit _)) >=>
              sym ⋆-assoc >=>
              ⋆-left (a1.tri-L _) >=>
              ⋆-left-id
        where
        open CategoryHelpers D

      outer = ⋆-cong (cong (F-mor (f1 ⋆F f3)) (unit-obj c)) (counit-obj (F-obj (f1 ⋆F f3) c)) >=>
              sym ⋆-assoc >=>
              ⋆-left (sym (F-⋆ f3 _ _) >=> cong (F-mor f3) inner) >=>
              a2.tri-L _
        where
        open CategoryHelpers E


    tri-R : (e : Obj E) -> (NT-obj unit (F-obj (f4 ⋆F f2) e)) ⋆⟨ C ⟩
                           (F-mor (f4 ⋆F f2) (NT-obj counit e)) == id C
    tri-R e = outer
      where
      module f1 = Functor f1
      module f2 = Functor f2
      module f3 = Functor f3
      module f4 = Functor f4

      inner : NT-obj a2.unit (f1.obj (f2.obj (f4.obj e))) ⋆⟨ D ⟩
              (f4.mor (f3.mor (NT-obj a1.counit (f4.obj e)) ⋆⟨ E ⟩ NT-obj a2.counit e)) ==
              NT-obj a1.counit (f4.obj e)
      inner = ⋆-right (F-⋆ f4 _ _) >=>
              sym ⋆-assoc >=>
              ⋆-left (NT-mor a2.unit _) >=>
              ⋆-assoc >=>
              ⋆-right (a2.tri-R _) >=>
              ⋆-right-id
        where
        open CategoryHelpers D

      outer =
        ⋆-cong (unit-obj (F-obj (f4 ⋆F f2) e)) (cong (F-mor (f4 ⋆F f2)) (counit-obj e)) >=>
        ⋆-assoc >=>
        ⋆-right (sym (F-⋆ f2 _ _) >=> cong f2.mor inner) >=>
        a1.tri-R _
        where
        open CategoryHelpers C

  compose-AdjointEquiv : AdjointEquiv (f1 ⋆F f3) (f4 ⋆F f2)
  compose-AdjointEquiv = adj , (snd unit-iso) , (snd counit-iso)
    where
    adj = record
      { unit = (fst unit-iso)
      ; counit = (fst counit-iso)
      ; tri-L = tri-L
      ; tri-R = tri-R
      }
