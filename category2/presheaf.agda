{-# OPTIONS --cubical --safe --exact-split #-}

module category2.presheaf where


open import base
open import cubical
open import category2.base hiding (_∘_)
open import equality-path
open import equality.square
open import category2.set
open import category2.constructions.functor
open import category2.constructions.product
open import category2.constructions.opposite
open import category2.morphism.iso
open import funext
open import functions
open import hlevel.base
open import hlevel
open import hlevel.htype
open import hlevel.pi


Presheaf : {ℓO ℓM : Level} (C : Category ℓO ℓM) (ℓ : Level) -> Type (ℓ-max* 3 (ℓ-suc ℓ) ℓO ℓM)
Presheaf C ℓ = Functorᵒᵖ C (hSetC ℓ)

PresheafC : {ℓO ℓM : Level} (C : Category ℓO ℓM) (ℓ : Level) -> Category (ℓ-max* 3 (ℓ-suc ℓ) ℓO ℓM) (ℓ-max* 3 ℓ ℓO ℓM)
PresheafC C ℓ = FunctorᵒᵖC C (hSetC ℓ)


module _ {ℓO ℓM : Level} (C : Category ℓO ℓM) (o₁ : Obj C) where
  private
    instance
      CS = Category.Str C

  HomFunctor : Functor C (hSetC ℓM)
  HomFunctor = record
    { obj = \o₂ -> C →[ o₁ , o₂ ] , isSet-Mor
    ; mor = \m₁ -> [ (\m₂ -> m₂ ⋆ m₁) ]
    ; preserves-idᵉ = \_ i -> [ (\m -> ⋆-right-idᵉ m i) ]
    ; preserves-⋆ᵉ = \m₁ m₂ i -> [ (\m₃ -> ⋆-assocᵉ m₃ m₁ m₂ (~ i)) ]
    }



  HomFunctorᵒᵖ : Functorᵒᵖ C (hSetC ℓM)
  HomFunctorᵒᵖ = record
    { obj = \o₂ -> C →[ o₂ , o₁ ] , isSet-Mor
    ; mor = \m₁ -> [ (\m₂ -> m₁ ⋆ m₂) ]
    ; preserves-idᵉ = \_ i -> [ (\m -> ⋆-left-idᵉ m i) ]
    ; preserves-⋆ᵉ = \m₁ m₂ i -> [ (\m₃ -> ⋆-assocᵉ m₁ m₂ m₃ i) ]
    }


-- yonedaᵉ : {ℓO ℓM : Level} (C : Category ℓO ℓM) (ℓ : Level) -> Functor C (PresheafC C ℓ)
-- yonedaᵉ C ℓ = record
--   { obj = \o -> ?
--   ; mor = ?
--   }

module _ {ℓO ℓM : Level} (C : Category ℓO ℓM) where
  private
    instance
      CS = Category.Str C

  yoneda : Functor C (PresheafC C ℓM)
  yoneda = record
    { obj = HomFunctorᵒᵖ C
    ; mor = η
    ; preserves-idᵉ = \_ -> natural-transformationᵒᵖ-path (\o i -> [ (\m -> ⋆-right-idᵉ m i) ])
    ; preserves-⋆ᵉ =
      \m₁ m₂ -> natural-transformationᵒᵖ-path (\o i -> [ (\m₃ -> ⋆-assocᵉ m₃ m₁ m₂ (~ i)) ])
    }
    where
    η : {x y : Obj C} -> (m : C →[ x , y ]) -> _
    η {x} {y} m₁ = record
      { obj = obj
      ; mor = mor
      }
      where
      obj : (o : Obj C) -> hSet→ _ _
      obj o = [ (\m₂ -> m₂ ⋆ m₁) ]
      opaque
        mor : ∀ {o₁ o₂} -> (m₂ : C →[ o₁ , o₂ ]) ->
          obj o₂ ⋆ (Functorᵒᵖ.mor (HomFunctorᵒᵖ C y) m₂) ==
          (Functorᵒᵖ.mor (HomFunctorᵒᵖ C x) m₂) ⋆ obj o₁
        mor m₂ i = [ (\m₃ -> ⋆-assocᵉ m₂ m₃ m₁ (~ i)) ]



module _ {ℓO ℓM : Level} (C : Category ℓO ℓM) where


  private
    instance
      CS = Category.Str C
    P = (ProdC (OpC C) (PresheafC C ℓM))
    P→ = ProdC→ (OpC C) (PresheafC C ℓM)
    Y = yoneda C
    module Y = Functor Y

    F₁⁻ : Functor P (hSetC ℓM)
    F₁⁻ = record
      { obj = obj
      ; mor = mor
      ; preserves-idᵉ = preserves-idᵉ
      ; preserves-⋆ᵉ = preserves-⋆ᵉ
      }
      where
      obj : Obj P -> Obj (hSetC ℓM)
      obj (o , p) = Functorᵒᵖ.obj p o
      mor : ∀ {o₁ o₂ : Obj P} -> P→ o₁ o₂ -> hSet→ (obj o₁) (obj o₂)
      mor {(o₁ , p₁)} {(o₂ , p₂)} ([ m ] , η) =
        NaturalTransformationᵒᵖ.obj η o₁ ⋆ Functorᵒᵖ.mor p₂ m

      opaque
        preserves-idᵉ : ∀ (o : Obj P) -> mor (idᵉ o) == idᵉ (obj o)
        preserves-idᵉ (_ , p₁) =
          ⋆-right (Functorᵒᵖ.preserves-id p₁) >=>
          ⋆-right-id

        preserves-⋆ᵉ : ∀ {o₁ o₂ o₃ : Obj P} (m₁ : P→ o₁ o₂) (m₂ : P→ o₂ o₃) ->
          mor (m₁ ⋆ m₂) == (mor m₁ ⋆ mor m₂)
        preserves-⋆ᵉ {o₁ , p₁} {o₂ , p₂} {o₃ , p₃} pm₁@([ m₁ ] , η₁) pm₂@([ m₂ ] , η₂)  =
          ⋆-right p₃.preserves-⋆ >=>
          sym (⋆-assocᵉ (η₁₂.obj o₁) (p₃.mor m₁) (p₃.mor m₂)) >=>
          cong (_⋆ p₃.mor m₂) step₂ >=>
          sym (⋆-assocᵉ (mor pm₁) (η₂.obj o₂) (p₃.mor m₂))
          where
          module p₁ = Functorᵒᵖ p₁
          module p₂ = Functorᵒᵖ p₂
          module p₃ = Functorᵒᵖ p₃
          module η₁ = NaturalTransformationᵒᵖ η₁
          module η₂ = NaturalTransformationᵒᵖ η₂
          η₁₂ : NaturalTransformationᵒᵖ p₁ p₃
          η₁₂ = η₁ ⋆ η₂
          module η₁₂ = NaturalTransformationᵒᵖ η₁₂

          step₂ : (η₁₂.obj o₁) ⋆ (p₃.mor m₁) == (mor pm₁) ⋆ (η₂.obj o₂)
          step₂ =
            ⋆-assocᵉ (η₁.obj o₁) (η₂.obj o₁) (p₃.mor m₁) >=>
            cong (η₁.obj o₁ ⋆_) (η₂.mor m₁) >=>
            sym (⋆-assocᵉ (η₁.obj o₁) (p₂.mor m₁) (η₂.obj o₂))

    F₁ : Functor P (hSetC (ℓ-max ℓO ℓM))
    F₁ = F₁⁻ ⋆F lift-hSet-Functor ℓO

    F₂ : Functor P (hSetC (ℓ-max ℓO ℓM))
    F₂ =  record
      { obj = obj
      ; mor = mor
      ; preserves-idᵉ = preserves-idᵉ
      ; preserves-⋆ᵉ = preserves-⋆ᵉ
      }
      where
      obj : Obj P -> Obj (hSetC (ℓ-max ℓO ℓM))
      obj (o , p) = NaturalTransformationᵒᵖ (Y.obj o) p , isSet-NaturalTransformationᵒᵖ

      mor : ∀ {o₁ o₂ : Obj P} -> P→ o₁ o₂ -> hSet→ (obj o₁) (obj o₂)
      mor {(o₁ , p₁)} {(o₂ , p₂)} ([ m ] , η₁) = [ (\η₂ -> Y.mor m ⋆ η₂ ⋆ η₁) ]

      preserves-idᵉ : ∀ (o : Obj P) -> mor (idᵉ o) == idᵉ (obj o)
      preserves-idᵉ _ i .hSet→.f η = (⋆-right-id >=> ⋆-left Y.preserves-id >=> ⋆-left-idᵉ η) i

      preserves-⋆ᵉ : ∀ {o₁ o₂ o₃ : Obj P} (m₁ : P→ o₁ o₂) (m₂ : P→ o₂ o₃) ->
        mor (m₁ ⋆ m₂) == (mor m₁ ⋆ mor m₂)
      preserves-⋆ᵉ {o₁} {o₂} {o₃} ([ m₁ ] , η₁) ([ m₂ ] , η₂) i .hSet→.f η₃ = ans i
        where
        ans : (Y.mor (m₂ ⋆ m₁) ⋆ η₃) ⋆ (η₁ ⋆ η₂) ==
              (Y.mor m₂ ⋆ ((Y.mor m₁ ⋆ η₃) ⋆ η₁)) ⋆ η₂
        ans =
          sym ⋆-assoc >=>
          ⋆-left (
            ⋆-left (⋆-left Y.preserves-⋆ >=> ⋆-assoc) >=>
            ⋆-assoc)

    yoneda-lemma : NatIso F₁ F₂
    yoneda-lemma = record
      { obj = obj
      ; mor = mor
      } ,
      \o -> snd (objΣ o)
      where
      module F₁ = Functor F₁
      module F₂ = Functor F₂

      objΣ : (o : Obj P) -> Σ (hSet→ (F₁.obj o) (F₂.obj o)) isIso
      objΣ (o₁ , p) =
        [ (\ (lift po) -> obj' po) ] ,
        (is-iso [ lift ∘ inv ]
                (\i -> [ (\ (lift x) -> lift (rightInv x i)) ])
                (\i -> [ (\x -> leftInv x i) ]))
        where
        module p = Functorᵒᵖ p
        h = HomFunctorᵒᵖ C o₁
        module h = Functorᵒᵖ h

        obj' : ⟨ p.obj o₁ ⟩ -> NaturalTransformationᵒᵖ h p
        obj' po₁ = record
          { obj = iobj
          ; mor = imor
          }
          where
          iobj : (o₂ : Obj C) -> hSet→ (C →[ o₂ , o₁ ] , isSet-Mor) (p.obj o₂)
          iobj _ = [ (\m -> hSet→.f (p.mor m) po₁) ]
          opaque
            imor : {o₂ o₃ : Obj C} -> (m : C →[ o₂ , o₃ ]) ->
                   iobj o₃ ⋆ p.mor m == h.mor m ⋆ iobj o₂
            imor m₁ i .hSet→.f m₂ = hSet→.f (p.preserves-⋆ᵉ m₁ m₂ (~ i)) po₁

        inv : NaturalTransformationᵒᵖ h p -> ⟨ p.obj o₁ ⟩
        inv η = NaturalTransformationᵒᵖ.obj η o₁ .hSet→.f id

        rightInv : ∀ (x : ⟨ p.obj o₁ ⟩) -> inv (obj' x) == x
        rightInv po₁ i = (p.preserves-idᵉ o₁ i) .hSet→.f po₁

        leftInv : ∀ (x : NaturalTransformationᵒᵖ h p) -> obj' (inv x) == x
        leftInv η = natural-transformationᵒᵖ-path ans
          where
          module η = NaturalTransformationᵒᵖ η

          ans : (o : Obj C) ->
            [ (\ (m : C →[ o , o₁ ]) -> (p.mor m) .hSet→.f (η.obj o₁ .hSet→.f id)) ] == η.obj o
          ans o i .hSet→.f m =
            ((\i -> η.mor m i .hSet→.f id) >=>
             (\i -> (η.obj o) .hSet→.f (⋆-right-idᵉ m i))) i

      obj : (o : Obj P) -> hSet→ (F₁.obj o) (F₂.obj o)
      obj o = fst (objΣ o)

      opaque
        mor : {o₁ o₂ : Obj P} (m : P→ o₁ o₂) -> obj o₁ ⋆ F₂.mor m == F₁.mor m ⋆ obj o₂
        mor {o₁@(o₁α , o₁β)} {o₂@(o₂α , o₂β)} m₁@([ m₁α ] , m₁β) i .hSet→.f (lift m₂) =
          ans i
          where
          module o₁β = Functorᵒᵖ o₁β
          module o₂β = Functorᵒᵖ o₂β
          module m₁β = NaturalTransformationᵒᵖ m₁β

          module _ where
            ans₂ : (o₃ : Obj C) ->
              Path (hSet→ _ _)
              [ (\ m₃ → m₁β.obj o₃ .hSet→.f ((o₁β.mor (m₃ ⋆ m₁α)) .hSet→.f m₂)) ]
              [ (\ m₃ → o₂β.mor m₃ .hSet→.f (o₂β.mor m₁α .hSet→.f (m₁β.obj o₁α .hSet→.f m₂))) ]
            ans₂ o₃ i .hSet→.f m₃ = ans₄ i .hSet→.f m₂
              where
              ans₄ : (o₁β.mor (m₃ ⋆ m₁α)) ⋆ m₁β.obj o₃ == ((m₁β.obj o₁α) ⋆ o₂β.mor m₁α) ⋆ o₂β.mor m₃
              ans₄ = sym (m₁β.mor (m₃ ⋆ m₁α)) >=> ⋆-right o₂β.preserves-⋆ >=>
                     sym (⋆-assocᵉ (m₁β.obj o₁α) (o₂β.mor m₁α) (o₂β.mor m₃))


            ans : hSet→.f (obj o₁ ⋆ F₂.mor m₁) (lift m₂) == hSet→.f (F₁.mor m₁ ⋆ obj o₂) (lift m₂)
            ans = natural-transformationᵒᵖ-path ans₂
