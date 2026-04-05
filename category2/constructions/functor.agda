{-# OPTIONS --cubical --safe --exact-split #-}

module category2.constructions.functor where


open import base
open import cubical
open import category2.base
open import equality-path
open import equality.square
open import category2.set
open import category2.morphism.iso
open import funext
open import hlevel.base
open import hlevel
open import equivalence
open import isomorphism
open import hlevel.pi


module _
  {ℓO₁ ℓO₂ ℓM₁ ℓM₂ : Level}
  {C₁ : Category ℓO₁ ℓM₁}
  {C₂ : Category ℓO₂ ℓM₂}
  (F G : Functorᵒᵖ C₁ C₂)
  where

  private
    module F = Functorᵒᵖ F
    module G = Functorᵒᵖ G
    instance
      CS₁ = Category.Str C₁
      CS₂ = Category.Str C₂

  record NaturalTransformationᵒᵖ : Type (ℓ-max* 3 ℓO₁ ℓM₁ ℓM₂) where
    field
      obj : (o : Obj C₁) -> C₂ →[ F.obj o , G.obj o ]
      {mor} : {o₁ o₂ : Obj C₁} -> (m : C₁ →[ o₁ , o₂ ]) ->
        (obj o₂ ⋆ G.mor m) == (F.mor m ⋆ obj o₁)

module _
  {ℓO₁ ℓO₂ ℓM₁ ℓM₂ : Level}
  {C₁ : Category ℓO₁ ℓM₁}
  {C₂ : Category ℓO₂ ℓM₂}
  {F G : Functorᵒᵖ C₁ C₂}
  where
  private
    instance
      CS₂ = Category.Str C₂

  isNatIsoᵒᵖ : Pred (NaturalTransformationᵒᵖ F G) (ℓ-max* 3 ℓO₁ ℓO₂ ℓM₂)
  isNatIsoᵒᵖ η = ∀ (o : Obj C₁) -> isIso (NaturalTransformationᵒᵖ.obj η o)

module _
  {ℓO₁ ℓO₂ ℓM₁ ℓM₂ : Level}
  {C₁ : Category ℓO₁ ℓM₁}
  {C₂ : Category ℓO₂ ℓM₂}
  (F G : Functor C₁ C₂)
  where

  private
    module F = Functor F
    module G = Functor G
    instance
      CS₁ = Category.Str C₁
      CS₂ = Category.Str C₂

  record NaturalTransformation : Type (ℓ-max* 3 ℓO₁ ℓM₁ ℓM₂) where
    field
      obj : (o : Obj C₁) -> C₂ →[ F.obj o , G.obj o ]
      {mor} : {o₁ o₂ : Obj C₁} -> (m : C₁ →[ o₁ , o₂ ]) ->
        obj o₁ ⋆ G.mor m == F.mor m ⋆ obj o₂

module _
  {ℓO₁ ℓO₂ ℓM₁ ℓM₂ : Level}
  {C₁ : Category ℓO₁ ℓM₁}
  {C₂ : Category ℓO₂ ℓM₂}
  {F G : Functor C₁ C₂}
  where
  private
    instance
      CS₂ = Category.Str C₂

  isNatIso : Pred (NaturalTransformation F G) (ℓ-max* 3 ℓO₁ ℓO₂ ℓM₂)
  isNatIso η = ∀ (o : Obj C₁) -> isIso (NaturalTransformation.obj η o)

module _
  {ℓO₁ ℓO₂ ℓM₁ ℓM₂ : Level}
  {C₁ : Category ℓO₁ ℓM₁}
  {C₂ : Category ℓO₂ ℓM₂}
  (F G : Functor C₁ C₂)
  where

  NatIso : Type (ℓ-max* 4 ℓO₁ ℓO₂ ℓM₁ ℓM₂)
  NatIso = Σ (NaturalTransformation F G) isNatIso





module _
  {ℓO₁ ℓO₂ ℓM₁ ℓM₂ : Level}
  {C₁ : Category ℓO₁ ℓM₁}
  {C₂ : Category ℓO₂ ℓM₂}
  {F G : Functor C₁ C₂}
  where

  private
    module F = Functor F
    module G = Functor G
    instance
      CS₁ = Category.Str C₁
      CS₂ = Category.Str C₂

  opaque
    natural-transformation-path :
      {η₁ η₂ : NaturalTransformation F G} ->
      ((o : Obj C₁) -> NaturalTransformation.obj η₁ o == NaturalTransformation.obj η₂ o) ->
      η₁ == η₂
    natural-transformation-path {η₁} {η₂} o-path =
      \i -> record { obj = \o -> o-path o i ; mor = mor-path i }
      where
      module η₁ = NaturalTransformation η₁
      module η₂ = NaturalTransformation η₂

      mor-path : PathP (\i -> {o₁ o₂ : Obj C₁} -> (m : C₁ →[ o₁ , o₂ ]) ->
                              o-path o₁ i ⋆ G.mor m == F.mor m ⋆ o-path o₂ i)
                       η₁.mor η₂.mor
      mor-path = isProp->PathP (\_ -> isPropΠⁱ2 \_ _ -> isPropΠ \_ -> isSet-Mor _ _)


  private
    NT-Obj : Type (ℓ-max ℓO₁ ℓM₂)
    NT-Obj = (o : Obj C₁) -> C₂ →[ F.obj o , G.obj o ]
    NT-Mor : NT-Obj -> Type (ℓ-max* 3 ℓO₁ ℓM₁ ℓM₂)
    NT-Mor obj =
      {o₁ o₂ : Obj C₁} -> (m : C₁ →[ o₁ , o₂ ]) ->
      obj o₁ ⋆ G.mor m == F.mor m ⋆ obj o₂

    NTΣ : Type (ℓ-max* 3 ℓO₁ ℓM₁ ℓM₂)
    NTΣ = Σ NT-Obj NT-Mor

    NT≃NTΣ : NaturalTransformation F G ≃ NTΣ
    NT≃NTΣ = isoToEquiv (iso fwd bkw (\_ -> refl) (\_ -> refl))
      where
      fwd : NaturalTransformation F G -> NTΣ
      fwd η = NaturalTransformation.obj η , NaturalTransformation.mor η
      bkw : NTΣ -> NaturalTransformation F G
      bkw (o , m) = record { obj = o ; mor = m }

    isSet-NTΣ : isSet NTΣ
    isSet-NTΣ = isSetΣ (isSetΠ \_ -> isSet-Mor)
                     (\o -> isSetΠⁱ \_ -> isSetΠⁱ \_ -> isSetΠ \_ -> isProp->isSet (isSet-Mor _ _))

  opaque
    isSet-NaturalTransformation : isSet (NaturalTransformation F G)
    isSet-NaturalTransformation = ≃-isSet (equiv⁻¹ NT≃NTΣ) isSet-NTΣ


module _
  {ℓO₁ ℓO₂ ℓM₁ ℓM₂ : Level}
  {C₁ : Category ℓO₁ ℓM₁}
  {C₂ : Category ℓO₂ ℓM₂}
  {F G : Functorᵒᵖ C₁ C₂}
  where

  private
    module F = Functorᵒᵖ F
    module G = Functorᵒᵖ G
    instance
      CS₁ = Category.Str C₁
      CS₂ = Category.Str C₂

  opaque
    natural-transformationᵒᵖ-path :
      {η₁ η₂ : NaturalTransformationᵒᵖ F G} ->
      ((o : Obj C₁) -> NaturalTransformationᵒᵖ.obj η₁ o == NaturalTransformationᵒᵖ.obj η₂ o) ->
      η₁ == η₂
    natural-transformationᵒᵖ-path {η₁} {η₂} o-path =
      \i -> record { obj = \o -> o-path o i ; mor = mor-path i }
      where
      module η₁ = NaturalTransformationᵒᵖ η₁
      module η₂ = NaturalTransformationᵒᵖ η₂

      mor-path : PathP (\i -> {o₁ o₂ : Obj C₁} -> (m : C₁ →[ o₁ , o₂ ]) ->
                              o-path o₂ i ⋆ G.mor m == F.mor m ⋆ o-path o₁ i)
                       η₁.mor η₂.mor
      mor-path = isProp->PathP (\_ -> isPropΠⁱ2 \_ _ -> isPropΠ \_ -> isSet-Mor _ _)

  private
    NT-Obj : Type (ℓ-max ℓO₁ ℓM₂)
    NT-Obj = (o : Obj C₁) -> C₂ →[ F.obj o , G.obj o ]
    NT-Mor : NT-Obj -> Type (ℓ-max* 3 ℓO₁ ℓM₁ ℓM₂)
    NT-Mor obj =
      {o₁ o₂ : Obj C₁} -> (m : C₁ →[ o₁ , o₂ ]) ->
      obj o₂ ⋆ G.mor m == F.mor m ⋆ obj o₁

    NTΣ : Type (ℓ-max* 3 ℓO₁ ℓM₁ ℓM₂)
    NTΣ = Σ NT-Obj NT-Mor

    NT≃NTΣ : NaturalTransformationᵒᵖ F G ≃ NTΣ
    NT≃NTΣ = isoToEquiv (iso fwd bkw (\_ -> refl) (\_ -> refl))
      where
      fwd : NaturalTransformationᵒᵖ F G -> NTΣ
      fwd η = NaturalTransformationᵒᵖ.obj η , NaturalTransformationᵒᵖ.mor η
      bkw : NTΣ -> NaturalTransformationᵒᵖ F G
      bkw (o , m) = record { obj = o ; mor = m }

    isSet-NTΣ : isSet NTΣ
    isSet-NTΣ = isSetΣ (isSetΠ \_ -> isSet-Mor)
                     (\o -> isSetΠⁱ \_ -> isSetΠⁱ \_ -> isSetΠ \_ -> isProp->isSet (isSet-Mor _ _))

  opaque
    isSet-NaturalTransformationᵒᵖ : isSet (NaturalTransformationᵒᵖ F G)
    isSet-NaturalTransformationᵒᵖ = ≃-isSet (equiv⁻¹ NT≃NTΣ) isSet-NTΣ




module _
  {ℓO₁ ℓO₂ ℓM₁ ℓM₂ : Level}
  {C₁ : Category ℓO₁ ℓM₁}
  {C₂ : Category ℓO₂ ℓM₂}
  where
  private
    instance
      CS₁ = Category.Str C₁
      CS₂ = Category.Str C₂
    NT = NaturalTransformation


    id-NT : {F : Functor C₁ C₂} -> NT F F
    id-NT = record
      { obj = \_ -> id
      ; mor = \_ -> ⋆-left-id >=> sym ⋆-right-id
      }

    _⋆NT_ : {F G H : Functor C₁ C₂} -> NT F G -> NT G H -> NT F H
    _⋆NT_ η₁ η₂ = record
      { obj = \o -> η₁.obj o ⋆ η₂.obj o
      ; mor = \m -> ⋆-assoc >=> ⋆-right (η₂.mor _) >=>
                    sym ⋆-assoc >=> ⋆-left (η₁.mor _) >=>
                    ⋆-assoc
      }
      where
      module η₁ = NaturalTransformation η₁
      module η₂ = NaturalTransformation η₂

  instance
    Functor-CategoryStr : CategoryStr (NaturalTransformation {C₁ = C₁} {C₂ = C₂})
    Functor-CategoryStr = record
      { id = id-NT
      ; _⋆_ = _⋆NT_
      ; ⋆-left-idᵉ = \_ -> natural-transformation-path (\_ -> ⋆-left-id)
      ; ⋆-right-idᵉ = \_ -> natural-transformation-path (\_ -> ⋆-right-id)
      ; ⋆-assocᵉ = \_ _ _ -> natural-transformation-path (\_ -> ⋆-assoc)
      ; isSet-Mor = isSet-NaturalTransformation
      }






module _
  {ℓO₁ ℓO₂ ℓM₁ ℓM₂ : Level}
  {C₁ : Category ℓO₁ ℓM₁}
  {C₂ : Category ℓO₂ ℓM₂}
  where
  private
    instance
      CS₁ = Category.Str C₁
      CS₂ = Category.Str C₂
    NT = NaturalTransformationᵒᵖ


    module _ {F G H : Functorᵒᵖ C₁ C₂} (η₁ : NT F G) (η₂ : NT G H) where
      private
        module F = Functorᵒᵖ F
        module H = Functorᵒᵖ H
        module η₁ = NaturalTransformationᵒᵖ η₁
        module η₂ = NaturalTransformationᵒᵖ η₂

      ⋆NTᵒᵖ-obj : (o : Obj C₁) -> C₂ →[ F.obj o , H.obj o ]
      ⋆NTᵒᵖ-obj o = η₁.obj o ⋆ η₂.obj o

    id-NT : {F : Functorᵒᵖ C₁ C₂} -> NT F F
    id-NT = record
      { obj = \_ -> id
      ; mor = \_ -> ⋆-left-id >=> sym ⋆-right-id
      }

  module _ {F G H : Functorᵒᵖ C₁ C₂} {η₁ : NT F G} {η₂ : NT G H} where
    private
      module F = Functorᵒᵖ F
      module H = Functorᵒᵖ H
      module η₁ = NaturalTransformationᵒᵖ η₁
      module η₂ = NaturalTransformationᵒᵖ η₂
      obj = ⋆NTᵒᵖ-obj η₁ η₂
    opaque
      ⋆NTᵒᵖ-mor : ∀ {o₁ o₂ : Obj C₁} -> (m : C₁ →[ o₁ , o₂ ]) ->
            obj o₂ ⋆ H.mor m == F.mor m ⋆ obj o₁
      ⋆NTᵒᵖ-mor _ =
        ⋆-assoc >=> ⋆-right (η₂.mor _) >=>
        sym ⋆-assoc >=> ⋆-left (η₁.mor _) >=>
        ⋆-assoc

  _⋆NTᵒᵖ_ : {F G H : Functorᵒᵖ C₁ C₂} -> NT F G -> NT G H -> NT F H
  _⋆NTᵒᵖ_ {F} {G} {H} η₁ η₂ = record
    { obj = ⋆NTᵒᵖ-obj η₁ η₂
    ; mor = ⋆NTᵒᵖ-mor {η₁ = η₁} {η₂ = η₂}
    }


  instance
    Functorᵒᵖ-CategoryStr : CategoryStr (NaturalTransformationᵒᵖ {C₁ = C₁} {C₂ = C₂})
    Functorᵒᵖ-CategoryStr = record
      { id = id-NT
      ; _⋆_ = _⋆NTᵒᵖ_
      ; ⋆-left-idᵉ = \_ -> natural-transformationᵒᵖ-path (\_ -> ⋆-left-id)
      ; ⋆-right-idᵉ = \_ -> natural-transformationᵒᵖ-path (\_ -> ⋆-right-id)
      ; ⋆-assocᵉ = \_ _ _ -> natural-transformationᵒᵖ-path (\_ -> ⋆-assoc)
      ; isSet-Mor = isSet-NaturalTransformationᵒᵖ
      }


module _ {ℓO₁ ℓO₂ ℓM₁ ℓM₂ : Level} (C₁ : Category ℓO₁ ℓM₁) (C₂ : Category ℓO₂ ℓM₂) where
  FunctorC : Category (ℓ-max* 4 ℓO₁ ℓO₂ ℓM₁ ℓM₂) (ℓ-max* 3 ℓO₁ ℓM₁ ℓM₂)
  FunctorC = Category▪ (Functor-CategoryStr {C₁ = C₁} {C₂ = C₂})
  FunctorᵒᵖC : Category (ℓ-max* 4 ℓO₁ ℓO₂ ℓM₁ ℓM₂) (ℓ-max* 3 ℓO₁ ℓM₁ ℓM₂)
  FunctorᵒᵖC = Category▪ (Functorᵒᵖ-CategoryStr {C₁ = C₁} {C₂ = C₂})
