{-# OPTIONS --cubical --safe --exact-split #-}

module univalence where

open import base
open import cubical
open import equality-path
open import equivalence
open import hlevel.base
open import isomorphism

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A A1 A2 : Type ℓ

ua : ∀ {A B : Type ℓ} -> A ≃ B -> A == B
ua {A = A} {B = B} e i = Glue B (\ { (i = i0) -> (A , e)
                                   ; (i = i1) -> (B , idEquiv B) })

private
  uaIdEquiv : ∀ {A : Type ℓ} -> ua (idEquiv A) == refl
  uaIdEquiv {A = A} i j = Glue A {φ = i ∨ j ∨ ~ j} (\_ -> A , idEquiv A)

  unglueIsEquiv : (A : Type ℓ) (φ : I)
                  (f : PartialP φ (\_ -> Σ[ T ∈ Type ℓ ] (T ≃ A))) ->
                  isEquiv {A = Glue A f} (unglue φ)
  unglueIsEquiv A φ f .equiv-proof b =
    let
      u : I -> Partial φ A
      u i = \{ (φ = i1) -> eqCtr (f 1=1 .snd) b .snd (~ i) }
      ctr : fiber (unglue φ) b
      ctr = ( glue (\{ (φ = i1) -> eqCtr (f 1=1 .snd) b .fst }) (hcomp u b)
            , \j -> hfill u (inS b) (~ j))
    in (ctr
       , (\ v i ->
            let
              u' : I -> Partial (φ ∨ i ∨ ~ i) A
              u' j = \{ (φ = i1) -> eqCtrPath (f 1=1 .snd) b v i .snd (~ j)
                      ; (i = i0) -> hfill u (inS b) j
                      ; (i = i1) -> v .snd (~ j) }
            in ( glue (\{ (φ = i1) -> eqCtrPath (f 1=1 .snd) b v i .fst }) (hcomp u' b)
               , \j -> hfill u' (inS b) (~ j))))

  unglueEquiv : (A : Type ℓ) (φ : I) (f : PartialP φ (\_ -> Σ[ T ∈ Type ℓ ] (T ≃ A))) ->
                (Glue A f) ≃ A
  unglueEquiv A φ f = (unglue φ) , unglueIsEquiv A φ f

  -- Pulled from core library and transitively from.
  -- https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ
  --
  EquivContr : (A : Type ℓ) -> isContr (Σ[ T ∈ Type ℓ ] (T ≃ A))
  EquivContr A .fst = (A , idEquiv A)
  EquivContr {ℓ = ℓ} A .snd w = \ { i .fst -> Glue A (f i)
                                  ; i .snd .fst -> unglueEquiv _ _ (f i) .fst
                                  ; i .snd .snd .equiv-proof -> unglueEquiv _ _ (f i) .snd .equiv-proof
                                  }
    where
    f : (i : I) -> PartialP (i ∨ ~ i) (\x -> Σ[ T ∈ Type ℓ ] (T ≃ A))
    f i = \{ (i = i0) -> A , idEquiv A ; (i = i1) -> w }

  contrSingleEquiv : {A1 A2 : Type ℓ} (e : A1 ≃ A2) -> (A2 , idEquiv A2) == (A1 , e)
  contrSingleEquiv {A1 = A1} {A2 = A2} e =
    isContr->isProp (EquivContr A2) (A2 , idEquiv A2) (A1 , e)

  EquivJ : {A1 A2 : Type ℓ₁} (P : (A : Type ℓ₁) -> (e : A ≃ A2) -> Type ℓ₂) ->
           (r : P A2 (idEquiv A2)) -> (e : A1 ≃ A2) -> P A1 e
  EquivJ P r e = subst (\ (t , e) -> P t e) (contrSingleEquiv e) r

  module Univalence (au : {ℓ : Level} {A1 A2 : Type ℓ} -> A1 == A2 -> A1 ≃ A2)
                    (au-refl : {ℓ : Level} {A : Type ℓ} -> au (refl) == idEquiv A) where
    ua-au : {A1 A2 : Type ℓ} -> (p : A1 == A2) -> ua (au p) == p
    ua-au = J (\_ p -> ua (au p) == p) (cong ua au-refl >=> uaIdEquiv)

    au-ua : {A1 A2 : Type ℓ} -> (e : A1 ≃ A2) -> au (ua e) == e
    au-ua = EquivJ (\_ e -> au (ua e) == e) (cong au uaIdEquiv >=> au-refl)

    i : {A1 A2 : Type ℓ} -> Iso (A1 == A2) (A1 ≃ A2)
    i .Iso.fun = au
    i .Iso.inv = ua
    i .Iso.rightInv = au-ua
    i .Iso.leftInv = ua-au


  equivEq : {A1 : Type ℓ₁} {A2 : Type ℓ₂} {e1 e2 : A1 ≃ A2} (p : e1 .fst == e2 .fst) -> e1 == e2
  equivEq p i .fst = p i
  equivEq {e1 = e1} {e2 = e2} p i .snd =
    isProp->PathPᵉ (\i -> isProp-isEquiv {f = p i}) (e1 .snd) (e2 .snd) i

  pathToEquiv-refl : pathToEquiv refl == idEquiv A
  pathToEquiv-refl {A = A} = equivEq (\i x -> transp (\_ -> A) i x)

univalence-iso : Iso (A1 == A2) (A1 ≃ A2)
univalence-iso = Univalence.i pathToEquiv pathToEquiv-refl

univalence : (A1 == A2) ≃ (A1 ≃ A2)
univalence = isoToEquiv univalence-iso

isoToPath : Iso A1 A2 -> A1 == A2
isoToPath f = ua (isoToEquiv f)

isoToPath-id-iso : Path (A == A) (isoToPath id-iso) refl
isoToPath-id-iso = cong ua isoToEquiv-id-iso >=> uaIdEquiv

transport-isoToPath : (i : Iso A1 A2) -> transport (isoToPath i) == Iso.fun i
transport-isoToPath i j x = transportRefl (Iso.fun i x) j -- (Iso.fun i x) j
