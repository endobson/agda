{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.sequence where

open import base
open import cubical
open import nat
open import equality-path
open import functions
open import hlevel.base
open import equivalence
open import isomorphism
open import type-algebra
open import pointed.base
open import univalence
open import equivalence.base


record Short3Sequence (ℓA ℓB ℓC : Level) : Type (ℓ-suc (ℓ-max* 3 ℓA ℓB ℓC)) where
  field
    A∙ : Type∙ ℓA
    B∙ : Type∙ ℓB
    C∙ : Type∙ ℓC
    f∙ : A∙ ->∙ B∙
    g∙ : B∙ ->∙ C∙

  A : Type ℓA
  A = fst A∙
  B : Type ℓB
  B = fst B∙
  C : Type ℓC
  C = fst C∙

  ★A : A
  ★A = snd A∙
  ★B : B
  ★B = snd B∙
  ★C : C
  ★C = snd C∙

  f : A -> B
  f = app∙ f∙
  g : B -> C
  g = app∙ g∙

  fp : f ★A == ★B
  fp = ->∙-path f∙
  gp : g ★B == ★C
  gp = ->∙-path g∙


record ℕ⁺-Sequence (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Ty∙ : ℕ -> Type∙ ℓ
    f∙ : (n : ℕ) -> Ty∙ n ->∙ Ty∙ (suc n)

record ℕ⁻-Sequence (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Ty∙ : ℕ -> Type∙ ℓ
    f∙ : (n : ℕ) -> Ty∙ (suc n) ->∙ Ty∙ n

  Ty : ℕ -> Type ℓ
  Ty n = ⟨ Ty∙ n ⟩
  f : (n : ℕ) -> Ty (suc n) -> Ty n
  f n = app∙ (f∙ n)

  short3 : ℕ -> Short3Sequence ℓ ℓ ℓ
  short3 i = record
    { A∙ = Ty∙ (suc (suc i))
    ; B∙ = Ty∙ (suc i)
    ; C∙ = Ty∙ i
    ; f∙ = f∙ (suc i)
    ; g∙ = f∙ i
    }


module _ {ℓA ℓB ℓC : Level} (S : Short3Sequence ℓA ℓB ℓC) where
  open Short3Sequence S

  record isFiberSequence-Short3 : Type (ℓ-max* 3 ℓA ℓB ℓC) where
    field
      isNull : ∀ a -> app∙ g∙ (app∙ f∙ a) == ★C
      isNull-Square :
        Square (isNull ★A) (->∙-path g∙) (cong (app∙ g∙) (->∙-path f∙)) refl

    total : A -> fiber (app∙ g∙) ★C
    total a = app∙ f∙ a , (isNull a)

    field
      isEquiv-total : isEquiv total

module _ {ℓA ℓB ℓC : Level} (S : Short3Sequence ℓA ℓB ℓC) where
  open Short3Sequence S

  record isFiberSequence-Short3' : Type (ℓ-max* 3 ℓA ℓB ℓC) where
    field
      isNull : f∙ >∙> g∙ == const->∙

    total : A -> ⟨ fiber∙ g∙ ⟩
    total a = app∙ f∙ a , (\i -> app∙ (isNull i) a)

    field
      isEquiv-total : isEquiv total




module _ {ℓ : Level} (S : ℕ⁻-Sequence ℓ) where

  record isFiberSequence-ℕ⁻ : Type ℓ where
    field
      isFiberSeq-short3 : ∀ n -> isFiberSequence-Short3 (ℕ⁻-Sequence.short3 S n)


module _ {ℓC ℓA : Level} (C∙@(C , ★C) : Type∙ ℓC) (f : C -> Type∙ ℓA) where
  TotalSpace∙ : Type∙ (ℓ-max ℓA ℓC)
  TotalSpace∙ = Σ C (fst ∘ f) , (★C , snd (f ★C))

module _ {ℓC ℓA : Level} (C∙@(C , ★C) : Type∙ ℓC) (f : C -> Type ℓA) (★f : f ★C)  where

  private
    Seq : Short3Sequence ℓA (ℓ-max ℓA ℓC) ℓC
    Seq = record
      { A∙ = f ★C , ★f
      ; B∙ = Σ∙ C∙ f ★f
      ; C∙ = C∙
      ; f∙ = ->∙-cons (\a -> ★C , a) refl
      ; g∙ = ->∙-cons fst refl
      }

    open Short3Sequence Seq hiding (C ; ★C ; f)

    isFiber-Seq : isFiberSequence-Short3 Seq
    isFiber-Seq = record
      { isNull = \a -> refl
      ; isNull-Square = \_ _ -> ★C
      ; isEquiv-total = isEquiv-total'
      }
      where
      total' : A -> fiber (app∙ g∙) ★C
      total' a = (★C , a) , \i -> ★C

      isEquiv-total' : isEquiv total'
      isEquiv-total' = snd (isoToEquiv (iso total' inv fb bf))
        where
        inv : fiber (app∙ g∙) ★C -> A
        inv ((c , a) , p) = transport (cong f p) a

        fb : ∀ x -> total' (inv x) == x
        fb ((c , a) , p) j = (p (~ j) , (transport-filler (cong f p) a (~ j))) , (\k -> p (k ∨ ~ j))
        bf : ∀ x -> inv (total' x) == x
        bf a = transportRefl a


  fibration->ShortFiberSequence : Σ (Short3Sequence ℓA (ℓ-max ℓA ℓC) ℓC) isFiberSequence-Short3
  fibration->ShortFiberSequence = Seq , isFiber-Seq

module _ {ℓB ℓC : Level} {B∙@(B , ★B) : Type∙ ℓB} {C∙@(C , ★C) : Type∙ ℓC} (f : B∙ ->∙ C∙) where

  private
    Seq : Short3Sequence (ℓ-max ℓB ℓC) ℓB ℓC
    Seq = record
      { A∙ = fiber (app∙ f) ★C , (★B , ->∙-path f)
      ; B∙ = B∙
      ; C∙ = C∙
      ; f∙ = ->∙-cons fst refl
      ; g∙ = f
      }

    open Short3Sequence Seq hiding (B ; C ; ★B ; ★C)

    isFiber-Seq : isFiberSequence-Short3 Seq
    isFiber-Seq = record
      { isNull = \ (b , p) j -> p j
      ; isNull-Square = refl
      ; isEquiv-total = idIsEquiv _
      }


  function->ShortFiberSequence :
    Σ (Short3Sequence (ℓ-max ℓB ℓC) ℓB ℓC) isFiberSequence-Short3
  function->ShortFiberSequence = Seq , isFiber-Seq




module _ {ℓB ℓC : Level} {B∙@(B , ★B) : Type∙ ℓB} {C∙@(C , ★C) : Type∙ ℓC} (g∙ : B∙ ->∙ C∙) where

  isFiberSeqExtension : (Σ[ A∙ ∈ Type∙ (ℓ-max ℓB ℓC) ] (A∙ ->∙ B∙)) -> Type _
  isFiberSeqExtension (A∙ , f∙) =
    isFiberSequence-Short3 (record { A∙ = A∙ ; B∙ = B∙ ; C∙ = C∙ ; f∙ = f∙ ; g∙ = g∙ })

  private
    Std-Seq : Σ (Short3Sequence (ℓ-max ℓB ℓC) ℓB ℓC) isFiberSequence-Short3
    Std-Seq = function->ShortFiberSequence g∙
    FS₁ = (snd Std-Seq)
    module S₁ = Short3Sequence (fst Std-Seq)
    module FS₁ = isFiberSequence-Short3 FS₁

    A₁ = S₁.A
    A₁∙ = S₁.A∙
    ★A₁ = snd S₁.A∙
    f₁∙ = S₁.f∙

  private
    module _ (E₂@((A₂∙@(A₂ , ★A₂) , f₂∙) , FS₂)  :
              (Σ (Σ[ A∙ ∈ Type∙ (ℓ-max ℓB ℓC) ] (A∙ ->∙ B∙))
                 isFiberSeqExtension)) where
      private
        module FS₂ = isFiberSequence-Short3 FS₂

      opaque
        isSame-ΣisFiberSeqExtension : ((A₁∙ , f₁∙) , FS₁) == E₂
        isSame-ΣisFiberSeqExtension =
          \i ->
            (A∙-path (~ i) , f∙-pathp (~ i)) ,
            record
              { isNull = isNull-pathp (~ i)
              ; isNull-Square = isNullSquare-pathp (~ i)
              ; isEquiv-total = isEquiv-total-pathp (~ i)
              }
          where
          A-eq : A₂ ≃ A₁
          A-eq = (_ , isFiberSequence-Short3.isEquiv-total FS₂)
          A-path : A₂ == A₁
          A-path = ua A-eq
          ★A-path : eqFun A-eq ★A₂ == ★A₁
          ★A-path j = ->∙-path f₂∙ j , FS₂.isNull-Square j
          ★A-pathp : PathP (\i -> A-path i) ★A₂ ★A₁
          ★A-pathp = ua-value-pathp A-eq ★A₂ ★A₁ ★A-path

          A∙-path : A₂∙ == A₁∙
          A∙-path = Type∙-path (A-eq , ★A-path)

          f-path : app∙ f₂∙ == app∙ f₁∙ ∘ eqFun A-eq
          f-path = refl
          f-pathp : PathP (\i -> fst (A∙-path i) -> B) (app∙ f₂∙) (app∙ f₁∙)
          f-pathp i a = app∙ f₁∙ (ua-unglue A-eq i a)

          f∙-pathp : PathP (\i -> (A∙-path i) ->∙ B∙) f₂∙ f₁∙
          f∙-pathp i = ->∙-cons (f-pathp i) (\j -> ->∙-path f₂∙ (i ∨ j))

          Af-path : (A₂∙ , f₂∙) == (A₁∙ , f₁∙)
          Af-path i = A∙-path i , f∙-pathp i

          isNull-pathp : PathP (\i -> (a : A-path i) -> app∙ g∙ (f-pathp i a) == ★C)
                               FS₂.isNull FS₁.isNull
          isNull-pathp i a j = FS₁.isNull (ua-unglue A-eq i a) j

          check-isNullSquare₁ : FS₁.isNull-Square == reflᵉ (->∙-path g∙)
          check-isNullSquare₁ = refl

          check-isNullSquare₂ : FS₂.isNull-Square i1 == (->∙-path g∙)
          check-isNullSquare₂ = refl

          isNullSquare-pathp :
            PathP (\i -> Square (isNull-pathp i (★A-pathp i)) (->∙-path g∙)
                                (cong (app∙ g∙) (->∙-path (f∙-pathp i))) refl)
                  FS₂.isNull-Square FS₁.isNull-Square
          isNullSquare-pathp i j k = FS₂.isNull-Square (j ∨ i) k

          total-pathp : PathP (\i -> A-path i -> fiber (app∙ g∙) ★C)
                              FS₂.total FS₁.total
          total-pathp i a = f-pathp i a , isNull-pathp i a

          isEquiv-total-pathp : PathP (\i -> isEquiv (total-pathp i))
                                      FS₂.isEquiv-total FS₁.isEquiv-total
          isEquiv-total-pathp = isProp->PathP (\i -> isProp-isEquiv)


  isContr-ΣisFiberSeqExtension :
    isContr (Σ (Σ[ A∙ ∈ Type∙ (ℓ-max ℓB ℓC) ] (A∙ ->∙ B∙))
               isFiberSeqExtension)
  isContr-ΣisFiberSeqExtension =
    ((A₁∙ , f₁∙) , FS₁) , isSame-ΣisFiberSeqExtension
