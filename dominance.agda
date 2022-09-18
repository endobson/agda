{-# OPTIONS --cubical --safe --exact-split #-}

module dominance where

open import base
open import equality-path
open import hlevel
open import equivalence
open import cubical renaming (I to I₀)
open import isomorphism
open import relation
open import univalence
open import type-algebra
open import sigma
open import sigma.base
open import funext
open import functions
open import transport

record isDominance {ℓ : Level} (D : Type ℓ -> Type ℓ) : Type (ℓ-suc ℓ) where
  field
    isProp-D : ∀ X -> isProp (D X)
    isProp-X : ∀ X -> D X -> isProp X
    D-Top : D (Lift ℓ Top)
    closed : ∀ X (Y : X -> Type ℓ) -> D X -> (∀ x -> D (Y x)) -> D (Σ X Y)

Dominance : (ℓ : Level) -> Type (ℓ-suc ℓ)
Dominance ℓ = Σ (Type ℓ -> Type ℓ) isDominance

Dominance-isContr : {ℓ : Level} -> Dominance ℓ
Dominance-isContr = isContr , record
  { isProp-D = \_ -> isProp-isContr
  ; isProp-X = \_ c -> isContr->isProp c
  ; D-Top = lift tt , \_ -> refl
  ; closed = \_ _ -> isContrΣ
  }

Dominance-isProp : {ℓ : Level} -> Dominance ℓ
Dominance-isProp = isProp , record
  { isProp-D = \_ -> isProp-isProp
  ; isProp-X = \_ c -> c
  ; D-Top = ≃-isProp (equiv⁻¹ (liftEquiv _ Top)) isPropTop
  ; closed = \_ _ -> isPropΣ
  }

Dominance-Dec : {ℓ : Level} -> Dominance ℓ
Dominance-Dec {ℓ} = D , record
  { isProp-D = isProp-D
  ; isProp-X = isProp-X
  ; D-Top = D-Top
  ; closed = closed
  }
  where
  D : Type ℓ -> Type ℓ
  D X = isProp X × Dec X

  isProp-D : ∀ X -> isProp (D X)
  isProp-D _ = isPropΣ isProp-isProp isPropDec

  isProp-X : ∀ X -> D X -> isProp X
  isProp-X _ = proj₁

  D-Top : D (Lift ℓ Top)
  D-Top = ≃-isProp (equiv⁻¹ (liftEquiv _ Top)) isPropTop , yes (lift tt)

  closed : ∀ X (Y : X -> Type ℓ) -> D X -> (∀ x -> D (Y x)) -> D (Σ X Y)
  closed X Y DX DY = isPropΣ (proj₁ DX) (\x -> proj₁ (DY x)) ,
                     (handle DX)
    where
    handle : D X -> Dec (Σ X Y)
    handle (isProp-X , yes x) with (DY x)
    ... | (_ , yes y) = yes (x , y)
    ... | (_ , no ¬y) = no \{ (x2 , y) -> ¬y (subst Y (isProp-X x2 x) y) }
    handle (_ , no ¬x) = no \{ (x , _) -> ¬x x }

PartialMap : {ℓ : Level} (D : Dominance ℓ) (X Y : Type ℓ) -> Type (ℓ-suc ℓ)
PartialMap {ℓ} (D , _) X Y = Σ[ R ∈ (REL X Y ℓ) ] (∀ (x : X) -> D (Σ Y (R x)))

PartialElement : {ℓ : Level} (D : Dominance ℓ) (Y : Type ℓ) -> Type (ℓ-suc ℓ)
PartialElement {ℓ} (D , _) Y = Σ[ I ∈ Type ℓ ] ((D I) × (I -> Y))

PartialMap≃MapPartialElement : {ℓ : Level} (D : Dominance ℓ) (X Y : Type ℓ) ->
                               PartialMap D X Y ≃ (X -> PartialElement D Y)
PartialMap≃MapPartialElement {ℓ} D X Y =
  isoToEquiv (iso forward backward forward-backward backward-forward)
  where
  forward : PartialMap D X Y -> X -> PartialElement D Y
  forward (R , DR) x = Σ Y (R x) , (DR x , fst)

  forward-fib : (f : X -> PartialElement D Y) -> fiber forward f
  forward-fib f = (R , DR) , p
    where
    R : REL X Y ℓ
    R x y = Σ[ i ∈ (fst (f x)) ] (snd (snd (f x)) i == y)

    module _ (x : X) where
      Rx : Pred Y ℓ
      Rx = R x

      I : Type ℓ
      I = fst (f x)
      DI : ⟨ D ⟩ I
      DI = fst (snd (f x))
      g : I -> Y
      g = snd (snd (f x))

      I-eq : I ≃ Σ Y Rx
      I-eq = ((Σ-isContr-eq (\i -> isContr-singleton (g i))) >eq> Σ-swap-eq)

      I-path : I == Σ Y Rx
      I-path = ua I-eq

      DR : ⟨ D ⟩ (Σ Y Rx)
      DR = transport (cong ⟨ D ⟩ I-path) DI

      I-path-D : PathP (\i -> (⟨ D ⟩ (I-path i))) DI DR
      I-path-D = isProp->PathP (\i -> isDominance.isProp-D (snd D) (I-path i))

      I-path-g : PathP (\i -> ((I-path i) -> Y)) g (fst)
      I-path-g = transP-right (sym transport-reduce) filler
        where
        filler : PathP (\i -> ((I-path i) -> Y))
                       (transport (\i -> ((I-path (~ i)) -> Y)) fst) fst
        filler = symP (transport-filler (\i -> ((I-path (~ i)) -> Y)) fst)

        transport-reduce : (transport (\i -> ((I-path (~ i)) -> Y)) fst) == g
        transport-reduce =
          transportβ-fun-domain (sym I-path) fst >=>
          funExt (\i -> cong fst (transportβ-ua I-eq i))


    p : forward (R , DR) == f
    p i x = I-path x (~ i) , I-path-D x (~ i) , I-path-g x (~ i)

  backward : (X -> PartialElement D Y) -> PartialMap D X Y
  backward f = fst (forward-fib f)

  forward-backward : (f : X -> PartialElement D Y) -> (forward (backward f)) == f
  forward-backward f = snd (forward-fib f)

  backward-forward : (f : PartialMap D X Y) -> (backward (forward f)) == f
  backward-forward f = ΣProp-path (isPropΠ (\x -> isDominance.isProp-D (snd D) _)) R-path
    where
    R : REL X Y ℓ
    R = fst f

    R' : REL X Y ℓ
    R' x y = Σ[ yr ∈ (Σ Y (R x)) ] (fst yr == y)

    R-eq : ∀ x y -> R' x y ≃ R x y
    R-eq x y = isoToEquiv (iso fr br fbr bfr)
      where
      fr : R' x y -> R x y
      fr ((y' , r) , p) = substᵉ (R x) p r
      br : R x y -> R' x y
      br r = (y , r) , refl
      fbr : ∀ r -> fr (br r) == r
      fbr r = transportRefl r
      bfr : ∀ r' -> br (fr r') == r'
      bfr ((y' , r) , p) = ans
        where
        ans : ((y , substᵉ (R x) p r) , refl) == ((y' , r) , p)
        ans i = ((p (~ i) , subst-filler (R x) p r (~ i)) , (\j -> p (~ i ∨ j)))

    R-path : R' == R
    R-path = funExt2 (\x y -> ua (R-eq x y))
