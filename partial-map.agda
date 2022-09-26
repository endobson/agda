{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import cubical renaming (I to I₀)
open import dominance
open import equality-path
open import equivalence
open import functions
open import funext
open import hlevel
open import isomorphism
open import relation
open import sigma
open import sigma.base
open import transport
open import truncation
open import type-algebra
open import univalence

module partial-map where

private
  variable
    ℓ : Level

PartialMap : (D : Dominance ℓ) (X Y : Type ℓ) -> Type (ℓ-suc ℓ)
PartialMap {ℓ} (D , _) X Y = Σ[ R ∈ (REL X Y ℓ) ] (∀ (x : X) -> D (Σ Y (R x)))

PartialMap-Rel-path : {A B : Type ℓ} (D : Dominance ℓ) {m1 m2 : PartialMap D A B} -> 
                      (fst m1) == (fst m2) -> m1 == m2
PartialMap-Rel-path D p = ΣProp-path (isPropΠ (\x -> Dominance.isProp-D D _)) p

PartialElement : (D : Dominance ℓ) (Y : Type ℓ) -> Type (ℓ-suc ℓ)
PartialElement {ℓ} (D , _) Y = Σ[ I ∈ Type ℓ ] ((D I) × (I -> Y))

InverseRelations : {ℓ : Level} {A B : Type ℓ} -> REL (REL A B ℓ) (REL B A ℓ) ℓ
InverseRelations R1 R2 = ∀ a b -> R1 a b ≃ R2 b a

InversePartialMaps : {X Y : Type ℓ} (D : Dominance ℓ) -> 
                     REL (PartialMap D X Y) (PartialMap D Y X) ℓ
InversePartialMaps D m1 m2 = (InverseRelations (fst m1) (fst m2))

Symmetric-InversePartialMaps : 
  {X Y : Type ℓ} -> (D : Dominance ℓ) -> 
  (m1 : PartialMap D X Y) -> (m2 : PartialMap D Y X) -> 
  InversePartialMaps D m1 m2 -> InversePartialMaps D m2 m1
Symmetric-InversePartialMaps D m1 m2 inv y x = equiv⁻¹ (inv x y)

isInvertibleMap : {X Y : Type ℓ} (D : Dominance ℓ) -> Pred (PartialMap D X Y) (ℓ-suc ℓ)
isInvertibleMap {X = X} {Y} D m1 = ∃ (PartialMap D Y X) (InversePartialMaps D m1)

module _ {ℓ : Level} {X Y : Type ℓ} (D : Dominance ℓ) where
  isLeftInverse : REL (PartialMap D X Y) (PartialMap D Y X) ℓ
  isLeftInverse m1 m2 = (∀ y -> (Σ[ x ∈ X ] (R1 x y)) ≃ (Σ[ x ∈ X ] (R2 y x)))
    where
    R1 = fst m1
    R2 = fst m2
  
  isRightInverse : REL (PartialMap D X Y) (PartialMap D Y X) ℓ
  isRightInverse m1 m2 = (∀ x -> (Σ[ y ∈ Y ] (R1 x y)) ≃ (Σ[ y ∈ Y ] (R2 y x)))
    where
    R1 = fst m1
    R2 = fst m2

  isProp-isLeftInverse : ∀ m1 m2 -> isProp (isLeftInverse m1 m2)
  isProp-isLeftInverse m1 m2 = isPropΠ (\y -> isProp-≃-right (Dominance.isProp-X D _ (snd m2 y)))

  isProp-isRightInverse : ∀ m1 m2 -> isProp (isRightInverse m1 m2)
  isProp-isRightInverse m1 m2 = isPropΠ (\x -> isProp-≃-left (Dominance.isProp-X D _ (snd m1 x)))


module _ {ℓ : Level} {X Y : Type ℓ} (D : Dominance ℓ) (m : PartialMap D X Y) 
         (inv : isInvertibleMap D m) (isPropR : ∀ x y -> isProp (⟨ m ⟩ x y)) where
  private
    inverses-same : isProp (Σ (PartialMap D Y X) (InversePartialMaps D m))
    inverses-same (m2 , inv2) (m3 , inv3) = ΣProp-path (\{m'} -> isProp-inverse {m'}) m2=m3
      where
      isProp-inverse : {m' : PartialMap D Y X} -> isProp (InversePartialMaps D m m')
      isProp-inverse {m'} in1 in2 = funExt2 (\a b -> isProp-≃-left (isPropR a b) (in1 a b) (in2 a b))
      
      m2=m3 : m2 == m3
      m2=m3 = PartialMap-Rel-path D (funExt2 (\ x y -> ua (equiv⁻¹ (inv2 y x) >eq> (inv3 y x))))
  
    unique-inverse' : (Σ (PartialMap D Y X) (InversePartialMaps D m))
    unique-inverse' = unsquash inverses-same inv

  unique-inverse : isContr (Σ (PartialMap D Y X) (InversePartialMaps D m))
  unique-inverse = unique-inverse' , inverses-same unique-inverse'


module _ {ℓ : Level} {X Y : Type ℓ} (D : Dominance ℓ) (m : PartialMap D X Y) 
         (inv : isInvertibleMap D m) (setY : isSet Y) where
  private
    propR : ∀ x y -> isProp (⟨ m ⟩ x y) 
    propR x y r1 r2 = 
      subst (\p -> (PathP (\i -> ⟨ m ⟩ x (p i)) r1 r2)) path2-refl path3
      where
      path1 : Path (Σ Y (⟨ m ⟩ x)) (y , r1) (y , r2)
      path1 = Dominance.isProp-X D _ (snd m x) _ _
  
      path2 : Path Y y y
      path2 = cong fst path1
  
      path3 : PathP (\i -> ⟨ m ⟩ x (path2 i)) r1 r2
      path3 = cong snd path1
  
      path2-refl : path2 == refl
      path2-refl = setY y y path2 refl

  setPartialMap-unique-inverse : isContr (Σ (PartialMap D Y X) (InversePartialMaps D m))
  setPartialMap-unique-inverse = unique-inverse D m inv propR


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
      I-path-D = isProp->PathP (\i -> Dominance.isProp-D D (I-path i))

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
  backward-forward f = ΣProp-path (isPropΠ (\x -> Dominance.isProp-D D _)) R-path
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
