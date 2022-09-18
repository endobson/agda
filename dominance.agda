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


domain-eq : {ℓ : Level} {A B C : Type ℓ} -> A ≃ B -> (A -> C) ≃ (B -> C)
domain-eq {ℓ} {A} {B} {C} eq = isoToEquiv (iso forward backward fb bf)
  where
  forward : (A -> C) -> (B -> C)
  forward ac b = ac (eqInv eq b)

  backward : (B -> C) -> (A -> C)
  backward bc a = bc (eqFun eq a)

  fb : ∀ bc -> forward (backward bc) == bc
  fb bc i b = bc (eqSec eq b i)

  bf : ∀ ac -> backward (forward ac) == ac
  bf ac i a = ac (eqRet eq a i)

-- module _ {ℓ : Level} (D : Dominance ℓ) (X Y : Type ℓ) where
--   private
--     forward : PartialMap D X Y -> X -> PartialElement D Y
--     forward (R , DR) x = Σ Y (R x) , (DR x , fst)
-- 
--   module _ (x : X) (e : PartialElement D Y) where
--     I = fst e
--     DI = fst (snd e)
--     g = snd (snd e)
-- 
--     DIg : (⟨ D ⟩ I × (I -> Y))
--     DIg = snd e
-- 
--     R : Y -> Type ℓ
--     R y = fiber g y
-- 
--     I≃ΣYR : I ≃ Σ Y R
--     I≃ΣYR = ((Σ-isContr-eq (\i -> isContr-singleton (g i))) >eq> Σ-swap-eq)
-- 
-- 
--     DR : ⟨ D ⟩ (Σ Y R)
--     DR = substᵉ ⟨ D ⟩ (ua I≃ΣYR) DI
-- 
--     pmap : PartialMap D X Y
--     pmap = (\_ -> R) , (\_ -> DR)
-- 
-- 
--     pmap3 : PathP (\ i -> (ua I≃ΣYR (~ i) -> Y)) 
--                   fst (transport (\i -> ua I≃ΣYR (~ i) -> Y) fst)
--     pmap3 = transport-filler (\i -> ua I≃ΣYR (~ i) -> Y) fst
-- 
--     pmap4 : Path (I -> Y)
--                  (transport (\i -> ua I≃ΣYR (~ i) -> Y) fst) g
--     pmap4 = 
--       transportβ-fun-domain (sym (ua I≃ΣYR)) fst >=>
--       funExt (\i -> cong fst (transportβ-ua I≃ΣYR i))
-- 
--     pmap2 : PathP (\ i -> (ua I≃ΣYR i -> Y)) g fst
--     pmap2 = transP-right (sym pmap4) (symP pmap3)
-- 
-- 
-- 
--     pmap-pathP : PathP (\ i -> ⟨ D ⟩ (ua I≃ΣYR (~ i)) × ((ua I≃ΣYR (~ i)) -> Y)) 
--                        (DR , fst) DIg
--     pmap-pathP i = subst-filler ⟨ D ⟩ (ua I≃ΣYR) DI (~ i) , pmap2 (~ i)
-- 
--     pmap-path : forward pmap x == e
--     pmap-path i = (ua I≃ΣYR (~ i)) , pmap-pathP i






PartialMap≃MapPartialElement : {ℓ : Level} (D : Dominance ℓ) (X Y : Type ℓ) -> 
                               PartialMap D X Y ≃ (X -> PartialElement D Y)
PartialMap≃MapPartialElement {ℓ} D X Y = 
  isoToEquiv (iso forward backward backward'2 forward')
  -- forward , record { equiv-proof = \f -> backward' f , prop-fibers f (backward' f) }
  where
  forward : PartialMap D X Y -> X -> PartialElement D Y
  forward (R , DR) x = Σ Y (R x) , (DR x , fst)

  backward' : (f : X -> PartialElement D Y) -> fiber forward f
  backward' f = (R , DR) , p
    where
    I : X -> Type ℓ
    I x = fst (f x)
    DI : (x : X) -> ⟨ D ⟩ (I x)
    DI x = fst (snd (f x))
    g : (x : X) -> I x -> Y
    g x = snd (snd (f x))

    DIg : (x : X) -> (⟨ D ⟩ (I x) × ((I x) -> Y))
    DIg x = snd (f x)

    R : REL X Y ℓ
    R x y = Σ[ i ∈ I x ] (g x i == y)

    I≃ΣY[Rx] : (x : X) -> I x ≃ Σ Y (R x)
    I≃ΣY[Rx] x = ((Σ-isContr-eq (\i -> isContr-singleton (g x i))) >eq> Σ-swap-eq)


    I≃ΣY[Rx]-take2 : (x : X) -> I x ≃ Σ Y (R x)
    I≃ΣY[Rx]-take2 x = isoToEquiv (iso f2 b2 fb2 bf2)
      where
      f2 : I x -> Σ Y (R x)
      f2 ix = g x ix , (ix , refl)

      b2 : Σ Y (R x) -> I x
      b2 (y , ix , p) = ix

      bf2 : ∀ ix -> b2 (f2 ix) == ix
      bf2 ix = refl

      fb2 : ∀ yr -> f2 (b2 yr) == yr
      fb2 (y , ix , p) i = p i , ix , (\j -> p (i ∧ j))



    I=ΣY[Rx] : (x : X) -> I x == Σ Y (R x)
    I=ΣY[Rx] x = ua (I≃ΣY[Rx] x)


    I≃ΣY[Rx]' : (x : X) -> (I x -> Y) ≃ (Σ Y (R x) -> Y)
    I≃ΣY[Rx]' x = domain-eq (I≃ΣY[Rx] x)

    I=ΣY[Rx]' : (x : X) -> (I x -> Y) == (Σ Y (R x) -> Y)
    I=ΣY[Rx]' x = ua (I≃ΣY[Rx]' x)

    I=ΣY[Rx]'P : (x : X) -> PathP (\i -> 
                  I=ΣY[Rx] x (~ i) -> Y) fst (transport (\i -> I=ΣY[Rx] x (~ i) -> Y) fst)
    I=ΣY[Rx]'P x = transport-filler (\i -> I=ΣY[Rx] x (~ i) -> Y) fst



    -- check-transport : (x : X) -> (transport (\i -> I=ΣY[Rx] x (~ i) -> Y) fst) == g x
    -- check-transport x = funExt path1
    --   where
    --   path1 : (z : I x) -> 
    --           transp (\i -> Y) i0 (fst (transp (λ j → I=ΣY[Rx] x (~ (i0 ∨ ~ j))) (i0 ∨ i0) z)) ==
    --           (g x z)
    --   path1 z = path2 >=> path3
    --     where
    --     path2 : transp (\i -> Y) i0 (fst (transp (λ j → I=ΣY[Rx] x (~ (i0 ∨ ~ j))) (i0 ∨ i0) z)) ==
    --             (fst (transp (λ j → I=ΣY[Rx] x (~ (i0 ∨ ~ j))) (i0 ∨ i0) z))
    --     path2 k = transp (\i -> Y) k (fst (transp (λ j → I=ΣY[Rx] x (~ (i0 ∨ ~ j))) (i0 ∨ i0) z))




    I≃ΣY[Rx]'2 : (x : X) -> ⟨ D ⟩ (I x) ≃ ⟨ D ⟩ (Σ Y (R x))
    I≃ΣY[Rx]'2 x = pathToEquiv (cong ⟨ D ⟩ (I=ΣY[Rx] x))


    I≃ΣY[Rx]'3 : (x : X) -> (⟨ D ⟩ (I x) × (I x -> Y)) ≃ 
                            (⟨ D ⟩ (Σ Y (R x)) × (Σ Y (R x) -> Y))
    I≃ΣY[Rx]'3 x = ×-equiv (I≃ΣY[Rx]'2 x) (I≃ΣY[Rx]' x)



    yfst : (x : X) -> Σ Y (R x) -> Y
    yfst _ = fst




    check-eq1 : (x : X) -> (fst ∘ eqFun (I≃ΣY[Rx] x)) == g x
    check-eq1 x = refl

    check-eq3 : (x : X) -> I₀ -> I=ΣY[Rx]' x i0 -- PathP (\i -> I=ΣY[Rx]' x (~ i)) fst (g x)
    check-eq3 x _ = transport-filler (ua (equiv⁻¹ (I≃ΣY[Rx]' x))) fst i1 
      -- transport-filler (ua (equiv⁻¹ (I≃ΣY[Rx]' x))) fst
      where
      P : Path (Type ℓ) (Σ Y (R x) -> Y) (I x -> Y) 
      P = (ua (equiv⁻¹ (I≃ΣY[Rx]' x)))

      check-eq3-0 : (i : I₀) -> (P i0)
      check-eq3-0 i = transport-filler (ua (equiv⁻¹ (I≃ΣY[Rx]' x))) fst i0
      check-eq3-1 : (i : I₀) -> (P i1)
      check-eq3-1 i = transport-filler (ua (equiv⁻¹ (I≃ΣY[Rx]' x))) fst i1
      check-eq3-2 : PathP (\i -> P i) fst (transport P fst)
      check-eq3-2 = transport-filler P fst

    DR' : (x : X) -> ⟨ D ⟩ (Σ Y (R x)) × ((Σ Y (R x)) -> Y)
    DR' x = eqFun (I≃ΣY[Rx]'3 x) (DIg x)

    DR : (x : X) -> ⟨ D ⟩ (Σ Y (R x))
    DR x = fst (DR' x)

    I=ΣY[Rx]'6 : (x : X) -> PathP (\i -> (⟨ D ⟩ (I=ΣY[Rx] x i))) (DI x) (DR x)
    I=ΣY[Rx]'6 x = isProp->PathP (\i -> isDominance.isProp-D (snd D) (I=ΣY[Rx] x i))

    I=ΣY[Rx]'7 : (x : X) -> PathP (\i -> ((I=ΣY[Rx] x i) -> Y)) (g x) (fst)
    I=ΣY[Rx]'7 x = transP-right (sym transport-reduce) filler
      where
      filler : PathP (\i -> ((I=ΣY[Rx] x i) -> Y)) 
                     (transport (\i -> ((I=ΣY[Rx] x (~ i)) -> Y)) fst) fst
      filler = symP (transport-filler (\i -> ((I=ΣY[Rx] x (~ i)) -> Y)) fst)

      transport-reduce : (transport (\i -> ((I=ΣY[Rx] x (~ i)) -> Y)) fst) == g x
      transport-reduce = 
        transportβ-fun-domain (sym (I=ΣY[Rx] x)) fst >=>
        funExt (\i -> cong fst (transportβ-ua (I≃ΣY[Rx] x) i))



    I=ΣY[Rx]'5 : (x : X) -> PathP (\i -> ((⟨ D ⟩ (I=ΣY[Rx] x i)) × ((I=ΣY[Rx] x i) -> Y)))
                                 (DIg x) (DR x , fst)
    I=ΣY[Rx]'5 x i = I=ΣY[Rx]'6 x i , I=ΣY[Rx]'7 x i


    I=ΣY[Rx]'4 : (x : X) -> Path (Σ[ T ∈ (Type ℓ) ] ((⟨ D ⟩ T) × (T -> Y)))
                                 (I x , DIg x) ((Σ Y (R x)) , (DR x , fst))
    I=ΣY[Rx]'4 x i = I=ΣY[Rx] x i , I=ΣY[Rx]'5 x i


    T-path2 : (x : X) -> (⟨ D ⟩ (I x) × (I x -> Y)) ==
                         (⟨ D ⟩ (Σ Y (R x)) × (Σ Y (R x) -> Y))
    T-path2 x = ua (I≃ΣY[Rx]'3 x)

  -- DIg'2 : (x : X) -> PathP (\i -> (⟨ D ⟩ (I=ΣY[Rx] x i) × ((I=ΣY[Rx] x i) -> Y)))
  --                          (DIg x) (DR' x)
  -- DIg'2 : (x : X) -> PathP (\i -> (T-path2 x i)) (DIg x) (DR' x)
  -- DIg'2 x i = glue (\{ (i = i0) -> (DIg x) ; (i = i1) -> (DR' x) }) (DR' x)



  -- DIg' : PathP (\i -> (∀ x -> ⟨ D ⟩ (I=ΣY[Rx] x i) × ((I=ΣY[Rx] x i) -> Y))) 
  --              DIg (\x -> DR x , fst)
  -- DIg' = transP-left DIg'3 (funExt (\x i -> DR x , ans4 x i))

    p : forward (R , DR) == f
    p i x = I=ΣY[Rx]'4 x (~ i)

  backward : (X -> PartialElement D Y) -> PartialMap D X Y
  backward f = fst (backward' f)



  backward'2 : (f : X -> PartialElement D Y) -> (forward (backward f)) == f
  backward'2 f = snd (backward' f)


  forward' : (f : PartialMap D X Y) -> (backward (forward f)) == f
  forward' f = ΣProp-path (isPropΠ (\x -> isDominance.isProp-D (snd D) _)) R-path
    where

    R : REL X Y ℓ
    R = fst f
    DR : ∀ x -> ⟨ D ⟩ (Σ Y (R x))
    DR = snd f

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



    

  --fb : ∀ pe -> forward (backward pe) == pe
  --fb f = funExt handle
  --  where
  --  handle : (x : X) -> forward (backward f) x == f x
  --  handle x = ?
  --    where

  --    R : REL X Y ℓ
  --    R x y with (f x)
  --    ... | (I , _ , g) = Σ[ i ∈ I ] (g i == y)

  --    I = fst (f x)
  --    DI = fst (snd (f x))
  --    g = snd (snd (f x))


  --    I=ΣY[Rx] : I == Σ Y (R x)
  --    I=ΣY[Rx] = ua ((Σ-isContr-eq (\i -> isContr-singleton (g i))) >eq> Σ-swap-eq)

