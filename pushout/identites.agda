{-# OPTIONS --cubical --safe --exact-split #-}

module pushout.identites where

open import base
open import cubical hiding (glue)
open import equality-path
open import equality.square
open import equivalence
open import funext
open import isomorphism
open import pushout
open import pushout.3x3-lemma
open import type-algebra

module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (f : A -> B) (g : A -> C) where
  Pushout-swap-iso : Iso (Pushout f g) (Pushout g f)
  Pushout-swap-iso = iso fwd bkw fb bf
    where
    fwd : (Pushout f g) -> (Pushout g f)
    fwd (inj-l b) = inj-r b
    fwd (inj-r c) = inj-l c
    fwd (glue a i) = glue a (~ i)

    bkw : (Pushout g f) -> (Pushout f g)
    bkw (inj-l c) = inj-r c
    bkw (inj-r b) = inj-l b
    bkw (glue a i) = glue a (~ i)

    fb : ∀ x -> fwd (bkw x) == x
    fb (inj-l c) = refl
    fb (inj-r b) = refl
    fb (glue a i) = refl

    bf : ∀ x -> bkw (fwd x) == x
    bf (inj-l b) = refl
    bf (inj-r c) = refl
    bf (glue a i) = refl

module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
         (f : A -> B) where
  Pushout-id-left-iso : Iso (Pushout (\a -> a) f) B
  Pushout-id-left-iso = iso fwd bkw fb bf
    where
    fwd : Pushout (\a -> a) f -> B
    fwd (inj-l a) = f a
    fwd (inj-r b) = b
    fwd (glue a i) = f a

    bkw : B -> Pushout (\a -> a) f
    bkw b = inj-r b

    fb : ∀ x -> fwd (bkw x) == x
    fb _ = refl
    bf : ∀ x -> bkw (fwd x) == x
    bf (inj-l a) = sym (glue a)
    bf (inj-r b) = refl
    bf (glue a i) j = glue a (i ∨ (~ j))

  Pushout-id-right-iso : Iso (Pushout f (\a -> a)) B
  Pushout-id-right-iso = Pushout-swap-iso f (\a -> a) >iso> Pushout-id-left-iso

module _ {ℓA ℓB₁ ℓC₁ ℓB₂ ℓC₂ : Level}
         {A : Type ℓA} {B₁ : Type ℓB₁} {C₁ : Type ℓC₁}
                       {B₂ : Type ℓB₂} {C₂ : Type ℓC₂}
         (f : A -> B₁) (g : A -> C₁)
         (eB : B₁ ≃ B₂) (eC : C₁ ≃ C₂)
         where
  private
    f' : A -> B₂
    f' a = eqFun eB (f a)
    g' : A -> C₂
    g' a = eqFun eC (g a)

    bComm : ∀ (b : B₁) -> cong (eqFun eB) (eqRet eB b) == eqSec eB (eqFun eB b)
    bComm b = rotate-square-ABCR->CARB (eqComm eB b)
    cComm : ∀ (c : C₁) -> cong (eqFun eC) (eqRet eC c) == eqSec eC (eqFun eC c)
    cComm c = rotate-square-ABCR->CARB (eqComm eC c)

  Pushout-sides-eq : (Pushout f g) ≃ (Pushout f' g')
  Pushout-sides-eq = isoToEquiv (iso fwd bkw fb bf)
    where

    fwd-filler : (a : A) (i : I) ->
      Path (Pushout f g) (inj-l (eqRet eB (f a) (~ i))) (inj-r (eqRet eC (g a) (~ i)))
    fwd-filler a i j =
      doubleCompPath-filler
        (\j -> inj-l (eqRet eB (f a) j))
        (\j -> glue a j)
        (\j -> inj-r (eqRet eC (g a) (~ j)))
        i j

    fwd : (Pushout f g) -> (Pushout f' g')
    fwd (inj-l b) = inj-l (eqFun eB b)
    fwd (inj-r c) = inj-r (eqFun eC c)
    fwd (glue a i) = glue a i

    center : ∀ (x : Pushout f' g') -> fiber fwd x
    center (inj-l b) =
      inj-l (eqInv eB b) , \i -> inj-l (eqSec eB b i)
    center (inj-r c) =
      inj-r (eqInv eC c) , \i -> inj-r (eqSec eC c i)
    center (glue a j) =
      fwd-filler a i1 j ,
      \i -> hcomp
        (\k -> (\{ (i = i0) -> fwd (fwd-filler a i1 j)
                 ; (i = i1) -> glue a j
                 ; (j = i0) -> inj-l (bComm (f a) k i)
                 ; (j = i1) -> inj-r (cComm (g a) k i)
                 }))
        (fwd (fwd-filler a (~ i) j))

    bkw : (Pushout f' g') -> (Pushout f g)
    bkw x = fst (center x)

    fb : ∀ x -> fwd (bkw x) == x
    fb x = snd (center x)

    bf : ∀ x -> bkw (fwd x) == x
    bf (inj-l b) i = inj-l (eqRet eB b i)
    bf (inj-r c) i = inj-r (eqRet eC c i)
    bf (glue a i) j = fwd-filler a (~ j) i

module _ {ℓA₁ ℓA₂ ℓB ℓC : Level}
         {A₁ : Type ℓA₁} {A₂ : Type ℓA₂}
         {B : Type ℓB} {C : Type ℓC}
         (f : A₁ -> B) (g : A₁ -> C)
         (eA : A₁ ≃ A₂)
         where

  private
    eA' : A₂ ≃ A₁
    eA' = equiv⁻¹ eA

    ef : A₁ -> A₂
    ef = eqFun eA
    ei : A₂ -> A₁
    ei = eqInv eA

    f' : A₂ -> B
    f' a = f (ei a)
    g' : A₂ -> C
    g' a = g (ei a)

    aComm : ∀ (a : A₂) -> cong ei (eqRet eA' a) == eqSec eA' (ei a)
    aComm a = rotate-square-ABCR->CARB (eqComm eA' a)

  Pushout-center-eq : (Pushout f g) ≃ (Pushout f' g')
  Pushout-center-eq = isoToEquiv (iso fwd bkw fb bf)
    where

    bkw : (Pushout f' g') -> (Pushout f g)
    bkw (inj-l b) = inj-l b
    bkw (inj-r c) = inj-r c
    bkw (glue a i) = glue (ei a) i

    lp : (a : A₁) -> Path (Pushout f' g') (inj-l (f (ei (ef a)))) (inj-l (f a))
    lp a j = inj-l (f (eqSec eA' a j))
    rp : (a : A₁) -> Path (Pushout f' g') (inj-r (g (ei (ef a)))) (inj-r (g a))
    rp a j = inj-r (g (eqSec eA' a j))

    filler : (a : A₁) ->
      PathP (\i -> Path (Pushout f' g') (lp a i) (rp a i))
        (glue (ef a))
        ((sym (lp a)) ∙∙ (glue (ef a)) ∙∙ (rp a))
    filler a = doubleCompPath-filler (sym (lp a)) (glue (ef a)) (rp a)

    fwd : (Pushout f g) -> (Pushout f' g')
    fwd (inj-l b) = inj-l b
    fwd (inj-r c) = inj-r c
    fwd (glue a i) = filler a i1 i

    fb : ∀ x -> fwd (bkw x) == x
    fb (inj-l b) = refl
    fb (inj-r c) = refl
    fb (glue a i) j = path j i
      where
      T : I -> Type (ℓ-max* 3 ℓA₂ ℓB ℓC)
      T i =
        PathP (\j -> Path (Pushout f' g')
                       (inj-l (f (aComm a i j)))
                       (inj-r (g (aComm a i j))))
          (glue (ef (ei a))) (glue a)

      path : Path (Path (Pushout f' g') _ _) (filler (ei a) i1) (glue a)
      path = transP-sym (symP (filler (ei a)))
                        (transp T i0 (\j -> glue (eqRet eA' a j)))

    bf : ∀ x -> bkw (fwd x) == x
    bf (inj-l b) = refl
    bf (inj-r c) = refl
    bf (glue a i) j =
      hcomp
        (\k -> (\{ (i = i0) -> inj-l (f (eqSec eA' a k))
                 ; (i = i1) -> inj-r (g (eqSec eA' a k))
                 ; (j = i0) -> bkw (filler a k i)
                 ; (j = i1) -> glue (eqSec eA' a k) i
                 }))
        (bkw (filler a i0 i))

module _ {ℓA₁ ℓB₁ ℓC₁ ℓA₂ ℓB₂ ℓC₂ : Level}
         {A₁ : Type ℓA₁} {B₁ : Type ℓB₁} {C₁ : Type ℓC₁}
         {A₂ : Type ℓA₂} {B₂ : Type ℓB₂} {C₂ : Type ℓC₂}
         (f : A₁ -> B₁) (g : A₁ -> C₁)
         (eA : A₁ ≃ A₂) (eB : B₁ ≃ B₂) (eC : C₁ ≃ C₂)
         where
  private
    f' : A₂ -> B₂
    f' a = eqFun eB (f (eqInv eA a))
    g' : A₂ -> C₂
    g' a = eqFun eC (g (eqInv eA a))

  Pushout-parts-eq : (Pushout f g) ≃ (Pushout f' g')
  Pushout-parts-eq =
    Pushout-sides-eq f g eB eC >eq>
    Pushout-center-eq _ _ eA

module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         {f : A -> B} {g : A -> C} {f' : A -> B} {g' : A -> C}
         (fp : ∀ a -> f a == f' a) (gp : ∀ a -> g a == g' a) where

  Pushout-function-iso : Iso (Pushout f g) (Pushout f' g')
  Pushout-function-iso = iso fwd bkw fb bf
    where
    f-filler : (a : A) (i : I) ->
      Path (Pushout f' g') (inj-l (fp a (~ i))) (inj-r (gp a (~ i)))
    f-filler a i =
      doubleCompPath-filler
        (\j -> inj-l (fp a j))
        (glue a)
        (\j -> inj-r (gp a (~ j)))
        i

    b-filler : (a : A) (i : I) ->
      Path (Pushout f g) (inj-l (fp a i)) (inj-r (gp a i))
    b-filler a i =
      doubleCompPath-filler
        (\j -> inj-l (fp a (~ j)))
        (glue a)
        (\j -> inj-r (gp a j))
        i

    fwd : (Pushout f g) -> (Pushout f' g')
    fwd (inj-l b) = (inj-l b)
    fwd (inj-r c) = (inj-r c)
    fwd (glue a i) = f-filler a i1 i

    bkw : (Pushout f' g') -> (Pushout f g)
    bkw (inj-l b) = (inj-l b)
    bkw (inj-r c) = (inj-r c)
    bkw (glue a i) = b-filler a i1 i

    fb : ∀ x -> fwd (bkw x) == x
    fb (inj-l _) = refl
    fb (inj-r _) = refl
    fb (glue a i) j =
      hcomp
        (\k -> \{ (i = i0) -> inj-l (fp a (j ∨ k))
                ; (i = i1) -> inj-r (gp a (j ∨ k))
                ; (j = i0) -> fwd (b-filler a k i)
                ; (j = i1) -> (f-filler a (~ j) i)
                })
        (f-filler a (~ j) i)

    bf : ∀ x -> bkw (fwd x) == x
    bf (inj-l _) = refl
    bf (inj-r _) = refl
    bf (glue a i) j =
      hcomp
        (\k -> \{ (i = i0) -> inj-l (fp a (~ (j ∨ k)))
                ; (i = i1) -> inj-r (gp a (~ (j ∨ k)))
                ; (j = i0) -> bkw (f-filler a k i)
                ; (j = i1) -> (b-filler a (~ j) i)
                })
        (b-filler a (~ j) i)


module _ {ℓA ℓB ℓC ℓD : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (f : A -> B) (g : A -> C) (D : Type ℓD) where

  module _ where
    private
      f' : A × D -> B × D
      f' (a , d) = f a , d
      g' : A × D -> C × D
      g' (a , d) = g a , d


    Pushout-extra-right-iso : Iso (Pushout f' g') (Pushout f g × D)
    Pushout-extra-right-iso = iso fwd bkw fb bf
      where
      fwd : (Pushout f' g') -> (Pushout f g × D)
      fwd = Pushout-rec
        (\ (b , d) -> inj-l b , d)
        (\ (c , d) -> inj-r c , d)
        (\ (a , d) i -> glue a i  , d)

      bkw : (Pushout f g × D) -> (Pushout f' g')
      bkw (p , d) = Pushout-rec
        (\ b -> inj-l (b , d))
        (\ c -> inj-r (c , d))
        (\ a i -> glue (a , d) i)
        p

      fb : ∀ x -> fwd (bkw x) == x
      fb (inj-l b , d) = refl
      fb (inj-r c , d) = refl
      fb (glue a i , d) = refl

      bf : ∀ x -> bkw (fwd x) == x
      bf (inj-l (b , d)) = refl
      bf (inj-r (c , d)) = refl
      bf (glue (a , d) i) = refl

  module _ where
    private
      f' : D × A -> D × B
      f' (d , a) = d , f a
      g' : D × A -> D × C
      g' (d , a) = d , g a


    Pushout-extra-left-iso : Iso (Pushout f' g') (D × Pushout f g)
    Pushout-extra-left-iso = iso fwd bkw fb bf
      where
      fwd : (Pushout f' g') -> (D × Pushout f g)
      fwd = Pushout-rec
        (\ (d , b) -> d , inj-l b)
        (\ (d , c) -> d , inj-r c)
        (\ (d , a) i -> d , glue a i)

      bkw : (D × Pushout f g) -> (Pushout f' g')
      bkw (d , p) = Pushout-rec
        (\ b -> inj-l (d , b))
        (\ c -> inj-r (d , c))
        (\ a i -> glue (d , a) i)
        p

      fb : ∀ x -> fwd (bkw x) == x
      fb (d , inj-l b) = refl
      fb (d , inj-r c) = refl
      fb (d , glue a i) = refl

      bf : ∀ x -> bkw (fwd x) == x
      bf (inj-l (d , b)) = refl
      bf (inj-r (d , c)) = refl
      bf (glue (d , a) i) = refl



module _ {ℓA ℓB ℓC : Level} (A : Type ℓA) (B : Type ℓB) (C : Type ℓC) where
  Join-assoc-eq : (Join (Join A B) C) ≃ (Join A (Join B C))
  Join-assoc-eq = equiv⁻¹ R-eq >eq> isoToEquiv m.iso >eq> C-eq
    where

    -- A   AB   B
    -- AC  ABC  BC
    -- AC  AC   C

    f1 : A × B -> A
    f1 = proj₁
    f2 : A × B -> B
    f2 = proj₂
    f3 : A × (B × C) -> A × C
    f3 (a , (b , c)) = a , c
    f4 : A × (B × C) -> B × C
    f4 (a , (b , c)) = b , c
    f5 : A × C -> A × C
    f5 ac = ac
    f6 : A × C -> C
    f6 = proj₂

    f7 : A × C -> A
    f7 = proj₁
    f8 : A × C -> A × C
    f8 ac = ac
    f9 : A × (B × C) -> A × B
    f9 (a , (b , c)) = a , b
    f10 : A × (B × C) -> A × C
    f10 (a , (b , c)) = a , c
    f11 : B × C -> B
    f11 = proj₁
    f12 : B × C -> C
    f12 = proj₂

    module m = 3x3 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
                   (\_ -> refl) (\_ -> refl) (\_ -> refl) (\_ -> refl)

    R-eq : m.R ≃ Join (Join A B) C
    R-eq = r-parts-eq >eq> pathToEquiv r-path
      where
      R₀-eq : m.R₀ ≃ (Join A B)
      R₀-eq = idEquiv _

      R₂-eq : m.R₂ ≃ (Join A B × C)
      R₂-eq = (Pushout-center-eq f3 f4 (isoToEquiv (iso⁻¹ (×-assoc-iso A B C)))) >eq>
              (isoToEquiv (Pushout-extra-right-iso _ _ C))

      R₄-eq : m.R₄ ≃ C
      R₄-eq = isoToEquiv (Pushout-id-left-iso f6)

      rf : (Join A B × C) -> Join A B
      rf = _
      rg : (Join A B × C) -> C
      rg = _
      r-parts-eq : m.R ≃ Pushout rf rg
      r-parts-eq = Pushout-parts-eq _ _ R₂-eq R₀-eq R₄-eq

      rf-path : ∀ x -> rf x == fst x
      rf-path (inj-l _ , c) = refl
      rf-path (inj-r _ , c) = refl
      rf-path (glue a i , c) j = doubleCompPath-filler refl (glue a) refl (~ j) i

      rg-path : ∀ x -> rg x == snd x
      rg-path (inj-l _ , c) = refl
      rg-path (inj-r _ , c) = refl
      rg-path (glue (a , b) i , c) = cong (eqFun R₄-eq) inner
        where
        inner : m.r₃ (glue (a , (b , c)) i) == glue (f10 (a , (b , c))) i
        inner j = doubleCompPath-filler refl (glue (f10 (a , (b , c)))) refl (~ j) i


      r-path : Pushout rf rg == Join (Join A B) C
      r-path i = Pushout (funExt rf-path i) (funExt rg-path i)


    C-eq : m.C ≃ Join A (Join B C)
    C-eq = c-parts-eq >eq> pathToEquiv c-path
      where
      C₀-eq : m.C₀ ≃ A
      C₀-eq = isoToEquiv (Pushout-id-right-iso f7)

      C₂-eq : m.C₂ ≃ (A × Join B C)
      C₂-eq = isoToEquiv (Pushout-extra-left-iso _ _ A)

      C₄-eq : m.C₄ ≃ (Join B C)
      C₄-eq = idEquiv _

      cf : (A × Join B C) -> A
      cf = _
      cg : (A × Join B C) -> Join B C
      cg = _
      c-parts-eq : m.C ≃ Pushout cf cg
      c-parts-eq = Pushout-parts-eq _ _ C₂-eq C₀-eq C₄-eq


      cf-path : ∀ x -> cf x == fst x
      cf-path (a , inj-l _) = refl
      cf-path (a , inj-r _) = refl
      cf-path (a , glue (b , c) i) = cong (eqFun C₀-eq) inner
        where
        inner : m.c₁ (glue (a , (b , c)) i) == glue (f3 (a , (b , c))) i
        inner j = doubleCompPath-filler refl (glue (f3 (a , (b , c)))) refl (~ j) i

      cg-path : ∀ x -> cg x == snd x
      cg-path (a , inj-l _) = refl
      cg-path (a , inj-r _) = refl
      cg-path (a , glue x i) j = doubleCompPath-filler refl (glue x) refl (~ j) i

      c-path : Pushout cf cg == Join A (Join B C)
      c-path i = Pushout (funExt cf-path i) (funExt cg-path i)
