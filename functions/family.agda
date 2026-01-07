{-# OPTIONS --cubical --safe --exact-split #-}

module functions.family where

open import base
open import cubical
open import equality-path
open import equality.path-composition-equivalence
open import equivalence
open import functions
open import funext
open import isomorphism
open import sigma
open import univalence


module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} where
  FamilyEq : (A -> C) -> (B -> C) -> Type (ℓ-max* 3 ℓA ℓB ℓC)
  FamilyEq f g = Σ[ e ∈ A ≃ B ] (f == g ∘ eqFun e)

  FiberEq : (A -> C) -> (B -> C) -> Type (ℓ-max* 3 ℓA ℓB ℓC)
  FiberEq f g = ∀ c -> fiber f c ≃ fiber g c

  private
    fiberEq->familyEq : ∀ {f g} -> FiberEq f g -> FamilyEq f g
    fiberEq->familyEq {f} {g} fiber-eq =
      isoToEquiv (iso A->B B->A B->A->B A->B->A) , sym (funExt A->B')
      where
      f-fib->g-fib : ∀ c -> fiber f c -> fiber g c
      f-fib->g-fib c fib = eqFun (fiber-eq c) fib
      g-fib->f-fib : ∀ c -> fiber g c -> fiber f c
      g-fib->f-fib c fib = eqInv (fiber-eq c) fib

      A->g-fib : ∀ a -> fiber g (f a)
      A->g-fib a = f-fib->g-fib (f a) (a , refl)

      A->B : A -> B
      A->B a = fst (A->g-fib a)
      A->B' : ∀ a -> g (A->B a) == f a
      A->B' a = snd (A->g-fib a)

      B->f-fib : ∀ b -> fiber f (g b)
      B->f-fib b = g-fib->f-fib (g b) (b , refl)

      B->A : B -> A
      B->A b = fst (B->f-fib b)

      A->B->A : ∀ a -> B->A (A->B a) == a
      A->B->A a = \i -> fst (path3 i)
        where
        fib : fiber g (f a)
        fib = (f-fib->g-fib (f a) (a , refl))

        b : B
        b = fst fib
        pb : g b == f a
        pb = snd fib

        path1 : g-fib->f-fib (f a) (b , pb) == (a , refl)
        path1 = eqRet (fiber-eq (f a)) (a , refl)
        path2 :
          PathP (\i -> fiber f (pb i))
            (g-fib->f-fib (g b) (b , refl))
            (g-fib->f-fib (f a) (b , pb))
        path2 i = g-fib->f-fib (pb i) (b , (\j -> pb (i ∧ j)))
        path3 : PathP (\i -> fiber f (pb i)) (B->f-fib b) (a , refl)
        path3 = transP-left path2 path1

      B->A->B : ∀ b -> A->B (B->A b) == b
      B->A->B b = \i -> fst (path3 i)
        where
        fib : fiber f (g b)
        fib = g-fib->f-fib (g b) (b , refl)

        a : A
        a = fst fib
        pa : f a == g b
        pa = snd fib

        path1 : f-fib->g-fib (g b) (a , pa) == (b , refl)
        path1 = eqSec (fiber-eq (g b)) (b , refl)
        path2 :
          PathP (\i -> fiber g (pa i))
            (f-fib->g-fib (f a) (a , refl))
            (f-fib->g-fib (g b) (a , pa))
        path2 i = f-fib->g-fib (pa i) (a , (\j -> pa (i ∧ j)))
        path3 : PathP (\i -> fiber g (pa i)) (A->g-fib a) (b , refl)
        path3 = transP-left path2 path1



    familyEq->fiberEq : ∀ {f g} -> FamilyEq f g -> FiberEq f g
    familyEq->fiberEq {f} {g} (e , f=ge) c =
      isoToEquiv (iso for back fb bf)
      where
      for : fiber f c -> fiber g c
      for (a , p) = (eqFun e a , (\i -> f=ge (~ i) a) >=> p)

      back : fiber g c -> fiber f c
      back (b , p) = (eqInv e b , ((\i -> f=ge i (eqInv e b)) >=> cong g (eqSec e b)) >=> p)

      fb : ∀ x -> for (back x) == x
      fb (b , p) = \i -> p' i , ans i
        where
        p' : eqFun e (eqInv e b) == b
        p' = eqSec e b

        path1 : PathP (\i -> (g (p' i) == c)) (cong g p' >=> p) (refl >=> p)
        path1 i = cong g (\j -> p' (i ∨ j)) >=> p

        path2 :
         ((\i -> f=ge (~ i) (eqInv e b)) >=> (((\i -> f=ge i (eqInv e b)) >=> cong g p') >=> p)) ==
         (cong g p' >=> p)
        path2 =
          sym (compPath-assoc _ _ _) >=>
          cong (_>=> p) (
            sym (compPath-assoc _ _ _) >=>
            cong (_>=> (cong g p')) (
              (compPath-sym _)) >=>
            compPath-refl-left _)

        ans : PathP (\i -> (g (p' i) == c))
          ((\i -> f=ge (~ i) (eqInv e b)) >=> (((\i -> f=ge i (eqInv e b)) >=> cong g p') >=> p))
          p
        ans = transP-mid path2 path1 (compPath-refl-left _)

      bf : ∀ x -> back (for x) == x
      bf (a , p) = \i -> p' i , ans i
        where
        p' : eqInv e (eqFun e a) == a
        p' = eqRet e a

        subpath1 : f (eqInv e (eqFun e a)) == g (eqFun e (eqInv e (eqFun e a)))
        subpath1 i = f=ge i (eqInv e (eqFun e a))
        subpath2 : f a == g (eqFun e a)
        subpath2 i = f=ge i a

        path1 : PathP (\i -> f (eqRet e a i) == (g (eqFun e a)))
                  (subpath1 >=> cong g (eqSec e (eqFun e a)))
                  (subpath2 >=> refl)
        path1 i = ((\j -> f=ge j (p' i)) >=> (\j -> (g (eqComm e a i j))))

        path2 : PathP (\i -> f (eqRet e a i) == c)
                  ((subpath1 >=> cong g (eqSec e (eqFun e a))) >=> ((\i -> f=ge (~ i) a) >=> p))
                  ((subpath2 >=> refl) >=> ((\i -> f=ge (~ i) a) >=> p))
        path2 i = path1 i >=> ((\j -> f=ge (~ j) a) >=> p)

        path3 : (((\i -> f=ge i a) >=> refl) >=> ((\i -> f=ge (~ i) a) >=> p)) == p
        path3 =
          cong (_>=> ((\i -> f=ge (~ i) a) >=> p)) (compPath-refl-right _) >=>
          sym (compPath-assoc _ _ _) >=>
          cong (_>=> p) (compPath-sym _) >=>
          compPath-refl-left p

        ans : PathP (\i -> (f (p' i) == c))
          ((subpath1 >=> cong g (eqSec e (eqFun e a))) >=> ((\i -> f=ge (~ i) a) >=> p))
          p
        ans = transP-left path2 path3

    fiber->family->fiber' : ∀ {f} {g} x c -> familyEq->fiberEq (fiberEq->familyEq {f} {g} x) c == x c
    fiber->family->fiber' {f} {g} eqs c = equiv-path ans
      where
      lhs₁ : fiber f c -> fiber g c
      lhs₁ (a , p) =
        fst (eqFun (eqs (f a)) (a , refl)) ,
        (snd (eqFun (eqs (f a)) (a , refl)) >=> p)

      lhs₂ : fiber f c -> fiber g c
      lhs₂ (a , p) =
        fst (eqFun (eqs c) (a , p)) ,
        snd (eqFun (eqs c) (a , p))

      module _ ((a , p) : fiber f c) where
        p₁ : fst (eqFun (eqs (f a)) (a , refl)) ==
             fst (eqFun (eqs c) (a , p))
        p₁ i = fst (eqFun (eqs (p i)) (a , (\j -> p (j ∧ i))))

        p₂ : PathP (\i -> g (p₁ i) == c)
               (snd (eqFun (eqs (f a)) (a , refl)) >=> p)
               (snd (eqFun (eqs c) (a , p)) >=> refl)
        p₂ i =
          (snd (eqFun (eqs (p i)) (a , (\j -> p (j ∧ i)))) >=> (\j -> p (j ∨ i)))

        p₃ : PathP (\i -> g (p₁ i) == c)
               (snd (eqFun (eqs (f a)) (a , refl)) >=> p)
               (snd (eqFun (eqs c) (a , p)))
        p₃ = transP-left p₂ (compPath-refl-right _)

      ans : lhs₁ == lhs₂
      ans = funExt (\fib i -> p₁ fib i , p₃ fib i)

    family->fiber->family : ∀ {f} {g} (x : FamilyEq f g) -> fiberEq->familyEq {f} {g} (familyEq->fiberEq x) == x
    family->fiber->family {f} {g} (eq , f=ge) = \i -> eq-path i , ans₂ i
      where
      fib-eq : FiberEq f g
      fib-eq = familyEq->fiberEq (eq , f=ge)

      A->B' : f == g ∘ (eqFun eq)
      A->B' = funExt (\a -> (refl >=> (\j -> f=ge j a)))

      ans₂ : Path (f == g ∘ eqFun eq) A->B' f=ge
      ans₂ = compPath-refl-left _

      eq-path : fst (fiberEq->familyEq fib-eq) == eq
      eq-path = equiv-path refl


  opaque
    FiberEq≃FamilyEq : ∀ (f : A -> C) (g : B -> C) -> FiberEq f g ≃ FamilyEq f g
    FiberEq≃FamilyEq f g =
      isoToEquiv (iso fiberEq->familyEq familyEq->fiberEq
                      family->fiber->family (\x -> funExt (fiber->family->fiber' x)))


module _ {ℓA ℓB : Level} {A₁ A₂ : Type ℓA} {B : Type ℓB} where
  FamilyPath : (A₁ -> B) -> (A₂ -> B) -> Type (ℓ-max (ℓ-suc ℓA) ℓB)
  FamilyPath f g = Path (Σ[ A ∈ Type ℓA ] (A -> B)) (A₁ , f) (A₂ , g)

  private
    FamilyPath₁ : (A₁ -> B) -> (A₂ -> B) -> Type (ℓ-max ℓA ℓB)
    FamilyPath₁ f g = Σ[ eq ∈ A₁ ≃ A₂ ] (PathP (\i -> ua eq i -> B) f g)

    FamilyPath₂ : (A₁ -> B) -> (A₂ -> B) -> Type (ℓ-max (ℓ-suc ℓA) ℓB)
    FamilyPath₂ f g = Σ[ A ∈ A₁ == A₂ ] (PathP (\i -> A i -> B) f g)

    FamilyEq≃FamilyPath₁ : ∀ (f : A₁ -> B) (g : A₂ -> B) -> (FamilyEq f g) ≃ (FamilyPath₁ f g)
    FamilyEq≃FamilyPath₁ f g = existential-eq (FamilyEq≃FamilyPath₁' f g)
      where
      FamilyEq≃FamilyPath₁' : ∀ (f : A₁ -> B) (g : A₂ -> B) (eq : A₁ ≃ A₂) ->
        (f == g ∘ eqFun eq) ≃ (PathP (\i -> ua eq i -> B) f g)
      FamilyEq≃FamilyPath₁' f g eq = for , isEquiv-for
        where
        u : (i : I) -> (a : ua eq i) -> B
        u i a = g (ua-unglue eq i a)

        for : f == g ∘ eqFun eq -> PathP (\i -> ua eq i -> B) f g
        for p = transP-right p (\i -> u i)

        isEquiv-for : isEquiv for
        isEquiv-for = isEquiv-transP-right (\i -> u i) _


    FamilyPath₁≃FamilyPath₂ : ∀ (f : A₁ -> B) (g : A₂ -> B) -> (FamilyPath₁ f g) ≃ (FamilyPath₂ f g)
    FamilyPath₁≃FamilyPath₂ f g = equiv⁻¹ (reindexΣ (equiv⁻¹ univalence) _)

    FamilyPath₂≃FamilyPath : ∀ (f : A₁ -> B) (g : A₂ -> B) -> (FamilyPath₂ f g) ≃ (FamilyPath f g)
    FamilyPath₂≃FamilyPath f g = isoToEquiv (iso for back (\_ -> refl) (\_ -> refl))
      where
      for : (FamilyPath₂ f g) -> (FamilyPath f g)
      for (Ap , fp) i = Ap i , fp i
      back : (FamilyPath f g) -> (FamilyPath₂ f g)
      back Afp = (\i -> (fst (Afp i))) , (\i -> (snd (Afp i)))

  opaque
    FamilyEq≃FamilyPath : ∀ (f : A₁ -> B) (g : A₂ -> B) -> (FamilyEq f g) ≃ (FamilyPath f g)
    FamilyEq≃FamilyPath f g =
      FamilyEq≃FamilyPath₁ f g >eq>
      FamilyPath₁≃FamilyPath₂ f g >eq>
      FamilyPath₂≃FamilyPath f g

  opaque
    FiberEq≃FamilyPath : ∀ (f : A₁ -> B) (g : A₂ -> B) -> FiberEq f g ≃ FamilyPath f g
    FiberEq≃FamilyPath f g = FiberEq≃FamilyEq f g >eq> FamilyEq≃FamilyPath f g
