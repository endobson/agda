{-# OPTIONS --cubical --safe --exact-split #-}

module finset.order where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finite-commutative-monoid.instances
open import finset
open import finset.order.base
open import finset.cardinality
open import finset.detachable
open import finset.instances
open import finset.search
open import finset.without-point
open import finsum
open import functions
open import functions.injective
open import funext
open import hlevel
open import nat.order
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import relation
open import sigma
open import sigma.base
open import sum
open import truncation
open import type-algebra
open import univalence
open import without-point


WellFounded-FinSet< : {ℓ : Level} -> WellFounded (FinSet< {ℓ} {ℓ})
WellFounded-FinSet< {ℓ} fs = Acc-FinSet< fs (WellFounded-Nat< (cardinality fs))
  where
  Acc-FinSet< : (fs : FinSet ℓ) (a : Acc _<_ (cardinality fs)) -> Acc FinSet< fs
  Acc-FinSet< fs1 (acc f) =
    (acc (\fs2 fs2<fs1 -> (Acc-FinSet< fs2 (f (cardinality fs2) fs2<fs1))))


private
  Injective->FinSet≤-FinT : (n1 n2 : Nat) (f : FinT n1 -> FinT n2) -> (Injective f) -> n1 ≤ n2
  Injective->FinSet≤-FinT zero _ f inj-f = zero-≤
  Injective->FinSet≤-FinT (suc n1) zero f inj-f = bot-elim (f (inj-l tt))
  Injective->FinSet≤-FinT (suc n1) (suc n2) f inj-f =
    suc-≤ (Injective->FinSet≤-FinT n1 n2 f' inj-f')
    where
    x : FinT (suc n2)
    x = f (inj-l tt)

    shift-out : (n : Nat) -> (i j : FinT (suc n)) -> i != j -> FinT n
    shift-out _ (inj-l tt) (inj-l tt) i!=j = bot-elim (i!=j refl)
    shift-out (suc n) (inj-r i) (inj-l tt) i!=j = i
    shift-out (suc n) (inj-l tt) (inj-r j) i!=j = (inj-l tt)
    shift-out (suc n) (inj-r i) (inj-r j) i!=j =
      inj-r (shift-out n i j (i!=j ∘ (cong inj-r)))

    shift-out-same : (n : Nat) -> (i1 i2 j : FinT (suc n)) ->
                     (i1!=j : i1 != j) -> (i2!=j : i2 != j) ->
                     shift-out n i1 j i1!=j == shift-out n i2 j i2!=j ->
                     i1 == i2
    shift-out-same _ (inj-l tt) _          (inj-l tt) i1!=j i2!=j p = bot-elim (i1!=j refl)
    shift-out-same _ (inj-r i1) (inj-l tt) (inj-l tt) i1!=j i2!=j p = bot-elim (i2!=j refl)
    shift-out-same _ (inj-l tt) (inj-l tt) (inj-r j) i1!=j i2!=j p = refl
    shift-out-same (suc n) (inj-r i1) (inj-r i2) (inj-l tt) i1!=j i2!=j p = cong inj-r p
    shift-out-same (suc n) (inj-r i1) (inj-l tt) (inj-r j) i1!=j i2!=j p =
      bot-elim (inj-l!=inj-r (sym p))
    shift-out-same (suc n) (inj-l tt) (inj-r i2) (inj-r j) i1!=j i2!=j p =
      bot-elim (inj-l!=inj-r p)
    shift-out-same (suc n) (inj-r i1) (inj-r i2) (inj-r j) i1!=j i2!=j p =
      cong inj-r (shift-out-same n i1 i2 j (i1!=j ∘ (cong inj-r)) (i2!=j ∘ (cong inj-r))
                                 (inj-r-injective p))

    f' : FinT n1 -> FinT n2
    f' i = shift-out n2 (f (inj-r i)) x (\i=j -> inj-l!=inj-r (sym (inj-f i=j)))

    inj-f' : Injective f'
    inj-f' {i1} {i2} f'i1=f'i2 =
      inj-r-injective (inj-f (shift-out-same n2 (f (inj-r i1)) (f (inj-r i2)) x
                                             (\i=j -> inj-l!=inj-r (sym (inj-f i=j)))
                                             (\i=j -> inj-l!=inj-r (sym (inj-f i=j)))
                                             f'i1=f'i2))

--  Injective-Fin->Surjective : (n : Nat) (f : FinT n -> FinT n) -> (Injective f) -> isSurjection f
--  Injective-Fin->Surjective zero f _ = \()
--  Injective-Fin->Surjective (suc n) f inj-f = ?



  ¬Surjection-Fin : (n1 n2 : Nat) (f : Fin n1 -> Fin n2) -> ¬ (isSurjection f) ->
                     ∃[ i ∈ Fin n2 ] (∀ j -> f j != i)
  ¬Surjection-Fin n1 n2 f ¬sur-f =
    handle (finite-search (FinSet-Fin n2) univPQ)
    where
    P : Fin n2 -> Type₀
    P i = ∀ j -> f j != i

    Q : Fin n2 -> Type₀
    Q i = ∃[ j ∈ Fin n1 ] (f j == i)

    univPQ : Universal (P ∪ Q)
    univPQ s = ⊎-swap (finite-search-dec (FinSet-Fin n1) (\j -> decide-fin (f j) s))

    handle : Inhabited P ⊎ Universal Q -> Inhabited P
    handle (inj-l p) = p
    handle (inj-r q) = bot-elim (¬sur-f q)


  FinSet≤-Fin-Collection : {ℓ : Level} (n : Nat) (A : Fin n -> FinSet ℓ) ->
                           (∀ i -> ∥ ⟨ A i ⟩  ∥) ->
                            n ≤ finiteSumᵉ (FinSet-Fin n) (\i -> cardinality (A i))
  FinSet≤-Fin-Collection zero    A inhabit = zero-≤
  FinSet≤-Fin-Collection (suc n) A inhabit =
    trans-≤-= (+-preserves-≤ lt1 (FinSet≤-Fin-Collection n A' inhabit')) p
    where
    A0 = A zero-fin
    A' = A ∘ suc-fin
    inhabit' = inhabit ∘ suc-fin

    lt1 : 1 ≤ cardinality A0
    lt1 = eqFun (inhabited-0<cardinality A0) (inhabit zero-fin)

    p : cardinality A0 + finiteSumᵉ (FinSet-Fin n) (\i -> cardinality (A' i)) ==
        finiteSumᵉ (FinSet-Fin (suc n)) (\i -> cardinality (A i))
    p = sym (finiteMerge-FinSuc _ _)


  FinSet≤-Fin-Collection' : (n : Nat) (A : Fin n -> FinSet ℓ-zero) ->
                            (∀ i -> ∥ ⟨ A i ⟩  ∥) ->
                            n ≤ cardinality (FinSet-Σ (FinSet-Fin n) A)
  FinSet≤-Fin-Collection' n A inhabit =
    subst (n ≤_) (sym (cardinality-Σ3 _ _)) (FinSet≤-Fin-Collection n A inhabit)


  Surjective->FinSet≤-Fin : (n1 n2 : Nat) (f : Fin n1 -> Fin n2) -> (isSurjection f) -> n2 ≤ n1
  Surjective->FinSet≤-Fin n1 n2 f sur-f =
    trans-≤-= (FinSet≤-Fin-Collection' n2 A sur-f) cA=n
    where
    A : Fin n2 -> FinSet ℓ-zero
    A i = FinSet-Detachable (FinSet-Fin n1) (\j -> (f j == i) , isSetFin _ _)
                            (\j -> discreteFin (f j) i)

    ΣA=Fin1 : (Σ[ i ∈ (Fin n2) ] ⟨ A i ⟩) == Fin n1
    ΣA=Fin1 =
      ua Σ-swap-eq >=>
      sym (ua (Σ-isContr-eq (\j -> isContr-singleton (f j))))

    fs-ΣA=Fin1 : (FinSet-Σ (FinSet-Fin n2) A) == FinSet-Fin n1
    fs-ΣA=Fin1 = (ΣProp-path isProp-isFinSet ΣA=Fin1)

    cA=n : cardinality (FinSet-Σ (FinSet-Fin n2) A) == n1
    cA=n = cong cardinality fs-ΣA=Fin1



module _ {ℓA ℓB : Level} (FA : FinSet ℓA) (FB : FinSet ℓB) where
  private
    A = fst FA
    B = fst FB
    fsA : isFinSetΣ A
    fsA = isFinSet->isFinSetΣ (snd FA)
    fsB : isFinSetΣ B
    fsB = isFinSet->isFinSetΣ (snd FB)

    nA nB : Nat
    nA = cardinality FA
    nB = cardinality FB

    eqA' : ∥ A ≃ FinT nA ∥
    eqA' = subst (\t -> (∥ A ≃ t ∥)) (sym (FinT=Fin nA)) (snd fsA)
    eqB' : ∥ B ≃ FinT nB ∥
    eqB' = subst (\t -> (∥ B ≃ t ∥)) (sym (FinT=Fin nB)) (snd fsB)

  Retraction->FinSet≤ : (f : A -> B) -> (Retraction f) -> FinSet≤ FA FB
  Retraction->FinSet≤ f (g , ret-g) = unsquash isProp-≤ (∥-map2 helper eqA' eqB')
    where
    helper : (A ≃ FinT nA) -> (B ≃ FinT nB) -> FinSet≤ FA FB
    helper eqA eqB = Injective->FinSet≤-FinT nA nB f' inj-f'
      where

      f' : FinT nA -> FinT nB
      f' = eqFun eqB ∘ f ∘ eqInv eqA

      g' : FinT nB -> FinT nA
      g' = eqFun eqA ∘ g ∘ eqInv eqB

      ret-g' : isRetractionOf f' g'
      ret-g' a =
        cong (eqFun eqA ∘ g) (eqRet eqB (f (eqInv eqA a))) >=>
        cong (eqFun eqA) (ret-g (eqInv eqA a)) >=>
        eqSec eqA a

      inj-f' : Injective f'
      inj-f' {a1} {a2} p = sym (ret-g' a1) >=> cong g' p >=> (ret-g' a2)

  Injective->FinSet≤ : (f : A -> B) -> (Injective f) -> FinSet≤ FA FB
  Injective->FinSet≤ f inj-f = unsquash isProp-≤ (∥-map2 helper eqA' eqB')
    where
    helper : (A ≃ FinT nA) -> (B ≃ FinT nB) -> FinSet≤ FA FB
    helper eqA eqB = Injective->FinSet≤-FinT nA nB f' inj-f'
      where

      f' : FinT nA -> FinT nB
      f' = eqFun eqB ∘ f ∘ eqInv eqA

      inj-f' : Injective f'
      inj-f' {a1} {a2} p =
        sym (eqSec eqA _) >=>
        cong (eqFun eqA) (inj-f (sym (eqRet eqB _) >=> (cong (eqInv eqB) p) >=> eqRet eqB _)) >=>
        eqSec eqA _


  Section->FinSet≤ : (f : A -> B) -> (Section f) -> FinSet≤ FB FA
  Section->FinSet≤ f (g , sec-g) =
    unsquash isProp-≤ (∥-map2 helper (snd fsB) (snd fsA))
    where
    helper : (B ≃ Fin nB) -> (A ≃ Fin nA) -> FinSet≤ FB FA
    helper eqB eqA = Surjective->FinSet≤-Fin nA nB f' sur-f'
      where

      f' : Fin nA -> Fin nB
      f' = eqFun eqB ∘ f ∘ eqInv eqA

      g' : Fin nB -> Fin nA
      g' = eqFun eqA ∘ g ∘ eqInv eqB

      sec-f' : isSectionOf f' g'
      sec-f' b =
        cong (eqFun eqB ∘ f) (eqRet eqA (g (eqInv eqB b))) >=>
        cong (eqFun eqB) (sec-g (eqInv eqB b)) >=>
        eqSec eqB b

      sur-f' : isSurjection f'
      sur-f' b = ∣ g' b , sec-f' b ∣


  Surjective->FinSet≤ : (f : A -> B) -> (isSurjection f) -> FinSet≤ FB FA
  Surjective->FinSet≤ f sur-f =
    unsquash isProp-≤ (∥-map2 helper (snd fsB) (snd fsA))
    where
    helper : (B ≃ Fin nB) -> (A ≃ Fin nA) -> FinSet≤ FB FA
    helper eqB eqA = Surjective->FinSet≤-Fin nA nB f' sur-f'
      where

      f' : Fin nA -> Fin nB
      f' = eqFun eqB ∘ f ∘ eqInv eqA

      sur-f' : isSurjection f'
      sur-f' b =
        ∥-map (\{ (a , p) -> (eqFun eqA a) , cong (eqFun eqB) (cong f (eqRet eqA a) >=> p) >=>
                                             eqSec eqB b})
              (sur-f (eqInv eqB b))

private
  ¬surjection->missed-point : {ℓA ℓB : Level} (A : FinSet ℓA) (B : FinSet ℓB)
                              (f : ⟨ A ⟩ -> ⟨ B ⟩) -> ¬ (isSurjection f) ->
                              ∃[ b ∈ ⟨ B ⟩ ] (∀ a -> f a != b)
  ¬surjection->missed-point A B f ¬sur =
    proj-¬r (find-section A B f)
      (\sec -> unsquash isPropBot (∥-map (¬sur ∘ Section->Surjection) sec))


module _ {ℓA ℓB : Level} (FA : FinSet ℓA) (FB : FinSet ℓB) (f : ⟨ FA ⟩ -> ⟨ FB ⟩)
         (inj-f : Injective f) (¬sur-f : ¬ (isSurjection f)) where
  private
    A = ⟨ FA ⟩
    B = ⟨ FB ⟩
    n = cardinality FA
    m = cardinality FB

    module _ (bad : Σ[ b ∈ B ] (∀ a -> f a != b)) where
      b = fst bad
      bad-f = snd bad

      f' : A -> WithoutPoint B b
      f' i = f i , bad-f i

      f'-inj : Injective f'
      f'-inj p = inj-f (cong fst p)

      lt1 : FinSet≤ FA (FinSet-WithoutPoint FB b)
      lt1 = (Injective->FinSet≤ FA (FinSet-WithoutPoint FB b) f' f'-inj)

      lt2 : FinSet< FA FB
      lt2 = trans-≤-< lt1 (FinSet<-WithoutPoint FB b)

  Injective-¬Surjective->FinSet< : FinSet< FA FB
  Injective-¬Surjective->FinSet< =
    unsquash isProp-< (∥-map lt2 (¬surjection->missed-point FA FB f ¬sur-f))

module _ {ℓA ℓB : Level} (FA : FinSet ℓA) (FB : FinSet ℓB) (f : ⟨ FA ⟩ -> ⟨ FB ⟩)
         (¬inj-f : ¬ (Injective f)) (sur-f : isSurjection f) where
  private
    A = ⟨ FA ⟩
    B = ⟨ FB ⟩

    module _ (bad : Σ[ a1 ∈ A ] Σ[ a2 ∈ A ] (a1 != a2 × f a1 == f a2)) where
      a1 = fst bad
      a2 = fst (snd bad)
      a1!=a2 = fst (snd (snd bad))
      fa1=fa2 = snd (snd (snd bad))

      A' : Type ℓA
      A' = WithoutPoint A a2

      a1' : A'
      a1' = a1 , a1!=a2

      f' : A' -> B
      f' (a , _) = f a

      sur-f' : isSurjection f'
      sur-f' b = ∥-map convert-fiber (sur-f b)
        where
        convert-fiber : fiber f b -> fiber f' b
        convert-fiber (a , fa=b) with (isFinSet->Discrete (snd FA) a a2)
        ... | (yes a=a2) = (a1 , a1!=a2) , fa1=fa2 >=> cong f (sym a=a2) >=> fa=b
        ... | (no a!=a2) = (a , a!=a2) , fa=b

      lt1 : FinSet≤ FB (FinSet-WithoutPoint FA a2)
      lt1 = Surjective->FinSet≤ (FinSet-WithoutPoint FA a2) FB f' sur-f'

      lt2 : FinSet< FB FA
      lt2 = trans-≤-< lt1 (FinSet<-WithoutPoint FA a2)
