{-# OPTIONS --cubical --safe --exact-split #-}

module finset.order where

open import additive-group
open import additive-group.instances.nat
open import base
open import cubical using (_≃_)
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finite-commutative-monoid.instances
open import finset
open import finset.cardinality
open import finset.detachable
open import finset.instances
open import finset.instances
open import finsum
open import functions
open import funext
open import hlevel
open import nat.order
open import order using (trans-≤-=)
open import order.instances.nat
open import ordered-semiring
open import ordered-semiring.instances.nat
open import relation
open import ring.implementations
open import sigma
open import sigma.base
open import sum
open import truncation
open import type-algebra
open import univalence


FinSetᵉ≤ : {ℓA ℓB : Level} -> (A : FinSet ℓA) -> (B : FinSet ℓB) -> Type₀
FinSetᵉ≤ A B = cardinality A ≤ cardinality B

FinSetᵉ< : {ℓA ℓB : Level} -> (A : FinSet ℓA) -> (B : FinSet ℓB) -> Type₀
FinSetᵉ< A B = cardinality A < cardinality B


WellFounded-FinSet< : {ℓ : Level} -> WellFounded (FinSetᵉ< {ℓ} {ℓ})
WellFounded-FinSet< {ℓ} fs = Acc-FinSet< fs (WellFounded-Nat< (cardinality fs))
  where
  Acc-FinSet< : (fs : FinSet ℓ) (a : Acc _<_ (cardinality fs)) -> Acc FinSetᵉ< fs
  Acc-FinSet< fs1 (acc f) = 
    (acc (\fs2 fs2<fs1 -> (Acc-FinSet< fs2 (f (cardinality fs2) fs2<fs1))))

FinSet< : {ℓA ℓB : Level} -> (A : Type ℓA) -> (B : Type ℓB) -> 
           {{fsA : FinSetStr A}} {{fsB : FinSetStr B}} -> Type₀
FinSet< A B = cardinalityⁱ A < cardinalityⁱ B

FinSet≤ : {ℓA ℓB : Level} -> (A : Type ℓA) -> (B : Type ℓB) -> 
           {{fsA : FinSetStr A}} {{fsB : FinSetStr B}} -> Type₀
FinSet≤ A B = cardinalityⁱ A ≤ cardinalityⁱ B

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



module _ {ℓA ℓB : Level} (A : Type ℓA) (B : Type ℓB)
         {{fsA-Str : FinSetStr A}} {{fsB-Str : FinSetStr B}} where
  private
    fsA : isFinSetΣ A
    fsA = isFinSet->isFinSetΣ (FinSetStr.isFin fsA-Str)
    fsB : isFinSetΣ B
    fsB = isFinSet->isFinSetΣ (FinSetStr.isFin fsB-Str)

    nA nB : Nat
    nA = cardinalityⁱ A 
    nB = cardinalityⁱ B

    eqA' : ∥ A ≃ FinT nA ∥
    eqA' = subst (\t -> (∥ A ≃ t ∥)) (sym (FinT=Fin nA)) (snd fsA)
    eqB' : ∥ B ≃ FinT nB ∥
    eqB' = subst (\t -> (∥ B ≃ t ∥)) (sym (FinT=Fin nB)) (snd fsB)

  Retraction->FinSet≤ : (f : A -> B) -> (Retraction f) -> FinSet≤ A B
  Retraction->FinSet≤ f (g , ret-g) = unsquash isProp≤ (∥-map2 helper eqA' eqB')
    where
    helper : (A ≃ FinT nA) -> (B ≃ FinT nB) -> FinSet≤ A B
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
 
  Section->FinSet≤ : (f : A -> B) -> (Section f) -> FinSet≤ B A
  Section->FinSet≤ f (g , sec-g) = 
    unsquash isProp≤ (∥-map2 helper (snd fsB) (snd fsA))
    where
    helper : (B ≃ Fin nB) -> (A ≃ Fin nA) -> FinSet≤ B A
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
