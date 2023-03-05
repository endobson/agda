{-# OPTIONS --cubical --safe --exact-split #-}

module order.homomorphism.fin where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality
open import equivalence
open import fin
open import functions
open import funext
open import hlevel
open import nat.order
open import order
open import order.homomorphism
open import order.instances.fin
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import relation
open import sigma.base
open import sum
open import finset.search
open import finset.instances
open import truncation

private
  RelStream : {ℓA ℓR : Level} {A : Type ℓA} (R : Rel A ℓR) -> Type (ℓ-max ℓA ℓR)
  RelStream {A = A} R = Σ[ As ∈ (Nat -> A) ] ∀ n -> R (As n) (As (suc n))

  DescStream : {ℓA ℓ< : Level} (A : Type ℓA) -> {{LinearOrderStr A ℓ<}} -> Type _
  DescStream A = RelStream {A = A} _>_

  AscStream : {ℓA ℓ< : Level} (A : Type ℓA) -> {{LinearOrderStr A ℓ<}} -> Type _
  AscStream A = RelStream {A = A} _<_

  ¬DescStreamNat : ¬ (DescStream Nat)
  ¬DescStreamNat (nats , desc) = rec (suc (nats 0)) 0 refl-≤
    where
    rec : (i j : Nat) -> nats j < i -> Bot
    rec zero    _ = zero-≮
    rec (suc i) j nj<si = rec i (suc j) (trans-<-≤ (desc j) (pred-≤ nj<si))

  ¬DescStreamFin : {n : Nat} -> ¬ (DescStream (Fin n))
  ¬DescStreamFin (fins , desc) = ¬DescStreamNat (nats , desc')
    where
    nats : Nat -> Nat
    nats n = Fin.i (fins n)
    desc' : ∀ n -> nats n > nats (suc n)
    desc' n = fin<⁻ (desc n)

  ¬AscStreamFin : {n : Nat} -> ¬ (AscStream (Fin n))
  ¬AscStreamFin {n = N} (fins , asc) = ¬DescStreamNat (nats , desc')
    where
    nats : Nat -> Nat
    nats n = fst (Fin.i<n (fins n))
    desc' : ∀ n -> nats n > nats (suc n)
    desc' n = extract (asc n)
      where
      extract : (fins n < fins (suc n)) -> nats n > nats (suc n)
      extract (fin< lt) = +₂-reflects-< (trans-<-= (+₁-preserves-< (suc-≤ lt)) p)
        where
        i-n = Fin.i (fins n)
        i-sn = Fin.i (fins (suc n))

        n-n = nats n
        n-sn = nats (suc n)

        p-n : n-n + (suc i-n) == N
        p-n = snd (Fin.i<n (fins n))
        p-sn : n-sn + (suc i-sn) == N
        p-sn = snd (Fin.i<n (fins (suc n)))
        p : n-sn + (suc i-sn) == n-n + (suc i-n)
        p = p-sn >=> sym p-n


  no-changed-indexes : (n : Nat) (f : (Σ (Fin n -> Fin n) LinearOrderʰ)) -> (i : Fin n) ->
                       i != ⟨ f ⟩ i -> Bot
  no-changed-indexes n (f , h) i i!=fi = handle (trichotomous-< i (f i))
    where
    handle : Tri< i (f i) -> Bot
    handle (tri= _ i=fi _) = i!=fi i=fi
    handle (tri< i<fi _ _) = ¬AscStreamFin (fins , asc)
      where
      module h = LinearOrderʰᵉ h
      fins : Nat -> Fin n
      fins zero = i
      fins (suc j) = f (fins j)

      asc : (j : Nat) -> fins j < fins (suc j)
      asc zero = i<fi
      asc (suc j) = h.preserves-< (asc j)
    handle (tri> _ _ i>fi) = ¬DescStreamFin (fins , desc)
      where
      module h = LinearOrderʰᵉ h
      fins : Nat -> Fin n
      fins zero = i
      fins (suc j) = f (fins j)

      desc : (j : Nat) -> fins j > fins (suc j)
      desc zero = i>fi
      desc (suc j) = h.preserves-< (desc j)

  all-same-indexes :
    (n : Nat) (f : (Σ (Fin n -> Fin n) LinearOrderʰ)) -> (∀ i -> i == ⟨ f ⟩ i)
  all-same-indexes n (f , h) =
    proj-¬l (finite-search-dec' (FinSet-Fin n) decP)
            (\ex -> unsquash isPropBot
                      (∥-map (\ (i , i!=fi) -> no-changed-indexes n (f , h) i i!=fi) ex))
    where
    decP : Decidable (\i -> i == f i)
    decP i = decide-fin i (f i)

∃!LinearOrderʰ-Fin-Fin : ∀ (n : Nat) -> ∃! (Fin n -> Fin n) LinearOrderʰ
∃!LinearOrderʰ-Fin-Fin n = center , contractible
  where
  center : Σ (Fin n -> Fin n) LinearOrderʰ
  center = idfun (Fin n) , record { preserves-< = \lt -> lt }

  abstract
    contractible : ∀ (f : Σ (Fin n -> Fin n) LinearOrderʰ) -> center == f
    contractible = (\ (f , h) -> ΣProp-path isProp-LinearOrderʰ (funExt (all-same-indexes n (f , h))))



∃!LinearOrderʰ-Fin-Fin' : ∀ {n1 n2 : Nat} -> n1 == n2 -> ∃! (Fin n1 -> Fin n2) LinearOrderʰ
∃!LinearOrderʰ-Fin-Fin' {n1} {n2} n1=n2 =
  ∃!-swap base new-center
  where
  f : Fin n1 -> Fin n2
  f (i , lt) = (i , subst (i <_) n1=n2 lt)
  f< : ∀ {x y} -> x < y -> f x < f y
  f< (fin< lt) = (fin< lt)

  new-center : Σ (Fin n1 -> Fin n2) LinearOrderʰ
  new-center = f , record { preserves-< = f< }

  base : ∃! (Fin n1 -> Fin n2) LinearOrderʰ
  base = subst (\n -> ∃! (Fin n1 -> Fin n) LinearOrderʰ)
           n1=n2 (∃!LinearOrderʰ-Fin-Fin n1)
