{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module order.homomorphism.fint where

open import base
open import equality
open import equivalence
open import fin-algebra
open import fint.same-index
open import functions
open import funext
open import hlevel.base
open import nat.order
open import order
open import order.homomorphism
open import order.instances.fint
open import order.instances.nat
open import relation
open import sigma.base
open import sum
open import finset.search
open import finset.instances
open import truncation

private
  RelStream : {ℓA ℓR : Level} {A : Type ℓA} (R : Rel A ℓR) -> Type (ℓ-max ℓA ℓR)
  RelStream {A = A} R = Σ[ As ∈ (Nat -> A) ] ∀ n -> R (As n) (As (suc n))

  DescStream : {ℓA ℓ< : Level} (A : Type ℓA) {A< : Rel A ℓ<} -> {{isLinearOrder A<}} -> Type _
  DescStream A = RelStream {A = A} _>_

  AscStream : {ℓA ℓ< : Level} (A : Type ℓA) {A< : Rel A ℓ<} -> {{isLinearOrder A<}} -> Type _
  AscStream A = RelStream {A = A} _<_

  ¬DescStreamNat : ¬ (DescStream Nat)
  ¬DescStreamNat (nats , desc) = rec (suc (nats 0)) 0 refl-≤
    where
    rec : (i j : Nat) -> nats j < i -> Bot
    rec zero    _ = zero-≮
    rec (suc i) j nj<si = rec i (suc j) (trans-<-≤ (desc j) (pred-≤ nj<si))

  ¬DescStreamFin : {n : Nat} -> ¬ (DescStream (FinT n))
  ¬DescStreamFin (fins , desc) = ¬DescStreamNat (nats , desc')
    where
    FinT->index : {n : Nat} -> FinT n -> Nat
    FinT->index {zero} ()
    FinT->index {suc n} (inj-l tt) = 0
    FinT->index {suc n} (inj-r i) = suc (FinT->index i)

    FinT->index< : {n : Nat} -> {i j : FinT n} -> i < j -> FinT->index i < FinT->index j
    FinT->index< {zero} ()
    FinT->index< {suc n} (finT<-lr) = zero-<
    FinT->index< {suc n} (finT<-rr i<j) = suc-≤ (FinT->index< i<j)

    nats : Nat -> Nat
    nats n = FinT->index (fins n)
    desc' : ∀ n -> nats n > nats (suc n)
    desc' n = FinT->index< (desc n)

  ¬AscStreamFin : {n : Nat} -> ¬ (AscStream (FinT n))
  ¬AscStreamFin (fins , asc) = ¬DescStreamNat (nats , desc')
    where
    FinT->index : {n : Nat} -> FinT n -> Nat
    FinT->index {zero} ()
    FinT->index {suc n} (inj-l tt) = n
    FinT->index {suc n} (inj-r i)  = (FinT->index i)

    FinT->index< : {n : Nat} (i : FinT n) -> FinT->index i < n
    FinT->index< {zero} ()
    FinT->index< {suc n} (inj-l tt) = refl-≤
    FinT->index< {suc n} (inj-r i)  = trans-< (FinT->index< i) refl-≤

    FinT->index<' : {n : Nat} {i j : FinT n} -> i < j -> FinT->index i > FinT->index j
    FinT->index<' {zero} ()
    FinT->index<' {suc n} (finT<-lr) = FinT->index< _
    FinT->index<' {suc n} (finT<-rr i<j) = FinT->index<' i<j

    nats : Nat -> Nat
    nats n = FinT->index (fins n)
    desc' : ∀ n -> nats n > nats (suc n)
    desc' n = FinT->index<' (asc n)

  no-changed-indexes : (n : Nat) (f : (Σ (FinT n -> FinT n) LinearOrderʰ)) -> (i : FinT n) ->
                       i != ⟨ f ⟩ i -> Bot
  no-changed-indexes n (f , h) i i!=fi = handle (trichotomous-< i (f i))
    where
    handle : Tri< i (f i) -> Bot
    handle (tri= _ i=fi _) = i!=fi i=fi
    handle (tri< i<fi _ _) = ¬AscStreamFin (fins , asc)
      where
      module h = LinearOrderʰᵉ h
      fins : Nat -> FinT n
      fins zero = i
      fins (suc j) = f (fins j)

      asc : (j : Nat) -> fins j < fins (suc j)
      asc zero = i<fi
      asc (suc j) = h.preserves-< (asc j)
    handle (tri> _ _ i>fi) = ¬DescStreamFin (fins , desc)
      where
      module h = LinearOrderʰᵉ h
      fins : Nat -> FinT n
      fins zero = i
      fins (suc j) = f (fins j)

      desc : (j : Nat) -> fins j > fins (suc j)
      desc zero = i>fi
      desc (suc j) = h.preserves-< (desc j)

  decide-fint : {n : Nat} (i j : FinT n) -> Dec (i == j)
  decide-fint {zero} ()
  decide-fint {suc n} (inj-l _) (inj-l _) = yes refl
  decide-fint {suc n} (inj-l _) (inj-r _) = no (inj-l!=inj-r)
  decide-fint {suc n} (inj-r _) (inj-l _) = no (inj-l!=inj-r ∘ sym)
  decide-fint {suc n} (inj-r i) (inj-r j) =
    case (decide-fint i j) of (\{
      (no f) -> no (f ∘ inj-r-injective) ;
      (yes p) -> yes (cong inj-r p)
    })


  all-same-indexes :
    (n : Nat) (f : (Σ (FinT n -> FinT n) LinearOrderʰ)) -> (∀ i -> i == ⟨ f ⟩ i)
  all-same-indexes n (f , h) =
    proj-¬l (finite-search-dec' (FinSet-FinT n) decP)
            (\ex -> unsquash isPropBot
                      (∥-map (\ (i , i!=fi) -> no-changed-indexes n (f , h) i i!=fi) ex))
    where
    decP : Decidable (\i -> i == f i)
    decP i = decide-fint i (f i)

∃!LinearOrderʰ-FinT-FinT : ∀ (n : Nat) -> ∃! (FinT n -> FinT n) LinearOrderʰ
∃!LinearOrderʰ-FinT-FinT n = center , contractible
  where
  center : Σ (FinT n -> FinT n) LinearOrderʰ
  center = idfun (FinT n) , record { preserves-< = \lt -> lt }

  abstract
    contractible : ∀ (f : Σ (FinT n -> FinT n) LinearOrderʰ) -> center == f
    contractible = (\ (f , h) -> ΣProp-path isProp-LinearOrderʰ (funExt (all-same-indexes n (f , h))))

LinearOrderʰ-FinT-FinT'-SameIndex :
  ∀ {n1 n2 : Nat} -> n1 == n2 -> {f : FinT n1 -> FinT n2} -> (h : LinearOrderʰ f) ->
    (i : FinT n1) -> SameIndex i (f i)
LinearOrderʰ-FinT-FinT'-SameIndex {n1} {n2} np {f} h i =
  transport (\j -> SameIndex i (c=f j i)) s

  where
  c = ∃!-val (∃!LinearOrderʰ-FinT-FinT n1)

  fp : Σ (FinT n1 -> FinT n2) LinearOrderʰ ==
       Σ (FinT n1 -> FinT n1) LinearOrderʰ
  fp i = Σ (FinT n1 -> FinT (np (~ i))) LinearOrderʰ

  c=f' : c == fst (transport fp (f , h))
  c=f' = ∃!-unique (∃!LinearOrderʰ-FinT-FinT n1)
            (fst (transport fp (f , h)))
            (snd (transport fp (f , h)))

  c=f : PathP (\i -> FinT n1 -> FinT (np i)) c f
  c=f = transP-right c=f' (\i -> fst (transport-filler fp (f , h) (~ i)))

  s : SameIndex i (c i)
  s = SameIndex-refl i
