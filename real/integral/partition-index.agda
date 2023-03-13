{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module real.integral.partition-index where

open import base
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finset
open import finset.detachable
open import functions
open import hlevel.base
open import isomorphism
open import maybe
open import nat
open import nat.order.base
open import order
open import order.instances.fin
open import order.instances.nat
open import relation
open import sum
open import truncation
open import type-algebra
open import sigma.base

data PartitionIndex (n : Nat) : Type₀ where
  pi-low : PartitionIndex n
  pi-mid : Fin n -> PartitionIndex n
  pi-high : PartitionIndex n

data PartitionBoundary (n : Nat) : Type₀ where
  pb-low : PartitionBoundary n
  pb-mid : Fin (suc n) -> PartitionBoundary n
  pb-high : PartitionBoundary n

LowPartitionBoundary : {n : Nat} -> PartitionBoundary n -> Type₀
LowPartitionBoundary pb-low     = Top
LowPartitionBoundary (pb-mid i) = Top
LowPartitionBoundary pb-high    = Bot

HighPartitionBoundary : {n : Nat} -> PartitionBoundary n -> Type₀
HighPartitionBoundary pb-low     = Bot
HighPartitionBoundary (pb-mid i) = Top
HighPartitionBoundary pb-high    = Top

isProp-LowPartitionBoundary :
  {n : Nat} -> (pb : PartitionBoundary n) -> isProp (LowPartitionBoundary pb)
isProp-LowPartitionBoundary pb-low     = isPropTop
isProp-LowPartitionBoundary (pb-mid i) = isPropTop
isProp-LowPartitionBoundary pb-high    = isPropBot

isProp-HighPartitionBoundary :
  {n : Nat} -> (pb : PartitionBoundary n) -> isProp (HighPartitionBoundary pb)
isProp-HighPartitionBoundary pb-low     = isPropBot
isProp-HighPartitionBoundary (pb-mid i) = isPropTop
isProp-HighPartitionBoundary pb-high    = isPropTop

Decidable-LowPartitionBoundary :
 {n : Nat} -> (pb : PartitionBoundary n) -> Dec (LowPartitionBoundary pb)
Decidable-LowPartitionBoundary pb-low     = yes tt
Decidable-LowPartitionBoundary (pb-mid i) = yes tt
Decidable-LowPartitionBoundary pb-high    = no (\x -> x)

Decidable-HighPartitionBoundary :
  {n : Nat} -> (pb : PartitionBoundary n) -> Dec (HighPartitionBoundary pb)
Decidable-HighPartitionBoundary pb-low     = no (\x -> x)
Decidable-HighPartitionBoundary (pb-mid i) = yes tt
Decidable-HighPartitionBoundary pb-high    = yes tt

isContr-Σ¬LowPartitionBoundary :
  {n : Nat} -> isContr (Σ (PartitionBoundary n) (Comp LowPartitionBoundary))
isContr-Σ¬LowPartitionBoundary {n} = ctr , contr
  where
  ctr = (pb-high , (\x -> x))
  contr : (x : Σ (PartitionBoundary n) (Comp LowPartitionBoundary)) -> ctr == x
  contr (pb-low , f) = bot-elim (f tt)
  contr (pb-mid _ , f) = bot-elim (f tt)
  contr (pb-high , f) = ΣProp-path (isPropΠ (\_ -> isPropBot)) refl

isContr-Σ¬HighPartitionBoundary :
  {n : Nat} -> isContr (Σ (PartitionBoundary n) (Comp HighPartitionBoundary))
isContr-Σ¬HighPartitionBoundary {n} = ctr , contr
  where
  ctr = (pb-low , (\x -> x))
  contr : (x : Σ (PartitionBoundary n) (Comp HighPartitionBoundary)) -> ctr == x
  contr (pb-low , f) = ΣProp-path (isPropΠ (\_ -> isPropBot)) refl
  contr (pb-mid _ , f) = bot-elim (f tt)
  contr (pb-high , f) = bot-elim (f tt)


data PartitionBoundary< {n : Nat} : Rel (PartitionBoundary n) ℓ-zero where
  pb<-low-mid : (i : Fin (suc n)) -> PartitionBoundary< pb-low (pb-mid i)
  pb<-low-high : PartitionBoundary< pb-low pb-high
  pb<-mid-mid : (i j : Fin (suc n)) -> (i < j) -> PartitionBoundary< (pb-mid i) (pb-mid j)
  pb<-mid-high : (i : Fin (suc n)) -> PartitionBoundary< (pb-mid i) pb-high

private
  abstract
    isProp-PartitionBoundary< : {n : Nat} {i j : PartitionBoundary n} -> isProp (PartitionBoundary< i j)
    isProp-PartitionBoundary< (pb<-low-mid i)       (pb<-low-mid i)       = refl
    isProp-PartitionBoundary< (pb<-low-high)        (pb<-low-high)        = refl
    isProp-PartitionBoundary< (pb<-mid-high i)      (pb<-mid-high i)      = refl
    isProp-PartitionBoundary< (pb<-mid-mid i j lt1) (pb<-mid-mid i j lt2) =
      cong (pb<-mid-mid i j) (isProp-< lt1 lt2)

    irrefl-PartitionBoundary< : {n : Nat} -> Irreflexive (PartitionBoundary< {n})
    irrefl-PartitionBoundary< (pb<-mid-mid i i lt) = irrefl-< lt

    trans-PartitionBoundary< : {n : Nat} -> Transitive (PartitionBoundary< {n})
    trans-PartitionBoundary< (pb<-low-mid i) (pb<-mid-mid i j lt) = (pb<-low-mid j)
    trans-PartitionBoundary< (pb<-low-mid i) (pb<-mid-high i) = pb<-low-high
    trans-PartitionBoundary< (pb<-mid-mid i j lt1) (pb<-mid-mid j k lt2) =
      pb<-mid-mid i k (trans-< lt1 lt2)
    trans-PartitionBoundary< (pb<-mid-mid i j lt) (pb<-mid-high j) = (pb<-mid-high i)

    connected-PartitionBoundary< : {n : Nat} -> Connected (PartitionBoundary< {n})
    connected-PartitionBoundary< {x = pb-low}     {y = pb-low}     ¬lt1 ¬lt2 = refl
    connected-PartitionBoundary< {x = pb-high}    {y = pb-high}    ¬lt1 ¬lt2 = refl
    connected-PartitionBoundary< {x = (pb-mid i)} {y = (pb-mid j)} ¬lt1 ¬lt2 =
      cong pb-mid (connected-< (¬lt1 ∘ pb<-mid-mid i j) (¬lt2 ∘ pb<-mid-mid j i))
    connected-PartitionBoundary< {x = pb-low}     {y = (pb-mid i)} ¬lt1 ¬lt2 =
      bot-elim (¬lt1 (pb<-low-mid i))
    connected-PartitionBoundary< {x = pb-low}     {y = pb-high}    ¬lt1 ¬lt2 =
      bot-elim (¬lt1 pb<-low-high)
    connected-PartitionBoundary< {x = (pb-mid i)} {y = pb-low}    ¬lt1 ¬lt2 =
      bot-elim (¬lt2 (pb<-low-mid i))
    connected-PartitionBoundary< {x = (pb-mid i)} {y = pb-high}    ¬lt1 ¬lt2 =
      bot-elim (¬lt1 (pb<-mid-high i))
    connected-PartitionBoundary< {x = pb-high}    {y = pb-low}     ¬lt1 ¬lt2 =
      bot-elim (¬lt2 pb<-low-high)
    connected-PartitionBoundary< {x = pb-high}    {y = (pb-mid i)} ¬lt1 ¬lt2 =
      bot-elim (¬lt2 (pb<-mid-high i))

    comparison-PartitionBoundary< : {n : Nat} -> Comparison (PartitionBoundary< {n})
    comparison-PartitionBoundary< a pb-low     c (pb<-low-mid i)      = ∣ inj-r (pb<-low-mid i)  ∣
    comparison-PartitionBoundary< a pb-low     c (pb<-low-high)       = ∣ inj-r (pb<-low-high)   ∣
    comparison-PartitionBoundary< a pb-low     c (pb<-mid-mid i j lt) = ∣ inj-r (pb<-low-mid j)  ∣
    comparison-PartitionBoundary< a pb-low     c (pb<-mid-high j)     = ∣ inj-r (pb<-low-high)   ∣
    comparison-PartitionBoundary< a (pb-mid i) c (pb<-low-high)       = ∣ inj-l (pb<-low-mid i)  ∣
    comparison-PartitionBoundary< a (pb-mid i) c (pb<-low-mid j)      = ∣ inj-l (pb<-low-mid i)  ∣
    comparison-PartitionBoundary< a (pb-mid i) c (pb<-mid-high j)     = ∣ inj-r (pb<-mid-high i) ∣
    comparison-PartitionBoundary< a pb-high    c (pb<-low-mid j)      = ∣ inj-l (pb<-low-high)   ∣
    comparison-PartitionBoundary< a pb-high    c (pb<-mid-mid i j lt) = ∣ inj-l (pb<-mid-high i) ∣
    comparison-PartitionBoundary< a pb-high    c (pb<-low-high)       = ∣ inj-l (pb<-low-high)   ∣
    comparison-PartitionBoundary< a pb-high    c (pb<-mid-high i)     = ∣ inj-l (pb<-mid-high i) ∣
    comparison-PartitionBoundary< a (pb-mid j) c (pb<-mid-mid i k lt) =
      ∥-map (⊎-map (pb<-mid-mid i j) (pb<-mid-mid j k)) (comparison-< i j k lt)



instance
  LinearOrderStr-PartitionBoundary : {n : Nat} -> LinearOrderStr (PartitionBoundary n) ℓ-zero
  LinearOrderStr-PartitionBoundary = record
    { _<_ = PartitionBoundary<
    ; isLinearOrder-< = record
      { isProp-< = isProp-PartitionBoundary<
      ; irrefl-< = irrefl-PartitionBoundary<
      ; trans-< = trans-PartitionBoundary<
      ; connected-< = connected-PartitionBoundary<
      ; comparison-< = comparison-PartitionBoundary<
      }
    }

  PartialOrderStr-PartitionBoundary : {n : Nat} -> PartialOrderStr (PartitionBoundary n) ℓ-zero
  PartialOrderStr-PartitionBoundary =
    NegatedLinearOrder LinearOrderStr-PartitionBoundary

  CompatibleOrderStr-PartitionBoundary : {n : Nat} -> CompatibleOrderStr _ _
  CompatibleOrderStr-PartitionBoundary {n} =
    CompatibleNegatedLinearOrder (LinearOrderStr-PartitionBoundary {n})

private
  abstract
    trichotomous-PartitionBoundary< : {n : Nat} -> Trichotomous (PartitionBoundary< {n})
    trichotomous-PartitionBoundary< pb-low     pb-low     = tri=' refl
    trichotomous-PartitionBoundary< pb-low     (pb-mid i) = tri<' (pb<-low-mid i)
    trichotomous-PartitionBoundary< pb-low     pb-high    = tri<' pb<-low-high
    trichotomous-PartitionBoundary< (pb-mid i) pb-low     = tri>' (pb<-low-mid i)
    trichotomous-PartitionBoundary< (pb-mid i) pb-high    = tri<' (pb<-mid-high i)
    trichotomous-PartitionBoundary< pb-high    pb-low     = tri>' pb<-low-high
    trichotomous-PartitionBoundary< pb-high    (pb-mid i) = tri>' (pb<-mid-high i)
    trichotomous-PartitionBoundary< pb-high    pb-high    = tri=' refl
    trichotomous-PartitionBoundary< i'@(pb-mid i) j'@(pb-mid j) = handle (trichotomous-< i j)
      where
      handle : Tri< i j -> Tri< i' j'
      handle (tri< lt _ _) = tri<' (pb<-mid-mid i j lt)
      handle (tri= _ eq _) = tri=' (cong pb-mid eq)
      handle (tri> _ _ gt) = tri>' (pb<-mid-mid j i gt)

instance

  DecidableLinearOrderStr-PartitionBoundary :
    {n : Nat} -> DecidableLinearOrderStr (LinearOrderStr-PartitionBoundary {n})
  DecidableLinearOrderStr-PartitionBoundary = record
    { trichotomous-< = trichotomous-PartitionBoundary<
    }

  TotalOrderStr-PartitionBoundary :
    {n : Nat} -> TotalOrderStr (PartialOrderStr-PartitionBoundary {n})
  TotalOrderStr-PartitionBoundary = TotalOrderStr-LinearOrder


index->low-boundary : {n : Nat} -> PartitionIndex n -> Σ (PartitionBoundary n) LowPartitionBoundary
index->low-boundary pi-low     = pb-low , tt
index->low-boundary (pi-mid i) = pb-mid (inc-fin i) , tt
index->low-boundary pi-high    = pb-mid (_ , refl-≤) , tt

index->high-boundary : {n : Nat} -> PartitionIndex n -> Σ (PartitionBoundary n) HighPartitionBoundary
index->high-boundary pi-low     = pb-mid zero-fin  , tt
index->high-boundary (pi-mid i) = pb-mid (suc-fin i) , tt
index->high-boundary pi-high    = pb-high , tt

index->low-boundary-eq : {n : Nat} -> PartitionIndex n ≃ Σ (PartitionBoundary n) LowPartitionBoundary
index->low-boundary-eq {n} =
  isoToEquiv (iso index->low-boundary low-boundary->index inv1 inv2)
  where
  low-boundary->index : Σ (PartitionBoundary n) LowPartitionBoundary -> PartitionIndex n
  low-boundary->index (pb-low , _) = pi-low
  low-boundary->index (pb-mid (i , (0 , p)) , _) = pi-high
  low-boundary->index (pb-mid (i , (suc j , p)) , _) = pi-mid (i , (j , cong pred p))

  inv1 : (b : Σ (PartitionBoundary n) LowPartitionBoundary) ->
         (index->low-boundary (low-boundary->index b)) == b
  inv1 (pb-low , _) = refl
  inv1 (pb-mid (i , (0 , p)) , _) = cong (\j -> pb-mid j , tt) (fin-i-path (cong pred (sym p)))
  inv1 (pb-mid (i , (suc _ , p)) , _) = cong (\j -> pb-mid j , tt) (fin-i-path refl)

  inv2 : (i : PartitionIndex n) -> (low-boundary->index (index->low-boundary i)) == i
  inv2 pi-low = refl
  inv2 (pi-mid i) = cong pi-mid (fin-i-path refl)
  inv2 pi-high = refl

index->high-boundary-eq : {n : Nat} -> PartitionIndex n ≃ Σ (PartitionBoundary n) HighPartitionBoundary
index->high-boundary-eq {n} =
  isoToEquiv (iso index->high-boundary high-boundary->index inv1 inv2)
  where
  high-boundary->index : Σ (PartitionBoundary n) HighPartitionBoundary -> PartitionIndex n
  high-boundary->index (pb-high , _) = pi-high
  high-boundary->index (pb-mid (0 , lt) , _) = pi-low
  high-boundary->index (pb-mid (suc i , lt) , _) = pi-mid (i , pred-≤ lt)

  inv1 : (b : Σ (PartitionBoundary n) HighPartitionBoundary) ->
         (index->high-boundary (high-boundary->index b)) == b
  inv1 (pb-high , _) = refl
  inv1 (pb-mid (0 , lt) , _) = cong (\j -> pb-mid j , tt) (fin-i-path refl)
  inv1 (pb-mid (suc i , lt) , _) = cong (\j -> pb-mid j , tt) (fin-i-path refl)

  inv2 : (i : PartitionIndex n) -> (high-boundary->index (index->high-boundary i)) == i
  inv2 pi-low = refl
  inv2 (pi-mid i) = cong pi-mid (fin-i-path refl)
  inv2 pi-high = refl


low-boundary<high-boundary : {n : Nat} -> (i : PartitionIndex n) ->
  ⟨ index->low-boundary i ⟩ < ⟨ index->high-boundary i ⟩
low-boundary<high-boundary {n} pi-low = low<high (index->high-boundary pi-low)
  where
  low<high : (i : Σ (PartitionBoundary n) HighPartitionBoundary) -> pb-low < ⟨ i ⟩
  low<high (pb-mid i , _) = pb<-low-mid i
  low<high (pb-high , _) = pb<-low-high
low-boundary<high-boundary (pi-mid i) =
  pb<-mid-mid (inc-fin i) (suc-fin i) (fin< refl-≤)
low-boundary<high-boundary {n} pi-high = low<high (index->low-boundary pi-high)
  where
  low<high : (i : Σ (PartitionBoundary n) LowPartitionBoundary) -> ⟨ i ⟩ < pb-high
  low<high (pb-low , _) = pb<-low-high
  low<high (pb-mid i , _) = pb<-mid-high i

module _ {ℓD ℓ< : Level} {D : Type ℓD} {{LO : LinearOrderStr D ℓ<}} where
  SuccessorOf : Rel D (ℓ-max ℓD ℓ<)
  SuccessorOf x y = x < y × ∀ z -> ¬ (x < z × z < y)

private
  SuccessorOf->suc : {x y : Nat} -> SuccessorOf x y -> suc x == y
  SuccessorOf->suc {x} {y} ((zero , p) , f) = p
  SuccessorOf->suc {x} {y} ((suc i , p) , f) =
    bot-elim (f (suc x) (refl-≤ , (i , +'-right-suc >=> p)))

  Nat->SuccessorOf : (n : Nat) -> SuccessorOf n (suc n)
  Nat->SuccessorOf n = refl-≤ , (\i (n<i , i<sn) -> irrefl-< (trans-<-≤ i<sn n<i))

  SuccessorOfFin->Fin : {n : Nat} {x y : Fin (suc n)} -> SuccessorOf x y ->
                        Σ[ i ∈ Fin n ] (x == inc-fin i × y == suc-fin i)
  SuccessorOfFin->Fin {n} {i , i<sn} {j , j<sn} (fin< i<j , f) =
    (i , trans-<-≤ i<j (pred-≤ j<sn)) , (fin-i-path refl) , (fin-i-path (sym p))
    where
    f' : ∀ z -> ¬ (i < z × z < j)
    f' z (i<z , z<j) = f (z , trans-< z<j j<sn) (fin< i<z , fin< z<j)

    p : suc i == j
    p = SuccessorOf->suc (i<j , f')

  Fin->SuccessorOf : {n : Nat} -> (i : Fin n) -> SuccessorOf (inc-fin i) (suc-fin i)
  Fin->SuccessorOf {n} i@(i' , i<n) = (fin< (fst adj)) , cases
    where
    adj : SuccessorOf i' (suc i')
    adj = Nat->SuccessorOf i'
    cases : (j : Fin (suc n)) -> (inc-fin i < j × j < suc-fin i) -> Bot
    cases (j' , _) (fin< lt1 , fin< lt2) = snd adj j' (lt1 , lt2)

SuccessorOf->Index : {n : Nat} {x y : PartitionBoundary n} -> SuccessorOf x y ->
                     Σ[ i ∈ PartitionIndex n ] (x == ⟨ index->low-boundary i ⟩ ×
                                                y == ⟨ index->high-boundary i ⟩)
SuccessorOf->Index {n} {pb-low}   {pb-mid _} (pb<-low-mid (0 , _) , f) =
  pi-low , (refl , cong pb-mid (fin-i-path refl))
SuccessorOf->Index {n} {pb-low}   {pb-mid _} (pb<-low-mid (suc i , lt) , f) =
  bot-elim (f (pb-mid (i , trans-< refl-≤ lt)) (pb<-low-mid _ , pb<-mid-mid _ _ (fin< refl-≤)))
SuccessorOf->Index {n} {pb-low}   {pb-high}  (pb<-low-high , f) =
  bot-elim (f (pb-mid zero-fin) (pb<-low-mid _ , pb<-mid-high _))
SuccessorOf->Index {n} {pb-mid _} {pb-mid _} (pb<-mid-mid i j i<j , f) =
  pi-mid (fst Σk) , (\i -> (pb-mid (fst (snd Σk) i))) , (\i -> (pb-mid (snd (snd Σk) i)))
  where
  f' : ∀ z -> ¬ (i < z × z < j)
  f' z (i<z , z<j) = f (pb-mid z) (pb<-mid-mid i z i<z , pb<-mid-mid z j z<j)

  Σk : Σ[ k ∈ Fin n ] (i == inc-fin k × j == suc-fin k)
  Σk = SuccessorOfFin->Fin (i<j , f')

SuccessorOf->Index {n} {pb-mid _} {pb-high} (pb<-mid-high i@(_ , (0 , p)) , f) =
  pi-high , cong pb-mid (fin-i-path (cong pred p)) , refl
SuccessorOf->Index {n} {pb-mid _} {pb-high} (pb<-mid-high (i , (suc j , p)) , f) =
  bot-elim (f (pb-mid (suc i , (j , +'-right-suc >=> p)))
              (pb<-mid-mid _ _ (fin< refl-≤) , pb<-mid-high _))


Index->SuccessorOf : {n : Nat} -> (i : PartitionIndex n) ->
                     SuccessorOf ⟨ index->low-boundary i ⟩ ⟨ index->high-boundary i ⟩
Index->SuccessorOf {n} pi-low = pb<-low-mid _ , cases
  where
  cases : (j : PartitionBoundary n) -> _
  cases (pb-mid j) (pb<-low-mid j , pb<-mid-mid j _ (fin< lt)) = zero-≮ lt
Index->SuccessorOf {n} pi-high = pb<-mid-high _ , cases
  where
  cases : (j : PartitionBoundary n) -> _
  cases (pb-mid j) (pb<-mid-mid _ (_ , lt1) (fin< lt2) , pb<-mid-high j) = irrefl-< check3
    where
    check1 : Fin.i j < suc n
    check1 = lt1
    check2 : n < Fin.i j
    check2 = lt2
    check3 : Fin.i j < Fin.i j
    check3 = trans-<-≤ check1 check2
Index->SuccessorOf {n} (pi-mid i) = pb<-mid-mid _ _ (fst adj) , cases
  where
  adj : SuccessorOf (inc-fin i) (suc-fin i)
  adj = Fin->SuccessorOf i
  cases : (j : PartitionBoundary n) -> (pb-mid (inc-fin i) < j ×
                                        j < pb-mid (suc-fin i)) -> Bot
  cases (pb-mid j) (pb<-mid-mid _ _ lt1 , pb<-mid-mid _ _ lt2) =
    snd adj j (lt1 , lt2)

private
  abstract
    PartitionIndex≃Fin : {n : Nat} -> PartitionIndex n ≃ Fin (suc (suc n))
    PartitionIndex≃Fin {n} =
      (isoToEquiv i) >eq> (Maybe-eq (equiv⁻¹ (Fin-Maybe-eq _))) >eq> (equiv⁻¹ (Fin-Maybe-eq _))
      where
      open Iso
      i : Iso (PartitionIndex n) (Maybe (Maybe (Fin n)))
      i .fun pi-low = nothing
      i .fun (pi-mid idx) = (just (just idx))
      i .fun pi-high = (just nothing)
      i .inv nothing = pi-low
      i .inv (just nothing) = pi-high
      i .inv (just (just idx)) = pi-mid idx
      i .leftInv pi-low = refl
      i .leftInv (pi-mid idx) = refl
      i .leftInv pi-high = refl
      i .rightInv nothing = refl
      i .rightInv (just nothing) = refl
      i .rightInv (just (just idx)) = refl

instance
  FinSetStr-PartitionIndex : {n : Nat} -> FinSetStr (PartitionIndex n)
  FinSetStr-PartitionIndex .FinSetStr.isFin = ∣ _ , PartitionIndex≃Fin ∣

private
  abstract
    PartitionBoundary≃Fin : {n : Nat} -> PartitionBoundary n ≃ Fin (suc (suc (suc n)))
    PartitionBoundary≃Fin {n} =
      (isoToEquiv i) >eq> (Maybe-eq (equiv⁻¹ (Fin-Maybe-eq _))) >eq> (equiv⁻¹ (Fin-Maybe-eq _))
      where
      open Iso
      i : Iso (PartitionBoundary n) (Maybe (Maybe (Fin (suc n))))
      i .fun pb-low = nothing
      i .fun (pb-mid idx) = (just (just idx))
      i .fun pb-high = (just nothing)
      i .inv nothing = pb-low
      i .inv (just nothing) = pb-high
      i .inv (just (just idx)) = pb-mid idx
      i .leftInv pb-low = refl
      i .leftInv (pb-mid idx) = refl
      i .leftInv pb-high = refl
      i .rightInv nothing = refl
      i .rightInv (just nothing) = refl
      i .rightInv (just (just idx)) = refl

FinSet-PartitionBoundary : (n : Nat) -> FinSet ℓ-zero
FinSet-PartitionBoundary n = (PartitionBoundary n) , ∣ _ , PartitionBoundary≃Fin ∣

FinSet-ΣLowPartitionBoundary : (n : Nat) -> FinSet ℓ-zero
FinSet-ΣLowPartitionBoundary n =
  FinSet-Detachable
    (FinSet-PartitionBoundary n)
    (\ pb -> LowPartitionBoundary pb , isProp-LowPartitionBoundary pb)
    Decidable-LowPartitionBoundary

FinSet-Σ¬LowPartitionBoundary : (n : Nat) -> FinSet ℓ-zero
FinSet-Σ¬LowPartitionBoundary n =
  FinSet-DetachableComp
    (FinSet-PartitionBoundary n)
    (\ pb -> LowPartitionBoundary pb , isProp-LowPartitionBoundary pb)
    Decidable-LowPartitionBoundary

FinSet-ΣHighPartitionBoundary : (n : Nat) -> FinSet ℓ-zero
FinSet-ΣHighPartitionBoundary n =
  FinSet-Detachable
    (FinSet-PartitionBoundary n)
    (\ pb -> HighPartitionBoundary pb , isProp-HighPartitionBoundary pb)
    Decidable-HighPartitionBoundary

FinSet-Σ¬HighPartitionBoundary : (n : Nat) -> FinSet ℓ-zero
FinSet-Σ¬HighPartitionBoundary n =
  FinSet-DetachableComp
    (FinSet-PartitionBoundary n)
    (\ pb -> HighPartitionBoundary pb , isProp-HighPartitionBoundary pb)
    Decidable-HighPartitionBoundary


instance
  FinSetStr-PartitionBoundary : {n : Nat} -> FinSetStr (PartitionBoundary n)
  FinSetStr-PartitionBoundary {n} .FinSetStr.isFin = snd (FinSet-PartitionBoundary n)

  FinSetStr-ΣLowPartitionBoundary :
    {n : Nat} -> FinSetStr (Σ (PartitionBoundary n) LowPartitionBoundary)
  FinSetStr-ΣLowPartitionBoundary {n} .FinSetStr.isFin = snd (FinSet-ΣLowPartitionBoundary n)

  FinSetStr-Σ¬LowPartitionBoundary :
    {n : Nat} -> FinSetStr (Σ (PartitionBoundary n) (Comp LowPartitionBoundary))
  FinSetStr-Σ¬LowPartitionBoundary {n} .FinSetStr.isFin = snd (FinSet-Σ¬LowPartitionBoundary n)

  FinSetStr-ΣHighPartitionBoundary :
    {n : Nat} -> FinSetStr (Σ (PartitionBoundary n) HighPartitionBoundary)
  FinSetStr-ΣHighPartitionBoundary {n} .FinSetStr.isFin = snd (FinSet-ΣHighPartitionBoundary n)

  FinSetStr-Σ¬HighPartitionBoundary :
    {n : Nat} -> FinSetStr (Σ (PartitionBoundary n) (Comp HighPartitionBoundary))
  FinSetStr-Σ¬HighPartitionBoundary {n} .FinSetStr.isFin = snd (FinSet-Σ¬HighPartitionBoundary n)
