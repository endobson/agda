{-# OPTIONS --cubical --safe --exact-split #-}

module subset where

open import apartness
open import base
open import equality
open import equivalence
open import fin
open import finset
open import finset.instances.boolean
open import functions
open import funext
open import hlevel
open import isomorphism
open import relation
open import sigma.base
open import truncation
open import univalence

-- A subtype of the type D
Subtype : {ℓD : Level} -> (D : Type ℓD) -> (ℓP : Level) -> Type (ℓ-max ℓD (ℓ-suc ℓP))
Subtype D ℓP = (D -> hProp ℓP)

module _ {ℓD ℓS : Level} {D : Type ℓD} (S : Subtype D ℓS) where
  ∈-Subtype : Type (ℓ-max ℓD ℓS)
  ∈-Subtype = Σ[ d ∈ D ] ⟨ S d ⟩

  ∉-Subtype : Type (ℓ-max ℓD ℓS)
  ∉-Subtype = Σ[ d ∈ D ] (¬ ⟨ S d ⟩)

  isSingletonSubtype : Type (ℓ-max ℓD ℓS)
  isSingletonSubtype = isContr ∈-Subtype

  isFiniteSubtype : Type (ℓ-max ℓD ℓS)
  isFiniteSubtype = isFinSet ∈-Subtype

  ∈-Subtype-ext : {e1 e2 : ∈-Subtype} -> ⟨ e1 ⟩ == ⟨ e2 ⟩ -> e1 == e2
  ∈-Subtype-ext p = ΣProp-path (\{d} -> (snd (S d))) p

  isFullSubtype : Type (ℓ-max ℓD ℓS)
  isFullSubtype = ∀ (d : D) -> ⟨ S d ⟩

UnivS : {ℓD : Level} -> (D : Type ℓD) -> Subtype D ℓ-zero
UnivS D _ = Top , isPropTop

UnivS' : {ℓD : Level} -> (D : Type ℓD) (ℓS : Level) -> Subtype D ℓS
UnivS' D ℓS _ = Lift ℓS Top , isProp-Lift isPropTop


module _ {ℓD ℓ# ℓS : Level} {D : Type ℓD} {#D : Rel D ℓ#} {{AD : isTightApartness #D}}
         (S : Subtype D ℓS) where
  isOpenSubtype : Type (ℓ-max* 3 ℓD ℓ# ℓS)
  isOpenSubtype = ∀ {d1 : D} -> ⟨ S d1 ⟩ -> (d2 : D) -> (⟨ S d2 ⟩ ⊎ (d1 # d2))

abstract
  isSet-Subtype : {ℓD ℓP : Level} {D : Type ℓD} -> isSet (Subtype D ℓP)
  isSet-Subtype = isSetΠ (\_ -> isSet-hProp)

-- Family of Ds indexed by I
Family : {ℓD ℓI : Level} -> Type ℓD -> Type ℓI -> Type (ℓ-max ℓD ℓI)
Family D I = I -> D

Family->Subtype : {ℓD ℓI : Level} -> {D : Type ℓD} -> {I : Type ℓI} ->
                   Family D I -> Subtype D (ℓ-max ℓD ℓI)
Family->Subtype {I = I} f d = (∃[ i ∈ I ] (f i == d)) , squash



-- A FinSubset is a finite amount of Ds
FinSubset : {ℓD : Level} (D : Type ℓD) (ℓI : Level) -> Type (ℓ-max ℓD (ℓ-suc ℓI))
FinSubset D ℓI = Σ[ I ∈ (FinSet ℓI) ] Σ[ f ∈ (⟨ I ⟩ -> D) ] (Injective f)

-- A Detachable subtype is a subtype for which membership is decidable
Detachable : {ℓD ℓ : Level} {D : Type ℓD} -> Subtype D ℓ -> Type (ℓ-max ℓD ℓ)
Detachable P = Decidable (fst ∘ P)


-- Partitions

FinitePartition : {ℓD  : Level} -> (D : Type ℓD) -> (ℓS ℓP : Level) -> Type _
FinitePartition D ℓS ℓP =
  Σ[ S ∈ FinSet ℓS ] Σ[ f ∈ (⟨ S ⟩ -> Subtype D ℓP) ]
    ((d : D) -> isContr (Σ[ s ∈ ⟨ S ⟩ ] ⟨ f s d ⟩))

BinaryPartition : {ℓD  : Level} -> (D : Type ℓD) -> (ℓS ℓP : Level) -> Type _
BinaryPartition D ℓS ℓP =
  Σ[ fp ∈ FinitePartition D ℓS ℓP ] (⟨ ⟨ fp ⟩ ⟩ ≃ Boolean)


-- Complement of subtypes
Subtype-Comp : {ℓD ℓP : Level} -> {D : Type ℓD} -> Subtype D ℓP -> Subtype D ℓP
Subtype-Comp S d = (¬ ⟨ S d ⟩) , isProp¬ _

Detachable-Comp : {ℓD ℓP : Level} -> {D : Type ℓD} -> (S : Subtype D ℓP) ->
                  (Detachable S) -> (Detachable (Subtype-Comp S))
Detachable-Comp S decide-S d = comp-dec (decide-S d)

-- Equivalence
Detachable-eq : {ℓD ℓP : Level} -> {D : Type ℓD} -> (S : Subtype D ℓP) -> (Detachable S) ->
                D ≃ ((∈-Subtype S) ⊎ (∉-Subtype S))
Detachable-eq {D = D} S decide = isoToEquiv i
  where
  split : {d : D} -> Dec ⟨ S d ⟩ -> ((∈-Subtype S) ⊎ (∉-Subtype S))
  split {d} (yes s) = inj-l (d , s)
  split {d} (no ¬s) = inj-r (d , ¬s)

  open Iso
  i : Iso D ((∈-Subtype S) ⊎ (∉-Subtype S))
  i .fun d = split (decide d)
  i .inv (inj-l (d , s)) = d
  i .inv (inj-r (d , s)) = d

  i .leftInv d = path (decide d)
    where
    path : (dec : (Dec ⟨ S d ⟩)) -> i .inv (split dec) == d
    path (yes _) = refl
    path (no _) = refl

  i .rightInv (inj-l (d , s)) = cong split path
    where
    path : decide d == yes s
    path = isPropDec (snd (S d)) _ _
  i .rightInv (inj-r (d , ¬s)) = cong split path
    where
    path : decide d == no ¬s
    path = isPropDec (snd (S d)) _ _

-- Same Subtypes
abstract
  same-Subtype : {ℓD ℓP : Level} -> {D : Type ℓD} -> {S1 S2 : Subtype D ℓP} ->
                 ({d : D} -> ⟨ S1 d ⟩ -> ⟨ S2 d ⟩) ->
                 ({d : D} -> ⟨ S2 d ⟩ -> ⟨ S1 d ⟩) ->
                 S1 == S2
  same-Subtype {D = D} {S1} {S2} forward backward = funExt proof
    where
    proof : (d : D) -> S1 d == S2 d
    proof d = ΣProp-path isProp-isProp (ua (isoToEquiv i))
      where
      i : Iso ⟨ S1 d ⟩ ⟨ S2 d ⟩
      i = isProp->iso forward backward (snd (S1 d)) (snd (S2 d))

-- Partition construction
module _ {ℓB ℓP : Level} {B : Type ℓB} (P : Subtype B ℓP) (decide : Detachable P) where

  Detachable->Partition : FinitePartition B ℓ-zero ℓP
  Detachable->Partition = (FinSet-Boolean , sub , isContr-Part)
    where
    sub : Boolean -> Subtype B ℓP
    sub true = P
    sub false = Subtype-Comp P

    isContr-Part : (b : B) -> isContr (Σ[ i ∈ Boolean ] ⟨ sub i b ⟩)
    isContr-Part b = handle (decide b)
      where
      unique-sub : (i1 i2 : Boolean) -> ⟨ sub i1 b ⟩ -> ⟨ sub i2 b ⟩ -> i1 == i2
      unique-sub true true   _   _   = refl
      unique-sub true  false pb  ¬pb = bot-elim (¬pb pb)
      unique-sub false true  ¬pb pb  = bot-elim (¬pb pb)
      unique-sub false false _   _   = refl

      isProp-Σsub : isProp (Σ[ i ∈ Boolean ] ⟨ sub i b ⟩)
      isProp-Σsub v1 v2 = ΣProp-path (\{i} -> snd (sub i b)) (unique-sub _ _ (snd v1) (snd v2))

      handle : Dec ⟨ P b ⟩ -> isContr (Σ[ i ∈ Boolean ] ⟨ sub i b ⟩)
      handle (yes pb) = (true , pb) , isProp-Σsub _
      handle (no ¬pb) = (false , ¬pb) , isProp-Σsub _

  Detachable->BinaryPartition : BinaryPartition B ℓ-zero ℓP
  Detachable->BinaryPartition = Detachable->Partition , idEquiv _
