{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-set where

open import base
open import univalence
open import equality-path
open import cubical
open import hlevel
open import equivalence
open import funext
open import order
open import order.homomorphism
open import isomorphism

LOSet : (ℓD ℓ< : Level) -> Type (ℓ-max (ℓ-suc ℓ<) (ℓ-suc ℓD))
LOSet ℓD ℓ< = Σ[ D ∈ Type ℓD ] (LinearOrderStr D ℓ<)

LOSet≃ : {ℓA ℓB ℓC ℓD : Level} -> LOSet ℓA ℓB -> LOSet ℓC ℓD -> Type _
LOSet≃ (A , OA) (B , OB) =
  Σ[ e ∈ (A ≃ B) ] (LinearOrderʰ (eqFun e) × LinearOrderʰ (eqInv e))
  where
  instance
    I-OA = LinearOrderStr.isLinearOrder-< OA
    I-OB = LinearOrderStr.isLinearOrder-< OB


module _ {ℓD ℓ< : Level} {S : LOSet ℓD ℓ<} {T : LOSet ℓD ℓ<} where
  private
    instance
      I-OS = LinearOrderStr.isLinearOrder-< (snd S)
      I-OT = LinearOrderStr.isLinearOrder-< (snd T)
    S' = ⟨ S ⟩
    T' = ⟨ T ⟩

  LOSet≃->paths : (LOSet≃ S T) -> Σ[ p ∈ (⟨ S ⟩ == ⟨ T ⟩) ]
                                    (PathP (\i -> p i -> p i -> Type ℓ<) _<_ _<_)
  LOSet≃->paths (e , (fh , bh)) = ua e , transP-right <-same <-transport
    where
    f = eqFun e

    f-id : PathP (\i -> ua e i -> T') f (idfun T')
    f-id = transP-mid
             (sym (transport-ua e))
             (\i s -> transport (\j -> ua e (i ∨ j)) s)
             (\i s -> transportRefl s i)

    <-transport : PathP (\i -> ua e i -> ua e i -> Type ℓ<) (\i j -> f i < f j) _<_
    <-transport k i j = f-id k i < f-id k j

    <-same : Path (S' -> S' -> Type ℓ<) _<_ (\i j -> f i < f j)
    <-same =
      funExt (\s1 -> funExt (\s2 -> ua (isoToEquiv (isProp->iso forward backward isProp-< isProp-<))))
      where
      forward : {s1 s2 : S'} -> s1 < s2 -> f s1 < f s2
      forward = LinearOrderʰ.preserves-< fh
      backward : {s1 s2 : S'} -> f s1 < f s2 -> s1 < s2
      backward f< =
        subst2 _<_ (eqRet e _) (eqRet e _) (LinearOrderʰ.preserves-< bh f<)


LOSet≃->path : {ℓD ℓ< : Level} {S : LOSet ℓD ℓ<} {T : LOSet ℓD ℓ<} -> (LOSet≃ S T) -> S == T
LOSet≃->path {S = S@(S' , S-str@(record {}))} {T = T@(T' , T-str@(record {}))} e = \i -> fst paths i , O-path i
  where
  paths = LOSet≃->paths {S = S} {T = T} e

  O-path : PathP (\i -> LinearOrderStr (fst paths i) _) S-str T-str
  O-path i = record
    { _<_ = snd paths i
    ; isLinearOrder-< = isProp->PathPᵉ (\i -> isProp-isLinearOrder (snd paths i))
                          (LinearOrderStr.isLinearOrder-< S-str)
                          (LinearOrderStr.isLinearOrder-< T-str)
                          i
    }



POSet : (ℓD ℓ< : Level) -> Type (ℓ-max (ℓ-suc ℓ<) (ℓ-suc ℓD))
POSet ℓD ℓ< = Σ[ D ∈ Type ℓD ] (PartialOrderStr D ℓ<)

POSet≃ : {ℓA ℓB ℓC ℓD : Level} -> POSet ℓA ℓB -> POSet ℓC ℓD -> Type _
POSet≃ (A , OA) (B , OB) =
  Σ[ e ∈ (A ≃ B) ] (PartialOrderʰ (eqFun e) × PartialOrderʰ (eqInv e))
  where
  instance
    I-OA = OA
    I-OB = OB

module _ {ℓD ℓ≤ : Level} {S : POSet ℓD ℓ≤} {T : POSet ℓD ℓ≤} where
  private
    instance
      I-OS = PartialOrderStr.isPartialOrder-≤ (snd S)
      I-OT = PartialOrderStr.isPartialOrder-≤ (snd T)
    S' = ⟨ S ⟩
    T' = ⟨ T ⟩

  POSet≃->paths : (POSet≃ S T) -> Σ[ p ∈ (⟨ S ⟩ == ⟨ T ⟩) ]
                                    (PathP (\i -> p i -> p i -> Type ℓ≤) _≤_ _≤_)
  POSet≃->paths (e , (fh , bh)) = ua e , transP-right ≤-same ≤-transport
    where
    f = eqFun e

    f-id : PathP (\i -> ua e i -> T') f (idfun T')
    f-id = transP-mid
             (sym (transport-ua e))
             (\i s -> transport (\j -> ua e (i ∨ j)) s)
             (\i s -> transportRefl s i)

    ≤-transport : PathP (\i -> ua e i -> ua e i -> Type ℓ≤) (\i j -> f i ≤ f j) _≤_
    ≤-transport k i j = f-id k i ≤ f-id k j

    ≤-same : Path (S' -> S' -> Type ℓ≤) _≤_ (\i j -> f i ≤ f j)
    ≤-same =
      funExt (\s1 -> funExt (\s2 -> ua (isoToEquiv (isProp->iso forward backward isProp-≤ isProp-≤))))
      where
      forward : {s1 s2 : S'} -> s1 ≤ s2 -> f s1 ≤ f s2
      forward = PartialOrderʰ.preserves-≤ fh
      backward : {s1 s2 : S'} -> f s1 ≤ f s2 -> s1 ≤ s2
      backward f≤ =
        subst2 _≤_ (eqRet e _) (eqRet e _) (PartialOrderʰ.preserves-≤ bh f≤)

POSet≃->path : {ℓD ℓ≤ : Level} {S : POSet ℓD ℓ≤} {T : POSet ℓD ℓ≤} -> (POSet≃ S T) -> S == T
POSet≃->path {S = (_ , S-str@(record {}))} {T = (_ , T-str@(record {}))} e = \i -> fst paths i , O-path i
  where
  paths = POSet≃->paths e

  O-path : PathP (\i -> PartialOrderStr (fst paths i) _) S-str T-str
  O-path i = record
    { _≤_ = snd paths i
    ; isPartialOrder-≤ = isProp->PathPᵉ (\i -> isProp-isPartialOrder (snd paths i))
                           (PartialOrderStr.isPartialOrder-≤ S-str)
                           (PartialOrderStr.isPartialOrder-≤ T-str)
                           i
    }
