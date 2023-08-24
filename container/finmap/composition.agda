{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module container.finmap.composition where

open import base
open import container.finmap
open import container.finmap.filter-map
open import equality
open import hlevel
open import maybe
open import relation

module _ {ℓV : Level} {V : Type ℓV}  where
  record FinMapComposition' (left right result : FinMap' V V) : Type ℓV where
    field
      forward : {v1 v2 v3 : V} -> HasKV' v1 v2 left -> HasKV' v2 v3 right -> HasKV' v1 v3 result
      backward : {v1 v3 : V} -> HasKV' v1 v3 result ->
                 Σ[ v2 ∈ V ] (HasKV' v1 v2 left × HasKV' v2 v3 right)

  open FinMapComposition'

  FinMapComposition'-empty-left :
    {m : FinMap' V V} -> FinMapComposition' [] m []
  FinMapComposition'-empty-left .forward ()
  FinMapComposition'-empty-left .backward ()

  FinMapComposition'-empty-right :
    {m : FinMap' V V} -> FinMapComposition' m [] []
  FinMapComposition'-empty-right .forward _ ()
  FinMapComposition'-empty-right .backward ()

  isInjectiveFinMap-FinMapComposition' : {m1 m2 m3 : FinMap' V V} ->
    isInjectiveFinMap' m1 ->
    isInjectiveFinMap' m2 ->
    FinMapComposition' m1 m2 m3 ->
    isInjectiveFinMap' m3
  isInjectiveFinMap-FinMapComposition' inj1 inj2 c hk1 hk2 =
    inj1 (fst (snd res1)) (subst (\v -> HasKV' _ v _) (sym p) (fst (snd res2)))
    where
    res1 = c .backward hk1
    res2 = c .backward hk2
    p = inj2 (snd (snd res1)) (snd (snd res2))

  isFunctionalFinMap-FinMapComposition' : {m1 m2 m3 : FinMap' V V} ->
    isFunctionalFinMap' m1 ->
    isFunctionalFinMap' m2 ->
    FinMapComposition' m1 m2 m3 ->
    isFunctionalFinMap' m3
  isFunctionalFinMap-FinMapComposition' fun1 fun2 c hk1 hk2 =
    fun2 (snd (snd res1)) (subst (\k -> HasKV' k _ _) (sym p) (snd (snd res2)))
    where
    res1 = c .backward hk1
    res2 = c .backward hk2
    p = fun1 (fst (snd res1)) (fst (snd res2))

  isBijectiveFinMap-FinMapComposition' : {m1 m2 m3 : FinMap' V V} ->
    isBijectiveFinMap' m1 ->
    isBijectiveFinMap' m2 ->
    FinMapComposition' m1 m2 m3 ->
    isBijectiveFinMap' m3
  isBijectiveFinMap-FinMapComposition' (inj1 , fun1) (inj2 , fun2) c =
    isInjectiveFinMap-FinMapComposition' inj1 inj2 c ,
    isFunctionalFinMap-FinMapComposition' fun1 fun2 c

module _ {ℓV : Level} {V : Type ℓV} {{disc'V : Discrete' V}} where
  private
    discV = Discrete'.f disc'V
    isSetV = Discrete->isSet discV

  private
    f : (v1 v2 v3 v4 : V) -> Maybe (V × V)
    f v1 v2 v3 v4 = case (discV v2 v3) of (\{
      (yes _) -> just (v1 , v4) ;
      (no _) -> nothing })

    f-refl : (v1 v23 v4 : V) -> f v1 v23 v23 v4 == just (v1 , v4)
    f-refl v1 v23 v4 with (discV v23 v23)
    ... | (yes _) = refl
    ... | (no ¬v23) = bot-elim (¬v23 refl)

    f-backward : (v1 v2 v3 v4 v5 v6 : V) -> f v1 v2 v3 v4 == just (v5 , v6) ->
                 v1 == v5 × v2 == v3 × v4 == v6
    f-backward v1 v2 v3 v4 v5 v6 p with (discV v2 v3)
    ... | (yes p23) = cong fst (just-injective p) , p23 , cong snd (just-injective p)
    ... | (no _) = bot-elim (just!=nothing (sym p))


  pre-compose-once-finmap' : (v1 v2 : V) -> FinMap' V V -> FinMap' V V
  pre-compose-once-finmap' v1 v2 = finmap'-filter-map (f v1 v2)

  finmap'-compose : FinMap' V V -> FinMap' V V -> FinMap' V V
  finmap'-compose [] m = []
  finmap'-compose (fm-cons v1 v2 m) m2 =
    fm'-union (pre-compose-once-finmap' v1 v2 m2)
              (finmap'-compose m m2)


  HasKey-pre-compose-once-finmap' : {v1 v2 v3 : V} {m : FinMap' V V} ->
    HasKV' v2 v3 m -> HasKV' v1 v3 (pre-compose-once-finmap' v1 v2 m)
  HasKey-pre-compose-once-finmap' {v1} {v2} {v3} {m} hkv =
    HasKey-finmap'-filter-map (f v1 v2) (v2 , v3 , hkv , f-refl v1 v2 v3)



  HasKey-finmap'-compose-forward :
    {v1 v2 v3 : V} {m1 m2 : FinMap' V V} ->
    HasKV' v1 v2 m1 -> HasKV' v2 v3 m2 -> HasKV' v1 v3 (finmap'-compose m1 m2)
  HasKey-finmap'-compose-forward {v1} {v2} {v3} {fm-cons k v m} {m2} (has-kv-skip _ _ hkv1) hkv2 =
    HasKV-fm'-union/right (HasKey-finmap'-compose-forward hkv1 hkv2)
  HasKey-finmap'-compose-forward {v1} {v2} {v3} {fm-cons k v m} {m2} (has-kv-here kp vp _) hkv2 =
    HasKV-fm'-union/left (subst2 (\ik iv -> HasKV' v1 v3 (pre-compose-once-finmap' ik iv m2))
                                 kp vp
                                 (HasKey-pre-compose-once-finmap' hkv2))

  HasKey-pre-compose-once-finmap'-backward : {v1 v1' v2 v3 : V} {m : FinMap' V V} ->
    HasKV' v1 v3 (pre-compose-once-finmap' v1' v2 m) -> (v1 == v1' × HasKV' v2 v3 m)
  HasKey-pre-compose-once-finmap'-backward {v1} {v1'} {v2} {v3} {m} hkv =
    sym (fst paths) ,
    subst2 (\k v -> HasKV' k v m) (sym (fst (snd paths))) (snd (snd paths)) (fst (snd (snd res)))

    where
    res : Σ[ v4 ∈ V ] Σ[ v5 ∈ V ] (HasKV' v4 v5 m × (f v1' v2 v4 v5 == just (v1 , v3)))
    res = HasKey-finmap'-filter-map-backward (f v1' v2) hkv
    paths = f-backward _ _ _ _ _ _ (snd (snd (snd res)))



  HasKey-finmap'-compose-backward :
    {v1 v3 : V} {m1 m2 : FinMap' V V} ->
    HasKV' v1 v3 (finmap'-compose m1 m2) -> Σ[ v2 ∈ V ] (HasKV' v1 v2 m1 × HasKV' v2 v3 m2)
  HasKey-finmap'-compose-backward {v1} {v3} m1@{fm-cons k v m1'} {m2} hkv =
    handle (discV v1 k)
           (HasKV-fm'-union/split (pre-compose-once-finmap' k v m2) (finmap'-compose m1' m2) hkv)
    where
    handle : Dec (v1 == k) ->
             (HasKV' v1 v3 (pre-compose-once-finmap' k v m2) ⊎
              HasKV' v1 v3 (finmap'-compose m1' m2)) ->
             Σ[ v2 ∈ V ] (HasKV' v1 v2 m1 × HasKV' v2 v3 m2)
    handle _ (inj-r hkv) =
      case (HasKey-finmap'-compose-backward hkv) of (\{ (k2 , l , r) -> (k2 , has-kv-skip _ _ l , r) })
    handle _ (inj-l hkv) =
      handle2 (HasKey-pre-compose-once-finmap'-backward hkv)
      where
      handle2 : (v1 == k × HasKV' v v3 m2) ->
                Σ[ v2 ∈ V ] (HasKV' v1 v2 m1 × HasKV' v2 v3 m2)
      handle2 (kp , hkv) = v , has-kv-here kp refl m1' , hkv


  FinMapComposition'-finmap-compose' :
    {m1 m2 : FinMap' V V} -> FinMapComposition' m1 m2 (finmap'-compose m1 m2)
  FinMapComposition'-finmap-compose' .FinMapComposition'.forward =
    HasKey-finmap'-compose-forward
  FinMapComposition'-finmap-compose' .FinMapComposition'.backward =
    HasKey-finmap'-compose-backward
