{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap where

open import base
open import fin
open import functions
open import nat
open import hlevel
open import relation
open import equality
open import sigma.base
open import sum
open import univalence
open import isomorphism
open import truncation
open import set-quotient

private
  variable
    ℓ : Level
    A B C D : Type ℓ


data FinMap' {ℓK ℓV : Level} (K : Type ℓK) (V : Type ℓV) : Type (ℓ-max ℓK ℓV) where
  [] : FinMap' K V
  fm-cons : K -> V -> FinMap' K V -> FinMap' K V

data HasKV' {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} (k : K) (v : V) : 
  (FinMap' K V) -> Type (ℓ-max ℓK ℓV) where
  has-kv-here : {k2 : K} {v2 : V} -> k == k2 -> v == v2 ->
                (m : FinMap' K V) -> HasKV' k v (fm-cons k2 v2 m)
  has-kv-skip : {m : FinMap' K V} -> (k2 : K) (v2 : V) ->
                HasKV' k v m -> HasKV' k v (fm-cons k2 v2 m)

fm'-rest : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> FinMap' K V -> FinMap' K V
fm'-rest [] = []
fm'-rest (fm-cons _ _ m) = m


HasKey' : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> REL K (FinMap' K V) (ℓ-max ℓK ℓV)
HasKey' {V = V} k m = Σ[ v ∈ V ] HasKV' k v m

HasKey'-skip : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} {k1 k2 : K} {v : V} {m : FinMap' K V} ->
               HasKey' k1 m -> HasKey' k1 (fm-cons k2 v m)
HasKey'-skip (v , hkv) = v , (has-kv-skip _ _ hkv)


fm'-value-map : {ℓK ℓV ℓV2 : Level} {K : Type ℓK} {V : Type ℓV} {V2 : Type ℓV2} -> 
                (K -> V -> V2) -> FinMap' K V -> FinMap' K V2
fm'-value-map f [] = []
fm'-value-map f (fm-cons k v m) = fm-cons k (f k v) (fm'-value-map f m)

fm'-value-map/HasKV : {ℓK ℓV ℓV2 : Level} {K : Type ℓK} {V : Type ℓV} {V2 : Type ℓV2}
                      (f : K -> V -> V2) -> {k : K} {v : V} {m : FinMap' K V} ->
                      HasKV' k v m -> HasKV' k (f k v) (fm'-value-map f m)
fm'-value-map/HasKV f (has-kv-here kp vp m) = has-kv-here kp (cong2 f kp vp) _
fm'-value-map/HasKV f (has-kv-skip k v hkv) = 
  has-kv-skip k (f k v) (fm'-value-map/HasKV f hkv)
                    

fm'-value-map/HasKV' : {ℓK ℓV ℓV2 : Level} {K : Type ℓK} {V : Type ℓV} {V2 : Type ℓV2}
                       (f : K -> V -> V2) -> {k : K} {v2 : V2} {m : FinMap' K V} ->
                       HasKV' k v2 (fm'-value-map f m) -> 
                       Σ[ v ∈ V ] (f k v == v2 × HasKV' k v m)
fm'-value-map/HasKV' f {m = (fm-cons k v m)} (has-kv-here kp vp _) = 
  v , cong2 f kp refl >=> sym vp , has-kv-here kp refl _
fm'-value-map/HasKV' f {m = (fm-cons k v m)} (has-kv-skip _ _ hkv) = 
  case (fm'-value-map/HasKV' f hkv) of (\{ (v , p , hkv) -> v , p , has-kv-skip _ _ hkv})


fm'-keys : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> FinMap' K V -> FinMap' K Top 
fm'-keys = fm'-value-map (\_ _ -> tt)

fm'-keys/HasKey : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                  {k : K} {m : FinMap' K V} -> HasKey' k m -> HasKey' k (fm'-keys m)
fm'-keys/HasKey (v , has-kv-here kp _ m) = (tt , has-kv-here kp refl (fm'-keys m))
fm'-keys/HasKey (v , has-kv-skip _ _ m) = 
  case (fm'-keys/HasKey (v , m)) of \{ (v , hkv) -> v , has-kv-skip _ _ hkv }

fm'-keys/HasKV' : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                  {k : K} {m : FinMap' K V} -> HasKV' k tt (fm'-keys m) ->
                  Σ[ v ∈ V ] (HasKV' k v m)
fm'-keys/HasKV' hkv = 
  case (fm'-value-map/HasKV' _ hkv) of (\{(v , _ , hkv) -> v , hkv})


DisjointKeys' : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> Rel (FinMap' K V) (ℓ-max ℓK ℓV)
DisjointKeys'  m1 m2 = ∀ {k} -> HasKey' k m1 -> HasKey' k m2 -> Bot

data HasUniqueKeys {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} : 
  Pred (FinMap' K V) (ℓ-max ℓK ℓV) where
  [] : HasUniqueKeys []
  fm-cons : {k : K} {m : FinMap' K V} -> ¬ (HasKey' k m) -> (v : V) -> 
            HasUniqueKeys m -> HasUniqueKeys (fm-cons k v m)

FinMap : {ℓK ℓV : Level} (K : Type ℓK) (V : Type ℓV) -> Type (ℓ-max ℓK ℓV)
FinMap K V = Σ (FinMap' K V) HasUniqueKeys


HasKV : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} ->
        K -> V -> (FinMap K V) -> Type (ℓ-max ℓK ℓV)
HasKV k v (m , _) = HasKV' k v m

HasKey : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> REL K (FinMap K V) (ℓ-max ℓK ℓV)
HasKey k (m , _) = HasKey' k m

DisjointKeys : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> Rel (FinMap K V) (ℓ-max ℓK ℓV)
DisjointKeys m1 m2 = ∀ {k} -> HasKey k m1 -> HasKey k m2 -> Bot


fm'-union : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
            (FinMap' K V) -> (FinMap' K V) -> (FinMap' K V)
fm'-union [] m = m
fm'-union (fm-cons k v m) m2 = fm-cons k v (fm'-union m m2)

module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} where

  HasKV-fm'-union/split :
    {k : K} {v : V} (fm1 fm2 : FinMap' K V) -> 
    HasKV' k v (fm'-union fm1 fm2) -> (HasKV' k v fm1) ⊎ (HasKV' k v fm2)
  HasKV-fm'-union/split [] _ hk = inj-r hk
  HasKV-fm'-union/split {k} (fm-cons _ _ fm1) fm2 (has-kv-here kp vp _) =
    inj-l (has-kv-here kp vp fm1)
  HasKV-fm'-union/split {k} (fm-cons _ _ fm1) fm2 (has-kv-skip _ _ hkv) = 
    case (HasKV-fm'-union/split fm1 fm2 hkv) of \{
      (inj-l hkv) -> inj-l (has-kv-skip _ _ hkv) ;
      (inj-r hkv) -> inj-r hkv }

  HasKey-fm'-union/split :
    {k : K} (fm1 fm2 : FinMap' K V) -> 
    HasKey' k (fm'-union fm1 fm2) -> (HasKey' k fm1) ⊎ (HasKey' k fm2)
  HasKey-fm'-union/split {k} fm1 fm2 (v , hkv) = 
    case (HasKV-fm'-union/split fm1 fm2 hkv) of \{
      (inj-l hkv) -> inj-l (v , hkv) ;
      (inj-r hkv) -> inj-r (v , hkv) }

  DisjointKeys-fm'-union :
    {fm1 fm2 fm3 : FinMap' K V} -> 
    DisjointKeys' fm1 fm2 -> DisjointKeys' fm1 fm3 -> DisjointKeys' fm1 (fm'-union fm2 fm3)
  DisjointKeys-fm'-union dis12 dis13 hk1 hk23 = 
    either (dis12 hk1) (dis13 hk1) (HasKey-fm'-union/split _ _ hk23)

  HasKV-fm'-union/left :
    {k : K} {v : V} {fm1 fm2 : FinMap' K V} -> 
    HasKV' k v fm1 -> HasKV' k v (fm'-union fm1 fm2)
  HasKV-fm'-union/left (has-kv-here kp vp _) = has-kv-here kp vp _
  HasKV-fm'-union/left (has-kv-skip k v hk) =
    has-kv-skip k v (HasKV-fm'-union/left hk)

  HasKV-fm'-union/right :
    {k : K} {v : V} {fm1 fm2 : FinMap' K V} -> 
    HasKV' k v fm2 -> HasKV' k v (fm'-union fm1 fm2)
  HasKV-fm'-union/right {fm1 = []} hk = hk
  HasKV-fm'-union/right {fm1 = (fm-cons k v m)} hk =
    has-kv-skip k v (HasKV-fm'-union/right hk)


isInjectiveFinMap' : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                     Pred (FinMap' K V) (ℓ-max ℓK ℓV)
isInjectiveFinMap' m = ∀ {k1 k2 v} -> HasKV' k1 v m -> HasKV' k2 v m -> k1 == k2

isFunctionalFinMap' : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                      Pred (FinMap' K V) (ℓ-max ℓK ℓV)
isFunctionalFinMap' m = ∀ {k v1 v2} -> HasKV' k v1 m -> HasKV' k v2 m -> v1 == v2

isBijectiveFinMap' : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                     Pred (FinMap' K V) (ℓ-max ℓK ℓV)
isBijectiveFinMap' = isInjectiveFinMap' ∩ isFunctionalFinMap'

isInjectiveFinMap'-rest : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                          (m : FinMap' K V) -> isInjectiveFinMap' m -> 
                          isInjectiveFinMap' (fm'-rest m)
isInjectiveFinMap'-rest [] f = f
isInjectiveFinMap'-rest (fm-cons k v m) f hkv1 hkv2 = f (has-kv-skip k v hkv1) (has-kv-skip k v hkv2)

isFunctionalFinMap'-rest : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                           (m : FinMap' K V) -> isFunctionalFinMap' m -> 
                           isFunctionalFinMap' (fm'-rest m)
isFunctionalFinMap'-rest [] f = f
isFunctionalFinMap'-rest (fm-cons k v m) f hkv1 hkv2 = f (has-kv-skip k v hkv1) (has-kv-skip k v hkv2)

isBijectiveFinMap'-rest : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                          (m : FinMap' K V) -> isBijectiveFinMap' m -> 
                          isBijectiveFinMap' (fm'-rest m)
isBijectiveFinMap'-rest m (inj , fun) = isInjectiveFinMap'-rest m inj , isFunctionalFinMap'-rest m fun

abstract
  isBijectiveFinMap'-single : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                              (k : K) (v : V) -> isBijectiveFinMap' (fm-cons k v [])
  isBijectiveFinMap'-single k v = inj , fun
    where
    inj : isInjectiveFinMap' (fm-cons k v [])
    inj (has-kv-here kp1 _ _) (has-kv-here kp2 _ _) = kp1 >=> sym kp2
    fun : isFunctionalFinMap' (fm-cons k v [])
    fun (has-kv-here _ vp1 _) (has-kv-here _ vp2 _) = vp1 >=> sym vp2

isBijectiveFinMap'-[] : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                        isBijectiveFinMap' {K = K} {V = V} []
isBijectiveFinMap'-[] = inj , fun
  where
  inj : isInjectiveFinMap' []
  inj ()
  fun : isFunctionalFinMap' []
  fun ()

fm'-invert : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
             (FinMap' K V) -> (FinMap' V K) 
fm'-invert [] = []
fm'-invert (fm-cons k v m) = fm-cons v k (fm'-invert m)

fm'-invert/Involution : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                        (m : FinMap' K V) -> (fm'-invert (fm'-invert m)) == m
fm'-invert/Involution [] = refl
fm'-invert/Involution (fm-cons k v m) = cong (fm-cons k v) (fm'-invert/Involution m)

fm'-invert/HasKV : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                   {k : K} {v : V} {m : FinMap' K V} -> HasKV' k v m -> 
                   HasKV' v k (fm'-invert m)
fm'-invert/HasKV (has-kv-here kp vp m) = has-kv-here vp kp (fm'-invert m)
fm'-invert/HasKV (has-kv-skip k v hkv) = has-kv-skip v k (fm'-invert/HasKV hkv)
                    

fm'-invert/unique-keys : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                         (m : FinMap' K V) -> HasUniqueKeys m -> isInjectiveFinMap' (fm'-invert m)
fm'-invert/unique-keys [] _ () 
fm'-invert/unique-keys (fm-cons k1 v1 m) (fm-cons ¬hk _ huk) 
                       (has-kv-here v2p k2p _) (has-kv-here v3p k3p _) = v2p >=> sym v3p
fm'-invert/unique-keys (fm-cons k1 v1 m) (fm-cons ¬hk _ huk) 
                       {v2} {v3} {k} (has-kv-here v2p kp _) (has-kv-skip _ _ hkv) =
                       bot-elim (¬hk (v3 , swapped-hkv))
  where
  swapped-hkv : HasKV' k1 v3 m
  swapped-hkv = subst2 (\k m -> HasKV' k v3 m) kp (fm'-invert/Involution m) (fm'-invert/HasKV hkv)
fm'-invert/unique-keys (fm-cons k1 v1 m) (fm-cons ¬hk _ huk) 
                       {v2} {v3} {k} (has-kv-skip _ _ hkv) (has-kv-here v3p kp _) =
                       bot-elim (¬hk (v2 , swapped-hkv))
  where
  swapped-hkv : HasKV' k1 v2 m
  swapped-hkv = subst2 (\k m -> HasKV' k v2 m) kp (fm'-invert/Involution m) (fm'-invert/HasKV hkv)

fm'-invert/unique-keys (fm-cons k1 v1 m) (fm-cons ¬hk _ huk) 
                       (has-kv-skip _ _ hkv1) (has-kv-skip _ _ hkv2) =
  fm'-invert/unique-keys m huk hkv1 hkv2
  

fm'-invert/injective : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                       (m : FinMap' K V) -> isInjectiveFinMap' m -> 
                       isFunctionalFinMap' (fm'-invert m)
fm'-invert/injective [] _ ()
fm'-invert/injective (fm-cons k1 v1 m) _
                     (has-kv-here k2p v2p _) (has-kv-here k3p v3p _) = v2p >=> sym v3p
fm'-invert/injective (fm-cons k v m) inj
                     (has-kv-skip _ _ hkv1) (has-kv-skip _ _ hkv2) = rec hkv1 hkv2
  where
  inj' : isInjectiveFinMap' m
  inj' hkv1 hkv2 = inj (has-kv-skip k v hkv1) (has-kv-skip k v hkv2)
  rec : isFunctionalFinMap' (fm'-invert m)
  rec = fm'-invert/injective m inj'

fm'-invert/injective (fm-cons k1 v1 m) inj
                     {v} {k2} {k3} hkv2@(has-kv-here vp _ _) hkv3@(has-kv-skip _ _ _) = 
                     inj swapped-hkv2 swapped-hkv3
  where
  swapped-hkv2 : HasKV' k2 v1 (fm-cons k1 v1 m)
  swapped-hkv2 = subst2 (\v m -> HasKV' k2 v (fm-cons k1 v1 m)) vp (fm'-invert/Involution m) (fm'-invert/HasKV hkv2)

  swapped-hkv3 : HasKV' k3 v1 (fm-cons k1 v1 m)
  swapped-hkv3 = subst2 (\v' m -> HasKV' k3 v' (fm-cons k1 v1 m)) vp (fm'-invert/Involution m) (fm'-invert/HasKV hkv3)
fm'-invert/injective (fm-cons k1 v1 m) inj
                     {v} {k2} {k3} hkv2@(has-kv-skip _ _ _) hkv3@(has-kv-here vp _ _) = 
                     inj swapped-hkv2 swapped-hkv3
  where
  swapped-hkv2 : HasKV' k2 v1 (fm-cons k1 v1 m)
  swapped-hkv2 = subst2 (\v m -> HasKV' k2 v (fm-cons k1 v1 m)) vp (fm'-invert/Involution m) (fm'-invert/HasKV hkv2)

  swapped-hkv3 : HasKV' k3 v1 (fm-cons k1 v1 m)
  swapped-hkv3 = subst2 (\v m -> HasKV' k3 v (fm-cons k1 v1 m)) vp (fm'-invert/Involution m) (fm'-invert/HasKV hkv3)

fm'-invert/functional : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                       (m : FinMap' K V) -> isFunctionalFinMap' m -> 
                       isInjectiveFinMap' (fm'-invert m)
fm'-invert/functional [] _ ()
fm'-invert/functional (fm-cons k1 v1 m) _
                      (has-kv-here v2p k2p _) (has-kv-here v3p k3p _) = v2p >=> sym v3p
fm'-invert/functional (fm-cons k v m) fun
                      (has-kv-skip _ _ hkv1) (has-kv-skip _ _ hkv2) = rec hkv1 hkv2
  where
  fun' : isFunctionalFinMap' m
  fun' hkv1 hkv2 = fun (has-kv-skip k v hkv1) (has-kv-skip k v hkv2)
  rec : isInjectiveFinMap' (fm'-invert m)
  rec = fm'-invert/functional m fun'
fm'-invert/functional (fm-cons k1 v1 m) fun
                      {v2} {v3} {k} hkv2@(has-kv-here _ kp _) hkv3@(has-kv-skip _ _ _) = 
                      fun swapped-hkv2 swapped-hkv3
  where
  swapped-hkv2 : HasKV' k1 v2 (fm-cons k1 v1 m)
  swapped-hkv2 = subst2 (\k m -> HasKV' k v2 (fm-cons k1 v1 m)) kp (fm'-invert/Involution m) (fm'-invert/HasKV hkv2)

  swapped-hkv3 : HasKV' k1 v3 (fm-cons k1 v1 m)
  swapped-hkv3 = subst2 (\k m -> HasKV' k v3 (fm-cons k1 v1 m)) kp (fm'-invert/Involution m) (fm'-invert/HasKV hkv3)
fm'-invert/functional (fm-cons k1 v1 m) fun
                      {v2} {v3} {k} hkv2@(has-kv-skip _ _ _) hkv3@(has-kv-here _ kp _) = 
                      fun swapped-hkv2 swapped-hkv3
  where
  swapped-hkv2 : HasKV' k1 v2 (fm-cons k1 v1 m)
  swapped-hkv2 = subst2 (\k m -> HasKV' k v2 (fm-cons k1 v1 m)) kp (fm'-invert/Involution m) (fm'-invert/HasKV hkv2)

  swapped-hkv3 : HasKV' k1 v3 (fm-cons k1 v1 m)
  swapped-hkv3 = subst2 (\k m -> HasKV' k v3 (fm-cons k1 v1 m)) kp (fm'-invert/Involution m) (fm'-invert/HasKV hkv3)


fm'-invert/bijective : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
                       (m : FinMap' K V) -> isBijectiveFinMap' m -> 
                       isBijectiveFinMap' (fm'-invert m)
fm'-invert/bijective m (inj , fun) = fm'-invert/functional m fun , fm'-invert/injective m inj



_fm⊆_ : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> FinMap' K V -> FinMap' K V -> Type (ℓ-max ℓK ℓV)
m1 fm⊆ m2 = ∀ {k} {v} -> HasKV' k v m1 -> HasKV' k v m2

_fm⊂_ : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> FinMap' K V -> FinMap' K V -> Type (ℓ-max ℓK ℓV)
_fm⊂_ {K = K} {V = V} m1 m2 = (m1 fm⊆ m2) × (Σ[ k ∈ K ] Σ[ v ∈ V ] (¬ (HasKV' k v m1) × HasKV' k v m2))

_fm⊂'_ : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> FinMap' K V -> FinMap' K V -> Type (ℓ-max ℓK ℓV)
_fm⊂'_ {K = K} {V = V} m1 m2 = 
  (m1 fm⊆ m2) × (∃![ kv ∈ (K × V) ] (¬ (HasKV' (proj₁ kv) (proj₂ kv) m1) × 
                                     HasKV' (proj₁ kv) (proj₂ kv) m2))

isBijective-fm⊆ : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} {fm1 fm2 : FinMap' K V} ->
                  fm1 fm⊆ fm2 -> isBijectiveFinMap' fm2 -> isBijectiveFinMap' fm1
isBijective-fm⊆ inc (inj , fun) =
  (\hk1 hk2 -> inj (inc hk1) (inc hk2)) , (\hk1 hk2 -> fun (inc hk1) (inc hk2))
            

module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} 
         {{disc'K : Discrete' K}} 
         {{isSet'V : isSet' V}} 
         where
  private
    discK = Discrete'.f disc'K
    isSetK = Discrete->isSet discK
    isSetV = isSet'.f isSet'V

  lookup' : (k : K) (m : FinMap' K V) -> Dec (HasKey' k m)
  lookup' k [] = no (\())
  lookup' k fm@(fm-cons k2 v2 m) = handle (discK k k2) (lookup' k m)
    where
    handle : Dec (k == k2) -> Dec (HasKey' k m) -> Dec (HasKey' k fm)
    handle (yes p) _      = yes (v2 , has-kv-here p refl m)
    handle (no ¬k=k2) (yes (v , hkv)) = yes (v , has-kv-skip k2 v2 hkv)
    handle (no ¬k=k2) (no ¬hkv) = no handle2
      where
      handle2 : ¬ (HasKey' k fm)
      handle2 (_ , (has-kv-here kp vp _)) = ¬k=k2 kp
      handle2 (v , (has-kv-skip _ _ hkv)) = ¬hkv (v , hkv)

  lookup : (k : K) (m : FinMap K V) -> Dec (HasKey k m)
  lookup k (m , _) = lookup' k m

  isUnique-HasKV2 : {k : K} {v1 v2 : V} (m : FinMap K V) -> 
                    HasKV k v1 m -> HasKV k v2 m -> v1 == v2
  isUnique-HasKV2 (m , !m) (has-kv-here _ vp1 _) (has-kv-here _ vp2 _) = 
    vp1 >=> sym vp2
  isUnique-HasKV2 ((fm-cons _ _ m') , (fm-cons _ _ !m')) 
                    (has-kv-skip _ _ hkv1') (has-kv-skip _ _ hkv2') =
    isUnique-HasKV2 (m' , !m') hkv1' hkv2' 
  isUnique-HasKV2 (fm-cons kn vn m' , (fm-cons ¬hk1' _ _))
                  (has-kv-here kp _ _) (has-kv-skip _ _ hkv2') =
    bot-elim (¬hk1' (subst (\k -> HasKey' k _) kp (_ , hkv2')))
  isUnique-HasKV2 (m , (fm-cons ¬hk2' _ _))
                  (has-kv-skip _ _ hkv1') (has-kv-here kp _ _) =
    bot-elim (¬hk2' (subst (\k -> HasKey' k _) kp (_ , hkv1')))


  isProp-HasKV2 : {k : K} {v : V} -> (m : FinMap K V) -> 
                  (hk1 : HasKV k v m) -> (hk2 : HasKV k v m) -> hk1 == hk2
  isProp-HasKV2 m (has-kv-here k1p v1p m') (has-kv-here k2p v2p m') = 
    \i -> has-kv-here (kp i) (vp i) m'
    where
    kp : k1p == k2p
    kp = isSetK _ _ k1p k2p
    vp : v1p == v2p
    vp = isSetV _ _ v1p v2p
  isProp-HasKV2 ((fm-cons _ _ m') , (fm-cons _ _ !m'))
                  (has-kv-skip _ _ hkv1') (has-kv-skip _ _ hkv2') =
    cong (has-kv-skip _ _) (isProp-HasKV2 (m' , !m') hkv1' hkv2')
  isProp-HasKV2 (_ , (fm-cons ¬hk1' _ _))
                (has-kv-here kp _ _) (has-kv-skip _ _ hkv2') =
    bot-elim (¬hk1' (subst (\k -> HasKey' k _) kp (_ , hkv2')))
  isProp-HasKV2 (_ , (fm-cons ¬hk2' _ _))
                (has-kv-skip _ _ hkv1') (has-kv-here kp _ _) =
    bot-elim (¬hk2' (subst (\k -> HasKey' k _) kp (_ , hkv1')))

module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} where
  record FinMapEq (l r : FinMap K V) : Type (ℓ-max ℓK ℓV) where
    field
      forward : {k : K} {v : V} -> HasKV k v l -> ∥ HasKV k v r ∥
      backward : {k : K} {v : V} -> HasKV k v r -> ∥ HasKV k v l ∥

FinMapQuot : {ℓK ℓV : Level} (K : Type ℓK) (V : Type ℓV) -> Type (ℓ-max ℓK ℓV)
FinMapQuot K V = FinMap K V / FinMapEq


module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} where
  private
    module FinMapQuotElim = SetQuotientElim (FinMap K V) FinMapEq

    HasKVQuot-hProp : K -> V -> FinMapQuot K V -> hProp (ℓ-max ℓK ℓV)
    HasKVQuot-hProp k v = 
      FinMapQuotElim.rec isSet-hProp (\m -> ∥ HasKV k v m ∥ , squash) same
      where
      same : (m1 m2 : FinMap K V) (eq : FinMapEq m1 m2) -> 
             (∥ HasKV k v m1 ∥ , squash) == (∥ HasKV k v m2 ∥ , squash)
      same m1 m2 eq = ΣProp-path isProp-isProp (isoToPath iso-hkv)
        where
        open Iso
        iso-hkv : Iso ∥ HasKV k v m1 ∥ ∥ HasKV k v m2 ∥
        iso-hkv .fun = ∥-bind (FinMapEq.forward eq)
        iso-hkv .inv = ∥-bind (FinMapEq.backward eq)
        iso-hkv .rightInv _ = squash _ _
        iso-hkv .leftInv _ = squash _ _

  HasKVQuot : K -> V -> FinMapQuot K V -> Type (ℓ-max ℓK ℓV)
  HasKVQuot k v m = fst (HasKVQuot-hProp k v m)

fm'-size : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> FinMap' K V -> Nat
fm'-size [] = 0
fm'-size (fm-cons k v m) = suc (fm'-size m)

-- fm'-rest : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> FinMap' K V -> FinMap' K V
-- fm'-rest [] = []
-- fm'-rest (fm-cons _ _ m) = m
--
-- ΣKV-skip : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} 
--            (k2 : K) (v2 : V) (m : FinMap' K V) ->
--            Σ[ k ∈ K ] Σ[ v ∈ V ] (HasKV' k v m) ->
--            Σ[ k ∈ K ] Σ[ v ∈ V ] (HasKV' k v (fm-cons k2 v2 m))
-- ΣKV-skip k2 v2 _ (k , v , hk) = k , v , has-kv-skip k2 v2 hk
-- 
-- at-index : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} (m : FinMap' K V) -> 
--            Fin (fm'-size m) -> Σ[ k ∈ K ] Σ[ v ∈ V ] (HasKV' k v m)
-- at-index [] z = bot-elim (¬fin-zero z)
-- at-index (fm-cons k v m) (zero , _) = k , v , has-kv-here m
-- at-index (fm-cons k v m) (suc i , lt) = ΣKV-skip k v _ (at-index m (i , pred-≤ lt))
-- 
-- at-index/suc : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} (m : FinMap' K V) (i : Fin (fm'-size m)) 
--                {k : K} {v : V} ->
--                at-index (fm-cons k v m) (suc-fin i) == ΣKV-skip k v m (at-index m i)
-- at-index/suc m (i , lt) {k} {v} j = ΣKV-skip k v m (at-index m (i , isProp≤ (pred-≤ (suc-≤ lt)) lt j))
-- 
-- hasKV-index : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} 
--               {k : K} {v : V} {m : FinMap' K V} -> (HasKV' k v m) -> Fin (fm'-size m)
-- hasKV-index (has-kv-here _) = zero-fin 
-- hasKV-index (has-kv-skip _ _ hkv) = suc-fin (hasKV-index hkv)
-- 
--               
-- at-hasKV-index : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} 
--                  {k : K} {v : V} {m : FinMap' K V} (hkv : HasKV' k v m) ->
--                  at-index m (hasKV-index hkv) == (k , v , hkv)
-- at-hasKV-index (has-kv-here _) = refl
-- at-hasKV-index (has-kv-skip _ _ hkv) = 
--   at-index/suc _ _ >=> cong (ΣKV-skip _ _ _) (at-hasKV-index hkv)

--hasKV-same-index : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} 
--                   {k : K} {v : V} {m : FinMap' K V} 
--                   (hkv1 : HasKV' k v m) ->
--                   (hkv2 : HasKV' k v m) ->
--                   hasKV-index hkv1 == hasKV-index hkv2 ->
--                   hkv1 == hkv2
--hasKV-same-index {K = K} {V = V} {k = k} {v} {m} hkv1 hkv2 hkp = ?
--  where
--  p : Path (Σ[ k ∈ K ] Σ[ v ∈ V ] (HasKV' k v m)) (k , v , hkv1) (k , v , hkv2) 
--  p = sym (at-hasKV-index hkv1) >=> cong (at-index m) hkp >=> (at-hasKV-index hkv2)
--  p2 : Path (Σ[ v ∈ V ] (HasKV' k v m)) (v , hkv1) (v , hkv2)
--  p2 = cong snd p
