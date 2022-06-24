{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap where

open import base
open import fin
open import functions
open import nat
open import hlevel
open import relation
open import equality

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


HasKey' : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> REL K (FinMap' K V) (ℓ-max ℓK ℓV)
HasKey' {V = V} k m = Σ[ v ∈ V ] HasKV' k v m


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
DisjointKeys  m1 m2 = ∀ {k} -> HasKey k m1 -> HasKey k m2 -> Bot

fm'-union : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> 
            (FinMap' K V) -> (FinMap' K V) -> (FinMap' K V)
fm'-union [] m = m
fm'-union (fm-cons k v m) m2 = fm-cons k v (fm'-union m m2)

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
    
  



-- fm'-size : {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} -> FinMap' K V -> Nat
-- fm'-size [] = 0
-- fm'-size (fm-cons k v m) = suc (fm'-size m)
-- 
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
