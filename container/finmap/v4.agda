{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.v4 where

open import base
open import cubical
open import equality-path
open import equivalence
open import finset
open import functions
open import funext
open import hlevel
open import isomorphism
open import maybe
open import nat
open import relation
open import sigma.base
open import sigma
open import truncation
open import set-quotient
open import univalence


private
  variable
    ℓ ℓK ℓV : Level
    K V : Type ℓ

private
  data RawFinMap (K : Type ℓK) (V : Type ℓV) : Type (ℓ-max ℓK ℓV) where
    raw-finmap-empty : RawFinMap K V
    raw-finmap-cons : K -> V -> RawFinMap K V -> RawFinMap K V


  module _ {K : Type ℓK} {V : Type ℓV} where
    data SameFinMap-Step : RawFinMap K V -> RawFinMap K V -> Type (ℓ-max ℓK ℓV) where
      same-finmap-same-key : (k1 k2 : K) (v1 v2 : V) (m : RawFinMap K V) -> k1 == k2 ->
        SameFinMap-Step (raw-finmap-cons k1 v1 (raw-finmap-cons k2 v2 m)) (raw-finmap-cons k1 v1 m)
      same-finmap-different-key : (k1 k2 : K) (v1 v2 : V) (m : RawFinMap K V) -> (k1 != k2) ->
        SameFinMap-Step (raw-finmap-cons k1 v1 (raw-finmap-cons k2 v2 m)) 
                        (raw-finmap-cons k2 v2 (raw-finmap-cons k1 v1 m))
      same-finmap-cons : (k1 k2 : K) (v1 v2 : V) (m1 m2 : RawFinMap K V) -> 
                         (k1 == k2) -> (v1 == v2) -> SameFinMap-Step m1 m2 -> 
        SameFinMap-Step (raw-finmap-cons k1 v1 m1) (raw-finmap-cons k2 v2 m2)


    data RawFinMap-HasKV : RawFinMap K V -> K -> V -> Type (ℓ-max ℓK ℓV) where
      raw-finmap-haskv-head : {k k2 : K} {v v2 : V} {m : RawFinMap K V} ->
                              k == k2 -> v == v2 ->
                              RawFinMap-HasKV (raw-finmap-cons k v m) k2 v2
      raw-finmap-haskv-cons : {k k2 : K} {v v2 : V} {m : RawFinMap K V} -> 
                              (k != k2) -> (hk : RawFinMap-HasKV m k2 v2) ->
                              RawFinMap-HasKV (raw-finmap-cons k v m) k2 v2


    RawFinMap-HasKey : RawFinMap K V -> K -> Type (ℓ-max ℓK ℓV)
    RawFinMap-HasKey m k = Σ[ v ∈ V ] (RawFinMap-HasKV m k v)



    module FinMapElim = SetQuotientElim (RawFinMap K V) SameFinMap-Step


FinMap : Type ℓK -> Type ℓV -> Type (ℓ-max ℓK ℓV)
FinMap K V = RawFinMap K V / SameFinMap-Step

finmap-empty : FinMap K V
finmap-empty = [ raw-finmap-empty ]

module _ {K : Type ℓK} {V : Type ℓV} where
  finmap-upsert : FinMap K V -> K -> V -> FinMap K V
  finmap-upsert m k v = FinMapElim.rec squash/ f same m
    where
    f : RawFinMap K V -> FinMap K V
    f m = [ raw-finmap-cons k v m ]
    same : (m1 m2 : RawFinMap K V) -> SameFinMap-Step m1 m2 -> f m1 == f m2
    same _ _ s = eq/ _ _ (same-finmap-cons _ _ _ _ _ _ refl refl s)


module _ {K : Type ℓK} {V : Type ℓV} {{disc'K : Discrete' K}} {{isSet'V : isSet' V}} where
  private
    disc-K : Discrete K
    disc-K = Discrete'.f disc'K

    isSet-K : isSet K
    isSet-K = Discrete->isSet disc-K

    isSet-V : isSet V
    isSet-V = isSet'.f isSet'V

  private
    isProp-RawFinMap-HasKV : (m : RawFinMap K V) (k : K) (v : V) -> isProp (RawFinMap-HasKV m k v)
    isProp-RawFinMap-HasKV (raw-finmap-empty) _ _ ()
    isProp-RawFinMap-HasKV (raw-finmap-cons k1 v1 m) k2 v2
      (raw-finmap-haskv-head pk1 pv1) (raw-finmap-haskv-head pk2 pv2) =
      cong2 raw-finmap-haskv-head (isSet-K _ _ pk1 pk2) (isSet-V _ _ pv1 pv2)
    isProp-RawFinMap-HasKV (raw-finmap-cons k1 v1 m) k2 v2
      (raw-finmap-haskv-cons ¬p _) (raw-finmap-haskv-head pk pv) =
      bot-elim (¬p pk)
    isProp-RawFinMap-HasKV (raw-finmap-cons k1 v1 m) k2 v2
     (raw-finmap-haskv-head pk pv) (raw-finmap-haskv-cons ¬p _) = 
      bot-elim (¬p pk)
    isProp-RawFinMap-HasKV (raw-finmap-cons k1 v1 m) k2 v2
      (raw-finmap-haskv-cons ¬p1 hk1) (raw-finmap-haskv-cons ¬p2 hk2) =
      cong2 raw-finmap-haskv-cons (isProp¬ _ ¬p1 ¬p2) (isProp-RawFinMap-HasKV _ _ _ hk1 hk2)


    isProp-RawFinMap-HasKey : (m : RawFinMap K V) (k : K) -> isProp (RawFinMap-HasKey m k)
    isProp-RawFinMap-HasKey (raw-finmap-empty) _ _ ()
    isProp-RawFinMap-HasKey m@(raw-finmap-cons k1 v1 m') k hk1 hk2 =
      ΣProp-path (\{v} -> isProp-RawFinMap-HasKV m k v) (handle hk1 hk2)
      where
      handle : {m : RawFinMap K V} -> (hk1 hk2 : RawFinMap-HasKey m k) -> ⟨ hk1 ⟩ == ⟨ hk2 ⟩
      handle (_ , raw-finmap-haskv-head _ pva) 
             (_ , raw-finmap-haskv-head _ pvb) =
        sym pva >=> pvb
      handle (_ , raw-finmap-haskv-cons ¬pk _) 
             (_ , raw-finmap-haskv-head pk _) = bot-elim (¬pk pk)
      handle (_ , raw-finmap-haskv-head pk _) 
             (_ , raw-finmap-haskv-cons ¬pk _) = bot-elim (¬pk pk)
      handle (va , raw-finmap-haskv-cons _ hka) 
             (vb , raw-finmap-haskv-cons _ hkb) =
        handle (va , hka) (vb , hkb)

  FinMap-HasKV' : FinMap K V -> K -> V -> hProp (ℓ-max ℓK ℓV)
  FinMap-HasKV' m k v = FinMapElim.rec isSet-hProp f same m
    where
    f : RawFinMap K V -> hProp (ℓ-max ℓK ℓV)
    f m = RawFinMap-HasKV m k v , isProp-RawFinMap-HasKV m k v

    step->eq-hk : (m1 m2 : RawFinMap K V) -> SameFinMap-Step m1 m2 -> 
                  RawFinMap-HasKV m1 k v <-> RawFinMap-HasKV m2 k v
    step->eq-hk m1 m2 (same-finmap-same-key k1 k2 v1 v2 m k1=k2) = m1->m2 , m2->m1
      where
      m1->m2 : RawFinMap-HasKV m1 k v -> RawFinMap-HasKV m2 k v
      m1->m2 (raw-finmap-haskv-head k1=k v1=v) =
        (raw-finmap-haskv-head k1=k v1=v)
      m1->m2 (raw-finmap-haskv-cons k1!=k (raw-finmap-haskv-cons _ hk)) =
        (raw-finmap-haskv-cons k1!=k hk)
      m1->m2 (raw-finmap-haskv-cons k1!=k (raw-finmap-haskv-head k2=k _)) =
        bot-elim (k1!=k (k1=k2 >=> k2=k))

      m2->m1 : RawFinMap-HasKV m2 k v -> RawFinMap-HasKV m1 k v
      m2->m1 (raw-finmap-haskv-head k1=k v1=v) =
        (raw-finmap-haskv-head k1=k v1=v)
      m2->m1 (raw-finmap-haskv-cons k1!=k hk) =
        (raw-finmap-haskv-cons k1!=k
          (raw-finmap-haskv-cons (\k2=k -> k1!=k (k1=k2 >=> k2=k)) hk))
          
    step->eq-hk m1 m2 (same-finmap-different-key k1 k2 v1 v2 m k1!=k2) = m1->m2 , m2->m1
      where
      m1->m2 : RawFinMap-HasKV m1 k v -> RawFinMap-HasKV m2 k v
      m1->m2 (raw-finmap-haskv-head k1=k v1=v) = 
        (raw-finmap-haskv-cons (\k2=k -> k1!=k2 (k1=k >=> sym k2=k))
                               (raw-finmap-haskv-head k1=k v1=v))
      m1->m2 (raw-finmap-haskv-cons k1!=k (raw-finmap-haskv-cons k2!=k hk)) = 
        (raw-finmap-haskv-cons k2!=k (raw-finmap-haskv-cons k1!=k hk))
      m1->m2 (raw-finmap-haskv-cons _ (raw-finmap-haskv-head k2=k v2=v)) = 
        (raw-finmap-haskv-head k2=k v2=v)

      m2->m1 : RawFinMap-HasKV m2 k v -> RawFinMap-HasKV m1 k v
      m2->m1 (raw-finmap-haskv-head k2=k v2=v) = 
        (raw-finmap-haskv-cons (\k1=k -> k1!=k2 (k1=k >=> sym k2=k))
                               (raw-finmap-haskv-head k2=k v2=v))
      m2->m1 (raw-finmap-haskv-cons k1!=k (raw-finmap-haskv-cons k2!=k hk)) = 
        (raw-finmap-haskv-cons k2!=k (raw-finmap-haskv-cons k1!=k hk))
      m2->m1 (raw-finmap-haskv-cons _ (raw-finmap-haskv-head k1=k v1=v)) = 
        (raw-finmap-haskv-head k1=k v1=v)

    step->eq-hk m1 m2 (same-finmap-cons k1 k2 v1 v2 m1' m2' k1=k2 v1=v2 s) = m1->m2 , m2->m1
      where
      m1->m2 : RawFinMap-HasKV m1 k v -> RawFinMap-HasKV m2 k v
      m1->m2 (raw-finmap-haskv-head k1=k v1=v) =
        (raw-finmap-haskv-head (sym k1=k2 >=> k1=k) (sym v1=v2 >=> v1=v))
      m1->m2 (raw-finmap-haskv-cons k1!=k hk) = 
        (raw-finmap-haskv-cons (\k2=k -> k1!=k (k1=k2 >=> k2=k)) 
                               (proj₁ (step->eq-hk m1' m2' s) hk))

      m2->m1 : RawFinMap-HasKV m2 k v -> RawFinMap-HasKV m1 k v
      m2->m1 (raw-finmap-haskv-head k2=k v2=v) =
        (raw-finmap-haskv-head (k1=k2 >=> k2=k) (v1=v2 >=> v2=v))
      m2->m1 (raw-finmap-haskv-cons k2!=k hk) = 
        (raw-finmap-haskv-cons (\k1=k -> k2!=k (sym k1=k2 >=> k1=k)) 
                               (proj₂ (step->eq-hk m1' m2' s) hk))


    same : (m1 m2 : RawFinMap K V)-> SameFinMap-Step m1 m2 -> f m1 == f m2
    same m1 m2 step = ΣProp-path isProp-isProp same-hkv
      where
      same-hkv : RawFinMap-HasKV m1 k v == RawFinMap-HasKV m2 k v
      same-hkv =
        let (m1->m2 , m2->m1) = (step->eq-hk m1 m2 step) in
          ua (isoToEquiv (isProp->iso m1->m2 m2->m1
               (isProp-RawFinMap-HasKV _ _ _) (isProp-RawFinMap-HasKV _ _ _)))

  FinMap-HasKV : FinMap K V -> K -> V -> Type (ℓ-max ℓK ℓV)
  FinMap-HasKV m k v = fst (FinMap-HasKV' m k v)

  isProp-FinMap-HasKV : (m : FinMap K V) (k : K) (v : V) -> isProp (FinMap-HasKV m k v)
  isProp-FinMap-HasKV m k v = snd (FinMap-HasKV' m k v)


  FinMap-HasKey : FinMap K V -> K -> Type (ℓ-max ℓK ℓV)
  FinMap-HasKey m k = Σ V (FinMap-HasKV m k)

  isProp-FinMap-HasKey : (m : FinMap K V)-> (k : K) -> isProp (FinMap-HasKey m k)
  isProp-FinMap-HasKey m k =
    FinMapElim.elimProp 
      {C = \m -> isProp (FinMap-HasKey m k)}
      (\_ -> isProp-isProp) (\m -> isProp-RawFinMap-HasKey m k) m


  finmap-contains : (m : FinMap K V) -> (k : K) -> Dec (FinMap-HasKey m k)
  finmap-contains m k = 
    FinMapElim.elimProp (\m -> (isPropDec (isProp-FinMap-HasKey m k))) f m
    where
    f : (m : RawFinMap K V) -> Dec (RawFinMap-HasKey m k)
    f raw-finmap-empty = no \()
    f (raw-finmap-cons k2 v m) = handle (disc-K k2 k)
      where
      handle : Dec (k2 == k) -> Dec (RawFinMap-HasKey (raw-finmap-cons k2 v m) k)
      handle (yes k2=k) = yes (v , raw-finmap-haskv-head k2=k refl)
      handle (no k2!=k) = handle2 (f m)
        where
        handle2 : Dec (RawFinMap-HasKey m k) -> Dec (RawFinMap-HasKey (raw-finmap-cons k2 v m) k)
        handle2 (yes (v , hk)) = yes (v , raw-finmap-haskv-cons k2!=k hk)
        handle2 (no ¬hkv) = no handle3 
          where
          handle3 : (RawFinMap-HasKey (raw-finmap-cons k2 v m) k) -> Bot
          handle3 (_ , raw-finmap-haskv-head k2=k _) = k2!=k k2=k
          handle3 (v , raw-finmap-haskv-cons _ hk) = ¬hkv (v , hk)


  

--  FinMap-HasKey' : FinMap K V -> K -> hProp (ℓ-max ℓK ℓV)
--  FinMap-HasKey' m k = FinMapElim.rec isSet-hProp f same m
--    where
--    f : RawFinMap K V -> hProp (ℓ-max ℓK ℓV)
--    f m = RawFinMap-HasKey m k , isProp-RawFinMap-HasKey m k 
--
--    step->eq-hk : (m1 m2 : RawFinMap K V) -> SameFinMap-Step m1 m2 -> 
--                  RawFinMap-HasKey m1 k <-> RawFinMap-HasKey m2 k
--    step->eq-hk m1 m2 (same-finmap-same-key k1 k2 v1 v2 m k1=k2) = m1->m2 , m2->m1
--      where
--      m1->m2 : RawFinMap-HasKey m1 k -> RawFinMap-HasKey m2 k
--      m1->m2 (raw-finmap-haskey-head _ _ _ _ k1=k) =
--        (raw-finmap-haskey-head _ _ _ _ k1=k)
--      m1->m2 (raw-finmap-haskey-cons _ _ _ k1!=k (raw-finmap-haskey-cons _ _ _ _ hk)) =
--        (raw-finmap-haskey-cons _ _ _ k1!=k hk)
--      m1->m2 (raw-finmap-haskey-cons _ _ _ k1!=k (raw-finmap-haskey-head _ _ _ _ k2=k)) =
--        bot-elim (k1!=k (k1=k2 >=> k2=k))
--
--      m2->m1 : RawFinMap-HasKey m2 k -> RawFinMap-HasKey m1 k
--      m2->m1 (raw-finmap-haskey-head _ _ _ _ k1=k) =
--        (raw-finmap-haskey-head _ _ _ _ k1=k)
--      m2->m1 (raw-finmap-haskey-cons _ _ _ k1!=k hk) =
--        (raw-finmap-haskey-cons _ _ _ k1!=k
--          (raw-finmap-haskey-cons _ _ _ (\k2=k -> k1!=k (k1=k2 >=> k2=k)) hk))
--    step->eq-hk m1 m2 (same-finmap-different-key k1 k2 v1 v2 m k1!=k2) = m1->m2 , m2->m1
--      where
--      m1->m2 : RawFinMap-HasKey m1 k -> RawFinMap-HasKey m2 k
--      m1->m2 (raw-finmap-haskey-head _ _ _ _ k1=k) = 
--        (raw-finmap-haskey-cons _ _ _ (\k2=k -> k1!=k2 (k1=k >=> sym k2=k))
--                               (raw-finmap-haskey-head _ _ _ _ k1=k))
--      m1->m2 (raw-finmap-haskey-cons _ _ _ k1!=k (raw-finmap-haskey-cons _ _ _ k2!=k hk)) = 
--        (raw-finmap-haskey-cons _ _ _ k2!=k (raw-finmap-haskey-cons _ _ _ k1!=k hk))
--      m1->m2 (raw-finmap-haskey-cons _ _ _ _ (raw-finmap-haskey-head _ _ _ _ k2=k)) = 
--        (raw-finmap-haskey-head _ _ _ _ k2=k)
--
--
--      m2->m1 : RawFinMap-HasKey m2 k -> RawFinMap-HasKey m1 k
--      m2->m1 (raw-finmap-haskey-head _ _ _ _ k2=k) = 
--        (raw-finmap-haskey-cons _ _ _ (\k1=k -> k1!=k2 (k1=k >=> sym k2=k))
--                               (raw-finmap-haskey-head _ _ _ _ k2=k))
--      m2->m1 (raw-finmap-haskey-cons _ _ _ k1!=k (raw-finmap-haskey-cons _ _ _ k2!=k hk)) = 
--        (raw-finmap-haskey-cons _ _ _ k2!=k (raw-finmap-haskey-cons _ _ _ k1!=k hk))
--      m2->m1 (raw-finmap-haskey-cons _ _ _ _ (raw-finmap-haskey-head _ _ _ _ k1=k)) = 
--        (raw-finmap-haskey-head _ _ _ _ k1=k)
--    step->eq-hk m1 m2 (same-finmap-cons k1 k2 v1 v2 m1' m2' k1=k2 v1=v2 s) = m1->m2 , m2->m1
--      where
--      m1->m2 : RawFinMap-HasKey m1 k -> RawFinMap-HasKey m2 k
--      m1->m2 (raw-finmap-haskey-head _ _ _ _ k1=k) =
--        (raw-finmap-haskey-head _ _ _ _ (sym k1=k2 >=> k1=k))
--      m1->m2 (raw-finmap-haskey-cons _ _ _ k1!=k hk) = 
--        (raw-finmap-haskey-cons _ _ _ (\k2=k -> k1!=k (k1=k2 >=> k2=k)) 
--                                (proj₁ (step->eq-hk m1' m2' s) hk))
--
--      m2->m1 : RawFinMap-HasKey m2 k -> RawFinMap-HasKey m1 k
--      m2->m1 (raw-finmap-haskey-head _ _ _ _ k2=k) =
--        (raw-finmap-haskey-head _ _ _ _ (k1=k2 >=> k2=k))
--      m2->m1 (raw-finmap-haskey-cons _ _ _ k2!=k hk) = 
--        (raw-finmap-haskey-cons _ _ _ (\k1=k -> k2!=k (sym k1=k2 >=> k1=k)) 
--                                (proj₂ (step->eq-hk m1' m2' s) hk))
--
--    same-hk : (m1 m2 : RawFinMap K V) -> SameFinMap-Step m1 m2 -> 
--              RawFinMap-HasKey m1 k == RawFinMap-HasKey m2 k
--    same-hk m1 m2 s =
--      let (m1->m2 , m2->m1) = step->eq-hk m1 m2 s in
--        ua (isoToEquiv (isProp->iso m1->m2 m2->m1
--             (isProp-RawFinMap-HasKey _ _) (isProp-RawFinMap-HasKey _ _)))
--
--    same : (m1 m2 : RawFinMap K V)-> SameFinMap-Step m1 m2 -> f m1 == f m2
--    same m1 m2 step = ΣProp-path isProp-isProp (same-hk m1 m2 step)

--    isProp-RawFinMap-HasKey : (m : RawFinMap K V) -> (k : K) -> isProp (RawFinMap-HasKey m k)
--    isProp-RawFinMap-HasKey (raw-finmap-empty) _ ()
--    isProp-RawFinMap-HasKey (raw-finmap-cons k1 v m) k2 
--      (raw-finmap-haskey-head _ _ _ _ p1) (raw-finmap-haskey-head _ _ _ _ p2) =
--      cong (raw-finmap-haskey-head _ _ _ _) (isSet-K _ _ p1 p2)
--    isProp-RawFinMap-HasKey (raw-finmap-cons k1 v m) k2 
--      (raw-finmap-haskey-cons _ _ _ ¬p _) (raw-finmap-haskey-head _ _ _ _ p) =
--      bot-elim (¬p p)
--    isProp-RawFinMap-HasKey (raw-finmap-cons k1 v m) k2 
--      (raw-finmap-haskey-head _ _ _ _ p) (raw-finmap-haskey-cons _ _ _ ¬p _) =
--      bot-elim (¬p p)
--    isProp-RawFinMap-HasKey (raw-finmap-cons k1 v m) k2 
--      (raw-finmap-haskey-cons _ _ _ ¬p1 hk1) (raw-finmap-haskey-cons _ _ _ ¬p2 hk2) =
--      cong2 (raw-finmap-haskey-cons _ _ _) (isProp¬ _ ¬p1 ¬p2) (isProp-RawFinMap-HasKey _ _ hk1 hk2)


--    data RawFinMap-HasKey : RawFinMap K V -> K -> Type (ℓ-max ℓK ℓV) where
--      raw-finmap-haskey-head : (k : K) (v : V) (m : RawFinMap K V) (k2 : K) -> 
--                               k == k2 ->
--                               RawFinMap-HasKey (raw-finmap-cons k v m) k2
--      raw-finmap-haskey-cons : (k : K) (v : V) {m : RawFinMap K V} (k2 : K) -> 
--                               (k != k2) ->
--                               (hk : RawFinMap-HasKey m k2) ->
--                               RawFinMap-HasKey (raw-finmap-cons k v m) k2
