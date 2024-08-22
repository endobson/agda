{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module container.finmap.v4 where

open import base
open import cubical
open import discrete
open import equality-path
open import equivalence
open import finset
open import functions
open import funext
open import hlevel
open import isomorphism
open import maybe
open import nat
open import nat.order
open import order
open import order.instances.nat
open import relation
open import set-quotient
open import sigma
open import sigma.base
open import truncation
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


    raw-finmap-size : RawFinMap K V -> Nat
    raw-finmap-size raw-finmap-empty = zero
    raw-finmap-size (raw-finmap-cons k v m) = suc (raw-finmap-size m)

    raw-finmap-cons!=empty : {k : K} {v : V} {m : RawFinMap K V} ->
                             (raw-finmap-cons k v m) != raw-finmap-empty
    raw-finmap-cons!=empty p = zero-suc-absurd (sym (cong raw-finmap-size p))

    RawFinMap-HasKey : RawFinMap K V -> K -> Type (ℓ-max ℓK ℓV)
    RawFinMap-HasKey m k = Σ[ v ∈ V ] (RawFinMap-HasKV m k v)

    data RawFinMap-HasUniqueKeys : RawFinMap K V -> Type (ℓ-max ℓK ℓV) where
      raw-finmap-unique-empty : RawFinMap-HasUniqueKeys raw-finmap-empty
      raw-finmap-unique-cons : {k : K} {v : V} {m : RawFinMap K V} (¬hk : ¬ (RawFinMap-HasKey m k)) ->
                               RawFinMap-HasUniqueKeys m ->
                               RawFinMap-HasUniqueKeys (raw-finmap-cons k v m)


    ¬RawFinMap-HasKey-empty : (m : RawFinMap K V) ->
      (m == raw-finmap-empty) <-> (∀ k -> ¬ (RawFinMap-HasKey m k))
    ¬RawFinMap-HasKey-empty m@raw-finmap-empty = forward , backward
      where
      forward : (m == raw-finmap-empty) -> (∀ k -> ¬ (RawFinMap-HasKey m k))
      forward _ k ()
      backward :  (∀ k -> ¬ (RawFinMap-HasKey m k)) -> (m == raw-finmap-empty)
      backward _ = refl
    ¬RawFinMap-HasKey-empty m@(raw-finmap-cons k v _) = forward , backward
      where
      forward : (m == raw-finmap-empty) -> (∀ k -> ¬ (RawFinMap-HasKey m k))
      forward p = bot-elim (raw-finmap-cons!=empty p)
      backward :  (∀ k -> ¬ (RawFinMap-HasKey m k)) -> (m == raw-finmap-empty)
      backward ¬hk = bot-elim (¬hk k (v , raw-finmap-haskv-head refl refl))

    module FinMapElim = SetQuotientElim (RawFinMap K V) SameFinMap-Step

    SameFinMap-Steps : RawFinMap K V -> RawFinMap K V -> Type (ℓ-max ℓK ℓV)
    SameFinMap-Steps = TransitiveReflexiveClosure SameFinMap-Step

    SameFinMap-Steps-cons : (k : K) (v : V) {m1 m2 : RawFinMap K V} -> SameFinMap-Steps m1 m2 ->
                            (SameFinMap-Steps (raw-finmap-cons k v m1) (raw-finmap-cons k v m2))
    SameFinMap-Steps-cons k v trc-refl = trc-refl
    SameFinMap-Steps-cons k v (trc-rel s) = trc-rel (same-finmap-cons _ _ _ _ _ _ refl refl s)
    SameFinMap-Steps-cons k v (trc-trans s1 s2) =
      trc-trans (SameFinMap-Steps-cons k v s1) (SameFinMap-Steps-cons k v s2)


    module _ (k : K) (v : V) where

      RawFinMap-HasKV-ReorderSteps : (m : RawFinMap K V) -> (RawFinMap-HasKV m k v) ->
                                     Σ[ m2 ∈ RawFinMap K V ] (SameFinMap-Steps m (raw-finmap-cons k v m2))
      RawFinMap-HasKV-ReorderSteps m@(raw-finmap-cons _ _ m') (raw-finmap-haskv-head kp vp) =
        m' , subst (SameFinMap-Steps m) (cong2 (\k v -> raw-finmap-cons k v m') kp vp) trc-refl
      RawFinMap-HasKV-ReorderSteps m@(raw-finmap-cons k2 v2 m') (raw-finmap-haskv-cons ¬kp hk) =
        _ , trc-trans (SameFinMap-Steps-cons k2 v2 (snd rec)) (trc-rel step)
        where
        rec : Σ[ m2 ∈ RawFinMap K V ] (SameFinMap-Steps m' (raw-finmap-cons k v m2))
        rec = RawFinMap-HasKV-ReorderSteps m' hk

        m2 : RawFinMap K V
        m2 = ⟨ rec ⟩

        step : SameFinMap-Step (raw-finmap-cons k2 v2 (raw-finmap-cons k v m2))
                               (raw-finmap-cons k v (raw-finmap-cons k2 v2 m2))
        step = same-finmap-different-key k2 k v2 v m2 ¬kp





    --RawFinMap-HasKV->Steps : (m1 m2 : RawFinMap K V) ->
    --                         (same : ∀ k v -> (RawFinMap-HasKV m1 k v) <-> (RawFinMap-HasKV m2 k v)) ->
    --                         SameFinMap-Steps m1 m2
    --RawFinMap-HasKV->Steps raw-finmap-empty raw-finmap-empty same = trc-refl
    --RawFinMap-HasKV->Steps (raw-finmap-cons k v m) raw-finmap-empty same =
    --  bot-elim (proj₁ (¬RawFinMap-HasKey-empty _) refl k
    --                  (v , proj₁ (same k v) (raw-finmap-haskv-head refl refl)))
    --RawFinMap-HasKV->Steps raw-finmap-empty (raw-finmap-cons k v m) same =
    --  bot-elim (proj₁ (¬RawFinMap-HasKey-empty _) refl k
    --                  (v , proj₂ (same k v) (raw-finmap-haskv-head refl refl)))
    --RawFinMap-HasKV->Steps (raw-finmap-cons k1 v1 m1) (raw-finmap-cons k2 v2 m2) same =
    --  ?

module _ {K : Type ℓK} {V : Type ℓV} {{disc'K : Discrete' K}} {{isSet'V : isSet' V}} where
  private
    isSet-K : isSet K
    isSet-K = Discrete->isSet decide-=

    isSet-V : isSet V
    isSet-V = isSet'.f isSet'V

    ℓKV : Level
    ℓKV = ℓ-max ℓK ℓV

  -- RawFinMap-HasKey-cons : (k k2 : K) (v2 : V) (m : RawFinMap K V) ->
  --                         RawFinMap-HasKey m k -> RawFinMap-HasKey (raw-finmap-cons k2 v2 m) k
  -- RawFinMap-HasKey-cons = ?

  module _ (k : K) (v : V) where
    private
      Ans : RawFinMap K V -> Type ℓKV
      Ans m = Σ[ m2 ∈ RawFinMap K V ] (SameFinMap-Steps (raw-finmap-cons k v m) (raw-finmap-cons k v m2)) ×
                                      ¬ (RawFinMap-HasKey m2 k)

    RawFinMap-HasKV-RemoveSteps : (m : RawFinMap K V) -> Ans m
    RawFinMap-HasKV-RemoveSteps (raw-finmap-empty) =
      raw-finmap-empty , trc-refl , \()
    RawFinMap-HasKV-RemoveSteps m@(raw-finmap-cons k2 v2 m') = handle (decide-= k k2)
      where
      rec : Ans m'
      rec = RawFinMap-HasKV-RemoveSteps m'
      m2 = fst rec
      steps = fst (snd rec)
      ¬hk = snd (snd rec)

      handle : Dec (k == k2) -> Ans m
      handle (yes k=k2) =
        m2 , trc-trans (trc-rel (same-finmap-same-key _ _ _ _ _ k=k2)) steps , ¬hk
      handle (no k!=k2) =
        (raw-finmap-cons k2 v2 m2) ,
        trc-trans (trc-trans (trc-rel (same-finmap-different-key _ _ _ _ _ k!=k2))
                             (SameFinMap-Steps-cons k2 v2 steps))
                  (trc-rel (same-finmap-different-key _ _ _ _ _ (k!=k2 ∘ sym))) ,
        ¬hk'
        where
        ¬hk' : ¬(RawFinMap-HasKey (raw-finmap-cons k2 v2 m2) k)
        ¬hk' (v , raw-finmap-haskv-head kp _) = k!=k2 (sym kp)
        ¬hk' (v , raw-finmap-haskv-cons _ hk) = ¬hk (v , hk)


  module _ (k : K) (v : V) where
    private
      Ans : RawFinMap K V -> Type ℓKV
      Ans m = Σ[ m2 ∈ RawFinMap K V ]
              (SameFinMap-Steps m (raw-finmap-cons k v m2)) × ¬ (RawFinMap-HasKey m2 k)

    RawFinMap-HasKV-ReorderRemoveSteps : (m : RawFinMap K V) -> (RawFinMap-HasKV m k v) -> Ans m
    RawFinMap-HasKV-ReorderRemoveSteps m hk =
      fst Σm3 , trc-trans (snd Σm2) (fst (snd Σm3)) , snd (snd Σm3)
      where
      Σm2 = RawFinMap-HasKV-ReorderSteps k v m hk
      Σm3 = RawFinMap-HasKV-RemoveSteps k v (fst Σm2)


  raw-finmap-remove : RawFinMap K V -> K -> RawFinMap K V
  raw-finmap-remove raw-finmap-empty k = raw-finmap-empty
  raw-finmap-remove (raw-finmap-cons k2 v2 m) k with (decide-= k k2)
  ... | (yes _) = raw-finmap-remove m k
  ... | (no _) = raw-finmap-cons k2 v2 (raw-finmap-remove m k)

  raw-finmap-remove-size≤ :
    (m : RawFinMap K V) (k : K) -> raw-finmap-size (raw-finmap-remove m k) ≤ raw-finmap-size m
  raw-finmap-remove-size≤ raw-finmap-empty k = refl-≤
  raw-finmap-remove-size≤ (raw-finmap-cons k2 v2 m) k with (decide-= k k2)
  ... | (yes _) = right-suc-≤ (raw-finmap-remove-size≤ m k)
  ... | (no _) = suc-≤ (raw-finmap-remove-size≤ m k)

  raw-finmap-remove-¬HasKey :
    (m : RawFinMap K V) (k : K) -> ¬ (RawFinMap-HasKey (raw-finmap-remove m k) k)
  raw-finmap-remove-¬HasKey raw-finmap-empty k ()
  raw-finmap-remove-¬HasKey (raw-finmap-cons k2 v2 m) k with (decide-= k k2)
  ... | (yes _) = raw-finmap-remove-¬HasKey m k
  ... | (no k!=k2) = ¬hk
    where
    ¬hk : ¬ (RawFinMap-HasKey (raw-finmap-cons k2 v2 (raw-finmap-remove m k)) k)
    ¬hk (v , raw-finmap-haskv-head k2=k _) = k!=k2 (sym k2=k)
    ¬hk (v , raw-finmap-haskv-cons _ hkv) =
      raw-finmap-remove-¬HasKey m k (v , hkv)

  raw-finmap-remove-HasKV :
    (m : RawFinMap K V) {k1 k2 : K} {v2 : V} -> k1 != k2 ->
    (RawFinMap-HasKV m k2 v2) <->
    (RawFinMap-HasKV (raw-finmap-remove m k1) k2 v2)
  raw-finmap-remove-HasKV raw-finmap-empty ¬kp = (\()) , (\())
  raw-finmap-remove-HasKV m@(raw-finmap-cons k3 v3 m') {k1} {k2} {v2} ¬k1=k2 with (decide-= k1 k3)
  ... | (yes k1=k3) = forward , backward
    where
    forward : (RawFinMap-HasKV m k2 v2) -> (RawFinMap-HasKV (raw-finmap-remove m' k1) k2 v2)
    forward (raw-finmap-haskv-head k3=k2 vp) = bot-elim (¬k1=k2 (k1=k3 >=> k3=k2))
    forward (raw-finmap-haskv-cons k3!=k2 hkv) = proj₁ (raw-finmap-remove-HasKV m' ¬k1=k2) hkv
    backward : (RawFinMap-HasKV (raw-finmap-remove m' k1) k2 v2) -> (RawFinMap-HasKV m k2 v2)
    backward hkv = raw-finmap-haskv-cons (\k3=k2 -> ¬k1=k2 (k1=k3 >=> k3=k2))
                                         (proj₂ (raw-finmap-remove-HasKV m' ¬k1=k2) hkv)

  ... | (no k1!=k3) = forward , backward
    where
    forward : (RawFinMap-HasKV m k2 v2) ->
              (RawFinMap-HasKV (raw-finmap-cons k3 v3 (raw-finmap-remove m' k1)) k2 v2)
    forward (raw-finmap-haskv-head kp vp) = (raw-finmap-haskv-head kp vp)
    forward (raw-finmap-haskv-cons k3!=k2 hkv) =
      raw-finmap-haskv-cons k3!=k2 (proj₁ (raw-finmap-remove-HasKV m' ¬k1=k2) hkv)

    backward : (RawFinMap-HasKV (raw-finmap-cons k3 v3 (raw-finmap-remove m' k1)) k2 v2) ->
               (RawFinMap-HasKV m k2 v2)
    backward (raw-finmap-haskv-head kp vp) = (raw-finmap-haskv-head kp vp)
    backward (raw-finmap-haskv-cons k3!=k2 hkv) =
      raw-finmap-haskv-cons k3!=k2 (proj₂ (raw-finmap-remove-HasKV m' ¬k1=k2) hkv)


  RawFinMap-SameKVs : RawFinMap K V -> RawFinMap K V -> Type (ℓ-max ℓK ℓV)
  RawFinMap-SameKVs m1 m2 = ∀ k v -> (RawFinMap-HasKV m1 k v) <-> (RawFinMap-HasKV m2 k v)

  raw-finmap-uniquify : (m : RawFinMap K V) ->
    Σ[ m2 ∈  RawFinMap K V ] (RawFinMap-SameKVs m m2 × RawFinMap-HasUniqueKeys m2)
  raw-finmap-uniquify m =
    loop m (raw-finmap-size m) refl-≤ ,
    loop-SameKVs m (raw-finmap-size m) refl-≤ ,
    loop-UniqueKeys m (raw-finmap-size m) refl-≤
    where
    loop :  (m : RawFinMap K V) (n : Nat) -> raw-finmap-size m ≤ n -> RawFinMap K V
    loop raw-finmap-empty _ _ = raw-finmap-empty
    loop (raw-finmap-cons k v m) zero lt = bot-elim (zero-≮ lt)
    loop (raw-finmap-cons k v m) (suc n) lt =
      raw-finmap-cons k v (loop (raw-finmap-remove m k) n
                                (trans-≤ (raw-finmap-remove-size≤ m k) (pred-≤ lt)))

    loop-SameKVs :
      (m : RawFinMap K V) (n : Nat) -> (lt : raw-finmap-size m ≤ n) ->
      ∀ k v -> (RawFinMap-HasKV m k v <-> RawFinMap-HasKV (loop m n lt) k v)
    loop-SameKVs raw-finmap-empty _ _ k v = (\()) , (\())
    loop-SameKVs (raw-finmap-cons k2 v2 m) zero lt k v = bot-elim (zero-≮ lt)
    loop-SameKVs m@(raw-finmap-cons k2 v2 m') n@(suc n') lt k v = forward , backward
      where
      forward : (RawFinMap-HasKV m k v -> RawFinMap-HasKV (loop m n lt) k v)
      forward (raw-finmap-haskv-head k2=k v2=v) = (raw-finmap-haskv-head k2=k v2=v)
      forward (raw-finmap-haskv-cons k2!=k hkv) =
        raw-finmap-haskv-cons k2!=k
          (proj₁ (loop-SameKVs (raw-finmap-remove m' k2) n'
                   (trans-≤ (raw-finmap-remove-size≤ m' k2) (pred-≤ lt)) k v)
                 (proj₁ (raw-finmap-remove-HasKV m' k2!=k) hkv))
      backward : (RawFinMap-HasKV (loop m n lt) k v -> RawFinMap-HasKV m k v)
      backward (raw-finmap-haskv-head k2=k v2=v) = (raw-finmap-haskv-head k2=k v2=v)
      backward (raw-finmap-haskv-cons k2!=k hkv) =
        raw-finmap-haskv-cons k2!=k
          (proj₂ (raw-finmap-remove-HasKV m' k2!=k)
                 (proj₂ (loop-SameKVs (raw-finmap-remove m' k2) n'
                                     (trans-≤ (raw-finmap-remove-size≤ m' k2) (pred-≤ lt)) k v)
                        hkv))

    loop-UniqueKeys :
      (m : RawFinMap K V) (n : Nat) -> (lt : raw-finmap-size m ≤ n) ->
      RawFinMap-HasUniqueKeys (loop m n lt)
    loop-UniqueKeys raw-finmap-empty _ _ =
      raw-finmap-unique-empty
    loop-UniqueKeys (raw-finmap-cons k v m) zero lt = bot-elim (zero-≮ lt)
    loop-UniqueKeys (raw-finmap-cons k v m) (suc n) lt =
      raw-finmap-unique-cons
        (\(v , hk) ->
          (raw-finmap-remove-¬HasKey m k)
          (v , (proj₂ (loop-SameKVs (raw-finmap-remove m k) n lt' k v) hk)))
        (loop-UniqueKeys (raw-finmap-remove m k) n lt')
      where
      lt' = (trans-≤ (raw-finmap-remove-size≤ m k) (pred-≤ lt))


  -- Left biased merge
  raw-finmap-merge : RawFinMap K V -> RawFinMap K V -> RawFinMap K V
  raw-finmap-merge raw-finmap-empty m2 = m2
  raw-finmap-merge (raw-finmap-cons k v m1) m2 = raw-finmap-cons k v (raw-finmap-merge m1 m2)

  -- module _ (m1 m2 : RawFinMap K V) {k : K} {v : V} where
  --   private
  --     AnsL : (m1 m2 : RawFinMap K V) -> Type ℓKV
  --     AnsL m1 m2 = RawFinMap-HasKV (raw-finmap-merge m1 m2) k v
  --     AnsR : (m1 m2 : RawFinMap K V) -> Type ℓKV
  --     AnsR m1 m2 = (RawFinMap-HasKV m1 k v ⊎ (¬ (RawFinMap-HasKV m1 k v) × (RawFinMap-HasKV m2 k v)))

  --   raw-finmap-merge-HasKV : AnsL m1 m2 <-> AnsR m1 m2
  --   raw-finmap-merge-HasKV = forward m1 m2 , backward m1 m2
  --     where
  --     forward : (m1 m2 : RawFinMap K V) -> AnsL m1 m2 -> AnsR m1 m2
  --     forward raw-finmap-empty _ hkv = inj-r ((\()) , hkv)
  --     forward (raw-finmap-cons k v m1) m2 (raw-finmap-haskv-head kp vp) =
  --       inj-l (raw-finmap-haskv-head kp vp)
  --     forward m1@(raw-finmap-cons k2 v2 m1') m2 (raw-finmap-haskv-cons ¬kp hkv) =
  --       handle (forward m1' m2 hkv)
  --       where
  --       handle : AnsR m1' m2 -> AnsR m1 m2
  --       handle (inj-l hkv) = (inj-l (raw-finmap-haskv-cons ¬kp hkv))
  --       handle (inj-r (¬hkv1' , hkv2)) = inj-r (¬hkv1 , hkv2)
  --         where
  --         ¬hkv1 : ¬ (RawFinMap-HasKV m1 k v)
  --         ¬hkv1 (raw-finmap-haskv-head kp _) = bot-elim (¬kp kp)
  --         ¬hkv1 (raw-finmap-haskv-cons _ hkv1') = bot-elim (¬hkv1' hkv1')

  --     backward : (m1 m2 : RawFinMap K V) -> AnsR m1 m2 -> AnsL m1 m2
  --     backward m1 m2 (inj-l (raw-finmap-haskv-head kp vp)) = (raw-finmap-haskv-head kp vp)
  --     backward m1 m2 (inj-l (raw-finmap-haskv-cons ¬kp hkv)) = ?
  --     backward m1 m2 (inj-r ( (raw-finmap-haskv-cons ¬kp hkv)) = ?


  -- module _ (magic : Bot) where
  --   private
  --     Ans : RawFinMap K V -> Type ℓKV
  --     Ans m = Σ[ m2 ∈ RawFinMap K V ]
  --             (SameFinMap-Steps m m2) × (RawFinMap-HasUniqueKeys m2)
  --   RawFinMap-UniqueKeys : (m : RawFinMap K V) -> Ans m
  --   RawFinMap-UniqueKeys m = loop m (WF-Smaller m)
  --     where
  --     Smaller : Rel (RawFinMap K V) ℓKV
  --     Smaller _ _ = bot-elim magic
  --     WF-Smaller : WellFounded Smaller
  --     WF-Smaller = bot-elim magic
  --     loop : (m : RawFinMap K V) -> Acc Smaller m -> Ans m
  --     loop (raw-finmap-empty) (acc f) = raw-finmap-empty , trc-refl , raw-finmap-unique-empty
  --     loop (raw-finmap-cons k v m') (acc f) =
  --       (raw-finmap-cons k v m2') ,
  --       SameFinMap-Steps-cons k v steps' ,
  --       ?
  --       where
  --       rec : Ans m'
  --       rec = loop m' (f m' ?)
  --       m2' = fst rec
  --       steps' = fst (snd rec)
  --       unique' = snd (snd rec)




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

  SameFinMap-Steps->path : {m1 m2 : RawFinMap K V} -> SameFinMap-Steps m1 m2 ->
                           Path (FinMap K V) [ m1 ] [ m2 ]
  SameFinMap-Steps->path trc-refl = refl
  SameFinMap-Steps->path (trc-rel r) = eq/ _ _ r
  SameFinMap-Steps->path (trc-trans r1 r2) =
    SameFinMap-Steps->path r1 >=> SameFinMap-Steps->path r2




module _ {K : Type ℓK} {V : Type ℓV} {{disc'K : Discrete' K}} {{isSet'V : isSet' V}} where
  private
    isSet-K : isSet K
    isSet-K = Discrete->isSet decide-=

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
    f (raw-finmap-cons k2 v m) = handle (decide-= k2 k)
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

  --module _ (magic : Bot) where
  --  FinMap-HasKV-path : (m1 m2 : FinMap K V) ->
  --                      (same : ∀ k v -> (FinMap-HasKV m1 k v) <-> (FinMap-HasKV m2 k v)) ->
  --                      m1 == m2
  --  FinMap-HasKV-path =  FinMapElim.elimProp2 (\m1 m2 -> isPropΠ (\_ -> squash/ m1 m2)) f
  --    where
  --    f : (m1 m2 : RawFinMap K V)
  --        (same : ∀ k v -> (RawFinMap-HasKV m1 k v) <-> (RawFinMap-HasKV m2 k v)) ->
  --        [ m1 ] == [ m2 ]
  --    f m1 m2 same = (SameFinMap-Steps->path ?)




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
