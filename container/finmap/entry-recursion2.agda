{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.entry-recursion2 where

open import base
open import container.finmap
open import cubical
open import equality-path
open import fin-algebra
open import finset
open import finset.instances
open import functions
open import hlevel
open import relation
open import subfinite
open import subfinite.discrete
open import sum
open import truncation
open import isomorphism
open import equivalence


-- doubleCompPath-refl-swap23 : 
--   {ℓ : Level} {A : Type ℓ} {a1 a2 a3 : A} ->
--   (p1 : a1 == a2) (p2 : a2 == a3) ->
--   (p1 ∙∙ refl ∙∙ p2) ==
--   (p1 ∙∙ p2 ∙∙ refl)
-- doubleCompPath-refl-swap23 p1 p2 i = p1 ∙∙ (\j -> p2 (j ∧ i)) ∙∙ (\j -> p2 (j ∨ i))
-- 
-- doubleCompPath-refl-swap12 : 
--   {ℓ : Level} {A : Type ℓ} {a1 a2 a3 : A} ->
--   (p1 : a1 == a2) (p2 : a2 == a3) ->
--   (p1 ∙∙ refl ∙∙ p2) ==
--   (refl ∙∙ p1 ∙∙ p2)
-- doubleCompPath-refl-swap12 p1 p2 i = (\j -> p1 (j ∧ (~ i))) ∙∙ (\j -> p1 (j ∨ (~ i))) ∙∙ p2
-- 
-- 
-- doubleCompPath-refl-collapse13 : 
--   {ℓ : Level} {A : Type ℓ} {a1 a2 : A} ->
--   (p1 : a1 == a2) ->
--   (refl ∙∙ p1 ∙∙ refl) == p1
-- doubleCompPath-refl-collapse13 p1 = sym (doubleCompPath-filler refl p1 refl)
-- 
-- doubleCompPath-refl-collapse23 : 
--   {ℓ : Level} {A : Type ℓ} {a1 a2 : A} ->
--   (p1 : a1 == a2) ->
--   (p1 ∙∙ refl ∙∙ refl) == p1
-- doubleCompPath-refl-collapse23 p1 = 
--   doubleCompPath-refl-swap12 p1 refl >=> doubleCompPath-refl-collapse13 p1
-- 
-- doubleCompPath-refl-collapse12 : 
--   {ℓ : Level} {A : Type ℓ} {a1 a2 : A} ->
--   (p1 : a1 == a2) ->
--   (refl ∙∙ refl ∙∙ p1) == p1
-- doubleCompPath-refl-collapse12 p1 = 
--   doubleCompPath-refl-swap23 refl p1 >=> doubleCompPath-refl-collapse13 p1
-- 
-- 
-- doubleCompPath-pathP-extract1 : 
--   {ℓ : Level} {A : Type ℓ} {a1 a2 a3 a4 : A} ->
--   (p1 : a1 == a2) (p2 : a2 == a3) (p3 : a3 == a4) ->
--   PathP (\i -> p1 i == a4) 
--         (p1 ∙∙ p2 ∙∙ p3) (refl ∙∙ p2 ∙∙ p3)
-- doubleCompPath-pathP-extract1 p1 p2 p3 i = (\j -> p1 (i ∨ j)) ∙∙ p2 ∙∙ p3
-- 
-- doubleCompPath-pathP-extract3 : 
--   {ℓ : Level} {A : Type ℓ} {a1 a2 a3 a4 : A} ->
--   (p1 : a1 == a2) (p2 : a2 == a3) (p3 : a3 == a4) ->
--   PathP (\i -> a1 == p3 (~ i)) 
--         (p1 ∙∙ p2 ∙∙ p3) (p1 ∙∙ p2 ∙∙ refl)
-- doubleCompPath-pathP-extract3 p1 p2 p3 i = p1 ∙∙ p2 ∙∙ (\j -> p3 ((~ i) ∧ j))
-- 
-- 
-- doubleCompPath-assoc : 
--   {ℓ : Level} {A : Type ℓ} {a1 a2 a3 a4 : A} ->
--   (p1 : a1 == a2) (p2 : a2 == a3) (p3 : a3 == a4) ->
--   ((p1 ∙∙ refl ∙∙ p2) ∙∙ refl ∙∙ p3) ==
--   (p1 ∙∙ refl ∙∙ (p2 ∙∙ refl ∙∙ p3))
-- doubleCompPath-assoc {A = A} {a1} {a2} {a3} {a4} p1 p2 p3 = t3
--   where
--   t1 : PathP (\i -> a1 == p2 (~ i)) (p1 ∙∙ refl ∙∙ p2) p1
--   t1 = transP-left (doubleCompPath-pathP-extract3 p1 refl p2) (doubleCompPath-refl-collapse23 p1)
-- 
--   t2 : PathP (\i -> p2 i == a4) (p2 ∙∙ refl ∙∙ p3) p3
--   t2 = transP-left (doubleCompPath-pathP-extract1 p2 refl p3) (doubleCompPath-refl-collapse12 p3)
-- 
--   t3 : Path (Path A a1 a4) ((p1 ∙∙ refl ∙∙ p2) ∙∙ refl ∙∙ p3) (p1 ∙∙ refl ∙∙ (p2 ∙∙ refl ∙∙ p3))
--   t3 i = t1 i ∙∙ refl ∙∙ (t2 (~ i))
-- 
-- 
-- pathP-refl-left : {ℓ : Level} {A : Type ℓ} {a1 a2 : A} (p : a1 == a2) ->
--                   PathP (\i -> a1 == p i) refl p
-- pathP-refl-left p i j = p (i ∧ j)



-- compPath-assoc : {ℓ : Level} {A : Type ℓ} {x y z w : A} ->
--                  (p : x == y) (q : y == z) (r : z == w) ->
--                  (p >=> q) >=> r == p >=> (q >=> r)
-- compPath-assoc = ?


module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} where
  AllEntries : Pred (FinMap' K V)  _
  AllEntries m = Σ[ k ∈ K ] Σ[ v ∈ V ] (HasKV' k v m)

  private
    hasKV-index : {k : K} {v : V} {m : FinMap' K V} -> (HasKV' k v m) -> FinT (fm'-size m)
    hasKV-index (has-kv-here _ _ _) = inj-l tt
    hasKV-index (has-kv-skip _ _ hkv) = inj-r (hasKV-index hkv)

    entry->index : {m : FinMap' K V} -> AllEntries m -> FinT (fm'-size m)
    entry->index (_ , _ , hkv) = hasKV-index hkv

    entry-skip : {m : FinMap' K V} (k2 : K) (v2 : V) ->
                 AllEntries m ->
                 AllEntries (fm-cons k2 v2 m)
    entry-skip k2 v2 (k , v , hk) = k , v , has-kv-skip k2 v2 hk

    index->entry : (m : FinMap' K V) -> FinT (fm'-size m) -> AllEntries m
    index->entry (fm-cons k v m) (inj-l tt) = k , v , has-kv-here refl refl m
    index->entry (fm-cons k v m) (inj-r i) = entry-skip k v (index->entry m i)

    ie-ei : (m : FinMap' K V) -> (e : AllEntries m) -> index->entry m (entry->index e) == e
    ie-ei (fm-cons k v m) (k2 , v2 , has-kv-here kp vp m) i = 
      kp (~ i) , vp (~ i) , has-kv-here (\j -> kp (j ∨ (~ i))) (\j -> vp (j ∨ (~ i))) m
    ie-ei (fm-cons k v m) (k2 , v2 , has-kv-skip kp vp hkv) = 
      cong (entry-skip k v) (ie-ei m (k2 , v2 , hkv))

    ei-ie : (m : FinMap' K V) -> (i : FinT (fm'-size m)) -> entry->index (index->entry m i) == i
    ei-ie (fm-cons k v m) (inj-l tt) = refl
    ei-ie (fm-cons k v m) (inj-r i) = cong inj-r (ei-ie m i)

  isFinSet-AllEntries : (m : FinMap' K V) -> isFinSet (AllEntries m)
  isFinSet-AllEntries m = ∣ n , isoToEquiv i >eq> pathToEquiv (FinT=Fin n) ∣
    where
    n = fm'-size m 
    i : Iso (AllEntries m) (FinT n)
    i = iso entry->index (index->entry m) (ei-ie m) (ie-ei m)


  private
    remove-skip : {k : K} {v : V} {k2 : K} {v2 : V} {m : FinMap' K V} -> 
                  (hkv : HasKV' k2 v2 (fm-cons k v m)) -> 
                  Right (hasKV-index hkv) -> HasKV' k2 v2 m
    remove-skip (has-kv-skip _ _ hk) _ = hk
                  

    has-kv-here!=skip : {k k2 : K} {v v2 : V} {m : FinMap' K V} {kp : k2 == k} {vp : v2 == v} 
                        {hk : HasKV' k2 v2 m} -> 
                        ¬ (Path (HasKV' k2 v2 (fm-cons k v m)) 
                                (has-kv-here kp vp m) (has-kv-skip k v hk))
    has-kv-here!=skip p = inj-l!=inj-r (cong hasKV-index p)



    module _ {k1 k2 k3 : K} {v1 v2 v3 : V} {m : FinMap' K V}
             (kp2 : k2 == k1) (kp3 : k3 == k1) 
             (vp2 : v2 == v1) (vp3 : v3 == v1) where
      private
        kp : k2 == k3
        kp = kp2 >=> sym kp3
        vp : v2 == v3
        vp = vp2 >=> sym vp3

      kv-here-same : PathP (\i -> HasKV' (kp i) (vp i) (fm-cons k1 v1 m))
                           (has-kv-here kp2 vp2 m) (has-kv-here kp3 vp3 m)
      kv-here-same = (\i -> has-kv-here (kp-f2' i) (vp-f2' i) m)
        where
  
        kp-c : ((sym kp2) >=> kp) == (sym kp3)
        kp-c = sym (compPath-assoc (sym kp2) kp2 (sym kp3)) >=>
               cong (_>=> sym kp3) (compPath-sym (sym kp2)) >=>
               compPath-refl-left (sym kp3)
  
        vp-c : ((sym vp2) >=> vp) == (sym vp3)
        vp-c = sym (compPath-assoc (sym vp2) vp2 (sym vp3)) >=>
               cong (_>=> sym vp3) (compPath-sym (sym vp2)) >=>
               compPath-refl-left (sym vp3)
  
        kp-f : PathP (\i -> k1 == kp i) (sym kp2) ((sym kp2) >=> kp)
        kp-f = compPath-filler (sym kp2) kp
  
        kp-f2 : PathP (\i -> k1 == kp i) (sym kp2) (sym kp3)
        kp-f2 = transP-left kp-f kp-c
  
        kp-f2' : PathP (\i -> kp i == k1) kp2 kp3
        kp-f2' i j = kp-f2 i (~ j)
  
        vp-f : PathP (\i -> v1 == vp i) (sym vp2) ((sym vp2) >=> vp)
        vp-f = compPath-filler (sym vp2) vp
  
        vp-f2 : PathP (\i -> v1 == vp i) (sym vp2) (sym vp3)
        vp-f2 = transP-left vp-f vp-c
  
        vp-f2' : PathP (\i -> vp i == v1) vp2 vp3
        vp-f2' i j = vp-f2 i (~ j)


    inj-has-kv-skip : (k : K) (v : V) (m : FinMap' K V) (hkv1 : HasKV' k v m) (hkv2 : HasKV' k v m)
                      (k2 : K) (v2 : V) -> 
                      (has-kv-skip k2 v2 hkv1) == (has-kv-skip k2 v2 hkv2) ->
                      hkv1 == hkv2
    inj-has-kv-skip k v m hkv1 hkv2 k2 v2 p = \i -> remove-skip (p i) (p' i)
      where
      p' : PathP (\i -> Right (hasKV-index (p i))) tt tt
      p' = isProp->PathP (\i -> isProp-Right)

--    inj-hasKV-index : {k : K} {v : V} {m : FinMap' K V} -> (hkv1 hkv2 : HasKV' k v m) -> 
--                      (hasKV-index hkv1) == (hasKV-index hkv2) ->
--                      hkv1 == hkv2
--    inj-hasKV-index (has-kv-here kp2 vp2 m) (has-kv-skip k v hkv3) p =
--      bot-elim (inj-l!=inj-r p)
--    inj-hasKV-index (has-kv-skip k v hkv2) (has-kv-here kp3 vp3 m) p =
--      bot-elim (inj-l!=inj-r (sym p))
--    inj-hasKV-index (has-kv-skip k v hkv2) (has-kv-skip k v hkv3) p =
--      cong (has-kv-skip k v) (inj-hasKV-index hkv2 hkv3 (inj-r-injective p))


    inj-entry->index : (m : FinMap' K V) -> (e1 e2 : AllEntries m) ->
                       (entry->index e1) == (entry->index e2) ->
                       e1 == e2
    inj-entry->index (fm-cons k v m) (k2 , v2 , has-kv-here kp2 vp2 m) 
                                     (k3 , v3 , has-kv-here kp3 vp3 m) _ =
      (\i -> _ , _ , kv-here-same kp2 kp3 vp2 vp3 i)
    inj-entry->index (fm-cons k v m) (k2 , v2 , has-kv-skip k v hk2) 
                                     (k3 , v3 , has-kv-skip k v hk3) p  = handle rec
      where
      rec : (k2 , v2 , hk2) == (k3 , v3 , hk3)
      rec = inj-entry->index m (k2 , v2 , hk2) (k3 , v3 , hk3) (inj-r-injective p)

      handle : (k2 , v2 , hk2) == (k3 , v3 , hk3) ->
               (k2 , v2 , has-kv-skip k v hk2) == (k3 , v3 , has-kv-skip k v hk3)
      handle p i = fst (p i) , fst (snd (p i)) , has-kv-skip k v (snd (snd (p i)))
    inj-entry->index (fm-cons k v m) (k2 , v2 , has-kv-skip k v hk2) 
                                     (k3 , v3 , has-kv-here kp3 vp3 m) p = 
      bot-elim (inj-l!=inj-r (sym p))
    inj-entry->index (fm-cons k v m) (k2 , v2 , has-kv-here kp2 vp2 m) 
                                     (k3 , v3 , has-kv-skip k v hk2) p = 
      bot-elim (inj-l!=inj-r p)


    module _ (m : FinMap' K V) where
      isBFinSet-AllEntries : isBFinSet (AllEntries m) ℓ-zero
      isBFinSet-AllEntries = 
        ∣ FinSet-FinT (fm'-size m) , entry->index , (inj-entry->index m _ _) ∣







    Discrete-AllEntries : (m : FinMap' K V) -> Discrete (AllEntries m)
    Discrete-AllEntries m = isBFinSet->Discrete (isBFinSet-AllEntries m)

      













