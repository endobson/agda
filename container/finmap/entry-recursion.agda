{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.entry-recursion where

open import base
open import container.finmap
open import equality
open import equivalence
open import fin-algebra
open import finset
open import hlevel
open import isomorphism
open import relation
open import truncation
open import nat.order

module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV} where

  data EntryStructure (m : FinMap' K V) : Type (ℓ-max ℓK ℓV) where
    entries-empty : ¬(Σ[ k ∈ K ] HasKey' k m) -> EntryStructure m
    entries-cons : (k : K) (v : V) -> HasKV' k v m -> (m' : FinMap' K V) ->
                   (m' fm⊆ m) ->
                   ¬ (HasKV' k v m') ->
                   ({k2 : K} {v2 : V} -> (k != k2) -> (v != v2) -> HasKV' k2 v2 m
                                      -> HasKV' k2 v2 m) ->
                   EntryStructure m' ->
                   EntryStructure m

  private
    R : Rel (FinMap' K V) (ℓ-max ℓK ℓV)
    R = _fm⊂'_
    
    R< : Rel (FinMap' K V) (ℓ-max ℓK ℓV)
    R< = _fm⊂_

  ¬HasKV-[] : {k : K} {v : V} -> ¬ (HasKV' k v [])
  ¬HasKV-[] ()

  fm⊆-[] : (m : FinMap' K V) -> m fm⊆ [] -> m == []
  fm⊆-[] [] _ = refl
  fm⊆-[] m@(fm-cons k v _) sub = bot-elim (¬HasKV-[] (sub (has-kv-here refl refl _)))


  ¬fm⊂'-[] : (m : FinMap' K V) -> ¬ (m fm⊂' [])
  ¬fm⊂'-[] _ (_ , entry) = ¬HasKV-[] (proj₂ (∃!-prop entry))



  Acc-fm⊂'-[] : Acc R []
  Acc-fm⊂'-[] = acc (\y r -> bot-elim (¬fm⊂'-[] y r))

  module _ {{disc'K : Discrete' K}} where
    private
      discK = Discrete'.f disc'K

    --Acc-fm⊂' : ∀ m -> Acc R m
    --Acc-fm⊂' [] = Acc-fm⊂'-[]
    --Acc-fm⊂' m@(fm-cons k v m') = acc handle
    --  where
    --  am' = Acc-fm⊂' m'
    --  handle : (m2 : FinMap' K V) -> m2 fm⊂' m -> Acc R m2
    --  handle m2 m2<m = ?

      
    -- Acc1 : ∀ n m -> fm'-size m ≤ n -> Acc R< m
    -- Acc1 zero [] _ = ?

  module _ (R1 R2 : Rel (FinMap' K V) (ℓ-max ℓK ℓV)) 
           (R1->R2 : ∀ m1 m2 -> R1 m1 m2 -> R2 m1 m2) where
    AccR2->AccR1 : ∀ m -> Acc R2 m -> Acc R1 m
    AccR2->AccR1 m1 (acc f) = acc (\m2 r1 -> (AccR2->AccR1 m2 (f m2 (R1->R2 m2 m1 r1))))
    

  module _ {ℓA ℓAR ℓB ℓBR : Level} (A : Type ℓA) (B : Type ℓB) 
           (f : A -> B)
           (RA : Rel A ℓAR) (RB : Rel B ℓBR)
           (RA->RB : ∀ a1 a2 -> RA a1 a2 -> RB (f a1) (f a2)) where
    AccRB->AccRA : ∀ a -> Acc RB (f a) -> Acc RA a
    AccRB->AccRA a1 (acc g) = acc (\a2 ra2a1 -> AccRB->AccRA a2 (g (f a2) (RA->RB a2 a1 ra2a1)))

  UniqueEntries : Pred (FinMap' K V)  _
  UniqueEntries m = Σ[ k ∈ K ] Σ[ v ∈ V ] ∥ HasKV' k v m ∥

  AllEntries : Pred (FinMap' K V)  _
  AllEntries m = Σ[ k ∈ K ] Σ[ v ∈ V ] (HasKV' k v m)

  AllEntries->UniqueEntries : ∀ {m} -> AllEntries m -> UniqueEntries m
  AllEntries->UniqueEntries (k , v , hkv) = k , v , ∣ hkv ∣

  private
    A->U = AllEntries->UniqueEntries

  isSurjection-A->U : {m : FinMap' K V} -> isSurjection (A->U {m})
  isSurjection-A->U (k , v , hkv) =
    ∥-map (\hkv -> (k , v , hkv) , cong (\p -> k , v , p) (squash _ _)) hkv


  module _ {{disc'K : Discrete' K}} {{disc'V : Discrete' V}} where
    private
      discK = Discrete'.f disc'K
      discV = Discrete'.f disc'V

    open Iso
    Iso-AllEntries-FinT : ∀ m -> Iso (AllEntries m) (FinT (fm'-size m))
    Iso-AllEntries-FinT [] .fun (_ , _ , ())
    Iso-AllEntries-FinT [] .inv ()
    Iso-AllEntries-FinT [] .leftInv (_ , _ , ())
    Iso-AllEntries-FinT [] .rightInv ()
    Iso-AllEntries-FinT (fm-cons _ _ m) .fun (_ , _ , (has-kv-here _ _ m)) =
      inj-l tt
    Iso-AllEntries-FinT (fm-cons _ _ m) .fun (k , v , (has-kv-skip _ _ hkv)) =
      inj-r (Iso-AllEntries-FinT m .fun (k , v , hkv))
    Iso-AllEntries-FinT (fm-cons k v m) .inv (inj-l tt) = 
      k , v , has-kv-here refl refl m
    Iso-AllEntries-FinT (fm-cons _ _ m) .inv (inj-r i) =
      case (Iso-AllEntries-FinT m .inv i) of (\{(k , v , hkv) -> k , v , has-kv-skip _ _ hkv})
    Iso-AllEntries-FinT (fm-cons k1 v1 m) .leftInv (k2 , v2 , (has-kv-here kp vp m)) = 
      (\i -> kp (~ i) , (vp (~ i)) , (has-kv-here (kp' i) (vp' i) m))
      where
      kp' : PathP (\i -> (kp (~ i)) == k1) refl kp
      kp' = isProp->PathP (\_ -> Discrete->isSet discK _ _)
      vp' : PathP (\i -> (vp (~ i)) == v1) refl vp
      vp' = isProp->PathP (\_ -> Discrete->isSet discV _ _)
    Iso-AllEntries-FinT (fm-cons k1 v1 m) .leftInv (k2 , v2 , (has-kv-skip k3 v3 hkv)) = 
      \i -> case (rec i) of (\{(k , v , hkv) -> k , v , has-kv-skip _ _ hkv})
      where
      rec : (Iso-AllEntries-FinT m .inv
                     (Iso-AllEntries-FinT m .fun (k2 , v2 , hkv))) == (k2 , v2 , hkv)
      rec = Iso-AllEntries-FinT m .leftInv (k2 , v2 , hkv)
     
    Iso-AllEntries-FinT (fm-cons _ _ m) .rightInv (inj-l tt) = refl
    Iso-AllEntries-FinT (fm-cons _ _ m) .rightInv (inj-r i) =
      cong inj-r (Iso-AllEntries-FinT m .rightInv i)

    isFinSet-AllEntries : (m : FinMap' K V) -> isFinSet (AllEntries m)
    isFinSet-AllEntries m = ∣ fm'-size m , isoToEquiv (Iso-AllEntries-FinT m) >eq> 
                                           pathToEquiv (FinT=Fin _) ∣

  module _ (m1 m2 : FinMap' K V) (m1⊂m2 : m1 fm⊂ m2) where
    private
      Um1->Um2 : UniqueEntries m1 -> UniqueEntries m2
      Um1->Um2 (k , v , hkv) = k , v , ∥-map (proj₁ m1⊂m2) hkv
    


