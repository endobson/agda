{-# OPTIONS --cubical --safe --exact-split #-}

module programming-languages.alpha-caml.alpha-equiv where

open import base
open import container.finmap
open import container.finmap.composition
open import container.finmap.remove
open import equality
open import functions
open import hlevel.base
open import list
open import nat
open import nat.order
open import order
open import order.instances.nat
open import programming-languages.alpha-caml
open import programming-languages.alpha-caml.multi-swap
open import programming-languages.alpha-caml.single-swap
open import programming-languages.renamings
open import relation
open import sum
open import truncation

    
data α-equiv : Rel Term ℓ-zero where
  var : (v : Atom) -> α-equiv (var v) (var v)
  const : (v : Atom) -> α-equiv (const v) (const v)
  empty : α-equiv empty empty
  branch : {t1 t2 t3 t4 : Term} -> α-equiv t1 t2 -> α-equiv t3 t4 ->
           α-equiv (branch t1 t3) (branch t2 t4)
  abstraction : {p1 p2 : Pattern} -> (p3 : Pattern) ->
    (r1 r2 : Renaming) -> 
    PatternRenaming p1 p3 r1 -> 
    PatternRenaming p2 p3 r2 -> 
    DisjointFinSet (atoms/pattern p3) (fm'-union (atoms/pattern p1) (atoms/pattern p2)) ->
    α-equiv (pattern/side outer p1) (pattern/side outer p2) ->
    α-equiv (use-renaming/term r1 (pattern/side inner p1))
            (use-renaming/term r2 (pattern/side inner p2)) ->
    α-equiv (abstraction p1) (abstraction p2)


private
  Reflexive-α-equiv' : (n : Nat) -> (t : Term) -> (term-depth t ≤ n) -> α-equiv t t
  Reflexive-α-equiv' _ (var v) lt = var v
  Reflexive-α-equiv' _ (const k) lt = const k 
  Reflexive-α-equiv' _ (empty) lt = empty
  Reflexive-α-equiv' zero (branch l r) lt = bot-elim (zero-≮ lt)
  Reflexive-α-equiv' (suc n) (branch l r) lt = 
    branch (Reflexive-α-equiv' n l (trans-≤ ≤-max-left (pred-≤ lt)))
           (Reflexive-α-equiv' n r (trans-≤ ≤-max-right (pred-≤ lt)))
  Reflexive-α-equiv' zero (abstraction p) lt = bot-elim (zero-≮ lt)
  Reflexive-α-equiv' (suc n) (abstraction p) lt = 
    let (p2 , r , pr , dis) = freshen-pattern p in
      abstraction p2 r r pr pr (DisjointKeys-fm'-union dis dis) 
        (Reflexive-α-equiv' n _ lt-outer)
        (Reflexive-α-equiv' n _ lt-inner)
      where
      r = (fst (snd (freshen-pattern p)))
      lt-outer : term-depth (pattern/side outer p) ≤ n
      lt-outer = trans-≤ (term-depth-pattern/side outer p) (pred-≤ lt)
      lt-inner : term-depth (use-renaming/term r (pattern/side inner p)) ≤ n
      lt-inner = trans-=-≤ (term-depth-use-renaming r _) 
                           (trans-≤ (term-depth-pattern/side inner p)
                                    (pred-≤ lt))

Reflexive-α-equiv : Reflexive α-equiv
Reflexive-α-equiv {t} = Reflexive-α-equiv' (term-depth t) t refl-≤

Symmetric-α-equiv : Symmetric α-equiv
Symmetric-α-equiv (var v) = (var v)
Symmetric-α-equiv (const v) = (const v)
Symmetric-α-equiv (empty) = (empty)
Symmetric-α-equiv (branch l r) = (branch (Symmetric-α-equiv l) (Symmetric-α-equiv r))
Symmetric-α-equiv (abstraction {p1} {p2} p3 r1 r2 pr1 pr2 disjoint outer-α inner-α) =
  (abstraction p3 r2 r1 pr2 pr1 disjoint' (Symmetric-α-equiv outer-α) (Symmetric-α-equiv inner-α))
  where
  disjoint' : DisjointFinSet (atoms/pattern p3) (fm'-union (atoms/pattern p2) (atoms/pattern p1))
  disjoint' hk3 hk21 = 
    disjoint hk3 (either (\{(v , hk) -> v , HasKV-fm'-union/right hk})
                         (\{(v , hk) -> v , HasKV-fm'-union/left hk})
                         (HasKey-fm'-union/split (atoms/pattern p2) (atoms/pattern p1) hk21))

α-equiv-single-swap :
  {t1 t2 : Term} -> (p : Atom × Atom) -> α-equiv t1 t2 -> 
  α-equiv (single-swap-term p t1) (single-swap-term p t2)
α-equiv-single-swap p (var v) = (var (single-swap-atom p v))
α-equiv-single-swap p (const v) = (const v)
α-equiv-single-swap p (empty) = (empty)
α-equiv-single-swap p (branch l r) = (branch (α-equiv-single-swap p l) (α-equiv-single-swap p r))
α-equiv-single-swap p (abstraction {p1} {p2} p3 r13 r23 pr13 pr23 disjoint outer-α inner-α) = 
  (abstraction p3' r13' r23' pr13' pr23' disjoint' outer-α' inner-α')
  where
  p1' = (single-swap-pattern p p1)
  p2' = (single-swap-pattern p p2)
  p3' = (single-swap-pattern p p3)
  r13' = single-swap-renaming p r13
  r23' = single-swap-renaming p r23
  pr13' = PatternRenaming-single-swap p pr13
  pr23' = PatternRenaming-single-swap p pr23
  dis31 : DisjointFinSet (atoms/pattern p3) (atoms/pattern p1)
  dis31 hk3 (v , hkv1) = disjoint hk3 (v , HasKV-fm'-union/left hkv1)
  dis31' : DisjointFinSet (atoms/pattern p3') (atoms/pattern p1')
  dis31' = subst2 DisjointFinSet
            (single-swap-finset-atoms/pattern p p3)
            (single-swap-finset-atoms/pattern p p1)
            (DisjointFinSet-single-swap-finset p dis31)

  dis32 : DisjointFinSet (atoms/pattern p3) (atoms/pattern p2)
  dis32 hk3 (v , hkv2) = disjoint hk3 (v , HasKV-fm'-union/right hkv2)
  dis32' : DisjointFinSet (atoms/pattern p3') (atoms/pattern p2')
  dis32' = subst2 DisjointFinSet
            (single-swap-finset-atoms/pattern p p3)
            (single-swap-finset-atoms/pattern p p2)
            (DisjointFinSet-single-swap-finset p dis32)

  disjoint' : DisjointFinSet (atoms/pattern p3') (fm'-union (atoms/pattern p1') (atoms/pattern p2'))
  disjoint' hk3 (v , hkv12) = 
    case (HasKV-fm'-union/split (atoms/pattern p1') (atoms/pattern p2') hkv12) of (\{
      (inj-l hkv1) -> dis31' hk3 (v , hkv1) ;
      (inj-r hkv2) -> dis32' hk3 (v , hkv2) })


  outer-α' = subst2 α-equiv (single-swap-term-pattern/side p outer p1) 
                            (single-swap-term-pattern/side p outer p2)
             (α-equiv-single-swap p outer-α)
  inner-α' = subst2 α-equiv 
                    (single-swap-term-use-renaming/term p r13 >=> 
                     cong (use-renaming/term r13') (single-swap-term-pattern/side p inner p1))
                    (single-swap-term-use-renaming/term p r23 >=> 
                     cong (use-renaming/term r23') (single-swap-term-pattern/side p inner p2))
             (α-equiv-single-swap p inner-α)

α-equiv-multi-swap :
  {t1 t2 : Term} -> (ps : List (Atom × Atom)) -> α-equiv t1 t2 -> 
  α-equiv (multi-swap-term ps t1) (multi-swap-term ps t2)
α-equiv-multi-swap [] a = a
α-equiv-multi-swap (p :: ps) a = α-equiv-single-swap p (α-equiv-multi-swap ps a)


-- find-swaps-renaming/term : 
--   (r : Renaming) -> (t : Term) -> 
--   DisjointFinSet (renaming-source-atoms r) (renaming-target-atoms r) ->
--   DisjointFinSet (renaming-target-atoms r) (atoms/term t) ->
--   Σ[ ps ∈ List (Atom × Atom) ] 
--     (use-renaming/term r t == multi-swap-term ps t)
-- find-swaps-renaming/term (m , r) t dis1 dis2 = handle m r dis1 dis2
--   where
--   handle : (m : FinMap' Atom Atom) (r : isRenaming m) ->
--            DisjointFinSet (renaming-source-atoms (m , r)) (renaming-target-atoms (m , r)) ->
--            DisjointFinSet (renaming-target-atoms (m , r)) (atoms/term t) ->
--            Σ[ ps ∈ List (Atom × Atom) ] 
--              (use-renaming/term (m , r) t == multi-swap-term ps t)
--   handle [] r dis1 dis2 = [] , rename-atom/term-identity t
--   handle m@(fm-cons k v m') r dis1 dis2 =
--     let 
--         dis1' : DisjointFinSet (renaming-source-atoms (m' , r')) (renaming-target-atoms (m' , r'))
--         dis1' hk1 hk2 = dis1 (HasKey'-skip hk1) (HasKey'-skip hk2)
--         dis2' : DisjointFinSet (renaming-target-atoms (m' , r')) (atoms/term t)
--         dis2' hk1 hk2 = dis2 (HasKey'-skip hk1) hk2
--         (ps , path) = handle m' r' dis1' dis2'
--     in ((k , v) :: ps) , path2 >=> cong (single-swap-term (k , v)) path
--     where
--     r' = (isBijectiveFinMap'-rest _ r) 
--     same-f : (a : Atom) -> HasKey' a (atoms/term t) -> 
--              (use-renaming (m , r) a) ==
--              (single-swap-atom (k , v) (use-renaming (m' , r') a))
--     same-f a hk-at = handle2 (lookup' a m)
--       where
--       handle2 : Dec (HasKey' a m) -> 
--                 (use-renaming (m , r) a) ==
--                 (single-swap-atom (k , v) (use-renaming (m' , r') a))
--       handle2 (yes (v2 , hk-am@(has-kv-here kp vp _))) =
--         use-renaming-HasKV (m , r) hk-am >=> vp >=>
--         ? >=>
--         cong (single-swap-atom (k , v)) (sym (use-renaming-¬HasKey (m' , r') ?))
--         where
--         ¬hk-m' : 
-- 
-- 
--     path3 : (rename-atom/term (use-renaming (fm-cons k v m' , r)) t) ==
--             (rename-atom/term (single-swap-atom (k , v) ∘ (use-renaming (m' , r'))) t)
--     path3 = rename-atom/term-support t same-f
-- 
-- 
--     path2 : (use-renaming/term (fm-cons k v m' , r) t) ==
--             (single-swap-term (k , v) (use-renaming/term (m' , r') t))
--     path2 = path3 >=> sym (rename-atom/term-compose (single-swap-atom (k , v)) (use-renaming (m' , r')) t)

--find-swaps-renaming/term (fm-cons k v m , r) t dis = ?

-- swaps-for-finmap' : (m : FinMap' Atom Atom) -> List (Atom × Atom)
-- swaps-for-finmap' [] = []
-- swaps-for-finmap' (fm-cons k v m) = 
--   (k , v) :: swaps-for-finmap' (finmap'-remove k m)


-- swaps-for-renaming : (r : Renaming) -> List (Atom × Atom)
-- swaps-for-renaming (m , _) = swaps-for-finmap' m

module _
  (swaps-for-renaming : (r : Renaming) -> List (Atom × Atom))
  (multi-swap-term-swaps-for-renaming : 
    (r : Renaming) -> 
    (t : Term) ->
    DisjointFinSet (renaming-target-atoms r) (atoms/term t) ->
    DisjointFinSet (renaming-source-atoms r) (renaming-target-atoms r) ->
    (use-renaming/term r t == multi-swap-term (swaps-for-renaming r) t))
  (α-equiv-use-renaming :
    (r : Renaming) -> 
    {t1 t2 : Term} ->
    (α-equiv t1 t2) ->
    α-equiv (use-renaming/term r t1) (use-renaming/term r t2))
  (use-renaming/term-invert-renaming :
    (r : Renaming) -> 
    {t : Term} ->
    (use-renaming/term (invert-renaming r) (use-renaming/term r t)) == t)
  (magic : {ℓ : Level} -> {A : Type ℓ} -> A)
  where

  private
    α-equiv-use-renaming' :
      (r : Renaming) -> 
      {t1 t2 : Term} ->
      DisjointFinSet (renaming-target-atoms r) (atoms/term t1) ->
      DisjointFinSet (renaming-target-atoms r) (atoms/term t2) ->
      DisjointFinSet (renaming-source-atoms r) (renaming-target-atoms r) ->
      (α-equiv t1 t2) ->
      α-equiv (use-renaming/term r t1) (use-renaming/term r t2)
    α-equiv-use-renaming' r dis-rt1 dis-rt2 dis-r α-eq =
      subst2 α-equiv
             (sym (multi-swap-term-swaps-for-renaming r _ dis-rt1 dis-r))
             (sym (multi-swap-term-swaps-for-renaming r _ dis-rt2 dis-r))
             (α-equiv-multi-swap (swaps-for-renaming r) α-eq)
      


  Transitive-α-equiv' : (n : Nat) -> {t1 t2 t3 : Term} -> 
    (term-depth t1 ≤ n) -> α-equiv t1 t2 -> α-equiv t2 t3 -> α-equiv t1 t3
  Transitive-α-equiv' _ _ (var v) (var v) = (var v)
  Transitive-α-equiv' _ _ (const v) (const v) = (const v)
  Transitive-α-equiv' _ _ (empty) (empty) = (empty)
  Transitive-α-equiv' zero lt (branch l1 r1) (branch l2 r2) = 
    bot-elim (zero-≮ lt)
  Transitive-α-equiv' (suc n) lt (branch l1 r1) (branch l2 r2) = 
    (branch (Transitive-α-equiv' n (trans-≤ ≤-max-left (pred-≤ lt)) l1 l2) 
            (Transitive-α-equiv' n (trans-≤ ≤-max-right (pred-≤ lt)) r1 r2))
  Transitive-α-equiv' zero lt (abstraction _ _ _ _ _ _ _ _) (abstraction _ _ _ _ _ _ _ _) = 
    bot-elim (zero-≮ lt)
  Transitive-α-equiv' (suc n) lt
    (abstraction {p1} {p2} p4 l-r1 l-r2 l-pr1 l-pr2 l-disjoint l-outer l-inner)
    (abstraction {p2} {p3} p5 r-r1 r-r2 r-pr1 r-pr2 r-disjoint r-outer r-inner) = 
    (abstraction p6 r1 r3 pr1 pr3 disjoint 
      (Transitive-α-equiv' n (trans-≤ (term-depth-pattern/side outer p1) (pred-≤ lt)) l-outer r-outer)
      α-renamed)
    where
    source : FinSet Atom
    source = (atoms/pattern p2)
    avoid : FinSet Atom
    avoid = fm'-union (atoms/pattern p1) (atoms/pattern p3)

    full-rename : Σ[ r ∈ Renaming ] (
                    (DisjointFinSet (renaming-target-atoms r) avoid) ×
                    (∀ k -> HasKey' k source -> HasKey' k ⟨ r ⟩))
    full-rename = find-fresh-rename source avoid

    Σpr2 : Σ[ p6 ∈ Pattern ] Σ[ r ∈ Renaming ] 
             (PatternRenaming p2 p6 r × 
              DisjointFinSet (atoms/pattern p6) avoid)
    Σpr2 = magic

    p6 : Pattern
    p6 = fst Σpr2
    r26 : Renaming
    r26 = fst (snd Σpr2)
    pr26 : PatternRenaming p2 p6 r26
    pr26 = (fst (snd (snd Σpr2)))

    tpat-l-12 = transitive-PatternRenaming l-pr1 (invert-PatternRenaming l-pr2)

    Σpr1 : Σ Renaming (PatternRenaming p1 p6)
    Σpr1 = fst ans2 , (snd (snd ans2))
      where
      ans1 = transitive-PatternRenaming l-pr1 (invert-PatternRenaming l-pr2)
      ans2 = transitive-PatternRenaming (snd (snd ans1)) pr26
    Σpr3 : Σ Renaming (PatternRenaming p3 p6)
    Σpr3 = fst ans2 , (snd (snd ans2))
      where
      ans1 = transitive-PatternRenaming r-pr2 (invert-PatternRenaming r-pr1)
      ans2 = transitive-PatternRenaming (snd (snd ans1)) pr26
  
    r1 : Renaming
    r3 : Renaming
    r1 = fst Σpr1
    r3 = fst Σpr3

  
    pr1 : PatternRenaming p1 p6 r1
    pr3 : PatternRenaming p3 p6 r3
    pr1 = snd Σpr1
    pr3 = snd Σpr3

    disjoint : DisjointFinSet (atoms/pattern p6) (fm'-union (atoms/pattern p1) (atoms/pattern p3))
    disjoint = snd (snd (snd Σpr2))


    l-r2i = invert-renaming l-r2
    r-r1i = invert-renaming r-r1

    check-l-inner : α-equiv (use-renaming/term l-r1 (pattern/side inner p1))
                            (use-renaming/term l-r2 (pattern/side inner p2))
    check-l-inner = l-inner

    check-r-inner : α-equiv (use-renaming/term r-r1 (pattern/side inner p2))
                            (use-renaming/term r-r2 (pattern/side inner p3))
    check-r-inner = r-inner
 
    α-step1 : α-equiv (use-renaming/term l-r2i (use-renaming/term l-r1 (pattern/side inner p1)))
                      (pattern/side inner p2)
    α-step1 = 
      subst (\t -> α-equiv (use-renaming/term l-r2i (use-renaming/term l-r1 (pattern/side inner p1)))
                           t)
            (use-renaming/term-invert-renaming l-r2) 
            (α-equiv-use-renaming' l-r2i magic magic magic l-inner)
    α-step2 : α-equiv (pattern/side inner p2)
                      (use-renaming/term r-r1i (use-renaming/term r-r2 (pattern/side inner p3)))
    α-step2 = 
      subst (\t -> α-equiv t 
                           (use-renaming/term r-r1i (use-renaming/term r-r2 (pattern/side inner p3))))
            (use-renaming/term-invert-renaming r-r1) 
            (α-equiv-use-renaming' r-r1i magic magic magic r-inner)
    α-step3 : α-equiv (use-renaming/term l-r2i (use-renaming/term l-r1 (pattern/side inner p1)))
                      (use-renaming/term r-r1i (use-renaming/term r-r2 (pattern/side inner p3)))
    α-step3 = Transitive-α-equiv' n lt' α-step1 α-step2
      where
      lt' : term-depth (use-renaming/term l-r2i (use-renaming/term l-r1 (pattern/side inner p1))) ≤ n
      lt' = trans-=-≤ ((term-depth-use-renaming l-r2i _) >=>
                       (term-depth-use-renaming l-r1 _))
                      (trans-≤ (term-depth-pattern/side inner p1)
                               (pred-≤ lt))


    α-step4 :
      α-equiv 
        (use-renaming/term r26 (use-renaming/term l-r2i (use-renaming/term l-r1 (pattern/side inner p1))))
        (use-renaming/term r26 (use-renaming/term r-r1i (use-renaming/term r-r2 (pattern/side inner p3))))
    α-step4 = (α-equiv-use-renaming' r26 magic magic magic α-step3)

    α-renamed : α-equiv (use-renaming/term r1 (pattern/side inner p1))
                        (use-renaming/term r3 (pattern/side inner p3))
    α-renamed = 
      subst2 α-equiv path1 path3 α-step4
      where
      fun1 : (a : Atom) -> (HasKey' a (atoms/term (pattern/side inner p1))) ->
             (use-renaming r26 (use-renaming l-r2i (use-renaming l-r1 a))) == 
             (use-renaming r1 a)
      fun1 a (v , hkv) = magic
      path1 : (use-renaming/term r26 (use-renaming/term l-r2i 
                (use-renaming/term l-r1 (pattern/side inner p1)))) == 
              (use-renaming/term r1 (pattern/side inner p1))
      path1 = rename-atom/term-compose _ _ _ >=> 
              rename-atom/term-compose _ _ _ >=>
              rename-atom/term-support _ fun1

      fun3 : (a : Atom) -> (HasKey' a (atoms/term (pattern/side inner p3))) ->
             (use-renaming r26 (use-renaming r-r1i (use-renaming r-r2 a))) ==
             (use-renaming r3 a)
      fun3 a (v , hkv) = magic
      path3 : (use-renaming/term r26 (use-renaming/term r-r1i 
                (use-renaming/term r-r2 (pattern/side inner p3)))) == 
              (use-renaming/term r3 (pattern/side inner p3))
      path3 = rename-atom/term-compose _ _ _ >=> 
              rename-atom/term-compose _ _ _ >=>
              rename-atom/term-support _ fun3

  Transitive-α-equiv : Transitive α-equiv
  Transitive-α-equiv {t1} = Transitive-α-equiv' (term-depth t1) refl-≤
