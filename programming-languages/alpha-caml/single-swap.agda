{-# OPTIONS --cubical --safe --exact-split #-}

module programming-languages.alpha-caml.single-swap where

open import base
open import container.finmap
open import container.finmap.entry-map
open import discrete
open import equality
open import functions
open import funext
open import programming-languages.alpha-caml
open import programming-languages.renamings
open import relation
open import sigma.base
open import sum

private
  instance
    isDiscrete'-Atom : Discrete' Atom
    isDiscrete'-Atom .Discrete'.f = DiscreteAtom

abstract
  single-swap-atom : (Atom × Atom) -> Atom -> Atom
  single-swap-atom (v1 , v2) v3 =
    handle (DiscreteAtom v1 v3) (DiscreteAtom v2 v3)
    where
    handle : Dec (v1 == v3) -> Dec (v2 == v3) -> Atom
    handle (yes _) _      = v2
    handle (no _) (yes _) = v1
    handle (no _) (no _)  = v3

  single-swap-atom-left :
    {v1 v2 v3 : Atom} -> v1 == v3 -> single-swap-atom (v1 , v2) v3 == v2
  single-swap-atom-left {v1} {v2} {v3} p with (DiscreteAtom v1 v3)
  ... | (yes _) = refl
  ... | (no ¬p) = bot-elim (¬p p)

  single-swap-atom-right :
    {v1 v2 v3 : Atom} -> v2 == v3 -> single-swap-atom (v1 , v2) v3 == v1
  single-swap-atom-right {v1} {v2} {v3} p with (DiscreteAtom v1 v3) | (DiscreteAtom v2 v3)
  ... | (yes p1) | _      = p >=> sym p1
  ... | (no _)  | (yes _) = refl
  ... | (no _)  | (no ¬p) = bot-elim (¬p p)

  single-swap-atom-neither :
    {v1 v2 v3 : Atom} -> v1 != v3 -> v2 != v3 -> single-swap-atom (v1 , v2) v3 == v3
  single-swap-atom-neither {v1} {v2} {v3} ¬p1 ¬p2 with (DiscreteAtom v1 v3) | (DiscreteAtom v2 v3)
  ... | (yes p1) | _        = bot-elim (¬p1 p1)
  ... | (no _)   | (yes p2) = bot-elim (¬p2 p2)
  ... | (no _)   | (no ¬p)  = refl

single-swap-term : (Atom × Atom) -> Term -> Term
single-swap-term p = rename-atom/term (single-swap-atom p)
single-swap-pattern : (Atom × Atom) -> Pattern -> Pattern
single-swap-pattern p = rename-atom/pattern (single-swap-atom p)



Identity-single-swap-atom : {v1 v2 a : Atom} -> v1 == v2 -> single-swap-atom (v1 , v2) a == a
Identity-single-swap-atom {v1} {v2} {a} p = handle (DiscreteAtom v1 a)
  where
  handle : Dec (v1 == a) -> single-swap-atom (v1 , v2) a == a
  handle (yes p1) = single-swap-atom-left p1 >=> sym p >=> p1
  handle (no ¬p1) = single-swap-atom-neither ¬p1 (\p2 -> ¬p1 (p >=> p2))

SplitSingleAtom : (v1 v2 v3 : Atom) -> Type₀
SplitSingleAtom v1 v2 v3 =
  ((v1 == v3 × single-swap-atom (v1 , v2) v3 == v2) ⊎
   (v2 == v3 × single-swap-atom (v1 , v2) v3 == v1)) ⊎
  (v1 != v3 × v2 != v3 × single-swap-atom (v1 , v2) v3 == v3)

split-single-swap-atom : (v1 v2 v3 : Atom) -> SplitSingleAtom v1 v2 v3
split-single-swap-atom v1 v2 v3 = handle (DiscreteAtom v1 v3) (DiscreteAtom v2 v3)
  where
  handle : Dec (v1 == v3) -> Dec (v2 == v3) -> SplitSingleAtom v1 v2 v3
  handle (yes p1) _        = inj-l (inj-l (p1 , single-swap-atom-left p1))
  handle (no ¬p1) (yes p2) = inj-l (inj-r (p2 , single-swap-atom-right p2))
  handle (no ¬p1) (no ¬p2) = inj-r (¬p1 , ¬p2 , single-swap-atom-neither ¬p1 ¬p2)


Injective-single-swap-atom : (p : Atom × Atom) -> Injective (single-swap-atom p)
Injective-single-swap-atom (v1 , v2) {a1} {a2} path =
  handle (DiscreteAtom v1 v2) (split-single-swap-atom v1 v2 a1) (split-single-swap-atom v1 v2 a2)
  where

  handle : Dec (v1 == v2) -> SplitSingleAtom v1 v2 a1 -> SplitSingleAtom v1 v2 a2 -> a1 == a2
  handle (yes v1=v2) _ _ =
    sym (Identity-single-swap-atom v1=v2) >=> path >=> Identity-single-swap-atom v1=v2
  handle (no v1!=v2) (inj-l (inj-l (v1=a1 , _))) (inj-l (inj-l (v1=a2 , _))) = sym v1=a1 >=> v1=a2
  handle (no v1!=v2) (inj-l (inj-r (v2=a1 , _))) (inj-l (inj-r (v2=a2 , _))) = sym v2=a1 >=> v2=a2
  handle (no v1!=v2) (inj-r (_ , _ , sa1)) (inj-r (_ , _ , sa2)) = sym sa1 >=> path >=> sa2
  handle (no v1!=v2) (inj-l (inj-l (_ , sa1))) (inj-l (inj-r (_ , sa2))) =
    bot-elim (v1!=v2 (sym sa2 >=> sym path >=> sa1))
  handle (no v1!=v2) (inj-l (inj-r (_ , sa1))) (inj-l (inj-l (_ , sa2))) =
    bot-elim (v1!=v2 (sym sa1 >=> path >=> sa2))
  handle (no v1!=v2) (inj-r (_ , v2!=a1 , sa1)) (inj-l (inj-l (_ , sa2))) =
    bot-elim (v2!=a1 (sym sa2 >=> sym path >=> sa1))
  handle (no v1!=v2) (inj-r (v1!=a1 , _ , sa1)) (inj-l (inj-r (_ , sa2))) =
    bot-elim (v1!=a1 (sym sa2 >=> sym path >=> sa1))
  handle (no v1!=v2) (inj-l (inj-l (_ , sa1))) (inj-r (_ , v2!=a2 , sa2)) =
    bot-elim (v2!=a2 (sym sa1 >=> path >=> sa2))
  handle (no v1!=v2) (inj-l (inj-r (_ , sa1))) (inj-r (v1!=a2 , _ , sa2)) =
    bot-elim (v1!=a2 (sym sa1 >=> path >=> sa2))

Involution-single-swap-atom : (p : Atom × Atom) -> Involution (single-swap-atom p)
Involution-single-swap-atom p@(a1 , a2) {a3} = handle (split-single-swap-atom a1 a2 a3)
  where
  handle : SplitSingleAtom a1 a2 a3 -> (single-swap-atom p (single-swap-atom p a3)) == a3
  handle (inj-l (inj-l (a1=a3 , sa3=a2))) =
    cong (single-swap-atom p) sa3=a2 >=> single-swap-atom-right refl >=> a1=a3
  handle (inj-l (inj-r (a2=a3 , sa3=a1))) =
    cong (single-swap-atom p) sa3=a1 >=> single-swap-atom-left refl >=> a2=a3
  handle (inj-r (_ , _ , sa3=a3)) =
    cong (single-swap-atom p) sa3=a3 >=> sa3=a3


single-swap-term-pattern/side : (p : Atom × Atom) (s : ScopeSpecifier) (pat : Pattern)  ->
  single-swap-term p (pattern/side s pat) == pattern/side s (single-swap-pattern p pat)
single-swap-term-pattern/side p s (var v) = refl
single-swap-term-pattern/side p s empty = refl
single-swap-term-pattern/side p s (branch l r) =
  cong2 branch (single-swap-term-pattern/side p s l) (single-swap-term-pattern/side p s r)
single-swap-term-pattern/side p outer (eoa outer t) = refl
single-swap-term-pattern/side p outer (eoa inner t) = refl
single-swap-term-pattern/side p inner (eoa outer t) = refl
single-swap-term-pattern/side p inner (eoa inner t) = refl

-- If r is a renaming between t1 and t2 then
-- single-swap-renaming is a renaming between single-swap-term t1 and single-swap-term t2
single-swap-renaming : (Atom × Atom) -> Renaming -> Renaming
single-swap-renaming p (m , inj-m1 , fun-m1) = m2 , inj-m2 , fun-m2
  where
  f : Atom -> Atom -> Atom × Atom
  f k v = single-swap-atom p k , single-swap-atom p v
  m2 = finmap'-entry-map f m

  abstract
    case-hkv : {k v : Atom} -> HasKV' k v m2 ->
                 Σ[ k2 ∈ Atom ] Σ[ v2 ∈ Atom ]
                   (HasKV' k2 v2 m × (single-swap-atom p k2 == k) × (single-swap-atom p v2 == v))
    case-hkv hkv =
      case (HasKey-finmap'-entry-map-backward f hkv) of
        (\{ (k2 , v2 , hkv , p) -> k2 , v2 , hkv , cong fst p , cong snd p })

    inj-m2 : isInjectiveFinMap' m2
    inj-m2 hkv1-m2 hkv2-m2 =
      let (k1 , v1 , hkv1 , kp1 , vp1) = case-hkv hkv1-m2
          (k2 , v2 , hkv2 , kp2 , vp2) = case-hkv hkv2-m2
          vp = Injective-single-swap-atom p (vp1 >=> sym vp2)
          hkv1' = subst (\v -> HasKV' k1 v m) vp hkv1
          kp = inj-m1 hkv1' hkv2
      in sym kp1 >=> cong (single-swap-atom p) kp >=> kp2

    fun-m2 : isFunctionalFinMap' m2
    fun-m2 hkv1-m2 hkv2-m2 =
      let (k1 , v1 , hkv1 , kp1 , vp1) = case-hkv hkv1-m2
          (k2 , v2 , hkv2 , kp2 , vp2) = case-hkv hkv2-m2
          kp = Injective-single-swap-atom p (kp1 >=> sym kp2)
          hkv1' = subst (\k -> HasKV' k v1 m) kp hkv1
          vp = fun-m1 hkv1' hkv2
      in sym vp1 >=> cong (single-swap-atom p) vp >=> vp2

HasKV-single-swap-renaming-backward : {k v : Atom} (p : Atom × Atom) (r : Renaming) ->
  HasKV' k v ⟨ (single-swap-renaming p r) ⟩ ->
  Σ[ k2 ∈ Atom ] Σ[ v2 ∈ Atom ]
    (HasKV' k2 v2 ⟨ r ⟩ ×
     (single-swap-atom p k2 , single-swap-atom p v2) == (k , v))
HasKV-single-swap-renaming-backward p r =
  HasKey-finmap'-entry-map-backward
    (\k v -> single-swap-atom p k , single-swap-atom p v)


HasKV-single-swap-renaming : {k v : Atom} (p : Atom × Atom) (r : Renaming) ->
  HasKV' k v ⟨ r ⟩ ->
  HasKV' (single-swap-atom p k) (single-swap-atom p v) ⟨ (single-swap-renaming p r) ⟩
HasKV-single-swap-renaming p r =
  HasKey-finmap'-entry-map (\k v -> single-swap-atom p k , single-swap-atom p v)


single-swap-renaming-single-renaming : {v1 v2 : Atom} (p : Atom × Atom) ->
  (single-swap-renaming p (single-renaming v1 v2)) ==
  (single-renaming (single-swap-atom p v1) (single-swap-atom p v2))
single-swap-renaming-single-renaming p = ΣProp-path isProp-isRenaming refl

single-swap-renaming-empty-renaming : (p : Atom × Atom) ->
  (single-swap-renaming p empty-renaming) == empty-renaming
single-swap-renaming-empty-renaming p = ΣProp-path isProp-isRenaming refl



use-renaming-single-swap-renaming : (p : Atom × Atom) (r : Renaming) (a : Atom) ->
  use-renaming (single-swap-renaming p r) a ==
  single-swap-atom p (use-renaming r (single-swap-atom p a))
use-renaming-single-swap-renaming p@(a1 , a2) r a = handle (lookup' (single-swap-atom p a) ⟨ r ⟩)
  where
  r2 : Renaming
  r2 = single-swap-renaming p r
  handle : Dec (HasKey' (single-swap-atom p a) ⟨ r ⟩) ->
           use-renaming (single-swap-renaming p r) a ==
           single-swap-atom p (use-renaming r (single-swap-atom p a))
  handle (yes (v , hkv-ssa-r)) =
    use-renaming-HasKV r2 hkv-a-r2 >=>
    cong (single-swap-atom p) (sym (use-renaming-HasKV r hkv-ssa-r))
    where
    hkv-ssa2-r2 : HasKV' (single-swap-atom p (single-swap-atom p a)) (single-swap-atom p v) ⟨ r2 ⟩
    hkv-ssa2-r2 = HasKV-single-swap-renaming p r hkv-ssa-r
    hkv-a-r2 : HasKV' a (single-swap-atom p v) ⟨ r2 ⟩
    hkv-a-r2 = subst (\k -> HasKV' k (single-swap-atom p v) ⟨ r2 ⟩) (Involution-single-swap-atom p)
                     hkv-ssa2-r2
  handle (no ¬hk-r) =
    use-renaming-¬HasKey r2 ¬hk-r2 >=>
    sym (Involution-single-swap-atom p) >=>
    cong (single-swap-atom p) (sym (use-renaming-¬HasKey r ¬hk-r))
    where
    ¬hk-r2 : ¬ (HasKey' a ⟨ r2 ⟩)
    ¬hk-r2 (v , hkv-r2) =
      let (k2 , v2 , hkv-r , paths) = HasKV-single-swap-renaming-backward p r hkv-r2
          path : single-swap-atom p k2 == a
          path = (cong fst paths)
          path' : k2 == single-swap-atom p a
          path' = sym (Involution-single-swap-atom p) >=> cong (single-swap-atom p) path
      in ¬hk-r (subst (\k -> HasKey' k ⟨ r ⟩) path' (v2 , hkv-r))



single-swap-renaming-single-swap-atom : (p : Atom × Atom) (r : Renaming) ->
  use-renaming (single-swap-renaming p r) ∘ single-swap-atom p ==
  single-swap-atom p ∘ use-renaming r
single-swap-renaming-single-swap-atom p@(a1 , a2) r = funExt handle
  where
  module _ (x : Atom) where
    Ans : Type₀
    Ans = use-renaming (single-swap-renaming p r) (single-swap-atom p x) ==
          single-swap-atom p (use-renaming r x)

    handle : Ans
    handle =
      use-renaming-single-swap-renaming p r (single-swap-atom p x) >=>
      cong (single-swap-atom p ∘ use-renaming r) (Involution-single-swap-atom p)



single-swap-term-use-renaming/term : {t : Term} (p : Atom × Atom) (r : Renaming) ->
  single-swap-term p (use-renaming/term r t) ==
  use-renaming/term (single-swap-renaming p r) (single-swap-term p t)
single-swap-term-use-renaming/term {t} p r = ans
  where
  ans : rename-atom/term (single-swap-atom p)
          (rename-atom/term (use-renaming r) t) ==
        rename-atom/term (use-renaming (single-swap-renaming p r))
          (rename-atom/term (single-swap-atom p) t)
  ans = (rename-atom/term-compose _ _ _) >=>
        cong (\f -> rename-atom/term f t) (sym (single-swap-renaming-single-swap-atom p r)) >=>
        sym (rename-atom/term-compose _ _ _)



RenamingUnion-single-swap : {r1 r2 r3 : Renaming} -> (p : Atom × Atom) ->
  RenamingUnion r1 r2 r3 ->
  RenamingUnion
    (single-swap-renaming p r1) (single-swap-renaming p r2) (single-swap-renaming p r3)
RenamingUnion-single-swap {r1} {r2} {r3} p ru .RenamingUnion.forward-left {k} {v} hk1 =
  let (k2 , v2 , hkv2 , paths) = HasKV-single-swap-renaming-backward p r1 hk1
  in subst2 (\k v -> HasKV' k v ⟨ (single-swap-renaming p r3) ⟩) (cong fst paths) (cong snd paths)
            (HasKV-single-swap-renaming p r3 (RenamingUnion.forward-left ru hkv2))
RenamingUnion-single-swap {r1} {r2} {r3} p ru .RenamingUnion.forward-right {k} {v} hk1 =
  let (k2 , v2 , hkv2 , paths) = HasKV-single-swap-renaming-backward p r2 hk1
  in subst2 (\k v -> HasKV' k v ⟨ (single-swap-renaming p r3) ⟩) (cong fst paths) (cong snd paths)
            (HasKV-single-swap-renaming p r3 (RenamingUnion.forward-right ru hkv2))
RenamingUnion-single-swap {r1} {r2} {r3} p ru .RenamingUnion.backward hk1 =
  let (k2 , v2 , hkv2 , paths) = HasKV-single-swap-renaming-backward p r3 hk1
      cases = RenamingUnion.backward ru hkv2
  in ⊎-map (\hk -> subst2 (\k v -> HasKV' k v ⟨ (single-swap-renaming p r1) ⟩)
                          (cong fst paths) (cong snd paths) (HasKV-single-swap-renaming p r1 hk))
           (\hk -> subst2 (\k v -> HasKV' k v ⟨ (single-swap-renaming p r2) ⟩)
                          (cong fst paths) (cong snd paths) (HasKV-single-swap-renaming p r2 hk))
           cases


PatternRenaming-single-swap : {p1 p2 : Pattern} {r : Renaming} ->
  (p : Atom × Atom) ->
  PatternRenaming p1 p2 r ->
  PatternRenaming (single-swap-pattern p p1) (single-swap-pattern p p2) (single-swap-renaming p r)
PatternRenaming-single-swap p (var v1 v2) = ans
  where
  v1' : Atom
  v1' = single-swap-atom p v1
  v2' : Atom
  v2' = single-swap-atom p v2
  ans : PatternRenaming (var v1') (var v2') (single-swap-renaming p (single-renaming v1 v2))
  ans = subst (PatternRenaming (var v1') (var v2')) (sym (single-swap-renaming-single-renaming p))
              (var v1' v2')


PatternRenaming-single-swap p (empty) =
  subst (PatternRenaming empty empty) (sym (single-swap-renaming-empty-renaming p)) empty
PatternRenaming-single-swap p (eoa s t1 t2) =
  subst (PatternRenaming (eoa s t1') (eoa s t2'))
        (sym (single-swap-renaming-empty-renaming p)) (eoa s t1' t2')
  where
  t1' = single-swap-term p t1
  t2' = single-swap-term p t2
PatternRenaming-single-swap p (branch p1 p2 p3 p4 r1 r2 r3 pr13 pr24 ru123) =
  (branch p1' p2' p3' p4' r1' r2' r3' pr13' pr24' ru123')
  where
  p1' = single-swap-pattern p p1
  p2' = single-swap-pattern p p2
  p3' = single-swap-pattern p p3
  p4' = single-swap-pattern p p4
  r1' = single-swap-renaming p r1
  r2' = single-swap-renaming p r2
  r3' = single-swap-renaming p r3
  pr13' = (PatternRenaming-single-swap p pr13)
  pr24' = (PatternRenaming-single-swap p pr24)
  ru123' = RenamingUnion-single-swap p ru123

single-swap-finset : (p : Atom × Atom) -> FinSet Atom -> FinSet Atom
single-swap-finset p =
  finmap'-entry-map (\ k v -> (single-swap-atom p k) , v)

DisjointFinSet-single-swap-finset : {fs1 fs2 : FinSet Atom} -> (p : Atom × Atom) ->
  DisjointFinSet fs1 fs2 -> DisjointFinSet (single-swap-finset p fs1) (single-swap-finset p fs2)
DisjointFinSet-single-swap-finset {fs1} {fs2} p dis {k} (_ , hk1) (_ , hk2) =
  let (k2 , tt , hkv2 , paths2) =
        HasKey-finmap'-entry-map-backward (\ k v -> (single-swap-atom p k) , v) hk1
      (k3 , tt , hkv3 , paths3) =
        HasKey-finmap'-entry-map-backward (\ k v -> (single-swap-atom p k) , v) hk2
      hkv3' : HasKV' k2 tt fs2
      hkv3' = subst (\k -> HasKV' k tt fs2)
                    (Injective-single-swap-atom p (cong fst paths3 >=> sym (cong fst paths2)))
                    hkv3
  in dis (tt , hkv2) (tt , hkv3')

single-swap-finset-fm-union : (p : Atom × Atom) -> (fs1 fs2 : FinSet Atom) ->
  single-swap-finset p (fm'-union fs1 fs2) ==
  fm'-union (single-swap-finset p fs1) (single-swap-finset p fs2)
single-swap-finset-fm-union p [] fs2 = refl
single-swap-finset-fm-union p (fm-cons k v fs1) fs2 =
  cong (fm-cons _ _) (single-swap-finset-fm-union p fs1 fs2)



single-swap-finset-atoms/term : (p : Atom × Atom) (t : Term) ->
 single-swap-finset p (atoms/term t) == atoms/term (single-swap-term p t)
single-swap-finset-atoms/pattern : (p : Atom × Atom) (pat : Pattern) ->
 single-swap-finset p (atoms/pattern pat) == atoms/pattern (single-swap-pattern p pat)

single-swap-finset-atoms/term p (var v) = refl
single-swap-finset-atoms/term p (const k) = refl
single-swap-finset-atoms/term p (empty) = refl
single-swap-finset-atoms/term p (abstraction pat) =
  single-swap-finset-atoms/pattern p pat
single-swap-finset-atoms/term p (branch l r) =
  (single-swap-finset-fm-union p (atoms/term l) (atoms/term r)) >=>
  cong2 fm'-union (single-swap-finset-atoms/term p l) (single-swap-finset-atoms/term p r)

single-swap-finset-atoms/pattern p (var v) = refl
single-swap-finset-atoms/pattern p (empty) = refl
single-swap-finset-atoms/pattern p (eoa s t) =
  single-swap-finset-atoms/term p t
single-swap-finset-atoms/pattern p (branch l r) =
  (single-swap-finset-fm-union p (atoms/pattern l) (atoms/pattern r)) >=>
  cong2 fm'-union (single-swap-finset-atoms/pattern p l) (single-swap-finset-atoms/pattern p r)
