{-# OPTIONS --cubical --safe --exact-split #-}

module programming-languages.alpha-caml where

open import container.finmap
open import base
open import relation
open import hlevel.base
open import equality
open import sum
open import functions
open import nat hiding (_≤_ ; trans-≤ ; _<_ ; _>_; trans-<-≤)
open import list
open import order
open import order.instances.nat
open import truncation

private
  variable
    ℓ : Level

Atom : Type₀
Atom = Nat

instance
  isSet'-Atom : isSet' Atom
  isSet'-Atom .isSet'.f = isSetNat

DiscreteAtom : Discrete Atom
DiscreteAtom = decide-nat

FinSet : Type ℓ -> Type ℓ
FinSet A = FinMap' A Top

DisjointFinSet : {ℓ : Level} {A : Type ℓ} -> FinSet A -> FinSet A -> Type ℓ
DisjointFinSet = DisjointKeys'

data ScopeSpecifier : Type₀ where
  inner : ScopeSpecifier
  outer : ScopeSpecifier

private
  inner!=outer : inner != outer
  inner!=outer p = transport (cong f p) tt
    where
    f : ScopeSpecifier -> Type₀
    f inner = Top
    f outer = Bot

DiscreteScopeSpecifier : Discrete ScopeSpecifier
DiscreteScopeSpecifier inner inner = yes refl
DiscreteScopeSpecifier inner outer = no inner!=outer
DiscreteScopeSpecifier outer inner = no (inner!=outer ∘ sym)
DiscreteScopeSpecifier outer outer = yes refl

data Term : Type₀
data Pattern : Type₀

data Pattern where
  empty : Pattern
  var : Atom -> Pattern
  branch : Pattern -> Pattern -> Pattern
  eoa : ScopeSpecifier -> Term -> Pattern

data Term where
  empty : Term
  const : Atom -> Term
  var : Atom -> Term
  branch : Term -> Term -> Term
  abstraction : Pattern -> Term

data SamePatternStructure : Rel Pattern ℓ-zero where
  empty : SamePatternStructure empty empty
  var : {v1 v2 : Atom} -> SamePatternStructure (var v1) (var v2)
  branch : {p1 p2 p3 p4 : Pattern} -> 
           SamePatternStructure p1 p2 -> 
           SamePatternStructure p3 p4 ->
           SamePatternStructure (branch p1 p3) (branch p3 p4)
  eoa : {s : ScopeSpecifier} {t1 t2 : Term} -> SamePatternStructure (eoa s t1) (eoa s t2)

term-depth : Term -> Nat
pattern-depth : Pattern -> Nat

term-depth empty = 1
term-depth (const _) = 1
term-depth (var _) = 1
term-depth (branch l r) = suc (max (term-depth l) (term-depth r))
term-depth (abstraction p) = suc (pattern-depth p)

pattern-depth empty = 1
pattern-depth (var v) = 1
pattern-depth (branch l r) = suc (max (pattern-depth l) (pattern-depth r))
pattern-depth (eoa _ t) = suc (term-depth t)

data TermDepth : Term -> Nat -> Type₀
data PatternDepth : Pattern -> Nat -> Type₀

data TermDepth where
  var : (v : Atom) -> TermDepth (var v) 1
  const : (v : Atom) -> TermDepth (const v) 1
  empty : TermDepth empty 1
  branch : {l r : Term} {ld rd : Nat} -> 
           TermDepth l ld -> TermDepth r rd -> TermDepth (branch l r) (suc (max ld rd))
  abstraction : {p : Pattern} {pd : Nat} -> PatternDepth p pd -> TermDepth (abstraction p) (suc pd)

data PatternDepth where
  var : (v : Atom) -> PatternDepth (var v) 1
  empty : PatternDepth empty 1
  branch : {l r : Pattern} {ld rd : Nat} -> 
           PatternDepth l ld -> PatternDepth r rd -> PatternDepth (branch l r) (suc (max ld rd))
  eoa : {t : Term} {td : Nat} -> 
        (s : ScopeSpecifier) -> TermDepth t td -> PatternDepth (eoa s t) (suc td)


isRenaming : Pred (FinMap' Atom Atom) ℓ-zero
isRenaming = isBijectiveFinMap'

Renaming : Type₀
Renaming = Σ (FinMap' Atom Atom) isRenaming

use-renaming : Renaming -> Atom -> Atom
use-renaming (m , isRename) = f m isRename
  where
  f : (m : FinMap' Atom Atom) -> isRenaming m -> Atom -> Atom
  f [] _ a = a
  f (fm-cons a1 a2 m) isRename a3 = 
    case (DiscreteAtom a1 a3) of \{
      (yes _) -> a2 ;
      (no _) -> f m (isBijectiveFinMap'-rest _ isRename) a3}

-- rename# : Atom -> Atom -> List (Atom × Atom) -> Type₀
-- 
-- data isRenaming where
--   [] : isRenaming []
--   rename-cons : {l : List (Atom × Atom)} -> (a1 a2 : Atom) -> (r : isRenaming l) -> 
--                 rename# a1 a2 l -> isRenaming ((a1 , a2) :: l)
-- 
-- rename# a1 a2 = ContainsAll \{(a3 , a4) -> (a1 != a3) × (a2 != a4)}

single-renaming : Atom -> Atom -> Renaming
single-renaming a1 a2 = _ , isBijectiveFinMap'-single a1 a2

empty-renaming : Renaming
empty-renaming = _ , isBijectiveFinMap'-[]

single-renaming-unique-value : {k1 v1 k2 v2 : Atom} -> HasKV' k1 v1 ⟨ single-renaming k2 v2 ⟩ -> 
                               (k1 == k2 × v1 == v2)
single-renaming-unique-value (has-kv-here kp vp _) = kp , vp



module _ (a1 : Atom) (a2 : Atom) where

  rename-atom/atom : Atom -> Atom
  rename-atom/atom v = 
    case (DiscreteAtom v a1) of \{
      (yes _) -> a2 ;
      (no _) -> v }


module _ (rename-atom/atom : Atom -> Atom) where

  rename-atom/term : Term -> Term
  rename-atom/pattern : Pattern -> Pattern

  rename-atom/term empty = empty
  rename-atom/term (const k) = const k
  rename-atom/term (var v) = var (rename-atom/atom v)
  rename-atom/term (branch t1 t2) = branch (rename-atom/term t1) (rename-atom/term t2)
  rename-atom/term (abstraction p) = abstraction (rename-atom/pattern p)

  rename-atom/pattern empty = empty
  rename-atom/pattern (var v) = var (rename-atom/atom v)
  rename-atom/pattern (branch p1 p2) = branch (rename-atom/pattern p1) (rename-atom/pattern p2)
  rename-atom/pattern (eoa s t) = eoa s (rename-atom/term t)

use-renaming/term : Renaming -> Term -> Term
use-renaming/term r = rename-atom/term (use-renaming r)



atoms/atom : Atom -> FinSet Atom
atoms/atom v = fm-cons v tt []

atoms/term : Term -> FinSet Atom
atoms/pattern : Pattern -> FinSet Atom

atoms/term empty = []
atoms/term (const _) = []
atoms/term (var v) = fm-cons v tt []
atoms/term (branch t1 t2) = fm'-union (atoms/term t1) (atoms/term t2)
atoms/term (abstraction p) = atoms/pattern p

atoms/pattern empty = []
atoms/pattern (var v) = fm-cons v tt []
atoms/pattern (branch p1 p2) = fm'-union (atoms/pattern p1) (atoms/pattern p2)
atoms/pattern (eoa s t) = atoms/term t

pattern/side : ScopeSpecifier -> Pattern -> Term
pattern/side _ empty  = empty
pattern/side _ (var _) = empty
pattern/side s (branch p1 p2) = (branch (pattern/side s p1) (pattern/side s p2))
pattern/side s1 (eoa s2 t) = 
  case (DiscreteScopeSpecifier s1 s2) of \{
    (yes _) -> t ;
    (no _) -> empty }

term-depth>0 : (t : Term) -> term-depth t > 0
term-depth>0 (var _) = zero-<
term-depth>0 (const _) = zero-<
term-depth>0 (empty) = zero-<
term-depth>0 (branch l r) = zero-<
term-depth>0 (abstraction p) = zero-<

term-depth-pattern/side : (s : ScopeSpecifier) (p : Pattern) ->
  term-depth (pattern/side s p) ≤ pattern-depth p
term-depth-pattern/side _ empty = refl-≤
term-depth-pattern/side _ (var _) = refl-≤
term-depth-pattern/side s (branch l r) = 
  suc-≤ (max-monotonic-≤ rec-l rec-r)
  where

  rec-l : term-depth (pattern/side s l) ≤ pattern-depth l
  rec-l = term-depth-pattern/side s l
  rec-r : term-depth (pattern/side s r) ≤ pattern-depth r
  rec-r = term-depth-pattern/side s r
term-depth-pattern/side inner (eoa inner _) = right-suc-≤ refl-≤
term-depth-pattern/side outer (eoa inner t) = right-suc-≤ (term-depth>0 t)
term-depth-pattern/side inner (eoa outer t) = right-suc-≤ (term-depth>0 t)
term-depth-pattern/side outer (eoa outer _) = right-suc-≤ refl-≤


module _ (f : Atom -> Atom) where
  term-depth-rename-atom/term : (t : Term) ->
    term-depth (rename-atom/term f t) == term-depth t
  pattern-depth-rename-atom/pattern : (p : Pattern) ->
    pattern-depth (rename-atom/pattern f p) == pattern-depth p

  term-depth-rename-atom/term (var _) = refl
  term-depth-rename-atom/term (const _) = refl
  term-depth-rename-atom/term empty = refl
  term-depth-rename-atom/term (branch l r) = 
    cong2 (\x y -> suc (max x y)) (term-depth-rename-atom/term l) (term-depth-rename-atom/term r)
  term-depth-rename-atom/term (abstraction p) =
    cong suc (pattern-depth-rename-atom/pattern p)

  pattern-depth-rename-atom/pattern (var _) = refl
  pattern-depth-rename-atom/pattern empty = refl
  pattern-depth-rename-atom/pattern (branch l r) = 
    cong2 (\x y -> suc (max x y)) (pattern-depth-rename-atom/pattern l)
                                  (pattern-depth-rename-atom/pattern r)
  pattern-depth-rename-atom/pattern (eoa s t) = 
    cong suc (term-depth-rename-atom/term t)

term-depth-use-renaming : (r : Renaming) (t : Term) ->
  term-depth (use-renaming/term r t) == term-depth t
term-depth-use-renaming r t = term-depth-rename-atom/term (use-renaming r) t


RenamingExtension : Renaming -> Renaming -> Type₀
RenamingExtension orig result = {k v : Atom} -> HasKV' k v ⟨ orig ⟩ -> HasKV' k v ⟨ result ⟩

isSubFinSet : FinSet Atom -> FinSet Atom -> Type₀
isSubFinSet fs1 fs2 = {k : Atom} -> HasKey' k fs2 -> HasKey' k fs1

record RenamingUnion (left right result : Renaming) : Type₀ where
  field
    forward-left : RenamingExtension left result
    forward-right : RenamingExtension right result
    backward : {k v : Atom} -> HasKV' k v ⟨ result ⟩ -> 
               HasKV' k v ⟨ left ⟩ ⊎ HasKV' k v ⟨ right ⟩


record CompatibleRenamings (r1 r2 : Renaming) : Type₀ where
  field
    range : {k v1 v2 : Atom} -> HasKV' k v1 ⟨ r1 ⟩ -> HasKV' k v2 ⟨ r2 ⟩ -> v1 == v2
    domain : {k1 k2 v : Atom} -> HasKV' k1 v ⟨ r1 ⟩ -> HasKV' k2 v ⟨ r2 ⟩ -> k1 == k2


data PatternRenaming : Pattern -> Pattern -> Renaming -> Type₀ where
  var : (v1 v2 : Atom) -> PatternRenaming (var v1) (var v2) (single-renaming v1 v2)
  empty : PatternRenaming empty empty empty-renaming
  eoa : (s : ScopeSpecifier) (t1 t2 : Term) -> PatternRenaming (eoa s t1) (eoa s t2) empty-renaming
  branch : (p1 p2 p3 p4 : Pattern) (r1 r2 r3 : Renaming) ->
           PatternRenaming p1 p3 r1 -> PatternRenaming p2 p4 r2 ->
           RenamingUnion r1 r2 r3 ->
           PatternRenaming (branch p1 p2) (branch p3 p4) r3
    
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


renaming-target-atoms : Renaming -> FinSet Atom
renaming-target-atoms r = fm'-keys (fm'-invert ⟨ r ⟩)

isFreshBoundOfRenaming : (r : Renaming) (v : Atom) -> Type₀
isFreshBoundOfRenaming r b = 
  (a : Atom) -> b ≤ a -> ¬ (Σ[ k ∈ Atom ] (HasKV' k a ⟨ r ⟩)) ×
                         ¬ (Σ[ v ∈ Atom ] (HasKV' a v ⟨ r ⟩))


isFreshBoundOfPattern : (p : Pattern) (v : Atom) -> Type₀
isFreshBoundOfPattern p b =
  {a : Atom} -> (HasKey' a (atoms/pattern p)) -> a < b 

isFreshBoundOfTerm : (t : Term) (v : Atom) -> Type₀
isFreshBoundOfTerm t b =
  {a : Atom} -> (HasKey' a (atoms/term t)) -> a < b 

computeFreshBoundOfRenaming : (r : Renaming) -> Σ Atom (isFreshBoundOfRenaming r)
computeFreshBoundOfRenaming (m , _) = handle m
  where
  isFreshBoundOfMap : (m : FinMap' Atom Atom) (v : Atom) -> Type₀
  isFreshBoundOfMap m b = 
    (a : Atom) -> b ≤ a -> ¬ (Σ[ k ∈ Atom ] (HasKV' k a m)) ×
                           ¬ (Σ[ v ∈ Atom ] (HasKV' a v m))


  handle : (m : FinMap' Atom Atom) -> Σ Atom (isFreshBoundOfMap m)
  handle [] = 0 , \a lt -> ((\{(_ , ())}) , (\{(_ , ())}))
  handle fm@(fm-cons k v m) = ans , freshBound
    where
    rec = handle m
    ans = max (suc (max k v)) (fst rec)
    
    freshBound : isFreshBoundOfMap fm ans
    freshBound a ans≤a = case-k , case-v
      where
      case-k : ¬ (Σ[ k ∈ Atom ] (HasKV' k a fm))
      case-k (_ , has-kv-here kp vp _) = irrefl-< lt
        where
        lt : v < v
        lt = (trans-<-≤
               (suc-≤ ≤-max-right)
               (trans-≤ (≤-max-left {suc (max k v)} {fst rec}) (trans-≤ ans≤a (path-≤ vp))))
      case-k (k , has-kv-skip _ _ hkv) =
        fst ((snd rec) a (trans-≤ ≤-max-right ans≤a)) (k , hkv)

      case-v : ¬ (Σ[ v ∈ Atom ] (HasKV' a v fm))
      case-v (_ , has-kv-here kp vp _) = irrefl-< lt
        where
        lt : k < k
        lt = (trans-<-≤
               (suc-≤ ≤-max-left)
               (trans-≤ (≤-max-left {suc (max k v)} {fst rec}) (trans-≤ ans≤a (path-≤ kp))))
      case-v (v , has-kv-skip _ _ hkv) =
        snd ((snd rec) a (trans-≤ ≤-max-right ans≤a)) (v , hkv)

record Supply (b : Atom) : Type₀ where
  field
    next-var : Atom
    b<next-var : b < next-var


  next-supply : Supply next-var
  next-supply = record {
    next-var = suc next-var ;
    b<next-var = refl-≤ }


initSupply : (b : Atom) -> Supply b
initSupply b = record {
    next-var = suc b ;
    b<next-var = refl-≤ }

computeFreshBoundOfPattern : (p : Pattern) -> Σ Atom (isFreshBoundOfPattern p)
computeFreshBoundOfTerm : (t : Term) -> Σ Atom (isFreshBoundOfTerm t)

computeFreshBoundOfPattern (var v) = suc v , \{ (_ , (has-kv-here kp vp _)) -> suc-≤ (path-≤ kp)}
computeFreshBoundOfPattern (empty) = 0 , \()
computeFreshBoundOfPattern (branch l r) =
  handle (computeFreshBoundOfPattern l) (computeFreshBoundOfPattern r)
  where
  handle : Σ Atom (isFreshBoundOfPattern l) -> Σ Atom (isFreshBoundOfPattern r) ->
           Σ Atom (isFreshBoundOfPattern (branch l r))
  handle (lb , fl) (rb , fb) = 
    max lb rb , \hk -> either (\hk -> trans-≤ (fl hk) ≤-max-left)
                              (\hk -> trans-≤ (fb hk) ≤-max-right)
                       (HasKey-fm'-union/split _ _ hk)
computeFreshBoundOfPattern (eoa _ t) = computeFreshBoundOfTerm t

computeFreshBoundOfTerm (var v) = suc v , \{ (_ , (has-kv-here kp vp _)) -> suc-≤ (path-≤ kp)}
computeFreshBoundOfTerm (empty) = 0 , \()
computeFreshBoundOfTerm (const _) = 0 , \()
computeFreshBoundOfTerm (branch l r) = handle (computeFreshBoundOfTerm l) (computeFreshBoundOfTerm r)
  where
  handle : Σ Atom (isFreshBoundOfTerm l) -> Σ Atom (isFreshBoundOfTerm r) ->
           Σ Atom (isFreshBoundOfTerm (branch l r))
  handle (lb , fl) (rb , fb) = 
    max lb rb , \hk -> either (\hk -> trans-≤ (fl hk) ≤-max-left)
                              (\hk -> trans-≤ (fb hk) ≤-max-right)
                       (HasKey-fm'-union/split _ _ hk)
computeFreshBoundOfTerm (abstraction p) = computeFreshBoundOfPattern p

find-fresh-rename : 
  (p : Pattern) -> 
  Σ[ r ∈ Renaming ] (
    (DisjointFinSet (renaming-target-atoms r) (atoms/pattern p)) ×
    (∀ k -> HasKey' k (atoms/pattern p) -> HasKey' k ⟨ r ⟩))
find-fresh-rename p = (renaming' , (inj-renaming , fun-renaming)) , dis , has-key
  where
  bound : Σ Atom (isFreshBoundOfPattern p)
  bound = computeFreshBoundOfPattern p
  b = fst bound
  fresh-b = snd bound


  f : Atom -> Top -> Atom
  f k _ = suc b +' k

  renaming' : FinMap' Atom Atom
  renaming' = fm'-value-map (\k _ -> suc b +' k) (atoms/pattern p)

  fun-renaming : isFunctionalFinMap' renaming'
  fun-renaming {k} {v1} {v2} hkv1 hkv2 =
    handle (fm'-value-map/HasKV' _ hkv1) (fm'-value-map/HasKV' _ hkv2)
    where
    handle : Σ[ v ∈ Top ] ((f k v == v1) × HasKV' k v (atoms/pattern p)) ->
             Σ[ v ∈ Top ] ((f k v == v2) × HasKV' k v (atoms/pattern p)) ->
             v1 == v2
    handle (tt , k1p , _) (tt , k2p , _) = sym k1p >=> k2p

  inj-renaming : isInjectiveFinMap' renaming'
  inj-renaming {k1} {k2} {v2} hkv1 hkv2 =
    handle (fm'-value-map/HasKV' _ hkv1) (fm'-value-map/HasKV' _ hkv2)
    where
    handle : Σ[ v ∈ Top ] ((f k1 v == v2) × HasKV' k1 v (atoms/pattern p)) ->
             Σ[ v ∈ Top ] ((f k2 v == v2) × HasKV' k2 v (atoms/pattern p)) ->
             k1 == k2
    handle (_ , k1p , _) (_ , k2p , _) = 
      +'-left-injective {suc b} (k1p >=> sym k2p)

  has-key : (∀ k -> HasKey' k (atoms/pattern p) -> HasKey' k renaming')
  has-key k (v , hkv) = _ , fm'-value-map/HasKV f hkv



  dis : (DisjointFinSet (fm'-keys (fm'-invert renaming')) (atoms/pattern p))
  dis {k} (tt , hkv1) (tt , hkv2) =
    bot-elim (irrefl-< (trans-≤ (fresh-b (tt , hkv2)) b≤k))

    where
    hkv-r : Σ[ v ∈ Atom ] (HasKV' v k renaming')
    hkv-r = 
      case (fm'-keys/HasKV' hkv1) of (\{(v , hkv) ->
        v , subst (HasKV' v k) (fm'-invert/Involution renaming') (fm'-invert/HasKV hkv)})

    b≤k : b ≤ k
    b≤k = handle (fm'-value-map/HasKV' f (snd hkv-r))
      where
      handle : Σ[ v ∈ Top ] (f (fst hkv-r) v == k ×  HasKV' (fst hkv-r) v (atoms/pattern p)) -> 
               b ≤ k
      handle (_ , p , _) = pred-≤ (right-suc-≤ sb≤k)
        where
        sb≤k : suc b ≤ k 
        sb≤k = (fst hkv-r) , +'-commute {fst hkv-r} {suc b} >=> p


    


   --  case (rec-p p b (initSupply b) empty-renaming fresh-b (\{_ (_ , ())})) of
   --    (\{(r , dis , keys , _) -> r , (\{k} -> (dis {k})) , keys})
   --  where 
   --  initial-bound : Σ Atom (isFreshBoundOfPattern p)
   --  initial-bound = computeFreshBoundOfRenaming p
   --  b = fst initial-bound
   --  fresh-b = snd initial-bound
  
   --  rec-p : (p : Pattern) -> (b : Atom) -> (s : Supply b) ->
   --          (init-r : Renaming)
   --          (freshBound : isFreshBoundOfPattern p b) ->
   --          (DisjointFinSet (renaming-target-atoms init-r) (atoms/pattern p)) ->
   --           Σ[ r ∈ Renaming ] (
   --             (DisjointFinSet (renaming-target-atoms r) (atoms/pattern p)) ×
   --             (∀ k -> HasKey' k (atoms/pattern p) -> HasKey' k ⟨ r ⟩) ×
   --             RenamingExtension init-r r)
   --  rec-t : (t : Term) -> (b : Atom) -> (s : Supply b) ->
   --          (init-r : Renaming)
   --          (freshBound : isFreshBoundOfTerm t b) ->
   --          (DisjointFinSet (renaming-target-atoms init-r) (atoms/term t)) ->
   --           Σ[ r ∈ Renaming ] (
   --             (DisjointFinSet (renaming-target-atoms r) (atoms/term t)) ×
   --             (∀ k -> HasKey' k (atoms/term t) -> HasKey' k ⟨ r ⟩) ×
   --             RenamingExtension init-r r)
  
   --  rec-p (empty) b s init-r _ dis = init-r , dis , (\{_ (_ , ())}) , (\hk -> hk)
   --  rec-p (eoa ss t) b s init-r fresh dis = rec-t t b s init-r fresh dis
  
   --  rec-t (empty) b s init-r _ dis = init-r , dis , (\{_ (_ , ())}) , (\hk -> hk)
   --  rec-t (abstraction p) b s init-r fresh dis = rec-p p b s init-r fresh dis


-- freshen-pattern : (p1 : Pattern) -> Σ[ p2 ∈ Pattern ] Σ[ r ∈ Renaming ] 
--                                     (PatternRenaming p1 p2 r × 
--                                      DisjointFinSet (atoms/pattern p2) (atoms/pattern p1))


renaming-union : (r1 r2 : Renaming) -> CompatibleRenamings r1 r2 ->
                 Σ[ r3 ∈ Renaming ] (RenamingUnion r1 r2 r3)
renaming-union ren1@(r1 , is-r1) ren2@(r2 , is-r2) c = ren , ru
  where
  fm = fm'-union r1 r2 

  isInj : isInjectiveFinMap' fm
  isInj {k1} {k2} {v} hk1 hk2 = handle (HasKV-fm'-union/split _ _ hk1) (HasKV-fm'-union/split _ _ hk2)
    where
    handle : (HasKV' k1 v r1 ⊎ HasKV' k1 v r2) ->
             (HasKV' k2 v r1 ⊎ HasKV' k2 v r2) ->
             k1 == k2
    handle (inj-l hkv1) (inj-l hkv2) = fst is-r1 hkv1 hkv2
    handle (inj-l hkv1) (inj-r hkv2) = 
      CompatibleRenamings.domain c hkv1 hkv2
    handle (inj-r hkv1) (inj-l hkv2) =
      sym (CompatibleRenamings.domain c hkv2 hkv1)
    handle (inj-r hkv1) (inj-r hkv2) = fst is-r2 hkv1 hkv2

  isFun : isFunctionalFinMap' fm
  isFun {k} {v1} {v2} hk1 hk2 = handle (HasKV-fm'-union/split _ _ hk1) (HasKV-fm'-union/split _ _ hk2)
    where
    handle : (HasKV' k v1 r1 ⊎ HasKV' k v1 r2) ->
             (HasKV' k v2 r1 ⊎ HasKV' k v2 r2) ->
             v1 == v2
    handle (inj-l hkv1) (inj-l hkv2) = snd is-r1 hkv1 hkv2
    handle (inj-l hkv1) (inj-r hkv2) = 
      CompatibleRenamings.range c hkv1 hkv2
    handle (inj-r hkv1) (inj-l hkv2) =
      sym (CompatibleRenamings.range c hkv2 hkv1)
    handle (inj-r hkv1) (inj-r hkv2) = snd is-r2 hkv1 hkv2

  ren : Renaming
  ren = (fm , isInj , isFun)
  ru : RenamingUnion ren1 ren2 ren
  ru .RenamingUnion.forward-left = HasKV-fm'-union/left
  ru .RenamingUnion.forward-right = HasKV-fm'-union/right
  ru .RenamingUnion.backward hk = HasKV-fm'-union/split _ _ hk

--module _ (renaming-union : (r1 r2 : Renaming) -> CompatibleRenamings r1 r2 ->
--                           Σ[ r3 ∈ Renaming ] (RenamingUnion r1 r2 r3))
--         (compatible-extension :
--           (r1 r2 r3 : Renaming) -> 
--           RenamingExtension r1 r2 ->
--           CompatibleRenamings r2 r3 ->
--           CompatibleRenamings r1 r3)
--         (compatible-union :
--           {r1 r2 r3 r4 : Renaming} -> 
--           RenamingUnion r1 r2 r3 ->
--           CompatibleRenamings r1 r4 ->
--           CompatibleRenamings r2 r4 ->
--           CompatibleRenamings r3 r4)
--         (Symmetric-CompatibleRenamings : 
--           (r1 r2 : Renaming) -> CompatibleRenamings r1 r2 -> CompatibleRenamings r2 r1)
--         (Symmetric-DisjointKeys : 
--           {s1 s2 : FinSet Atom} -> DisjointKeys' s1 s2 -> DisjointKeys' s2 s1)
--  where
--  freshen-pattern : (p1 : Pattern) (init-r : Renaming) ->
--                    (DisjointFinSet (renaming-target-atoms init-r) (atoms/pattern p1)) -> 
--                    (bound : Atom) ->
--                    Σ[ p2 ∈ Pattern ] Σ[ r ∈ Renaming ] 
--                    (PatternRenaming p1 p2 r × 
--                     DisjointFinSet (atoms/pattern p2) (atoms/pattern p1) ×
--                     CompatibleRenamings r init-r)
--  freshen-pattern p1@(var v) init-r dis-init-r _ = handle (lookup' v ⟨ init-r ⟩)
--    where
--    handle : Dec (HasKey' v ⟨ init-r ⟩) ->
--             Σ[ p2 ∈ Pattern ] Σ[ r ∈ Renaming ] 
--             (PatternRenaming p1 p2 r × 
--              DisjointFinSet (atoms/pattern p2) (atoms/pattern p1) ×
--              CompatibleRenamings r init-r)
--    handle (no ¬k∈r) = var v2 , single-renaming v v2 , var v v2 , dis , compat
--      where
--  
--      bound : Σ Atom (isFreshBoundOfRenaming init-r)
--      bound = computeFreshBoundOfRenaming init-r
--      b = fst bound
--      
--      v2 : Atom
--      v2 = max (suc v) b 
--      b≤v2 : b ≤ v2
--      b≤v2 = ≤-max-right
--      v2!=v : v2 != v
--      v2!=v p = irrefl-< (trans-<-≤ lt lt2)
--        where
--        lt : (suc v) ≤ v2
--        lt = ≤-max-left {suc v} {b}
--        lt2 : v2 ≤ v
--        lt2 = (path-≤ p)
--    
--      dis : DisjointFinSet (fm-cons v2 tt []) (fm-cons v tt [])
--      dis (_ , has-kv-here kp _ _) (_ , has-kv-here kp2 _ _) = bot-elim (v2!=v (sym kp >=> kp2))
--  
--      compat : CompatibleRenamings (single-renaming v v2) init-r
--      compat .CompatibleRenamings.range {k} {v3} {v4} hkv1 hkv2 = bot-elim (¬k∈r (v4 , hkv'))
--        where
--        paths : k == v × v3 == v2
--        paths = single-renaming-unique-value hkv1
--        hkv' : HasKV' v v4 ⟨ init-r ⟩
--        hkv' = subst (\k -> HasKV' k v4 ⟨ init-r ⟩) (fst paths) hkv2
--      compat .CompatibleRenamings.domain {k1} {k2} {v3} hkv1 hkv2 =
--        bot-elim (fst ((snd bound) v2 b≤v2) (k2 , hkv'))
--        where
--        paths : k1 == v × v3 == v2
--        paths = single-renaming-unique-value hkv1
--        hkv' : HasKV' k2 v2 ⟨ init-r ⟩
--        hkv' = subst (\v -> HasKV' k2 v ⟨ init-r ⟩) (snd paths) hkv2
--    handle (yes (v2 , kv2∈r)) = var v2 , single-renaming v v2 , var v v2 , dis , compat
--      where
--      v∈atoms : HasKey' v (atoms/pattern p1)
--      v∈atoms = tt , has-kv-here refl refl []
--
--      v2∈init-r : HasKey' v2 (fm'-keys (fm'-invert ⟨ init-r ⟩))
--      v2∈init-r = fm'-keys/HasKey (v , fm'-invert/HasKV kv2∈r)
--
--      v2!=v : v2 != v
--      v2!=v v2=v = dis-init-r (subst (\v -> HasKey' v (fm'-keys (fm'-invert ⟨ init-r ⟩))) 
--                                     v2=v v2∈init-r) 
--                              v∈atoms
--
--      dis : DisjointFinSet (fm-cons v2 tt []) (fm-cons v tt [])
--      dis (_ , has-kv-here kp _ _) (_ , has-kv-here kp2 _ _) = bot-elim (v2!=v (sym kp >=> kp2))
--
--      compat : CompatibleRenamings (single-renaming v v2) init-r
--      compat .CompatibleRenamings.range {k} {v3} {v4} hkv1 hkv2 = 
--        (snd (snd init-r)) check-kv2∈r hkv2
--        where
--        paths : k == v × v3 == v2
--        paths = single-renaming-unique-value hkv1
--        check-kv2∈r : HasKV' k v3 ⟨ init-r ⟩
--        check-kv2∈r = subst2 (\k v -> HasKV' k v ⟨ init-r ⟩) (sym (fst paths)) (sym (snd paths)) kv2∈r
--
--      compat .CompatibleRenamings.domain {k1} {k2} {v3} hkv1 hkv2 =
--        (fst (snd init-r)) check-kv2∈r hkv2
--        where
--        paths : k1 == v × v3 == v2
--        paths = single-renaming-unique-value hkv1
--        check-kv2∈r : HasKV' k1 v3 ⟨ init-r ⟩
--        check-kv2∈r = subst2 (\k v -> HasKV' k v ⟨ init-r ⟩) (sym (fst paths)) (sym (snd paths)) kv2∈r
--
--
--  freshen-pattern (empty) init-r _ _ = empty , empty-renaming , empty , (\()) , compat
--    where
--    compat : CompatibleRenamings empty-renaming init-r
--    compat = record { range = \() ; domain = \() }
--  freshen-pattern (eoa s t) init-r _ _ = (eoa s empty) , empty-renaming , eoa s t empty , (\()) , compat
--    where
--    compat : CompatibleRenamings empty-renaming init-r
--    compat = record { range = \() ; domain = \() }
--  freshen-pattern (branch l1 r1) init-r dis-init-r init-bound =
--    branch (fst fresh-l) (fst fresh-r) ,
--    final-rename ,
--    branch _ _ _ _ _ _ _ (fst (snd (snd fresh-l))) (fst (snd (snd fresh-r))) final-rename-union ,
--    dis-final ,
--    compat-final
--    where
--    dis-init-r-l1 : DisjointFinSet (renaming-target-atoms init-r) (atoms/pattern l1)
--    dis-init-r-l1 = ?
--
--    fresh-l : Σ[ l2 ∈ Pattern ] Σ[ r ∈ Renaming ] 
--                    (PatternRenaming l1 l2 r × 
--                     DisjointFinSet (atoms/pattern l2) (atoms/pattern l1) ×
--                     CompatibleRenamings r init-r)
--    fresh-l = freshen-pattern l1 init-r dis-init-r-l1 init-bound
--
--    rename-l = (fst (snd fresh-l))
--
--    Σinit-r2 : Σ Renaming (RenamingUnion rename-l init-r)
--    Σinit-r2 = (renaming-union rename-l init-r (snd (snd (snd (snd fresh-l)))))
--    init-r2 = fst Σinit-r2
--
--    dis-init-r2-r1 : DisjointFinSet (renaming-target-atoms init-r2) (atoms/pattern r1)
--    dis-init-r2-r1 = ?
--
--    fresh-r : Σ[ r2 ∈ Pattern ] Σ[ r ∈ Renaming ] 
--                    (PatternRenaming r1 r2 r × 
--                     DisjointFinSet (atoms/pattern r2) (atoms/pattern r1) ×
--                     CompatibleRenamings r init-r2)
--    fresh-r = freshen-pattern r1 init-r2 dis-init-r2-r1 init-bound
--
--    rename-r = (fst (snd fresh-r))
--
--    Σfinal-rename : Σ Renaming (RenamingUnion rename-l rename-r)
--    Σfinal-rename = renaming-union rename-l rename-r ?
--    final-rename = fst Σfinal-rename
--    final-rename-union = snd Σfinal-rename
--      
--    dis-final : DisjointFinSet (atoms/pattern (branch (fst fresh-l) (fst fresh-r)))
--                               (atoms/pattern (branch l1 r1))
--    dis-final = (DisjointKeys-fm'-union d1 d2)
--      where
--      d-ll : DisjointFinSet (atoms/pattern l1) (atoms/pattern (fst fresh-l)) 
--      d-ll = Symmetric-DisjointKeys (fst (snd (snd (snd fresh-l))))
--      d-lr : DisjointFinSet (atoms/pattern l1) (atoms/pattern (fst fresh-r)) 
--      d-lr = ?
--      d-rl : DisjointFinSet (atoms/pattern r1) (atoms/pattern (fst fresh-l)) 
--      d-rl = ?
--      d-rr : DisjointFinSet (atoms/pattern r1) (atoms/pattern (fst fresh-r)) 
--      d-rr = Symmetric-DisjointKeys (fst (snd (snd (snd fresh-r))))
--
--
--
--
--      d1 : DisjointFinSet (atoms/pattern (branch (fst fresh-l) (fst fresh-r))) (atoms/pattern l1)
--      d1 = Symmetric-DisjointKeys (DisjointKeys-fm'-union d-ll d-lr)
--      d2 : DisjointFinSet (atoms/pattern (branch (fst fresh-l) (fst fresh-r))) (atoms/pattern r1)
--      d2 = Symmetric-DisjointKeys (DisjointKeys-fm'-union d-rl d-rr)
-- 
--     
-- 
-- 
--     compat-r2 : CompatibleRenamings init-r rename-r
--     compat-r2 = (compatible-extension init-r init-r2 rename-r 
--                                       (RenamingUnion.forward-right (snd Σinit-r2))
--                                       (Symmetric-CompatibleRenamings 
--                                         rename-r init-r2
--                                         (snd (snd (snd (snd fresh-r)))))
--                                       )
-- 
--     compat-final : CompatibleRenamings final-rename init-r
--     compat-final = compatible-union final-rename-union (snd (snd (snd (snd fresh-l)))) 
--                                     (Symmetric-CompatibleRenamings _ _ compat-r2)


retractions-compatible : (r1 r2 r3 : Renaming) -> 
                         RenamingExtension r1 r3 ->
                         RenamingExtension r2 r3 ->
                         CompatibleRenamings r1 r2
retractions-compatible r1 r2 r3 ext13 ext23 = record { range = range ; domain = domain }
  where
  range : {k v1 v2 : Atom} -> HasKV' k v1 ⟨ r1 ⟩ -> HasKV' k v2 ⟨ r2 ⟩ -> v1 == v2
  range hkv1 hkv2 = (snd (snd r3)) (ext13 hkv1) (ext23 hkv2)
  domain : {k1 k2 v : Atom} -> HasKV' k1 v ⟨ r1 ⟩ -> HasKV' k2 v ⟨ r2 ⟩ -> k1 == k2
  domain hkv1 hkv2 = (fst (snd r3)) (ext13 hkv1) (ext23 hkv2)

retractions-union : (r1 r2 r3 r4 : Renaming) -> 
                    RenamingExtension r1 r3 ->
                    RenamingExtension r2 r3 ->
                    RenamingUnion r1 r2 r4 ->
                    RenamingExtension r4 r3
retractions-union r1 r2 r3 r4 ext13 ext23 u124 hkv4 = 
  either ext13 ext23 (RenamingUnion.backward u124 hkv4)
  


toplevel-apply-rename : (p : Pattern) (r : Renaming) -> 
                        (∀ k -> HasKey' k (atoms/pattern p) -> HasKey' k ⟨ r ⟩) ->
                        Σ[ p2 ∈ Pattern ] Σ[ r2 ∈ Renaming ] (
                        RenamingExtension r2 r × 
                        PatternRenaming p p2 r2 ×
                        isSubFinSet (renaming-target-atoms r) (atoms/pattern p2))
toplevel-apply-rename (empty) r all-keys = 
  empty , empty-renaming , (\()) , empty , (\())
toplevel-apply-rename (var v) r all-keys = 
  var v2 , single-renaming v v2 , ext , var v v2 , sub
  where
  Σv2 = all-keys v (tt , has-kv-here refl refl []) 

  v2 : Atom
  v2 = fst Σv2
  ext : {k3 v3 : Atom} -> HasKV' k3 v3 ⟨ (single-renaming v v2) ⟩ -> HasKV' k3 v3 ⟨ r ⟩
  ext hk = subst2 (\ k v -> HasKV' k v ⟨ r ⟩) (sym (fst paths)) (sym (snd paths)) (snd Σv2)
    where
    paths = single-renaming-unique-value hk

  sub : {k3 : Atom} -> HasKey' k3 (fm-cons v2 tt []) -> HasKey' k3 (renaming-target-atoms r)
  sub (_ , (has-kv-here vp _ [])) = 
    subst (\ k -> HasKey' k (renaming-target-atoms r)) (sym vp) 
          (fm'-keys/HasKey (v , (fm'-invert/HasKV (snd Σv2))))
toplevel-apply-rename (eoa s t) r all-keys = 
  (eoa s (empty)) , empty-renaming , (\()) , eoa s t (empty) , (\())
toplevel-apply-rename (branch l r) ren all-keys = 
  handle (toplevel-apply-rename l ren all-keys-l) (toplevel-apply-rename r ren all-keys-r)
  where
  all-keys-l : ∀ k -> HasKey' k (atoms/pattern l) -> HasKey' k ⟨ ren ⟩
  all-keys-l k (v , hkv) = all-keys k (v , HasKV-fm'-union/left hkv)
  all-keys-r : ∀ k -> HasKey' k (atoms/pattern r) -> HasKey' k ⟨ ren ⟩
  all-keys-r k (v , hkv) = all-keys k (v , HasKV-fm'-union/right hkv)
  handle : Σ[ l2 ∈ Pattern ] Σ[ ren-l ∈ Renaming ] (
           RenamingExtension ren-l ren × PatternRenaming l l2 ren-l × 
           isSubFinSet (renaming-target-atoms ren) (atoms/pattern l2)) ->
           Σ[ r2 ∈ Pattern ] Σ[ ren-r ∈ Renaming ] (
           RenamingExtension ren-r ren × PatternRenaming r r2 ren-r ×
           isSubFinSet (renaming-target-atoms ren) (atoms/pattern r2)) ->
           Σ[ p2 ∈ Pattern ] Σ[ ren-p2 ∈ Renaming ] (
           RenamingExtension ren-p2 ren × PatternRenaming (branch l r) p2 ren-p2 × 
           isSubFinSet (renaming-target-atoms ren) (atoms/pattern p2))
  handle (l2 , ren-l , ext-l , pr-l , sub-l) (r2 , ren-r , ext-r , pr-r , sub-r) =
    (branch l2 r2) , (fst Σren-p2) , 
    retractions-union _ _ ren _ ext-l ext-r (snd Σren-p2) ,
    branch _ _ _ _ _ _ _ pr-l pr-r (snd Σren-p2) ,
    sub
    where
    Σren-p2 = renaming-union ren-l ren-r (retractions-compatible _ _ ren ext-l ext-r)
    sub : isSubFinSet (renaming-target-atoms ren) (atoms/pattern (branch l2 r2))
    sub hk = either sub-l sub-r (HasKey-fm'-union/split _ _ hk)

freshen-pattern : (p1 : Pattern) -> Σ[ p2 ∈ Pattern ] Σ[ r ∈ Renaming ] 
                                      (PatternRenaming p1 p2 r × 
                                      DisjointFinSet (atoms/pattern p2) (atoms/pattern p1))
freshen-pattern p1 = 
  p2 , (fst (snd Σpattern)) , (fst (snd (snd (snd Σpattern)))) , disjoint
  where
  Σrename = find-fresh-rename p1
  Σpattern = toplevel-apply-rename p1 (fst Σrename) (snd (snd Σrename))
  p2 = (fst Σpattern)

  isSub : isSubFinSet (renaming-target-atoms (fst Σrename)) (atoms/pattern p2)
  isSub = (snd (snd (snd (snd Σpattern))))

  

  disjoint : DisjointFinSet (atoms/pattern p2) (atoms/pattern p1)
  disjoint hkv2 hkv1 = (fst (snd Σrename)) (isSub hkv2) hkv1



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


