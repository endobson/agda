{-# OPTIONS --cubical --safe --exact-split #-}

module programming-languages.alpha-caml where

open import container.finmap
open import container.finmap.composition
open import container.finmap.entry-map
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
open import programming-languages.renamings

private
  variable
    ℓ : Level

Atom : Type₀
Atom = Nat

instance
  isSet'-Atom : isSet' Atom
  isSet'-Atom .isSet'.f = isSetNat

module _ where
  abstract
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

module _ (f g : Atom -> Atom) where

  rename-atom/term-compose : (t : Term) ->
   rename-atom/term f (rename-atom/term g t) ==
   rename-atom/term (f ∘ g) t
  rename-atom/pattern-compose : (p : Pattern) ->
   rename-atom/pattern f (rename-atom/pattern g p) ==
   rename-atom/pattern (f ∘ g) p

  rename-atom/term-compose empty = refl
  rename-atom/term-compose (const k) = refl
  rename-atom/term-compose (var v) = refl
  rename-atom/term-compose (branch t1 t2) = 
    cong2 branch (rename-atom/term-compose t1) (rename-atom/term-compose t2)
  rename-atom/term-compose (abstraction p) = 
    cong abstraction (rename-atom/pattern-compose p)

  rename-atom/pattern-compose empty = refl
  rename-atom/pattern-compose (var v) = refl
  rename-atom/pattern-compose (branch p1 p2) =
    cong2 branch (rename-atom/pattern-compose p1) (rename-atom/pattern-compose p2)
  rename-atom/pattern-compose (eoa s t) = 
    cong (eoa s) (rename-atom/term-compose t)


rename-atom/term-identity : (t : Term) ->
   rename-atom/term (\x -> x) t == t
rename-atom/pattern-identity : (p : Pattern) ->
   rename-atom/pattern (\x -> x) p == p

rename-atom/term-identity empty = refl
rename-atom/term-identity (const k) = refl
rename-atom/term-identity (var v) = refl
rename-atom/term-identity (branch t1 t2) = 
  cong2 branch (rename-atom/term-identity t1) (rename-atom/term-identity t2)
rename-atom/term-identity (abstraction p) = 
  cong abstraction (rename-atom/pattern-identity p)

rename-atom/pattern-identity empty = refl
rename-atom/pattern-identity (var v) = refl
rename-atom/pattern-identity (branch p1 p2) =
  cong2 branch (rename-atom/pattern-identity p1) (rename-atom/pattern-identity p2)
rename-atom/pattern-identity (eoa s t) = 
  cong (eoa s) (rename-atom/term-identity t)


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


rename-atom/term-support : {f g : Atom -> Atom} ->
   (t : Term) -> 
   ((a : Atom) -> HasKey' a (atoms/term t) -> f a == g a) ->
   rename-atom/term f t == rename-atom/term g t
rename-atom/pattern-support : {f g : Atom -> Atom} ->
   (p : Pattern) -> 
   ((a : Atom) -> HasKey' a (atoms/pattern p) -> f a == g a) ->
   rename-atom/pattern f p == rename-atom/pattern g p

rename-atom/term-support (var v) fg =
  cong var (fg v (tt , has-kv-here refl refl []))
rename-atom/term-support (const k) fg = refl
rename-atom/term-support (empty) fg = refl
rename-atom/term-support {f} {g} (branch t1 t2) fg = 
  cong2 branch (rename-atom/term-support t1 fg1) (rename-atom/term-support t2 fg2)
  where
  fg1 : (a : Atom) -> HasKey' a (atoms/term t1) -> f a == g a
  fg1 a (v , hkv) = fg a (v , HasKV-fm'-union/left hkv)
  fg2 : (a : Atom) -> HasKey' a (atoms/term t2) -> f a == g a
  fg2 a (v , hkv) = fg a (v , HasKV-fm'-union/right hkv)
rename-atom/term-support (abstraction p) fg = 
  cong abstraction (rename-atom/pattern-support p fg)

rename-atom/pattern-support (var v) fg =
  cong var (fg v (tt , has-kv-here refl refl []))
rename-atom/pattern-support (empty) fg = refl
rename-atom/pattern-support {f} {g} (branch t1 t2) fg =
  cong2 branch (rename-atom/pattern-support t1 fg1) (rename-atom/pattern-support t2 fg2)
  where
  fg1 : (a : Atom) -> HasKey' a (atoms/pattern t1) -> f a == g a
  fg1 a (v , hkv) = fg a (v , HasKV-fm'-union/left hkv)
  fg2 : (a : Atom) -> HasKey' a (atoms/pattern t2) -> f a == g a
  fg2 a (v , hkv) = fg a (v , HasKV-fm'-union/right hkv)
rename-atom/pattern-support (eoa s t) fg = 
  cong (eoa s) (rename-atom/term-support t fg)


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



isSubFinSet : FinSet Atom -> FinSet Atom -> Type₀
isSubFinSet fs1 fs2 = {k : Atom} -> HasKey' k fs2 -> HasKey' k fs1



data PatternRenaming : Pattern -> Pattern -> Renaming -> Type₀ where
  var : (v1 v2 : Atom) -> PatternRenaming (var v1) (var v2) (single-renaming v1 v2)
  empty : PatternRenaming empty empty empty-renaming
  eoa : (s : ScopeSpecifier) (t1 t2 : Term) -> PatternRenaming (eoa s t1) (eoa s t2) empty-renaming
  branch : (p1 p2 p3 p4 : Pattern) (r1 r2 r3 : Renaming) ->
           PatternRenaming p1 p3 r1 -> PatternRenaming p2 p4 r2 ->
           RenamingUnion r1 r2 r3 ->
           PatternRenaming (branch p1 p2) (branch p3 p4) r3

invert-PatternRenaming : {p1 p2 : Pattern} {r : Renaming} -> 
                         PatternRenaming p1 p2 r -> PatternRenaming p2 p1 (invert-renaming r)
invert-PatternRenaming {p1} {p2} (var v1 v2) = 
  subst (PatternRenaming p2 p1) (sym invert-single-renaming) (var v2 v1)
invert-PatternRenaming {p1} {p2} empty = 
  subst (PatternRenaming p2 p1) (sym invert-empty-renaming) empty
invert-PatternRenaming {p1} {p2} (eoa s t1 t2) = 
  subst (PatternRenaming p2 p1) (sym invert-empty-renaming) (eoa s t2 t1)
invert-PatternRenaming (branch p1 p2 p3 p4 r1 r2 r3 pr1 pr2 ru) = 
  (branch p3 p4 p1 p2 (invert-renaming r1) (invert-renaming r2) (invert-renaming r3) 
          (invert-PatternRenaming pr1) (invert-PatternRenaming pr2)
          (invert-RenamingUnion ru))

PatternRenamings->MatchedRenamings :
  {p1 p2 p3 : Pattern} {r1 r2 : Renaming} ->
  PatternRenaming p1 p2 r1 -> PatternRenaming p2 p3 r2 ->
  MatchedRenamings r1 r2
PatternRenamings->MatchedRenamings (var v1 v2) (var v2 v3) (has-kv-here kp vp _) =
  v3 , has-kv-here vp refl []
PatternRenamings->MatchedRenamings (empty) (empty) ()
PatternRenamings->MatchedRenamings (eoa s t1 t2) (eoa s t2 t3) ()
PatternRenamings->MatchedRenamings
  (branch p1 p2 p3 p4 r13 r24 ur1 pr13 pr24 ru1)
  (branch p3 p4 p5 p6 r35 r46 ur2 pr35 pr46 ru2) {k} {v} hkv-ur1 =
  handle (RenamingUnion.backward ru1 hkv-ur1)
  where
  handle : (HasKV' k v ⟨ r13 ⟩) ⊎ (HasKV' k v ⟨ r24 ⟩) -> Σ[ v2 ∈ Atom ] (HasKV' v v2 ⟨ ur2 ⟩)
  handle (inj-l hkv-r13) = 
    case (PatternRenamings->MatchedRenamings pr13 pr35 hkv-r13) of
      (\{ (v2 , hkv-r35) -> v2 , RenamingUnion.forward-left ru2 hkv-r35})
  handle (inj-r hkv-r24) = 
    case (PatternRenamings->MatchedRenamings pr24 pr46 hkv-r24) of
      (\{ (v2 , hkv-r46) -> v2 , RenamingUnion.forward-right ru2 hkv-r46})


transitive-PatternRenaming :
  {p1 p2 p3 : Pattern} {r1 r2 : Renaming} -> 
  PatternRenaming p1 p2 r1 -> PatternRenaming p2 p3 r2 ->
  Σ[ r3 ∈ Renaming ] (RenamingComposition r1 r2 r3 × PatternRenaming p1 p3 r3)
transitive-PatternRenaming (var v1 v2) (var v2 v3) = 
  single-renaming v1 v3 , RenamingComposition-single-renaming , var v1 v3
transitive-PatternRenaming (empty) (empty) = 
  empty-renaming , FinMapComposition'-empty-left , empty
transitive-PatternRenaming (eoa s t1 t2) (eoa s t2 t3) =
  empty-renaming , FinMapComposition'-empty-left , eoa s t1 t3
transitive-PatternRenaming
  (branch p1 p2 p3 p4 r13 r24 ur1 pr13 pr24 ru1)
  (branch p3 p4 p5 p6 r35 r46 ur2 pr35 pr46 ru2) =
  final-r , 
  c-final-r ,
  (branch p1 p2 p5 p6 (fst Σpr15) (fst Σpr26) final-r (snd (snd Σpr15)) (snd (snd Σpr26)) ans)
  where
  Σpr15 = transitive-PatternRenaming pr13 pr35
  Σpr26 = transitive-PatternRenaming pr24 pr46
  Σur = Σcompose-renamings ur1 ur2
  r7 = fst (Σpr15)
  r8 = fst (Σpr26)
  final-r = (fst Σur)
  c-final-r = (snd Σur)

  ans : RenamingUnion r7 r8 final-r
  ans = (RenamingUnion-RenamingComposition ru1 ru2 (fst (snd Σpr15)) (fst (snd Σpr26)) c-final-r
                                           (PatternRenamings->MatchedRenamings pr13 pr35)
                                           (PatternRenamings->MatchedRenamings pr24 pr46))


   

isFreshBoundOfSet : (fs : FinSet Atom) (v : Atom) -> Type₀
isFreshBoundOfSet fs b = {a : Atom} -> (HasKey' a fs) -> a < b 

isFreshBoundOfPattern : (p : Pattern) (v : Atom) -> Type₀
isFreshBoundOfPattern p = isFreshBoundOfSet (atoms/pattern p)

isFreshBoundOfTerm : (t : Term) (v : Atom) -> Type₀
isFreshBoundOfTerm t = isFreshBoundOfSet (atoms/term t)


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

computeFreshBoundOfSet : (fs : FinSet Atom) -> Σ Atom (isFreshBoundOfSet fs)
computeFreshBoundOfSet [] = 0 , \()
computeFreshBoundOfSet (fm-cons v _ m) = handle (computeFreshBoundOfSet m)
  where
  handle : Σ Atom (isFreshBoundOfSet m) -> Σ Atom (isFreshBoundOfSet (fm-cons v tt m) )
  handle (b , fb) = max (suc v) b , fresh
    where
    fresh : isFreshBoundOfSet (fm-cons v tt m) (max (suc v) b) 
    fresh (_ , (has-kv-here vp _ _)) = trans-≤ (suc-≤ (path-≤ vp)) (≤-max-left {suc v} {b})
    fresh (_ , (has-kv-skip _ _ hkv)) = trans-≤ (fb (tt , hkv)) ≤-max-right 


computeFreshBoundOfPattern : (p : Pattern) -> Σ Atom (isFreshBoundOfPattern p)
computeFreshBoundOfPattern p = computeFreshBoundOfSet (atoms/pattern p)
computeFreshBoundOfTerm : (t : Term) -> Σ Atom (isFreshBoundOfTerm t)
computeFreshBoundOfTerm t = computeFreshBoundOfSet (atoms/term t)

find-fresh-rename : 
  (source : FinSet Atom) (avoid : FinSet Atom) -> 
  Σ[ r ∈ Renaming ] (
    (DisjointFinSet (renaming-target-atoms r) avoid) ×
    (∀ k -> HasKey' k source -> HasKey' k ⟨ r ⟩))
find-fresh-rename source avoid = (renaming' , (inj-renaming , fun-renaming)) , dis , has-key
  where
  bound : Σ Atom (isFreshBoundOfSet avoid)
  bound = computeFreshBoundOfSet avoid
  b = fst bound
  fresh-b = snd bound

  f : Atom -> Top -> Atom
  f k _ = suc b +' k

  renaming' : FinMap' Atom Atom
  renaming' = fm'-value-map (\k _ -> suc b +' k) source

  fun-renaming : isFunctionalFinMap' renaming'
  fun-renaming {k} {v1} {v2} hkv1 hkv2 =
    handle (fm'-value-map/HasKV' _ hkv1) (fm'-value-map/HasKV' _ hkv2)
    where
    handle : Σ[ v ∈ Top ] ((f k v == v1) × HasKV' k v source) ->
             Σ[ v ∈ Top ] ((f k v == v2) × HasKV' k v source) ->
             v1 == v2
    handle (tt , k1p , _) (tt , k2p , _) = sym k1p >=> k2p

  inj-renaming : isInjectiveFinMap' renaming'
  inj-renaming {k1} {k2} {v2} hkv1 hkv2 =
    handle (fm'-value-map/HasKV' _ hkv1) (fm'-value-map/HasKV' _ hkv2)
    where
    handle : Σ[ v ∈ Top ] ((f k1 v == v2) × HasKV' k1 v source) ->
             Σ[ v ∈ Top ] ((f k2 v == v2) × HasKV' k2 v source) ->
             k1 == k2
    handle (_ , k1p , _) (_ , k2p , _) = 
      +'-left-injective {suc b} (k1p >=> sym k2p)

  has-key : (∀ k -> HasKey' k source -> HasKey' k renaming')
  has-key k (v , hkv) = _ , fm'-value-map/HasKV f hkv



  dis : (DisjointFinSet (fm'-keys (fm'-invert renaming')) avoid)
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
      handle : Σ[ v ∈ Top ] (f (fst hkv-r) v == k ×  HasKV' (fst hkv-r) v source) -> 
               b ≤ k
      handle (_ , p , _) = pred-≤ (right-suc-≤ sb≤k)
        where
        sb≤k : suc b ≤ k 
        sb≤k = (fst hkv-r) , +'-commute {fst hkv-r} {suc b} >=> p



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
  Σrename = find-fresh-rename (atoms/pattern p1) (atoms/pattern p1)
  Σpattern = toplevel-apply-rename p1 (fst Σrename) (snd (snd Σrename))
  p2 = (fst Σpattern)

  isSub : isSubFinSet (renaming-target-atoms (fst Σrename)) (atoms/pattern p2)
  isSub = (snd (snd (snd (snd Σpattern))))

  

  disjoint : DisjointFinSet (atoms/pattern p2) (atoms/pattern p1)
  disjoint hkv2 hkv1 = (fst (snd Σrename)) (isSub hkv2) hkv1


