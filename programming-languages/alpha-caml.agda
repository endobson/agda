{-# OPTIONS --cubical --safe --exact-split #-}

module programming-languages.alpha-caml where

open import base
open import relation
open import equality
open import functions
open import nat
open import list

private
  variable
    ℓ : Level

Atom : Type₀
Atom = Nat

DiscreteAtom : Discrete Atom
DiscreteAtom = decide-nat

FinSet : Type ℓ -> Type ℓ
FinSet = List

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

data isRenaming : Pred (List (Atom × Atom)) ℓ-zero
rename# : Atom -> Atom -> List (Atom × Atom) -> Type₀

data isRenaming where
  [] : isRenaming []
  rename-cons : {l : List (Atom × Atom)} -> (a1 a2 : Atom) -> (r : isRenaming l) -> 
                rename# a1 a2 l -> isRenaming ((a1 , a2) :: l)

rename# a1 a2 = ContainsAll \{(a3 , a4) -> (a1 != a3) × (a2 != a4)}


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


atoms/atom : Atom -> FinSet Atom
atoms/atom v = [ v ]

atoms/term : Term -> FinSet Atom
atoms/pattern : Pattern -> FinSet Atom

atoms/term empty = []
atoms/term (const _) = []
atoms/term (var v) = [ v ]
atoms/term (branch t1 t2) = atoms/term t1 ++ atoms/term t2
atoms/term (abstraction p) = atoms/pattern p

atoms/pattern empty = []
atoms/pattern (var v) = [ v ]
atoms/pattern (branch p1 p2) = atoms/pattern p1 ++ atoms/pattern p2
atoms/pattern (eoa s t) = atoms/term t

pattern/side : ScopeSpecifier -> Pattern -> Term
pattern/side _ empty  = empty
pattern/side _ (var _) = empty
pattern/side s (branch p1 p2) = (branch (pattern/side s p1) (pattern/side s p2))
pattern/side s1 (eoa s2 t) = 
  case (DiscreteScopeSpecifier s1 s2) of \{
    (yes _) -> t ;
    (no _) -> empty }


    
data α-equiv : Rel Term ℓ-zero where
  var : (v : Atom) -> α-equiv (var v) (var v)
  const : (v : Atom) -> α-equiv (const v) (const v)
  empty : α-equiv empty empty
  branch : {t1 t2 t3 t4 : Term} -> α-equiv t1 t2 -> α-equiv t3 t4 ->
           α-equiv (branch t1 t3) (branch t3 t4)
  abstraction : {p1 p2 : Pattern} ->
    α-equiv (abstraction p1) (abstraction p2)


-- lamA : Atom
-- lamA = 0
-- 
-- data LC : Pred Term ℓ-zero where
--   lam : 

