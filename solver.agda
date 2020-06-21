{-# OPTIONS --cubical --safe --exact-split #-}

module solver where

open import base
open import equality
open import fin
open import list
open import nat
open import ring
open import relation

import int

data Syntax (n : Nat) : Type₀ where
  _⊕_ : Syntax n -> Syntax n -> Syntax n
  _⊗_ : Syntax n -> Syntax n -> Syntax n
  var : Fin n -> Syntax n

data RingSyntax (n : Nat) : Type₀ where
  _⊕_ : RingSyntax n -> RingSyntax n -> RingSyntax n
  _⊗_ : RingSyntax n -> RingSyntax n -> RingSyntax n
  ⊖_ : RingSyntax n -> RingSyntax n
  ©_ : int.Int -> RingSyntax n
  var : Fin n -> RingSyntax n



infixl 6 _⊕_
infixl 7 _⊗_

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B C : Type ℓ

  data Vec (A : Type ℓ) : Nat -> Type ℓ where
    [] : Vec A zero
    _::_  : {n : Nat} -> (a : A) -> Vec A n -> Vec A (suc n)

  lookup : {n : Nat} -> Vec A n -> Fin n -> A
  lookup (a :: _) zero-fin = a
  lookup (_ :: v) (suc-fin f) = lookup v f

  Nary-level : (i j : Level) -> Nat -> Level
  Nary-level i j zero = j
  Nary-level i j (suc m) = (ℓ-max i (Nary-level i j m))

  Nary : (n : Nat) -> Type ℓ₁ -> Type ℓ₂ -> Type (Nary-level ℓ₁ ℓ₂ n)
  Nary zero _ B = B
  Nary (suc m) A B = A -> Nary m A B

  ∀ⁿ : {A : Type ℓ₁} -> (n : Nat) -> Nary n A (Type ℓ₂) -> Type (Nary-level ℓ₁ ℓ₂ n)
  ∀ⁿ zero P = P
  ∀ⁿ (suc m) P = ∀ x -> ∀ⁿ m (P x)

  ∀ⁿʰ : {A : Type ℓ₁} -> (n : Nat) -> Nary n A (Type ℓ₂) -> Type (Nary-level ℓ₁ ℓ₂ n)
  ∀ⁿʰ zero P = P
  ∀ⁿʰ (suc m) P = ∀ {x} -> ∀ⁿʰ m (P x)

  curry : (n : Nat) -> (Vec A n -> B) -> Nary n A B
  curry zero f = f []
  curry (suc m) f = (\e -> curry m (\v -> f (e :: v)))

  apply : (n : Nat) -> Nary n A B -> Vec A n -> B
  apply zero b [] = b
  apply (suc m) f (a :: v) = apply m (f a) v


  apply-curry-id : (n : Nat) -> (f : (Vec A n) -> B) -> (vec : Vec A n)
                   -> (apply n (curry n f) vec) == f vec
  apply-curry-id zero f [] = refl
  apply-curry-id (suc m) f (e :: v) = apply-curry-id m (\ v2 -> f (e :: v2)) v

  Eq : {A : Type ℓ₁} -> (n : Nat) -> (REL B C ℓ₂)
       -> (REL (Nary n A B) (Nary n A C) (Nary-level ℓ₁ ℓ₂ n))
  Eq n r f g = ∀ⁿ n (curry n (\ vec -> r (apply n f vec) (apply n g vec)))

  Eqʰ : {A : Type ℓ₁} -> (n : Nat) -> (REL B C ℓ₂)
        -> (REL (Nary n A B) (Nary n A C) (Nary-level ℓ₁ ℓ₂ n))
  Eqʰ n r f g = ∀ⁿʰ n (curry n (\ vec -> r (apply n f vec) (apply n g vec)))

  vec-map : {n : Nat} -> (A -> B) -> Vec A n -> Vec B n
  vec-map f [] = []
  vec-map f (e :: v) = (f e) :: (vec-map f v)

  all-fins : (n : Nat) -> Vec (Fin n) n
  all-fins zero = []
  all-fins (suc n) = zero-fin :: vec-map suc-fin (all-fins n)

  close : (n : Nat) -> Nary n (Syntax n) B -> B
  close n f =  apply n f (vec-map var (all-fins n))

  close' : (n : Nat) -> Nary n (RingSyntax n) B -> B
  close' n f =  apply n f (vec-map var (all-fins n))

  cong-curry : (n : Nat) (f : Vec A n -> B) -> (g : Vec A n -> B) -> ((v : Vec A n) -> (f v) == (g v))
               -> Eq n _==_ (curry n f) (curry n g)
  cong-curry zero f g f=g = f=g []
  cong-curry {A = A} {B = B} (suc n) f g f=g e = cong-curry n f' g' f=g'
    where
    f' : Vec A n -> B
    f' v = f (e :: v)
    g' : Vec A n -> B
    g' v = g (e :: v)
    f=g' : (v : Vec A n) -> (f' v) == (g' v)
    f=g' v = f=g (e :: v)

  cong-curry⁻¹ : (n : Nat) (f : Vec A n -> B) -> (g : Vec A n -> B)
               -> Eq n _==_ (curry n f) (curry n g)
               -> ((v : Vec A n) -> (f v) == (g v))
  cong-curry⁻¹ zero f g f=g [] = f=g
  cong-curry⁻¹ {A = A} {B = B} (suc n) f g f=g (e :: v) =
    (cong-curry⁻¹ n (\ v -> f (e :: v)) (\ v -> g (e :: v)) (f=g e)) v

  unhide-∀ⁿ : (n : Nat) -> {f : Nary n A (Type ℓ)}  -> ∀ⁿʰ n f -> ∀ⁿ n f
  unhide-∀ⁿ zero v = v
  unhide-∀ⁿ (suc n) g = (\ x -> (unhide-∀ⁿ n (g {x})))

  data Order {A : Type ℓ} : A -> A -> Type ℓ where
    less-than : {x y : A} -> Order x y
    equal-to : {x y : A} -> x == y -> Order x y
    greater-than : {x y : A} -> Order x y

  compare-nat : (x y : Nat) -> Order x y
  compare-nat zero zero = equal-to refl
  compare-nat (suc _) zero = greater-than
  compare-nat zero (suc _) = less-than
  compare-nat (suc m) (suc n) with compare-nat m n
  ... | less-than = less-than
  ... | equal-to p = equal-to (cong suc p)
  ... | greater-than = greater-than

  compare-fin : {n : Nat} (x y : Fin n) -> Order x y
  compare-fin m n with compare-nat (fin->nat m) (fin->nat n)
  ... | less-than = less-than
  ... | equal-to p = equal-to (transport (sym fin->nat-path) p)
  ... | greater-than = greater-than

  fin< : {n : Nat} -> Fin n -> Fin n -> Boolean
  fin< i j with compare-fin i j
  ... | less-than = true
  ... | equal-to _ = false
  ... | greater-than = false


  compare-list : ((a b : A) -> Order a b) -> (x y : List A) -> Order x y
  compare-list _ [] [] = equal-to refl
  compare-list _ (_ :: _) [] = greater-than
  compare-list _ [] (_ :: _) = less-than
  compare-list compare-elem (el :: ll) (er :: lr) with compare-elem el er
  ... | less-than = less-than
  ... | greater-than = greater-than
  ... | equal-to elem-pr with compare-list compare-elem ll lr
  ...    | less-than = less-than
  ...    | greater-than = greater-than
  ...    | equal-to list-pr = equal-to (\i -> (elem-pr i) :: (list-pr i))


module RingSolver {Domain : Type ℓ} (R : Ring Domain) where

  module _ (n : Nat) where
    private
      module R = Ring R
      open module M = Ring (ReaderRing (Vec Domain n) R)

      Meaning = (Vec Domain n) -> Domain

      -- Names of the normal forms

      Var : Type₀
      Var = Fin n

      Vars = List Var

      record Term : Type₀ where
        constructor term
        field
          multiplier : int.Int
          vars : Vars

      Terms : Type₀
      Terms = List Term

      record Expr : Type₀ where
        constructor expr
        field
          terms : Terms


      compare-vars : (x y : Vars) -> Order x y
      compare-vars = compare-list compare-fin



      term-* : Term -> Term -> Term
      term-* (term m1 vs1) (term m2 vs2) =
        (term (m1 int.* m2) (insertion-sort fin< (vs1 ++ vs2)))

      minus-one-term : Term
      minus-one-term = (term (int.- (int.int 1)) [])

      term-- : Term -> Term
      term-- = term-* minus-one-term

      merge-equal-terms : (t1 t2 : Term) -> (Term.vars t1 == Term.vars t2) -> Term
      merge-equal-terms (term m1 vars1) (term m2 vars2) _ = (term (m1 int.+ m2) vars1)

      merge-terms : Terms -> Terms -> Terms
      merge-terms1 : Term -> Terms -> Terms -> Terms

      merge-terms [] terms = terms
      merge-terms (t :: ts1) ts2 = merge-terms1 t ts1 ts2

      merge-terms1 t1 terms1 [] = t1 :: terms1
      merge-terms1 t1 terms1 (t2 :: terms2)
        with compare-vars (Term.vars t1) (Term.vars t2)
      ... | less-than = t1 :: (merge-terms1 t2 terms2 terms1)
      ... | greater-than = t2 :: (merge-terms1 t1 terms1 terms2)
      ... | equal-to pr = (merge-equal-terms t1 t2 pr) :: (merge-terms terms1 terms2)

      insertion-sort-terms' : Terms -> Terms -> Terms
      insertion-sort-terms' [] acc = acc
      insertion-sort-terms' (e :: l) acc = insertion-sort-terms' l (merge-terms1 e [] acc)

      insertion-sort-terms : Terms -> Terms
      insertion-sort-terms terms = insertion-sort-terms' terms []

      all-products : Terms -> Terms -> Terms
      all-products [] _ = []
      all-products (t1 :: terms1) terms2 =
        (merge-terms
          (insertion-sort-terms (map (term-* t1) terms2))
          (all-products terms1 terms2))

      filter-zero-terms : Terms -> Terms
      filter-zero-terms [] = []
      filter-zero-terms ((term (int.zero-int) vars) :: terms) =
        filter-zero-terms terms
      filter-zero-terms (term@(term (int.pos _) vars) :: terms) =
        term :: filter-zero-terms terms
      filter-zero-terms (term@(term (int.neg _) vars) :: terms) =
        term :: filter-zero-terms terms



      expr-+ : Expr -> Expr -> Expr
      expr-+ (expr terms1) (expr terms2) =
        (expr (filter-zero-terms (merge-terms terms1 terms2)))

      expr-* : Expr -> Expr -> Expr
      expr-* (expr terms1) (expr terms2) =
        (expr (all-products terms1 terms2))

      expr-- : Expr -> Expr
      expr-- (expr terms) = (expr (map term-- terms))

      normalize : RingSyntax n -> Expr
      normalize (var i) = expr ((term (int.int 1) (i :: [])) :: [])
      normalize (© x) = expr ((term x []) :: [])
      normalize (l ⊕ r) = expr-+ (normalize l) (normalize r)
      normalize (l ⊗ r) = expr-* (normalize l) (normalize r)
      normalize (⊖ e) = expr-- (normalize e)

      ⟦_⟧var : Var -> Meaning
      ⟦ i ⟧var env = lookup env i

      ⟦_⟧vars : Vars -> Meaning
      ⟦ is ⟧vars = (product (map ⟦_⟧var is))

      ⟦_⟧term : Term -> Meaning
      ⟦ (term m vars) ⟧term = (lift-int m) * ⟦ vars ⟧vars

      ⟦_⟧terms : Terms -> Meaning
      ⟦ terms ⟧terms = (sum (map ⟦_⟧term terms))

      ⟦_⟧norm : Expr -> Meaning
      ⟦ (expr terms) ⟧norm = ⟦ terms ⟧terms

      ⟦_⇓⟧ : RingSyntax n -> Meaning
      ⟦ e ⇓⟧ = ⟦ (normalize e) ⟧norm

      ⟦_⟧ : RingSyntax n -> Meaning
      ⟦ (var i) ⟧ env = lookup env i
      ⟦ (© x) ⟧ = (lift-int x)
      ⟦ l ⊕ r ⟧ = ⟦ l ⟧ + ⟦ r ⟧
      ⟦ l ⊗ r ⟧ = ⟦ l ⟧ * ⟦ r ⟧
      ⟦ ⊖ e ⟧ = - ⟦ e ⟧


      ++-vars≈ :
        ∀ vs1 vs2 -> ⟦ vs1 ++ vs2 ⟧vars == ⟦ vs1 ⟧vars * ⟦ vs2 ⟧vars
      ++-vars≈ vs1 vs2 = product-map-inject-++ ⟦_⟧var {vs1} {vs2}

      ++-terms≈ :
        ∀ ts1 ts2 -> ⟦ ts1 ++ ts2 ⟧terms == ⟦ ts1 ⟧terms + ⟦ ts2 ⟧terms
      ++-terms≈ ts1 ts2 = sum-map-inject-++ ⟦_⟧term {ts1} {ts2}

      ++-terms-flip :
        ∀ ts1 ts2 -> ⟦ ts1 ++ ts2 ⟧terms == ⟦ ts2 ++ ts1 ⟧terms
      ++-terms-flip ts1 ts2 =
        ++-terms≈ ts1 ts2 >=> (+-commute {⟦ ts1 ⟧terms} {⟦ ts2 ⟧terms}) >=> (sym (++-terms≈ ts2 ts1))

      merge-equal-terms≈ : ∀ t1 t2 pr
        -> ⟦ (merge-equal-terms t1 t2 pr) ⟧term == ⟦ t1 ⟧term + ⟦ t2 ⟧term
      merge-equal-terms≈ t1@(term m1 vars1) t2@(term m2 vars2) pr =
        begin
          ⟦ (merge-equal-terms t1 t2 pr) ⟧term
        ==<>
          (lift-int (m1 int.+ m2)) * ⟦ vars1 ⟧vars
        ==< *-left (sym (+-lift-int {m1} {m2})) >
          ((lift-int m1) + (lift-int m2)) * ⟦ vars1 ⟧vars
        ==< *-distrib-+-right >
          (lift-int m1) * ⟦ vars1 ⟧vars +
          (lift-int m2) * ⟦ vars1 ⟧vars
        ==< +-right (*-right (\i -> ⟦ pr i ⟧vars)) >
          (lift-int m1) * ⟦ vars1 ⟧vars +
          (lift-int m2) * ⟦ vars2 ⟧vars
        ==<>
          ⟦ t1 ⟧term + ⟦ t2 ⟧term
        end


      merge-terms≈ :
        ∀ ts1 ts2 -> ⟦ (merge-terms ts1 ts2) ⟧terms ==  ⟦ ts1 ++ ts2 ⟧terms
      merge-terms1≈ :
        ∀ t ts1 ts2 -> ⟦ (merge-terms1 t ts1 ts2) ⟧terms == ⟦ (t :: ts1) ++ ts2 ⟧terms

      merge-terms≈ [] ts = refl
      merge-terms≈ (e :: ts1) ts2 = merge-terms1≈ e ts1 ts2

      merge-terms1≈ t1 ts1 [] = ++-terms-flip [] (t1 :: ts1)
      merge-terms1≈ t1@(term m1 vars1) ts1 (t2@(term m2 vars2) :: ts2)
        with (compare-vars vars1 vars2)
      ... | less-than =
        begin
          ⟦ t1 ⟧term + ⟦ merge-terms1 t2 ts2 ts1 ⟧terms
        ==< +-right (merge-terms1≈ t2 ts2 ts1) >
          ⟦ t1 ⟧term + ⟦ (t2 :: ts2) ++ ts1 ⟧terms
        ==< +-right (++-terms-flip (t2 :: ts2) ts1) >
          ⟦ t1 ⟧term + ⟦ ts1 ++ (t2 :: ts2) ⟧terms
        ==<>
          ⟦ (t1 :: ts1) ++ (t2 :: ts2) ⟧terms
        end
      ... | greater-than =
        begin
          ⟦ t2 ⟧term + ⟦ merge-terms1 t1 ts1 ts2 ⟧terms
        ==< +-right (merge-terms1≈ t1 ts1 ts2) >
          ⟦ t2 ⟧term + ⟦ (t1 :: ts1) ++ ts2 ⟧terms
        ==< +-right (++-terms-flip (t1 :: ts1) ts2) >
          ⟦ t2 ⟧term + ⟦ ts2 ++ (t1 :: ts1) ⟧terms
        ==<>
          ⟦ (t2 :: ts2) ++ (t1 :: ts1) ⟧terms
        ==< ++-terms-flip (t2 :: ts2) (t1 :: ts1) >
          ⟦ (t1 :: ts1) ++ (t2 :: ts2) ⟧terms
        end
      ... | equal-to pr =
        begin
          ⟦ (merge-equal-terms t1 t2 pr) ⟧term + ⟦ merge-terms ts1 ts2 ⟧terms
        ==< +-left (merge-equal-terms≈ t1 t2 pr) >
          (⟦ t1 ⟧term + ⟦ t2 ⟧term) + ⟦ merge-terms ts1 ts2 ⟧terms
        ==< +-right (merge-terms≈ ts1 ts2) >
          (⟦ t1 ⟧term + ⟦ t2 ⟧term) + ⟦ ts1 ++ ts2 ⟧terms
        ==< +-right (++-terms-flip ts1 ts2) >
          (⟦ t1 ⟧term + ⟦ t2 ⟧term) + ⟦ ts2 ++ ts1 ⟧terms
        ==< +-assoc >
          ⟦ t1 ⟧term + ⟦ (t2 :: ts2) ++ ts1 ⟧terms
        ==< +-right (++-terms-flip (t2 :: ts2) ts1) >
           ⟦ (t1 :: ts1) ++ (t2 :: ts2) ⟧terms
        end


      insertion-sort'≈ :
        ∀ ts1 ts2 -> ⟦ (insertion-sort-terms' ts1 ts2) ⟧terms == ⟦ ts1 ++ ts2 ⟧terms
      insertion-sort'≈ [] ts2 = refl
      insertion-sort'≈ (t :: ts1) ts2 =
        begin
          ⟦ (insertion-sort-terms' (t :: ts1) ts2) ⟧terms
        ==<>
          ⟦ insertion-sort-terms' ts1 (merge-terms1 t [] ts2) ⟧terms
        ==< insertion-sort'≈ ts1 (merge-terms1 t [] ts2) >
          ⟦ ts1 ++ (merge-terms1 t [] ts2) ⟧terms
        ==< ++-terms≈ ts1 (merge-terms1 t [] ts2) >
          ⟦ ts1 ⟧terms + ⟦ (merge-terms1 t [] ts2) ⟧terms
        ==< +-right (merge-terms1≈ t [] ts2) >
          ⟦ ts1 ⟧terms + ⟦ (t :: []) ++ ts2 ⟧terms
        ==< +-right (++-terms≈ (t :: []) ts2) >
          ⟦ ts1 ⟧terms + (⟦ (t :: []) ⟧terms + ⟦ ts2 ⟧terms)
        ==< sym +-assoc >
          (⟦ ts1 ⟧terms + ⟦ (t :: []) ⟧terms) + ⟦ ts2 ⟧terms
        ==< +-left +-commute >
          (⟦ (t :: []) ⟧terms + ⟦ ts1 ⟧terms) + ⟦ ts2 ⟧terms
        ==< +-left (sym (++-terms≈ (t :: []) ts1)) >
          ⟦ (t :: ts1) ⟧terms + ⟦ ts2 ⟧terms
        ==< sym (++-terms≈ (t :: ts1) ts2) >
          ⟦ (t :: ts1) ++ ts2 ⟧terms
        end

      insertion-sort≈ :
        ∀ ts -> ⟦ (insertion-sort-terms ts) ⟧terms == ⟦ ts ⟧terms
      insertion-sort≈ ts = insertion-sort'≈ ts [] >=> ++-terms-flip ts []

      insertion-sort-vars≈ :
        ∀ vs -> ⟦ (insertion-sort fin< vs) ⟧vars == ⟦ vs ⟧vars
      insertion-sort-vars≈ vs =
        sym (product-map-Permutation ⟦_⟧var (Permutation-insertion-sort fin< vs))


      term-*≈ : ∀ t1 t2 -> ⟦ (term-* t1 t2) ⟧term == ⟦ t1  ⟧term * ⟦ t2 ⟧term
      term-*≈ t1@(term m1 vs1) t2@(term m2 vs2) =
        begin
          ⟦ (term-* t1 t2) ⟧term
        ==<>
          ⟦ (term (m1 int.* m2) (insertion-sort fin< (vs1 ++ vs2))) ⟧term
        ==<>
          (lift-int (m1 int.* m2)) * ⟦ (insertion-sort fin< (vs1 ++ vs2)) ⟧vars
        ==< *-right (insertion-sort-vars≈ (vs1 ++ vs2)) >
          (lift-int (m1 int.* m2)) * ⟦ (vs1 ++ vs2) ⟧vars
        ==< *-right (++-vars≈ vs1 vs2) >
          (lift-int (m1 int.* m2)) * (⟦ vs1 ⟧vars * ⟦ vs2 ⟧vars)
        ==< *-left (sym (*-lift-int {m1} {m2})) >
          ((lift-int m1) * (lift-int m2)) * (⟦ vs1 ⟧vars * ⟦ vs2 ⟧vars)
        ==< *-assoc >
          (lift-int m1) * ((lift-int m2) * (⟦ vs1 ⟧vars * ⟦ vs2 ⟧vars))
        ==< *-right (sym *-assoc) >
          (lift-int m1) * (((lift-int m2) * ⟦ vs1 ⟧vars) * ⟦ vs2 ⟧vars)
        ==< *-right (*-left *-commute) >
          (lift-int m1) * ((⟦ vs1 ⟧vars * (lift-int m2)) * ⟦ vs2 ⟧vars)
        ==< *-right *-assoc >
          (lift-int m1) * (⟦ vs1 ⟧vars * ((lift-int m2) * ⟦ vs2 ⟧vars))
        ==< sym *-assoc >
          ((lift-int m1) * ⟦ vs1 ⟧vars) * ((lift-int m2) * ⟦ vs2 ⟧vars)
        ==<>
          ⟦ t1  ⟧term * ⟦ t2 ⟧term
        end


      map-term-*≈ : ∀ t ts -> ⟦ (map (term-* t) ts) ⟧terms == ⟦ t  ⟧term * ⟦ ts ⟧terms
      map-term-*≈ t [] = sym *-right-zero
      map-term-*≈ t (t2 :: ts) =
        begin
          ⟦ (map (term-* t) (t2 :: ts)) ⟧terms
        ==<>
          ⟦ term-* t t2 ⟧term + ⟦ (map (term-* t) ts) ⟧terms
        ==< +-right (map-term-*≈ t ts) >
          ⟦ term-* t t2 ⟧term + ⟦ t ⟧term * ⟦ ts ⟧terms
        ==< +-left (term-*≈ t t2) >
          ⟦ t ⟧term * ⟦ t2 ⟧term + ⟦ t ⟧term * ⟦ ts ⟧terms
        ==< sym *-distrib-+-left >
          ⟦ t ⟧term * (⟦ t2 ⟧term + ⟦ ts ⟧terms)
        ==<>
          ⟦ t  ⟧term * ⟦ (t2 :: ts) ⟧terms
        end

      all-products≈ :
        ∀ ts1 ts2 -> ⟦ (all-products ts1 ts2) ⟧terms
                     == ⟦ ts1 ⟧terms * ⟦ ts2 ⟧terms
      all-products≈ [] ts2 = sym *-left-zero
      all-products≈ (t :: ts1) ts2 =
        begin
          ⟦ (all-products (t :: ts1) ts2) ⟧terms
        ==<>
          ⟦ merge-terms
             (insertion-sort-terms (map (term-* t) ts2))
             (all-products ts1 ts2) ⟧terms
        ==< merge-terms≈
             (insertion-sort-terms (map (term-* t) ts2))
             (all-products ts1 ts2) >
          ⟦ (insertion-sort-terms (map (term-* t) ts2))
            ++ (all-products ts1 ts2) ⟧terms
        ==< ++-terms≈ (insertion-sort-terms (map (term-* t) ts2))
                      (all-products ts1 ts2) >
          ⟦ (insertion-sort-terms (map (term-* t) ts2)) ⟧terms
          + ⟦ (all-products ts1 ts2) ⟧terms
        ==< +-left (insertion-sort≈ (map (term-* t) ts2)) >
          ⟦ (map (term-* t) ts2) ⟧terms + ⟦ (all-products ts1 ts2) ⟧terms
        ==< +-right (all-products≈ ts1 ts2) >
          ⟦ (map (term-* t) ts2) ⟧terms + ⟦ ts1 ⟧terms * ⟦ ts2 ⟧terms
        ==< +-left (map-term-*≈ t ts2) >
          ⟦ t  ⟧term * ⟦ ts2 ⟧terms + ⟦ ts1 ⟧terms * ⟦ ts2 ⟧terms
        ==< sym *-distrib-+-right >
          (⟦ t  ⟧term + ⟦ ts1 ⟧terms) * ⟦ ts2 ⟧terms
        ==<>
          ⟦ (t :: ts1) ⟧terms * ⟦ ts2 ⟧terms
        end


      filtered-terms≈ :
        ∀ ts -> ⟦ (filter-zero-terms ts) ⟧terms == ⟦ ts ⟧terms
      filtered-terms≈ [] = refl
      filtered-terms≈ (t@(term (int.zero-int) _) :: ts) =
        begin
          ⟦ (filter-zero-terms (t :: ts)) ⟧terms
        ==<>
          ⟦ (filter-zero-terms ts) ⟧terms
        ==< (filtered-terms≈ ts) >
          ⟦ ts ⟧terms
        ==< sym +-left-zero >
          0# + ⟦ ts ⟧terms
        ==< +-left (sym zero-term≈) >
          ⟦ t ⟧term + ⟦ ts ⟧terms
        ==<>
          ⟦ t :: ts ⟧terms
        end
        where
        zero-term≈ : ⟦ t ⟧term == 0#
        zero-term≈ = *-left-zero
      filtered-terms≈ (t@(term (int.neg _) vars) :: ts) =
        +-right (filtered-terms≈ ts)
      filtered-terms≈ (t@(term (int.pos _) vars) :: ts) =
        +-right (filtered-terms≈ ts)


      filtered-merge-terms≈ :
        ∀ ts1 ts2 -> ⟦ (filter-zero-terms (merge-terms ts1 ts2)) ⟧terms
                     == ⟦ ts1 ⟧terms + ⟦ ts2 ⟧terms
      filtered-merge-terms≈ ts1 ts2 =
        filtered-terms≈ (merge-terms ts1 ts2) >=>
        merge-terms≈ ts1 ts2 >=>
        ++-terms≈ ts1 ts2

      minus-one-term≈ : ⟦ minus-one-term ⟧term == - 1#
      minus-one-term≈ =
        begin
          ⟦ minus-one-term ⟧term
        ==<>
          ⟦ (term (int.- (int.int 1)) []) ⟧term
        ==< *-right-one >
          (lift-int (int.- (int.int 1)))
        ==< cong -_ +-right-zero >
          - 1#
        end


      expr--≈ : ∀ e -> ⟦ expr-- e ⟧norm == - ⟦ e ⟧norm
      expr--≈ e@(expr terms) =
        begin
          ⟦ expr-- e ⟧norm
        ==< map-term-*≈ minus-one-term terms >
          ⟦ minus-one-term ⟧term * ⟦ e ⟧norm
        ==< *-left minus-one-term≈ >
          - 1# * ⟦ e ⟧norm
        ==< *-left-minus-one >
          - ⟦ e ⟧norm
        end


      correct : (e : RingSyntax n) -> ⟦ e ⇓⟧ == ⟦ e ⟧
      correct (var i) =
        begin
          ⟦ (var i) ⇓⟧
        ==<>
          ⟦ ((term (int.int 1) (i :: [])) :: []) ⟧terms
        ==< +-right-zero >
          ⟦ (term (int.int 1) (i :: [])) ⟧term
        ==< *-left (+-right-zero) >=> *-left-one >
          ⟦ (i :: []) ⟧vars
        ==< *-right-one >
          ⟦ i ⟧var
        ==<>
          ⟦ (var i) ⟧
        end
      correct (© x) =
        begin
          ⟦ (© x) ⇓⟧
        ==<>
          ⟦ ((term x []) :: []) ⟧terms
        ==< +-right-zero >
          ⟦ (term x []) ⟧term
        ==< *-right-one >
          (lift-int x)
        ==<>
          ⟦ (© x) ⟧
        end
      correct (⊖ e) =
        begin
          ⟦ (⊖ e) ⇓⟧
        ==<>
          ⟦ expr-- (normalize e) ⟧norm
        ==< expr--≈ (normalize e) >
          - ⟦ (normalize e) ⟧norm
        ==<>
          - ⟦ e ⇓⟧
        ==< cong -_ (correct e) >
          - ⟦ e ⟧
        ==<>
          ⟦ (⊖ e) ⟧
        end
      correct (l ⊕ r) =
        begin
          ⟦ (l ⊕ r) ⇓⟧
        ==<>
          ⟦ normalize (l ⊕ r) ⟧norm
        ==< normalize-split >
          ⟦ normalize l ⟧norm + ⟦ normalize r ⟧norm
        ==<>
          ⟦ l ⇓⟧ + ⟦ r ⇓⟧
        ==< (cong2 _+_ (correct l) (correct r)) >
          ⟦ l ⟧ + ⟦ r ⟧
        ==<>
          ⟦ (l ⊕ r) ⟧
        end
        where
        normalize-split :
          ⟦ normalize (l ⊕ r) ⟧norm ==
          ⟦ normalize l ⟧norm + ⟦ normalize r ⟧norm
        normalize-split with (normalize l)  | (normalize r)
        ...                | (expr l-terms) | (expr r-terms) =
          filtered-merge-terms≈ l-terms r-terms
      correct  (l ⊗ r) =
        begin
          ⟦ (l ⊗ r) ⇓⟧
        ==<>
          ⟦ normalize (l ⊗ r) ⟧norm
        ==< normalize-split >
          ⟦ normalize l ⟧norm * ⟦ normalize r ⟧norm
        ==<>
          ⟦ l ⇓⟧ * ⟦ r ⇓⟧
        ==< (cong2 _*_ (correct l) (correct r)) >
          ⟦ l ⟧ * ⟦ r ⟧
        ==<>
          ⟦ (l ⊗ r) ⟧
        end
        where
        normalize-split :
          ⟦ normalize (l ⊗ r) ⟧norm ==
          ⟦ normalize l ⟧norm * ⟦ normalize r ⟧norm
        normalize-split with (normalize l)  | (normalize r)
        ...                | (expr l-terms) | (expr r-terms) =
          all-products≈ l-terms r-terms


    solve : (f : Nary n (RingSyntax n) ((RingSyntax n) × (RingSyntax n)))
            ->  Eqʰ n _==_ (curry n ⟦ proj₁ (close' n f) ⇓⟧) (curry n ⟦ proj₂ (close' n f) ⇓⟧)
            ->  Eq n _==_ (curry n ⟦ proj₁ (close' n f) ⟧) (curry n ⟦ proj₂ (close' n f) ⟧)
    solve f hidden-normal-proof = full-reg-proof
      where
      e₁ : RingSyntax n
      e₁ = proj₁ (close' n f)
      e₂ : RingSyntax n
      e₂ = proj₂ (close' n f)

      full-normal-proof : Eq n _==_ (curry n ⟦ e₁ ⇓⟧) (curry n ⟦ e₂ ⇓⟧)
      full-normal-proof = unhide-∀ⁿ n hidden-normal-proof

      inner-normal-proof : (ρ : (Vec Domain n)) -> (⟦ e₁ ⇓⟧ ρ) == (⟦ e₂ ⇓⟧ ρ)
      inner-normal-proof = cong-curry⁻¹ n (⟦ e₁ ⇓⟧) (⟦ e₂ ⇓⟧) full-normal-proof

      prove : (ρ : Vec Domain n) -> ⟦ e₁ ⇓⟧ ρ == ⟦ e₂ ⇓⟧ ρ -> ⟦ e₁ ⟧ ρ == ⟦ e₂ ⟧ ρ
      prove ρ pr = (sym (\i -> (correct e₁ i ρ))) >=> pr >=> (\i -> (correct e₂ i ρ))

      inner-reg-proof : (ρ : (Vec Domain n)) -> (⟦ e₁ ⟧ ρ) == (⟦ e₂ ⟧ ρ)
      inner-reg-proof v = (prove v (inner-normal-proof v))

      full-reg-proof : Eq n _==_ (curry n ⟦ e₁ ⟧) (curry n ⟦ e₂ ⟧)
      full-reg-proof = cong-curry n (⟦ e₁ ⟧) (⟦ e₂ ⟧) inner-reg-proof



module Solver {Domain : Type ℓ} (S : Semiring Domain) where
  module S = Semiring S

  module _ (n : Nat) where

    open module M = Semiring (ReaderSemiring (Vec Domain n) S)
    Meaning = Vec Domain n -> Domain

    ⟦_⟧ : Syntax n -> Meaning
    ⟦ (var i) ⟧ env = lookup env i
    ⟦ l ⊕ r ⟧ = ⟦ l ⟧ + ⟦ r ⟧
    ⟦ l ⊗ r ⟧ = ⟦ l ⟧ * ⟦ r ⟧


    data Term : Type₀ where
      var : Fin n -> Term
      _⊗_ : Term -> Term -> Term


    term< : Term -> Term -> Boolean
    term< t1 t2 = res
      where
      flatten : Term -> List (Fin n)
      flatten (var i) = (i :: [])
      flatten (l ⊗ r) = (flatten l) ++ (flatten r)
      res : Boolean
      res with (compare-list compare-fin (insertion-sort fin< (flatten t1))
                                         (insertion-sort fin< (flatten t2)))
      ... | less-than = true
      ... | greater-than = false
      ... | equal-to _ = false



    all-pairs : List Term -> List Term -> List Term
    all-pairs [] b = []
    all-pairs (e :: a) b = (map (e ⊗_) b) ++ (all-pairs a b)

    linearize : Syntax n -> List Term
    linearize (var i) = (var i) :: []
    linearize (l ⊕ r) = (linearize l) ++ (linearize r)
    linearize (l ⊗ r) = all-pairs (linearize l) (linearize r)


    ⟦_⟧term : Term -> Meaning
    ⟦ (var i) ⟧term env = lookup env i
    ⟦ t1 ⊗ t2  ⟧term = ⟦ t1  ⟧term * ⟦ t2 ⟧term


    ⟦_⟧terms : List Term -> Meaning
    ⟦ l ⟧terms = (sum (map ⟦_⟧term l))


    terms-eval-inject-++ : (a b : List Term) -> ⟦ a ++ b ⟧terms == ⟦ a ⟧terms + ⟦ b ⟧terms
    terms-eval-inject-++ a b = (sum-map-inject-++ ⟦_⟧term {a} {b})


    terms-eval-inject-map-⊗ :
      {e : Term} -> {b : List Term}
      -> ⟦ (map (e ⊗_) b) ⟧terms == ⟦ e ⟧term * ⟦ b ⟧terms
    terms-eval-inject-map-⊗ {e} {[]} = sym (*-right-zero {⟦ e ⟧term})
    terms-eval-inject-map-⊗ {e} {(e2 :: b)} =
      begin
        ⟦ (map (e ⊗_) (e2 :: b)) ⟧terms
      ==<>
        ⟦ (map (e ⊗_) (e2 :: [])) ++ (map (e ⊗_) b) ⟧terms
      ==< terms-eval-inject-++ (map (e ⊗_) (e2 :: [])) (map (e ⊗_) b) >
        ⟦ map (e ⊗_) (e2 :: []) ⟧terms + ⟦ (map (e ⊗_) b) ⟧terms
      ==<>
        (⟦ e ⊗ e2 ⟧term + 0#) + ⟦ (map (e ⊗_) b) ⟧terms
      ==< +-left (+-right-zero {⟦ e ⊗ e2 ⟧term}) >
        ⟦ e ⊗ e2 ⟧term + ⟦ (map (e ⊗_) b) ⟧terms
      ==< +-right {⟦ e ⊗ e2 ⟧term} (terms-eval-inject-map-⊗ {e} {b}) >
        ⟦ e ⊗ e2 ⟧term + ⟦ e ⟧term * ⟦ b ⟧terms
      ==<>
        ⟦ e ⟧term * ⟦ e2 ⟧term + ⟦ e ⟧term * ⟦ b ⟧terms
      ==< sym (*-distrib-+-left {⟦ e ⟧term}) >
        ⟦ e ⟧term * (⟦ e2 ⟧term + ⟦ b ⟧terms)
      ==<>
        ⟦ e ⟧term * ⟦ (e2 :: b) ⟧terms
      end


    terms-eval-inject-all-pairs : {a b : List Term}
      -> ⟦ (all-pairs a b) ⟧terms == ⟦ a ⟧terms * ⟦ b ⟧terms
    terms-eval-inject-all-pairs {[]} {b} = sym (*-left-zero {⟦ b ⟧terms})
    terms-eval-inject-all-pairs {e :: a} {b} =
      begin
        ⟦ (all-pairs (e :: a) b) ⟧terms
      ==<>
        ⟦ (map (e ⊗_) b) ++ (all-pairs a b) ⟧terms
      ==< terms-eval-inject-++ (map (e ⊗_) b) (all-pairs a b) >
        (⟦ (map (e ⊗_) b) ⟧terms) + (⟦ (all-pairs a b) ⟧terms)
      ==< +-left (terms-eval-inject-map-⊗ {e} {b}) >
        (⟦ e ⟧term * ⟦ b ⟧terms) + ⟦ (all-pairs a b) ⟧terms
      ==< +-right {(⟦ e ⟧term * ⟦ b ⟧terms)}
                    (terms-eval-inject-all-pairs {a} {b}) >
        (⟦ e ⟧term * ⟦ b ⟧terms) + (⟦ a ⟧terms * ⟦ b ⟧terms)
      ==< sym (*-distrib-+-right {⟦ e ⟧term}) >
        (⟦ e ⟧term + ⟦ a ⟧terms) * ⟦ b ⟧terms
      ==<>
        ⟦ (e :: a) ⟧terms * ⟦ b ⟧terms
      end




    terms-eval-inject-linearize-⊕ :
      {e1 e2 : Syntax n}
      -> ⟦ linearize (e1 ⊕ e2) ⟧terms ==
         ⟦ linearize e1 ⟧terms + ⟦ linearize e2 ⟧terms
    terms-eval-inject-linearize-⊕ {e1} {e2} =
      terms-eval-inject-++ (linearize e1) (linearize e2)

    terms-eval-inject-linearize-⊗ :
      {e1 e2 : Syntax n}
      -> ⟦ linearize (e1 ⊗ e2) ⟧terms ==
         ⟦ linearize e1 ⟧terms * ⟦ linearize e2 ⟧terms
    terms-eval-inject-linearize-⊗ {e1} {e2} =
      terms-eval-inject-all-pairs {linearize e1} {linearize e2}

    terms-eval-inject-insertion-sort :
      {ts : List Term}
      -> ⟦ (insertion-sort term< ts) ⟧terms == ⟦ ts ⟧terms
    terms-eval-inject-insertion-sort {ts} =
      sym (sum-map-Permutation (\ t -> ⟦ t ⟧term) (Permutation-insertion-sort term< ts))


    ⟦_⇓⟧ : Syntax n -> Meaning
    ⟦ e ⇓⟧ = ⟦ (insertion-sort term< (linearize e)) ⟧terms

    correct : (e : Syntax n) -> ⟦ e ⇓⟧ == ⟦ e ⟧
    correct (var i) = +-right-zero
    correct (l ⊕ r) =
      begin
        ⟦ l ⊕ r ⇓⟧
      ==<>
        ⟦ insertion-sort term< (linearize (l ⊕ r)) ⟧terms
      ==< terms-eval-inject-insertion-sort {linearize (l ⊕ r)} >
        ⟦ linearize (l ⊕ r) ⟧terms
      ==< terms-eval-inject-linearize-⊕ {l} {r} >
        ⟦ linearize l ⟧terms + ⟦ linearize r ⟧terms
      ==< (+-cong
              (sym (terms-eval-inject-insertion-sort {linearize l}))
              (sym (terms-eval-inject-insertion-sort {linearize r}))) >
        ⟦ insertion-sort term< (linearize l) ⟧terms +
        ⟦ insertion-sort term< (linearize r) ⟧terms
      ==< +-cong (correct l) (correct r) >
        ⟦ l ⟧ + ⟦ r ⟧
      ==<>
        ⟦ l ⊕ r ⟧
      end
    correct (l ⊗ r)=
      begin
        ⟦ l ⊗ r ⇓⟧
      ==<>
        ⟦ insertion-sort term< (linearize (l ⊗ r)) ⟧terms
      ==< terms-eval-inject-insertion-sort {linearize (l ⊗ r)} >
        ⟦ linearize (l ⊗ r) ⟧terms
      ==< terms-eval-inject-linearize-⊗ {l} {r} >
        ⟦ linearize l ⟧terms * ⟦ linearize r ⟧terms
      ==< (*-cong
              (sym (terms-eval-inject-insertion-sort {linearize l}))
              (sym (terms-eval-inject-insertion-sort {linearize r}))) >
        ⟦ insertion-sort term< (linearize l) ⟧terms *
        ⟦ insertion-sort term< (linearize r) ⟧terms
      ==< *-cong (correct l) (correct r) >
        ⟦ l ⟧ * ⟦ r ⟧
      ==<>
        ⟦ l ⊗ r ⟧
      end



    solve : (f : Nary n (Syntax n) ((Syntax n) × (Syntax n)))
            ->  Eqʰ n _==_ (curry n ⟦ (proj₁ (close n f)) ⇓⟧) (curry n ⟦ proj₂ (close n f) ⇓⟧)
            ->  Eq n _==_ (curry n ⟦ proj₁ (close n f) ⟧) (curry n ⟦ proj₂ (close n f) ⟧)
    solve f hidden-normal-proof = full-reg-proof
      where
      e₁ : Syntax n
      e₁ = proj₁ (close n f)
      e₂ : Syntax n
      e₂ = proj₂ (close n f)

      full-normal-proof : Eq n _==_ (curry n ⟦ e₁ ⇓⟧) (curry n ⟦ e₂ ⇓⟧)
      full-normal-proof = unhide-∀ⁿ n hidden-normal-proof

      inner-normal-proof : (ρ : (Vec Domain n)) -> (⟦ e₁ ⇓⟧ ρ) == (⟦ e₂ ⇓⟧ ρ)
      inner-normal-proof = cong-curry⁻¹ n (⟦ e₁ ⇓⟧) (⟦ e₂ ⇓⟧) full-normal-proof

      prove : (ρ : Vec Domain n) -> ⟦ e₁ ⇓⟧ ρ == ⟦ e₂ ⇓⟧ ρ -> ⟦ e₁ ⟧ ρ == ⟦ e₂ ⟧ ρ
      prove ρ pr = (sym (\i -> (correct e₁ i ρ))) >=> pr >=> (\i -> (correct e₂ i ρ))

      inner-reg-proof : (ρ : (Vec Domain n)) -> (⟦ e₁ ⟧ ρ) == (⟦ e₂ ⟧ ρ)
      inner-reg-proof v = (prove v (inner-normal-proof v))

      full-reg-proof : Eq n _==_ (curry n ⟦ e₁ ⟧) (curry n ⟦ e₂ ⟧)
      full-reg-proof = cong-curry n (⟦ e₁ ⟧) (⟦ e₂ ⟧) inner-reg-proof


module NatSolver = Solver NatSemiring
module IntSolver = RingSolver IntRing

module examples where
  module semi where
    example1 : (a b c d : Nat) -> (a +' c) +' (b +' d) == a +' (b +' c) +' d
    example1 = NatSolver.solve 4 (\ a b c d -> ((a ⊕ c) ⊕ (b ⊕ d)) , (a ⊕ (b ⊕ c)) ⊕ d) refl

    example2 : (a b c : Nat) -> (a +' b) *' c == (b *' c) +' (a *' c)
    example2 = NatSolver.solve 3 (\ a b c -> (a ⊕ b) ⊗ c , (b ⊗ c) ⊕ (a ⊗ c)) refl

    example3 : (a b c d : Nat) -> (a +' c) *' (b +' d) == a *' b +' c *' d +' c *' b +' a *' d
    example3 = NatSolver.solve 4 (\ a b c d -> ((a ⊕ c) ⊗ (b ⊕ d)) ,
                                               (a ⊗ b) ⊕ (c ⊗ d) ⊕ (c ⊗ b) ⊕ (a ⊗ d)) refl

  module full where
    open int

    example1 : (a b c d : Int) -> (a + c) * (b + d) == a * b + c * d + c * b + a * d
    example1 = IntSolver.solve 4 (\ a b c d -> ((a ⊕ c) ⊗ (b ⊕ d)) ,
                                               (a ⊗ b) ⊕ (c ⊗ d) ⊕ (c ⊗ b) ⊕ (a ⊗ d)) refl


    example2 : (x y a b : Int) ->
         (x + y) * (a + b) + (x + - y) * (a + - b) ==
         (x * b + x * - b) + ((x * a + y * b) + ((x * a + - y * - b) + (y * a + - y * a)))
    example2 =
     IntSolver.solve 4
       (\ x y a b ->
         (x ⊕ y) ⊗ (a ⊕ b) ⊕ (x ⊕ (⊖ y)) ⊗ (a ⊕ (⊖ b)) ,
         (x ⊗ b ⊕ x ⊗ (⊖ b)) ⊕ ((x ⊗ a ⊕ y ⊗ b) ⊕ ((x ⊗ a ⊕ (⊖ y) ⊗ (⊖ b)) ⊕ (y ⊗ a ⊕ (⊖ y) ⊗ a))))
       refl

    example3 : (x y a b : Int) ->
        (x + y) * (a + b) + (x + - y) * (a + - b) ==
        (int 2) * (x * a + y * b)
    example3 =
      IntSolver.solve 4
        (\ x y a b  ->
          (x ⊕ y) ⊗ (a ⊕ b) ⊕ (x ⊕ (⊖ y)) ⊗ (a ⊕ (⊖ b)) ,
          (© (int 2)) ⊗ (x ⊗ a ⊕ y ⊗ b))
        refl




