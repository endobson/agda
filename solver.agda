{-# OPTIONS --cubical --safe --exact-split #-}

module solver where

open import base
open import list
open import ring
open import equality
open import relation
open import nat
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
import int

data Syntax (n : Nat) : Set where
  _⊕_ : Syntax n -> Syntax n -> Syntax n
  _⊗_ : Syntax n -> Syntax n -> Syntax n
  var : Fin n -> Syntax n

data RingSyntax (n : Nat) : Set where
  _⊕_ : RingSyntax n -> RingSyntax n -> RingSyntax n
  _⊗_ : RingSyntax n -> RingSyntax n -> RingSyntax n
  ⊖_ : RingSyntax n -> RingSyntax n
  var : Fin n -> RingSyntax n


infixl 6 _⊕_
infixl 7 _⊗_

private 
  variable
    i a b c : Level
    A : Set a
    B : Set b
    C : Set c

  data Vec (A : Set a) : Nat -> Set a where
    [] : Vec A zero
    _::_  : {n : Nat} -> (a : A) -> Vec A n -> Vec A (suc n)
  
  lookup : {n : Nat} -> Vec A n -> Fin n -> A
  lookup (a :: _) zero-fin = a
  lookup (_ :: v) (suc-fin f) = lookup v f
  
  Nary-level : (i j : Level) -> Nat -> Level
  Nary-level i j zero = j
  Nary-level i j (suc m) = i ⊔ (Nary-level i j m)

  Nary : (n : Nat) -> Set a -> Set b -> Set (Nary-level a b n)
  Nary zero _ B = B
  Nary (suc m) A B = A -> Nary m A B

  ∀ⁿ : {A : Set a} -> (n : Nat) -> Nary n A (Set i) -> Set (Nary-level a i n)
  ∀ⁿ zero P = P
  ∀ⁿ (suc m) P = ∀ x -> ∀ⁿ m (P x)

  ∀ⁿʰ : {A : Set a} -> (n : Nat) -> Nary n A (Set i) -> Set (Nary-level a i n)
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

  Eq : {A : Set a} -> (n : Nat) -> (REL B C i) 
       -> (REL (Nary n A B) (Nary n A C) (Nary-level a i n))
  Eq n r f g = ∀ⁿ n (curry n (\ vec -> r (apply n f vec) (apply n g vec)))
  
  Eqʰ : {A : Set a} -> (n : Nat) -> (REL B C i) 
        -> (REL (Nary n A B) (Nary n A C) (Nary-level a i n))
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
  
  unhide-∀ⁿ : {A : Set a} -> (n : Nat) -> {f : Nary n A (Set i)}  -> ∀ⁿʰ n f -> ∀ⁿ n f
  unhide-∀ⁿ zero v = v
  unhide-∀ⁿ (suc n) g = (\ x -> (unhide-∀ⁿ n (g {x})))


  data Order : Set where
    less-than : Order
    equal-to : Order
    greater-than : Order
  
  compare-nat : Nat -> Nat -> Order
  compare-nat zero zero = equal-to
  compare-nat (suc _) zero = greater-than
  compare-nat zero (suc _) = less-than
  compare-nat (suc m) (suc n) = compare-nat m n
  
  compare-fin : {n : Nat} -> Fin n -> Fin n -> Order
  compare-fin m n = compare-nat (fin->nat m) (fin->nat n)
  
  fin< : {n : Nat} -> Fin n -> Fin n -> Boolean
  fin< i j with compare-fin i j
  ... | less-than = true
  ... | equal-to = false
  ... | greater-than = false
  
  
  compare-list : (A -> A -> Order) -> List A -> List A -> Order
  compare-list _ [] [] = equal-to
  compare-list _ (_ :: _) [] = greater-than
  compare-list _ [] (_ :: _) = less-than
  compare-list compare-elem (el :: ll) (er :: lr) with compare-elem el er
  ... | equal-to = compare-list compare-elem ll lr
  ... | less-than = less-than
  ... | greater-than = greater-than


module RingSolver (R : Ring {lzero}) where

  module _ (n : Nat) where
    private
      module R = Ring R
      open module M = Ring (ReaderRing (Vec R.Domain n) R)
        renaming (Domain to Meaning)

      record NormalTerm : Set where
        constructor normal-term
        field
          multiplier : int.Int
          vars : List (Fin n)
  
      record NormalExpr : Set where
        constructor normal-expr
        field
          terms : List NormalTerm 


  
      compare-term : NormalTerm -> NormalTerm -> Order
      compare-term (normal-term _ vars1) (normal-term _ vars2) =
        compare-list compare-fin vars1 vars2
  
      normal-term-- : NormalTerm -> NormalTerm
      normal-term-- (normal-term m vars) = (normal-term (int.- m) vars)
  
      multiply-term : NormalTerm -> NormalTerm -> NormalTerm
      multiply-term (normal-term m1 vs1) (normal-term m2 vs2) =
        (normal-term (m1 int.* m2) (insertion-sort fin< (vs1 ++ vs2)))
  
      merge-terms : List NormalTerm -> List NormalTerm -> List NormalTerm
      merge-terms1 : NormalTerm -> List NormalTerm -> List NormalTerm -> List NormalTerm
  
      merge-terms [] terms = terms
      merge-terms (term :: terms1) terms2 = merge-terms1 term terms1 terms2
  
      merge-terms1 t1 terms1 [] = t1 :: terms1
      merge-terms1 t1@(normal-term m1 vars1) terms1 (t2@(normal-term m2 _) :: terms2) 
        with compare-term t1 t2
      ... | less-than = t1 :: (merge-terms1 t2 terms2 terms1)
      ... | greater-than = t2 :: (merge-terms1 t1 terms1 terms2)
      ... | equal-to = (normal-term (m1 int.+ m2) vars1) :: (merge-terms terms1 terms2)
  
  
      insertion-sort-terms : List NormalTerm -> List NormalTerm
      insertion-sort-terms terms = rec terms []
        where
        rec : List NormalTerm -> List NormalTerm -> List NormalTerm
        rec [] acc = acc
        rec (e :: l) acc = rec l (merge-terms1 e [] acc)
  
      all-products : List NormalTerm -> List NormalTerm -> List NormalTerm
      all-products [] _ = []
      all-products (t1 :: terms1) terms2 = 
        (merge-terms
          (insertion-sort-terms (map (multiply-term t1) terms2))
          (all-products terms1 terms2))
  
      filter-zero-multiplier-terms : List NormalTerm -> List NormalTerm
      filter-zero-multiplier-terms [] = []
      filter-zero-multiplier-terms ((normal-term (int.zero-int) vars) :: terms) =
        filter-zero-multiplier-terms terms
      filter-zero-multiplier-terms (term@(normal-term (int.pos _) vars) :: terms) =
        term :: filter-zero-multiplier-terms terms
      filter-zero-multiplier-terms (term@(normal-term (int.neg _) vars) :: terms) =
        term :: filter-zero-multiplier-terms terms
  
      
  
      normal-expr-+ : NormalExpr -> NormalExpr -> NormalExpr
      normal-expr-+ (normal-expr terms1) (normal-expr terms2) =
        (normal-expr (filter-zero-multiplier-terms (merge-terms terms1 terms2)))
  
      normal-expr-* : NormalExpr -> NormalExpr -> NormalExpr
      normal-expr-* (normal-expr terms1) (normal-expr terms2) =
        (normal-expr (insertion-sort-terms (all-products terms1 terms2)))
  
      normal-expr-- : NormalExpr -> NormalExpr
      normal-expr-- (normal-expr terms) = (normal-expr (map normal-term-- terms))
  
      normalize : RingSyntax n -> NormalExpr
      normalize (var i) = normal-expr ((normal-term (int.int 1) (i :: [])) :: [])
      normalize (l ⊕ r) = normal-expr-+ (normalize l) (normalize r)
      normalize (l ⊗ r) = normal-expr-* (normalize l) (normalize r)
      normalize (⊖ e) = normal-expr-- (normalize e)

      ⟦_⟧var : Fin n -> Meaning
      ⟦ i ⟧var env = lookup env i
  
      ⟦_⟧term : NormalTerm -> Meaning
      ⟦ (normal-term m vars) ⟧term = (lift-constant m) * (product (map ⟦_⟧var vars))

      ⟦_⟧terms : List NormalTerm -> Meaning
      ⟦ terms ⟧terms = (sum (map ⟦_⟧term terms))
  
      ⟦_⟧norm : NormalExpr -> Meaning
      ⟦ (normal-expr terms) ⟧norm = ⟦ terms ⟧terms
  
      ⟦_⇓⟧ : RingSyntax n -> Meaning
      ⟦ e ⇓⟧ = ⟦ (normalize e) ⟧norm
  
      ⟦_⟧ : RingSyntax n -> Meaning
      ⟦ (var i) ⟧ env = lookup env i
      ⟦ l ⊕ r ⟧ = ⟦ l ⟧ + ⟦ r ⟧
      ⟦ l ⊗ r ⟧ = ⟦ l ⟧ * ⟦ r ⟧
      ⟦ ⊖ e ⟧ = - ⟦ e ⟧
  
  
      merge-terms-same-meaning : 
        (l-terms : List NormalTerm) -> (r-terms : List NormalTerm)
        ->  ⟦ (merge-terms l-terms r-terms) ⟧terms 
            ==  ⟦ l-terms ⟧terms + ⟦ r-terms ⟧terms 
      merge-terms1-same-meaning : 
        (el : NormalTerm)
        -> (l-terms : List NormalTerm) -> (r-terms : List NormalTerm)
        -> ⟦ (merge-terms1 el l-terms r-terms) ⟧terms
           ==
           ⟦ (el :: l-terms) ⟧terms + ⟦ r-terms ⟧terms
  
      merge-terms-same-meaning [] r-terms = sym +-left-zero 
      merge-terms-same-meaning (e :: l-terms) r-terms = 
        merge-terms1-same-meaning e l-terms r-terms
  
      merge-terms1-same-meaning e l-terms [] = sym +-right-zero
      merge-terms1-same-meaning el l-terms (er :: r-terms) 
        with (compare-term el er)
      ... | less-than =
        begin
          ⟦ el ⟧term + 
          (sum (map ⟦_⟧term (merge-terms1 er r-terms l-terms)))
        ==< +-right (merge-terms1-same-meaning er r-terms l-terms) >
          ⟦ el ⟧term + 
          ((sum (map ⟦_⟧term (er :: r-terms))) + 
           (sum (map ⟦_⟧term l-terms)))
        ==< +-right (+-commute) >
          ⟦ el ⟧term + 
          ((sum (map ⟦_⟧term l-terms)) +
           (sum (map ⟦_⟧term (er :: r-terms))))
        ==< sym +-assoc >
          (sum (map ⟦_⟧term (el :: l-terms))) + 
          (sum (map ⟦_⟧term (er :: r-terms)))
        end
      ... | greater-than =
        begin
          ⟦ er ⟧term + 
          (sum (map ⟦_⟧term (merge-terms1 el l-terms r-terms)))
        ==< +-right (merge-terms1-same-meaning el l-terms r-terms) >
          ⟦ er ⟧term + 
          ((sum (map ⟦_⟧term (el :: l-terms))) + 
           (sum (map ⟦_⟧term r-terms)))
        ==< +-right (+-commute) >
          ⟦ er ⟧term + 
          ((sum (map ⟦_⟧term r-terms)) +
           (sum (map ⟦_⟧term (el :: l-terms))))
        ==< sym +-assoc >
          (⟦ er ⟧term + 
           (sum (map ⟦_⟧term r-terms))) +
          (sum (map ⟦_⟧term (el :: l-terms)))
        ==<>
          (sum (map ⟦_⟧term (er :: r-terms))) +
          (sum (map ⟦_⟧term (el :: l-terms)))
        ==< +-commute >
          (sum (map ⟦_⟧term (el :: l-terms))) + 
          (sum (map ⟦_⟧term (er :: r-terms)))
        end
      ... | equal-to = bot-elim ?
  
      sorted-product-same-meaning : 
        (l-terms : List NormalTerm) -> (r-terms : List NormalTerm)
        -> (⟦ (insertion-sort-terms (all-products l-terms r-terms))⟧terms)
           ==
           ⟦ l-terms ⟧terms * ⟦ r-terms ⟧terms
      sorted-product-same-meaning = bot-elim ?
  
      filtered-terms-same-meaning : 
        ∀ ts -> ⟦ (filter-zero-multiplier-terms ts) ⟧terms == ⟦ ts ⟧terms
      filtered-terms-same-meaning [] = refl
      filtered-terms-same-meaning (term@(normal-term (int.zero-int) vars) :: terms) =
        begin
          (sum (map ⟦_⟧term (filter-zero-multiplier-terms (term :: terms))))
        ==<>
          (sum (map ⟦_⟧term (filter-zero-multiplier-terms terms)))
        ==< (filtered-terms-same-meaning terms) >
          (sum (map ⟦_⟧term terms))
        ==< sym +-left-zero >
          0# + (sum (map ⟦_⟧term terms))
        ==< +-left (sym *-left-zero) >
          0# * (product (map (\ i env -> lookup env i) vars)) + (sum (map ⟦_⟧term terms))
        ==<>
          ⟦ term ⟧term + (sum (map ⟦_⟧term terms))
        ==<>
          (sum (map ⟦_⟧term (term :: terms)))
        end
      filtered-terms-same-meaning (term@(normal-term (int.neg _) vars) :: terms) =
        +-right (filtered-terms-same-meaning terms)
      filtered-terms-same-meaning (term@(normal-term (int.pos _) vars) :: terms) =
        +-right (filtered-terms-same-meaning terms)
  
  
      filtered-merge-terms-same-meaning : 
        (l-terms : List NormalTerm) -> (r-terms : List NormalTerm)
        -> (sum (map ⟦_⟧term (filter-zero-multiplier-terms (merge-terms l-terms r-terms))))
           ==
           (sum (map ⟦_⟧term l-terms)) + (sum (map ⟦_⟧term r-terms))
      filtered-merge-terms-same-meaning l-terms r-terms = 
        filtered-terms-same-meaning (merge-terms l-terms r-terms) >=>
        merge-terms-same-meaning l-terms r-terms
  
  
  
  
      correct : (e : RingSyntax n) -> ⟦ e ⇓⟧ == ⟦ e ⟧ 
      correct = ?
      -- correct (var i) = 
      --   begin
      --     ⟦ (var i) ⇓⟧ 
      --   ==<>
      --     (sum (((1# + 0#) * product (map (lookup env) (i :: []))) :: []))
      --   ==< +-right-zero >
      --     ((1# + 0#) * product (map (lookup env) (i :: [])))
      --   ==< *-left +-right-zero >
      --     1# * product (map (lookup env) (i :: []))
      --   ==< *-left-one >
      --     product (map (lookup env) (i :: []))
      --   ==< *-right-one >
      --     lookup env i
      --   ==<>
      --     ⟦ (var i) ⟧ env 
      --   end
      -- correct (⊖ e) env =
      --   begin
      --     ⟦ (⊖ e) ⇓⟧ env 
      --   ==<>
      --     ⟦ (normalize (⊖ e)) ⟧norm env
      --   ==< norm-correct e >
      --     - (⟦ (normalize e) ⟧norm env)
      --   ==<>
      --     - (⟦ e ⇓⟧ env)
      --   ==< (cong -_ (correct e env)) >
      --     - (⟦ e ⟧ env)
      --   ==<>
      --     ⟦ (⊖ e) ⟧ env 
      --   end
      --   where
      --   term-correct : (term : NormalTerm) ->  
      --                  ⟦ (normal-term-- term) ⟧term env == - (⟦ term ⟧term env)
      --   term-correct (normal-term mult vars) = 
      --     begin
      --       ⟦ (normal-term-- (normal-term mult vars)) ⟧term env 
      --     ==<>
      --       ⟦ (normal-term (int.- mult) vars) ⟧term env 
      --     ==<>
      --       (lift-constant (int.- mult)) * (product (map (lookup env) vars))
      --     ==< *-left (sym (minus-lift-constant {mult})) >
      --       (- (lift-constant mult) * (product (map (lookup env) vars)))
      --     ==< minus-extract-left >
      --       - ((lift-constant mult) * (product (map (lookup env) vars)))
      --     ==<>
      --       - (⟦ (normal-term mult vars) ⟧term env)
      --     end
  
      --   terms-correct : (terms : List NormalTerm) ->  
      --                   ⟦ (normal-expr (map normal-term-- terms)) ⟧norm env ==
      --                   - (⟦ (normal-expr terms) ⟧norm env)
      --   terms-correct [] =  sym minus-zero
      --   terms-correct (e :: l) =
      --     begin
      --       ⟦ (normal-expr (map normal-term-- (e :: l))) ⟧norm env
      --     ==<>
      --       ⟦ (normal-term-- e) ⟧term env +
      --       ⟦ (normal-expr (map normal-term-- l)) ⟧norm env
      --     ==< +-right (terms-correct l) >
      --       ⟦ (normal-term-- e) ⟧term env +
      --       - ⟦ (normal-expr l) ⟧norm env
      --     ==< +-left (term-correct e) >
      --       - ⟦ e ⟧term env +
      --       - ⟦ (normal-expr l) ⟧norm env
      --     ==< sym minus-distrib-plus >
      --       - (⟦ e ⟧term env +
      --          ⟦ (normal-expr l) ⟧norm env)
      --     ==<>
      --       - (⟦ (normal-expr (e :: l)) ⟧norm env)
      --     end
      --   norm-correct : (e : RingSyntax n) -> 
      --                   ⟦ (normalize (⊖ e)) ⟧norm env == - ⟦ (normalize e) ⟧norm env
      --   norm-correct e with (normalize e)
      --   ... | (normal-expr terms) = terms-correct terms
      -- correct (l ⊕ r) env = 
      --   begin
      --     ⟦ (l ⊕ r) ⇓⟧ env 
      --   ==<>
      --     ⟦ normalize (l ⊕ r) ⟧norm env
      --   ==< normalize-split >
      --     ⟦ normalize l ⟧norm env + ⟦ normalize r ⟧norm env
      --   ==<>
      --     ⟦ l ⇓⟧ env + ⟦ r ⇓⟧ env 
      --   ==< (cong2 _+_ (correct l env) (correct r env)) >
      --     ⟦ l ⟧ env + ⟦ r ⟧ env 
      --   ==<>
      --     ⟦ (l ⊕ r) ⟧ env 
      --   end
      --   where
      --   normalize-split : 
      --     ⟦ normalize (l ⊕ r) ⟧norm env ==
      --     ⟦ normalize l ⟧norm env + ⟦ normalize r ⟧norm env
      --   normalize-split with (normalize l) | (normalize r)
      --   ... | (normal-expr l-terms) | (normal-expr r-terms) = 
      --     filtered-merge-terms-same-sum env l-terms r-terms
      -- correct  (l ⊗ r) env = 
      --   begin
      --     ⟦ (l ⊗ r) ⇓⟧ env 
      --   ==<>
      --     ⟦ normalize (l ⊗ r) ⟧norm env
      --   ==< normalize-split >
      --     ⟦ normalize l ⟧norm env * ⟦ normalize r ⟧norm env
      --   ==<>
      --     ⟦ l ⇓⟧ env * ⟦ r ⇓⟧ env 
      --   ==< (cong2 _*_ (correct l env) (correct r env)) >
      --     ⟦ l ⟧ env * ⟦ r ⟧ env 
      --   ==<>
      --     ⟦ (l ⊗ r) ⟧ env 
      --   end
      --   where
      --   normalize-split : 
      --     ⟦ normalize (l ⊗ r) ⟧norm env ==
      --     ⟦ normalize l ⟧norm env * ⟦ normalize r ⟧norm env
      --   normalize-split with (normalize l) | (normalize r)
      --   ... | (normal-expr l-terms) | (normal-expr r-terms) = 
      --     sorted-product-same-meaning env l-terms r-terms


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
    
      inner-normal-proof : (ρ : (Vec R.Domain n)) -> (⟦ e₁ ⇓⟧ ρ) == (⟦ e₂ ⇓⟧ ρ)
      inner-normal-proof = cong-curry⁻¹ n (⟦ e₁ ⇓⟧) (⟦ e₂ ⇓⟧) full-normal-proof

      prove : (ρ : Vec R.Domain n) -> ⟦ e₁ ⇓⟧ ρ == ⟦ e₂ ⇓⟧ ρ -> ⟦ e₁ ⟧ ρ == ⟦ e₂ ⟧ ρ
      prove ρ pr = (sym (\i -> (correct e₁ i ρ))) >=> pr >=> (\i -> (correct e₂ i ρ))
    
      inner-reg-proof : (ρ : (Vec R.Domain n)) -> (⟦ e₁ ⟧ ρ) == (⟦ e₂ ⟧ ρ)
      inner-reg-proof v = (prove v (inner-normal-proof v))
    
      full-reg-proof : Eq n _==_ (curry n ⟦ e₁ ⟧) (curry n ⟦ e₂ ⟧)
      full-reg-proof = cong-curry n (⟦ e₁ ⟧) (⟦ e₂ ⟧) inner-reg-proof



module Solver (S : Semiring {lzero}) where
  module S = Semiring S

  module _ (n : Nat) where

    open module M = Semiring (ReaderSemiring (Vec S.Domain n) S)
      renaming (Domain to Meaning)

    ⟦_⟧ : Syntax n -> Meaning
    ⟦ (var i) ⟧ env = lookup env i
    ⟦ l ⊕ r ⟧ = ⟦ l ⟧ + ⟦ r ⟧
    ⟦ l ⊗ r ⟧ = ⟦ l ⟧ * ⟦ r ⟧
  
  
    data Term : Set where
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
      ... | equal-to = false
  


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
    
      inner-normal-proof : (ρ : (Vec S.Domain n)) -> (⟦ e₁ ⇓⟧ ρ) == (⟦ e₂ ⇓⟧ ρ)
      inner-normal-proof = cong-curry⁻¹ n (⟦ e₁ ⇓⟧) (⟦ e₂ ⇓⟧) full-normal-proof

      prove : (ρ : Vec S.Domain n) -> ⟦ e₁ ⇓⟧ ρ == ⟦ e₂ ⇓⟧ ρ -> ⟦ e₁ ⟧ ρ == ⟦ e₂ ⟧ ρ
      prove ρ pr = (sym (\i -> (correct e₁ i ρ))) >=> pr >=> (\i -> (correct e₂ i ρ))
    
      inner-reg-proof : (ρ : (Vec S.Domain n)) -> (⟦ e₁ ⟧ ρ) == (⟦ e₂ ⟧ ρ)
      inner-reg-proof v = (prove v (inner-normal-proof v))
    
      full-reg-proof : Eq n _==_ (curry n ⟦ e₁ ⟧) (curry n ⟦ e₂ ⟧)
      full-reg-proof = cong-curry n (⟦ e₁ ⟧) (⟦ e₂ ⟧) inner-reg-proof
  
    
  
  

module NatSolver = Solver NatSemiring
module IntSolver = Solver IntSemiring

private
  open int

  example1 : (a b c d : Nat) -> (a +' c) +' (b +' d) == a +' (b +' c) +' d
  example1 = NatSolver.solve 4 (\ a b c d -> ((a ⊕ c) ⊕ (b ⊕ d)) , (a ⊕ (b ⊕ c)) ⊕ d) refl

  example2 : (a b c : Nat) -> (a +' b) *' c == (b *' c) +' (a *' c)
  example2 = NatSolver.solve 3 (\ a b c -> (a ⊕ b) ⊗ c , (b ⊗ c) ⊕ (a ⊗ c)) refl

  example3 : (a b c d : Nat) -> (a +' c) *' (b +' d) == a *' b +' c *' d +' c *' b +' a *' d
  example3 = NatSolver.solve 4 (\ a b c d -> ((a ⊕ c) ⊗ (b ⊕ d)) , 
                                             (a ⊗ b) ⊕ (c ⊗ d) ⊕ (c ⊗ b) ⊕ (a ⊗ d)) refl

  example4 : (a b c d : Int) -> (a + c) * (b + d) == a * b + c * d + c * b + a * d
  example4 = IntSolver.solve 4 (\ a b c d -> ((a ⊕ c) ⊗ (b ⊕ d)) , 
                                             (a ⊗ b) ⊕ (c ⊗ d) ⊕ (c ⊗ b) ⊕ (a ⊗ d)) refl

  example5 : (x y a b -y -b : Int) ->
       (x + y) * (a + b) + (x + -y) * (a + -b) ==
       (x * b + x * -b) + ((x * a + y * b) + ((x * a + -y * -b) + (y * a + -y * a)))
  example5 =
   IntSolver.solve 6
     (\ x y a b -y -b ->
       (x ⊕ y) ⊗ (a ⊕ b) ⊕ (x ⊕ -y) ⊗ (a ⊕ -b) ,
       (x ⊗ b ⊕ x ⊗ -b) ⊕ ((x ⊗ a ⊕ y ⊗ b) ⊕ ((x ⊗ a ⊕ -y ⊗ -b) ⊕ (y ⊗ a ⊕ -y ⊗ a))))
     refl
