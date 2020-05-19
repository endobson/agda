module solver where

open import base
open import list
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

record Semiring {a : Level} : Set (lsuc a) where
  infixl 7 _*_
  infixl 6 _+_

  field
    Domain : Set a
    0# : Domain
    1# : Domain
    _+_ : Domain -> Domain -> Domain
    _*_ : Domain -> Domain -> Domain
    +-assoc : {m n o : Domain} -> (m + n) + o == m + (n + o)
    +-commute : {m n : Domain} -> (m + n) == (n + m)
    *-assoc : {m n o : Domain} -> (m * n) * o == m * (n * o)
    *-commute : {m n : Domain} -> (m * n) == (n * m)
    +-left-zero : {m : Domain} -> (0# + m) == m
    *-left-zero : {m : Domain} -> (0# * m) == 0#
    *-left-one : {m : Domain} -> (1# * m) == m
    *-distrib-+-right : {m n o : Domain} -> (m + n) * o == (m * o) + (n * o)

  +-right-zero : {m : Domain} -> (m + 0#) == m
  +-right-zero {m} = (+-commute {m} {0#}) >=> (+-left-zero {m})

  *-right-zero : {m : Domain} -> (m * 0#) == 0#
  *-right-zero {m} = (*-commute {m} {0#}) >=> (*-left-zero {m})
  *-right-one : {m : Domain} -> (m * 1#) == m
  *-right-one {m} = (*-commute {m} {1#}) >=> (*-left-one {m})

  *-distrib-+-left : {m n o : Domain} -> m * (n + o) == (m * n) + (m * o)
  *-distrib-+-left {m} {n} {o} =
    begin
      m * (n + o) 
    ==< (*-commute {m} {n + o}) >
      (n + o) * m
    ==< (*-distrib-+-right {n} {o} {m}) >
      n * m + o * m
    ==< (cong2 _+_ (*-commute {n} {m}) (*-commute {o} {m})) >
      (m * n) + (m * o)
    end

  +-right : {m n p : Domain} -> (n == p) -> m + n == m + p
  +-right {m} id = cong (\x -> m + x) id
  
  +-left : {m n p : Domain} -> (n == p) -> n + m == p + m
  +-left {m} id = cong (\x -> x + m) id
  
  +-cong : {m n p o : Domain} -> m == p -> n == o -> m + n == p + o
  +-cong = cong2 _+_

  *-right : {m n p : Domain} -> (n == p) -> m * n == m * p
  *-right {m} id = cong (\x -> m * x) id
  
  *-left : {m n p : Domain} -> (n == p) -> n * m == p * m
  *-left {m} id = cong (\x -> x * m) id
  
  *-cong : {m n p o : Domain} -> m == p -> n == o -> m * n == p * o
  *-cong = cong2 _*_


record Ring {a : Level} : Set (lsuc a) where
  field
    {{semiring}} : Semiring {a}
    -_ : Semiring.Domain semiring -> Semiring.Domain semiring
    +-inverse : {x : Semiring.Domain semiring} 
                -> (Semiring._+_ semiring x (- x)) == Semiring.0# semiring

  open Semiring semiring public

  minus-zero : (- 0#) == 0#
  minus-zero =
    begin
      (- 0#)
    ==< sym +-left-zero >
      0# + (- 0#)
    ==< +-inverse >
      0#
    end

  postulate minus-double-inverse : {a : Domain} -> - - a == a

  minus-unique : {a b : Domain} -> a + b == 0# -> b == - a
  minus-unique {a} {b} pr =
    begin
      b
    ==< sym +-left-zero >
      0# + b
    ==< +-left (sym +-inverse) >
      (a + - a) + b
    ==< +-left +-commute >
      (- a + a) + b
    ==< +-assoc >
      - a + (a + b)
    ==< +-right pr >
      - a + 0#
    ==< +-right-zero  >
      - a
    end

  *-left-minus-one : {a : Domain} -> (- 1#) * a == - a
  *-left-minus-one {a} = 
    begin
      - 1# * a
    ==< sym +-left-zero >
      0# + - 1# * a
    ==< +-left (sym +-inverse) >
      (a + - a) + - 1# * a
    ==< +-left +-commute >
      (- a + a) + - 1# * a
    ==< +-assoc >
      - a + (a + - 1# * a)
    ==< +-right (+-left (sym *-left-one)) >
      - a + (1# * a + - 1# * a)
    ==< +-right (sym *-distrib-+-right) >
      - a + ((1# + - 1#) * a)
    ==< +-right (*-left +-inverse) >
      - a + (0# * a)
    ==< +-right *-left-zero >
      - a + 0#
    ==< +-right-zero >
      - a
    end

  minus-extract-left : {a b : Domain} -> (- a * b) == - (a * b)
  minus-extract-left {a} {b} =
    begin
      - a * b
    ==< *-left (sym *-left-minus-one) >
      (- 1# * a) * b
    ==< *-assoc >
      - 1# * (a * b)
    ==< *-left-minus-one >
      - (a * b)
    end

  minus-distrib-plus : {a b : Domain} -> - (a + b) == - a + - b
  minus-distrib-plus {a} {b} =
    begin
      - (a + b)
    ==< sym *-left-minus-one >
      - 1# * (a + b)
    ==< *-distrib-+-left >
      - 1# * a + - 1# * b
    ==< +-left *-left-minus-one >
      - a + - 1# * b
    ==< +-right *-left-minus-one >
      - a + - b
    end

  private
    lift-constant-nat-helper : Nat -> Domain
    lift-constant-nat-helper zero = 0#
    lift-constant-nat-helper (suc n) = (1# + (lift-constant-nat-helper n))

  lift-constant : int.Int -> Domain
  lift-constant (int.nonneg x) = lift-constant-nat-helper x
  lift-constant (int.neg x) = - lift-constant-nat-helper (suc x)

  minus-lift-constant : {x : int.Int} -> - (lift-constant x) == lift-constant (int.- x)
  minus-lift-constant {int.zero-int} = minus-zero
  minus-lift-constant {int.pos x} = refl
  minus-lift-constant {int.neg x} = minus-double-inverse
  



NatSemiring : Semiring
NatSemiring = record {
  Domain = Nat;
  0# = 0;
  1# = 1;
  _+_ = _+'_;
  _*_ = _*'_;
  +-assoc = (\ {m} {n} {o} -> (+'-assoc {m} {n} {o}));
  +-commute = (\ {m} {n} -> (+'-commute {m} {n}));
  *-assoc = (\ {m} {n} {o} -> (*'-assoc {m} {n} {o}));
  *-commute = (\ {m} {n} -> (*'-commute {m} {n}));
  +-left-zero = refl;
  *-left-zero = refl;
  *-left-one = +'-right-zero;
  *-distrib-+-right = (\ {m} {n} {o} -> *'-distrib-+' {m} {n} {o}) }

IntSemiring : Semiring
IntSemiring = record {
  Domain = int.Int;
  0# = (int.int 0);
  1# = (int.int 1);
  _+_ = int._+_;
  _*_ = int._*_;
  +-assoc = (\ {m} {n} {o} -> (int.+-assoc {m} {n} {o}));
  +-commute = (\ {m} {n} -> (int.+-commute {m} {n}));
  *-assoc = (\ {m} {n} {o} -> (int.*-assoc {m} {n} {o}));
  *-commute = (\ {m} {n} -> (int.*-commute {m} {n}));
  +-left-zero = refl;
  *-left-zero = refl;
  *-left-one = int.+-right-zero;
  *-distrib-+-right = (\ {m} {n} {o} -> int.*-distrib-+ {m} {n} {o}) }




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
  ... | _ = false
  
  
  compare-list : (A -> A -> Order) -> List A -> List A -> Order
  compare-list _ [] [] = equal-to
  compare-list _ (_ :: _) [] = greater-than
  compare-list _ [] (_ :: _) = less-than
  compare-list compare-elem (el :: ll) (er :: lr) with compare-elem el er
  ... | equal-to = compare-list compare-elem ll lr
  ... | order = order


module RingSolver (R : Ring {lzero}) where
  private
    open Ring R

    sum : List Domain -> Domain
    sum [] = 0#
    sum (a :: l) = a + sum l

    product : List Domain -> Domain
    product [] = 1#
    product (a :: l) = a * product l

    sum-inject-++ : {a b : List Domain} -> sum (a ++ b) == sum a + sum b
    sum-inject-++ {[]} {b} = sym (+-left-zero {sum b})
    sum-inject-++ {e :: a} {b} = 
      begin
        sum ((e :: a) ++ b)
      ==<> 
        e + (sum (a ++ b))
      ==< +-right {e} (sum-inject-++ {a} {b}) >
        e + (sum a + sum b)
      ==< sym (+-assoc {e}) >
        (e + sum a) + sum b
      ==<> 
        sum (e :: a) + sum b
      end

    sum-map-inject-++ : (f : A -> Domain) {a1 a2 : List A} 
                        -> (sum (map f (a1 ++ a2))) == (sum (map f a1)) + (sum (map f a2))
    sum-map-inject-++ f {a1} {a2} = 
      (cong sum (map-inject-++ f {a1} {a2})) >=> (sum-inject-++ {map f a1})

    sum-map-Insertion : {a : A} {as1 as2 : (List A)} -> (f : A -> Domain) -> (Insertion A a as1 as2)
                         -> (sum (map f (a :: as1))) == (sum (map f as2))
    sum-map-Insertion f (insertion-base a as) = refl
    sum-map-Insertion f (insertion-cons {a} {as1} {as2} a2 ins) = 
      begin
        (sum (map f (a :: (a2 :: as1))))
      ==<>
        (f a) + ((f a2) + (sum (map f as1)))
      ==< sym (+-assoc {f a}) >
        ((f a) + (f a2)) + (sum (map f as1))
      ==< +-left (+-commute {f a} {f a2}) >
        ((f a2) + (f a)) + (sum (map f as1))
      ==< +-assoc {f a2} >
        (f a2) + ((f a) + (sum (map f as1)))
      ==< +-right {f a2} (sum-map-Insertion f ins) >
        (f a2) + (sum (map f as2))
      ==<>
        (sum (map f (a2 :: as2)))
      end

    sum-map-Permutation : {as1 as2 : (List A)} -> (f : A -> Domain) -> (Permutation A as1 as2)
                         -> (sum (map f as1)) == (sum (map f as2))
    sum-map-Permutation f (permutation-empty) = refl
    sum-map-Permutation f (permutation-cons {a} {as1} {as2} {as3} perm ins) =
      (+-right {f a} (sum-map-Permutation f perm)) >=> (sum-map-Insertion f ins)


    variable n : Nat

    record NormalTerm (n : Nat) : Set where
      constructor normal-term
      field
        multiplier : int.Int
        vars : List (Fin n)

    record NormalExpr (n : Nat) : Set where
      constructor normal-expr
      field
        terms : List (NormalTerm n)

    compare-term : NormalTerm n -> NormalTerm n -> Order
    compare-term (normal-term _ vars1) (normal-term _ vars2) =
      compare-list compare-fin vars1 vars2

    normal-term-- : NormalTerm n -> NormalTerm n
    normal-term-- (normal-term m vars) = (normal-term (int.- m) vars)

    multiply-term : NormalTerm n -> NormalTerm n -> NormalTerm n
    multiply-term (normal-term m1 vs1) (normal-term m2 vs2) =
      (normal-term (m1 int.* m2) (insertion-sort fin< (vs1 ++ vs2)))

    merge-terms : List (NormalTerm n) -> List (NormalTerm n) -> List (NormalTerm n)
    merge-terms1 : NormalTerm n -> List (NormalTerm n) -> List (NormalTerm n) -> List (NormalTerm n)

    merge-terms [] terms = terms
    merge-terms (term :: terms1) terms2 = merge-terms1 term terms1 terms2

    merge-terms1 t1 terms1 [] = t1 :: terms1
    merge-terms1 t1@(normal-term m1 vars1) terms1 (t2@(normal-term m2 _) :: terms2) 
      with compare-term t1 t2
    ... | less-than = t1 :: (merge-terms1 t2 terms2 terms1)
    ... | greater-than = t2 :: (merge-terms1 t1 terms1 terms2)
    ... | equal-to = (normal-term (m1 int.+ m2) vars1) :: (merge-terms terms1 terms2)


    insertion-sort-terms : List (NormalTerm n) -> List (NormalTerm n)
    insertion-sort-terms terms = rec terms []
      where
      rec : List (NormalTerm n) -> List (NormalTerm n) -> List (NormalTerm n)
      rec [] acc = acc
      rec (e :: l) acc = rec l (merge-terms1 e [] acc)

    all-products : List (NormalTerm n) -> List (NormalTerm n) -> List (NormalTerm n)
    all-products [] _ = []
    all-products (t1 :: terms1) terms2 = 
      (merge-terms
        (insertion-sort-terms (map (multiply-term t1) terms2))
        (all-products terms1 terms2))

    filter-zero-multiplier-terms : List (NormalTerm n) -> List (NormalTerm n)
    filter-zero-multiplier-terms [] = []
    filter-zero-multiplier-terms ((normal-term (int.zero-int) vars) :: terms) =
      filter-zero-multiplier-terms terms
    filter-zero-multiplier-terms (term :: terms) =
      term :: filter-zero-multiplier-terms terms

    

    normal-expr-+ : NormalExpr n -> NormalExpr n -> NormalExpr n
    normal-expr-+ (normal-expr terms1) (normal-expr terms2) =
      (normal-expr (filter-zero-multiplier-terms (merge-terms terms1 terms2)))

    normal-expr-* : NormalExpr n -> NormalExpr n -> NormalExpr n
    normal-expr-* (normal-expr terms1) (normal-expr terms2) =
      (normal-expr (insertion-sort-terms (all-products terms1 terms2)))

    normal-expr-- : NormalExpr n -> NormalExpr n
    normal-expr-- (normal-expr terms) = (normal-expr (map normal-term-- terms))

    normalize : RingSyntax n -> NormalExpr n
    normalize (var i) = normal-expr ((normal-term (int.int 1) (i :: [])) :: [])
    normalize (l ⊕ r) = normal-expr-+ (normalize l) (normalize r)
    normalize (l ⊗ r) = normal-expr-* (normalize l) (normalize r)
    normalize (⊖ e) = normal-expr-- (normalize e)

    ⟦_⟧term_ : NormalTerm n -> Vec Domain n -> Domain
    ⟦ (normal-term m vars) ⟧term env = (lift-constant m) * (product (map (lookup env) vars))


    ⟦_⟧norm_ : NormalExpr n -> Vec Domain n -> Domain
    ⟦ (normal-expr terms) ⟧norm env = (sum (map (⟦_⟧term env) terms))


    ⟦_⟧ : RingSyntax n -> Vec Domain n -> Domain
    ⟦ (var i) ⟧ env = lookup env i
    ⟦ l ⊕ r ⟧ env = ⟦ l ⟧ env + ⟦ r ⟧ env
    ⟦ l ⊗ r ⟧ env = ⟦ l ⟧ env * ⟦ r ⟧ env
    ⟦ ⊖ e ⟧ env = - ⟦ e ⟧ env

    ⟦_⇓⟧ : RingSyntax n -> Vec Domain n -> Domain
    ⟦ e ⇓⟧ env = ⟦ (normalize e) ⟧norm env

    postulate NYI : Bot

    merge-terms-same-sum : 
      {n : Nat} -> (env : (Vec Domain n)) 
      -> (l-terms : List (NormalTerm n)) -> (r-terms : List (NormalTerm n))
      -> (sum (map (⟦_⟧term env) (merge-terms l-terms r-terms)))
         ==
         (sum (map (⟦_⟧term env) l-terms)) + (sum (map (⟦_⟧term env) r-terms))
    merge-terms1-same-sum : 
      {n : Nat} -> (env : (Vec Domain n)) 
      -> (el : (NormalTerm n))
      -> (l-terms : List (NormalTerm n)) -> (r-terms : List (NormalTerm n))
      -> (sum (map (⟦_⟧term env) (merge-terms1 el l-terms r-terms)))
         ==
         (sum (map (⟦_⟧term env) (el :: l-terms))) + (sum (map (⟦_⟧term env) r-terms))

    merge-terms-same-sum env [] r-terms = sym +-left-zero 
    merge-terms-same-sum env (e :: l-terms) r-terms = 
      merge-terms1-same-sum env e l-terms r-terms

    merge-terms1-same-sum env e l-terms [] = sym +-right-zero
    merge-terms1-same-sum {n = n} env el l-terms (er :: r-terms) 
      with (compare-term el er)
    ... | less-than =
      begin
        ⟦ el ⟧term env + 
        (sum (map (⟦_⟧term env) (merge-terms1 er r-terms l-terms)))
      ==< +-right (merge-terms1-same-sum env er r-terms l-terms) >
        ⟦ el ⟧term env + 
        ((sum (map (⟦_⟧term env) (er :: r-terms))) + 
         (sum (map (⟦_⟧term env) l-terms)))
      ==< +-right (+-commute) >
        ⟦ el ⟧term env + 
        ((sum (map (⟦_⟧term env) l-terms)) +
         (sum (map (⟦_⟧term env) (er :: r-terms))))
      ==< sym +-assoc >
        (sum (map (⟦_⟧term env) (el :: l-terms))) + 
        (sum (map (⟦_⟧term env) (er :: r-terms)))
      end
    ... | greater-than =
      begin
        ⟦ er ⟧term env + 
        (sum (map (⟦_⟧term env) (merge-terms1 el l-terms r-terms)))
      ==< +-right (merge-terms1-same-sum env el l-terms r-terms) >
        ⟦ er ⟧term env + 
        ((sum (map (⟦_⟧term env) (el :: l-terms))) + 
         (sum (map (⟦_⟧term env) r-terms)))
      ==< +-right (+-commute) >
        ⟦ er ⟧term env + 
        ((sum (map (⟦_⟧term env) r-terms)) +
         (sum (map (⟦_⟧term env) (el :: l-terms))))
      ==< sym +-assoc >
        (⟦ er ⟧term env + 
         (sum (map (⟦_⟧term env) r-terms))) +
        (sum (map (⟦_⟧term env) (el :: l-terms)))
      ==<>
        (sum (map (⟦_⟧term env) (er :: r-terms))) +
        (sum (map (⟦_⟧term env) (el :: l-terms)))
      ==< +-commute >
        (sum (map (⟦_⟧term env) (el :: l-terms))) + 
        (sum (map (⟦_⟧term env) (er :: r-terms)))
      end
    ... | equal-to = bot-elim NYI

    sorted-product-same-product : 
      {n : Nat} -> (env : (Vec Domain n)) 
      -> (l-terms : List (NormalTerm n)) -> (r-terms : List (NormalTerm n))
      -> (sum (map (⟦_⟧term env) (insertion-sort-terms (all-products l-terms r-terms))))
         ==
         (sum (map (⟦_⟧term env) l-terms)) * (sum (map (⟦_⟧term env) r-terms))
    sorted-product-same-product = bot-elim NYI

    filtered-terms-same-sum : 
      {n : Nat} -> (env : (Vec Domain n)) 
      -> (terms : List (NormalTerm n)) 
      -> (sum (map (⟦_⟧term env) (filter-zero-multiplier-terms terms)))
         ==
         (sum (map (⟦_⟧term env) terms))
    filtered-terms-same-sum env [] = refl
    filtered-terms-same-sum env (term@(normal-term (int.zero-int) vars) :: terms) =
      begin
        (sum (map (⟦_⟧term env) (filter-zero-multiplier-terms (term :: terms))))
      ==<>
        (sum (map (⟦_⟧term env) (filter-zero-multiplier-terms terms)))
      ==< (filtered-terms-same-sum env terms) >
        (sum (map (⟦_⟧term env) terms))
      ==< sym +-left-zero >
        0# + (sum (map (⟦_⟧term env) terms))
      ==< +-left (sym *-left-zero) >
        0# * (product (map (lookup env) vars)) + (sum (map (⟦_⟧term env) terms))
      ==<>
        ⟦ term ⟧term env + (sum (map (⟦_⟧term env) terms))
      ==<>
        (sum (map (⟦_⟧term env) (term :: terms)))
      end
    filtered-terms-same-sum env (term@(normal-term (int.neg _) vars) :: terms) =
      +-right (filtered-terms-same-sum env terms)
    filtered-terms-same-sum env (term@(normal-term (int.pos _) vars) :: terms) =
      +-right (filtered-terms-same-sum env terms)


    filtered-merge-terms-same-sum : 
      {n : Nat} -> (env : (Vec Domain n)) 
      -> (l-terms : List (NormalTerm n)) -> (r-terms : List (NormalTerm n))
      -> (sum (map (⟦_⟧term env) (filter-zero-multiplier-terms (merge-terms l-terms r-terms))))
         ==
         (sum (map (⟦_⟧term env) l-terms)) + (sum (map (⟦_⟧term env) r-terms))
    filtered-merge-terms-same-sum env l-terms r-terms = 
      filtered-terms-same-sum env (merge-terms l-terms r-terms) >=>
      merge-terms-same-sum env l-terms r-terms




    correct : (e : RingSyntax n) -> (env : Vec Domain n)
              -> ⟦ e ⇓⟧ env == ⟦ e ⟧ env 
    correct (var i) env = 
      begin
        ⟦ (var i) ⇓⟧ env 
      ==<>
        (sum (((1# + 0#) * product (map (lookup env) (i :: []))) :: []))
      ==< +-right-zero >
        ((1# + 0#) * product (map (lookup env) (i :: [])))
      ==< *-left +-right-zero >
        1# * product (map (lookup env) (i :: []))
      ==< *-left-one >
        product (map (lookup env) (i :: []))
      ==< *-right-one >
        lookup env i
      ==<>
        ⟦ (var i) ⟧ env 
      end
    correct {n = n} (⊖ e) env =
      begin
        ⟦ (⊖ e) ⇓⟧ env 
      ==<>
        ⟦ (normalize (⊖ e)) ⟧norm env
      ==< norm-correct e >
        - (⟦ (normalize e) ⟧norm env)
      ==<>
        - (⟦ e ⇓⟧ env)
      ==< (cong -_ (correct e env)) >
        - (⟦ e ⟧ env)
      ==<>
        ⟦ (⊖ e) ⟧ env 
      end
      where
      term-correct : (term : (NormalTerm n)) ->  
                     ⟦ (normal-term-- term) ⟧term env == - (⟦ term ⟧term env)
      term-correct (normal-term mult vars) = 
        begin
          ⟦ (normal-term-- (normal-term mult vars)) ⟧term env 
        ==<>
          ⟦ (normal-term (int.- mult) vars) ⟧term env 
        ==<>
          (lift-constant (int.- mult)) * (product (map (lookup env) vars))
        ==< *-left (sym (minus-lift-constant {mult})) >
          (- (lift-constant mult) * (product (map (lookup env) vars)))
        ==< minus-extract-left >
          - ((lift-constant mult) * (product (map (lookup env) vars)))
        ==<>
          - (⟦ (normal-term mult vars) ⟧term env)
        end

      terms-correct : (terms : List (NormalTerm n)) ->  
                      ⟦ (normal-expr (map normal-term-- terms)) ⟧norm env ==
                      - (⟦ (normal-expr terms) ⟧norm env)
      terms-correct [] =  sym minus-zero
      terms-correct (e :: l) =
        begin
          ⟦ (normal-expr (map normal-term-- (e :: l))) ⟧norm env
        ==<>
          ⟦ (normal-term-- e) ⟧term env +
          ⟦ (normal-expr (map normal-term-- l)) ⟧norm env
        ==< +-right (terms-correct l) >
          ⟦ (normal-term-- e) ⟧term env +
          - ⟦ (normal-expr l) ⟧norm env
        ==< +-left (term-correct e) >
          - ⟦ e ⟧term env +
          - ⟦ (normal-expr l) ⟧norm env
        ==< sym minus-distrib-plus >
          - (⟦ e ⟧term env +
             ⟦ (normal-expr l) ⟧norm env)
        ==<>
          - (⟦ (normal-expr (e :: l)) ⟧norm env)
        end
      norm-correct : (e : RingSyntax n) -> 
                      ⟦ (normalize (⊖ e)) ⟧norm env == - ⟦ (normalize e) ⟧norm env
      norm-correct e with (normalize e)
      ... | (normal-expr terms) = terms-correct terms
    correct {n} (l ⊕ r) env = 
      begin
        ⟦ (l ⊕ r) ⇓⟧ env 
      ==<>
        ⟦ normalize (l ⊕ r) ⟧norm env
      ==< normalize-split >
        ⟦ normalize l ⟧norm env + ⟦ normalize r ⟧norm env
      ==<>
        ⟦ l ⇓⟧ env + ⟦ r ⇓⟧ env 
      ==< (cong2 _+_ (correct l env) (correct r env)) >
        ⟦ l ⟧ env + ⟦ r ⟧ env 
      ==<>
        ⟦ (l ⊕ r) ⟧ env 
      end
      where
      normalize-split : 
        ⟦ normalize (l ⊕ r) ⟧norm env ==
        ⟦ normalize l ⟧norm env + ⟦ normalize r ⟧norm env
      normalize-split with (normalize l) | (normalize r)
      ... | (normal-expr l-terms) | (normal-expr r-terms) = 
        filtered-merge-terms-same-sum env l-terms r-terms
    correct {n} (l ⊗ r) env = 
      begin
        ⟦ (l ⊗ r) ⇓⟧ env 
      ==<>
        ⟦ normalize (l ⊗ r) ⟧norm env
      ==< normalize-split >
        ⟦ normalize l ⟧norm env * ⟦ normalize r ⟧norm env
      ==<>
        ⟦ l ⇓⟧ env * ⟦ r ⇓⟧ env 
      ==< (cong2 _*_ (correct l env) (correct r env)) >
        ⟦ l ⟧ env * ⟦ r ⟧ env 
      ==<>
        ⟦ (l ⊗ r) ⟧ env 
      end
      where
      normalize-split : 
        ⟦ normalize (l ⊗ r) ⟧norm env ==
        ⟦ normalize l ⟧norm env * ⟦ normalize r ⟧norm env
      normalize-split with (normalize l) | (normalize r)
      ... | (normal-expr l-terms) | (normal-expr r-terms) = 
        sorted-product-same-product env l-terms r-terms

    --   begin
    --     ⟦ l ⊕ r ⇓⟧ env
    --   ==<>
    --     ⟦ insertion-sort term< (linearize (l ⊕ r)) ⟧terms env
    --   ==< terms-eval-inject-insertion-sort env {linearize (l ⊕ r)} >
    --     ⟦ linearize (l ⊕ r) ⟧terms env
    --   ==< terms-eval-inject-linearize-⊕ env {l} {r} >
    --     ⟦ linearize l ⟧terms env + ⟦ linearize r ⟧terms env
    --   ==< (+-cong 
    --           (sym (terms-eval-inject-insertion-sort env {linearize l}))
    --           (sym (terms-eval-inject-insertion-sort env {linearize r}))) >
    --     ⟦ insertion-sort term< (linearize l) ⟧terms env + 
    --     ⟦ insertion-sort term< (linearize r) ⟧terms env
    --   ==< +-cong (correct l env) (correct r env) >
    --     ⟦ l ⟧ env + ⟦ r ⟧ env 
    --   ==<>
    --     ⟦ l ⊕ r ⟧ env 
    --   end
    -- correct {n} (l ⊗ r) env = 
    --   begin
    --     ⟦ l ⊗ r ⇓⟧ env
    --   ==<>
    --     ⟦ insertion-sort term< (linearize (l ⊗ r)) ⟧terms env
    --   ==< terms-eval-inject-insertion-sort env {linearize (l ⊗ r)} >
    --     ⟦ linearize (l ⊗ r) ⟧terms env
    --   ==< terms-eval-inject-linearize-⊗ env {l} {r} >
    --     ⟦ linearize l ⟧terms env * ⟦ linearize r ⟧terms env
    --   ==< (*-cong 
    --           (sym (terms-eval-inject-insertion-sort env {linearize l}))
    --           (sym (terms-eval-inject-insertion-sort env {linearize r}))) >
    --     ⟦ insertion-sort term< (linearize l) ⟧terms env * 
    --     ⟦ insertion-sort term< (linearize r) ⟧terms env
    --   ==< *-cong (correct l env) (correct r env) >
    --     ⟦ l ⟧ env * ⟦ r ⟧ env 
    --   ==<>
    --     ⟦ l ⊗ r ⟧ env 
    --   end


  solve : (n : Nat) -> (f : Nary n (RingSyntax n) ((RingSyntax n) × (RingSyntax n)))
          ->  Eqʰ n _==_ (curry n ⟦ proj₁ (close' n f) ⇓⟧) (curry n ⟦ proj₂ (close' n f) ⇓⟧)
          ->  Eq n _==_ (curry n ⟦ proj₁ (close' n f) ⟧) (curry n ⟦ proj₂ (close' n f) ⟧)
  solve n f hidden-normal-proof = full-reg-proof
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
    prove ρ pr = (sym (correct e₁ ρ)) >=> pr >=> (correct e₂ ρ)
  
    inner-reg-proof : (ρ : (Vec Domain n)) -> (⟦ e₁ ⟧ ρ) == (⟦ e₂ ⟧ ρ)
    inner-reg-proof v = (prove v (inner-normal-proof v))
  
    full-reg-proof : Eq n _==_ (curry n ⟦ e₁ ⟧) (curry n ⟦ e₂ ⟧)
    full-reg-proof = cong-curry n (⟦ e₁ ⟧) (⟦ e₂ ⟧) inner-reg-proof



module Solver (S : Semiring {lzero}) where
  open Semiring S

  module _ (n : Nat) where
    ⟦_⟧ : Syntax n -> Vec Domain n -> Domain
    ⟦ (var i) ⟧ env = lookup env i
    ⟦ l ⊕ r ⟧ env = ⟦ l ⟧ env + ⟦ r ⟧ env
    ⟦ l ⊗ r ⟧ env = ⟦ l ⟧ env * ⟦ r ⟧ env
  
  
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
      ... | _ = false
  

    sum : List Domain -> Domain
    sum [] = 0#
    sum (a :: l) = a + sum l

    sum-inject-++ : {a b : List Domain} -> sum (a ++ b) == sum a + sum b
    sum-inject-++ {[]} {b} = sym (+-left-zero {sum b})
    sum-inject-++ {e :: a} {b} = 
      begin
        sum ((e :: a) ++ b)
      ==<> 
        e + (sum (a ++ b))
      ==< +-right {e} (sum-inject-++ {a} {b}) >
        e + (sum a + sum b)
      ==< sym (+-assoc {e}) >
        (e + sum a) + sum b
      ==<> 
        sum (e :: a) + sum b
      end

    sum-map-inject-++ : (f : A -> Domain) {a1 a2 : List A} 
                        -> (sum (map f (a1 ++ a2))) == (sum (map f a1)) + (sum (map f a2))
    sum-map-inject-++ f {a1} {a2} = 
      (cong sum (map-inject-++ f {a1} {a2})) >=> (sum-inject-++ {map f a1})

    sum-map-Insertion : {a : A} {as1 as2 : (List A)} -> (f : A -> Domain) -> (Insertion A a as1 as2)
                         -> (sum (map f (a :: as1))) == (sum (map f as2))
    sum-map-Insertion f (insertion-base a as) = refl
    sum-map-Insertion f (insertion-cons {a} {as1} {as2} a2 ins) = 
      begin
        (sum (map f (a :: (a2 :: as1))))
      ==<>
        (f a) + ((f a2) + (sum (map f as1)))
      ==< sym (+-assoc {f a}) >
        ((f a) + (f a2)) + (sum (map f as1))
      ==< +-left (+-commute {f a} {f a2}) >
        ((f a2) + (f a)) + (sum (map f as1))
      ==< +-assoc {f a2} >
        (f a2) + ((f a) + (sum (map f as1)))
      ==< +-right {f a2} (sum-map-Insertion f ins) >
        (f a2) + (sum (map f as2))
      ==<>
        (sum (map f (a2 :: as2)))
      end

    sum-map-Permutation : {as1 as2 : (List A)} -> (f : A -> Domain) -> (Permutation A as1 as2)
                         -> (sum (map f as1)) == (sum (map f as2))
    sum-map-Permutation f (permutation-empty) = refl
    sum-map-Permutation f (permutation-cons {a} {as1} {as2} {as3} perm ins) =
      (+-right {f a} (sum-map-Permutation f perm)) >=> (sum-map-Insertion f ins)
    


  
  
    all-pairs : List Term -> List Term -> List Term
    all-pairs [] b = []
    all-pairs (e :: a) b = (map (e ⊗_) b) ++ (all-pairs a b)
  
    linearize : Syntax n -> List Term
    linearize (var i) = (var i) :: []
    linearize (l ⊕ r) = (linearize l) ++ (linearize r)
    linearize (l ⊗ r) = all-pairs (linearize l) (linearize r)
  
    Meaning : Set
    Meaning = Vec Domain n -> Domain

    infix 4 _≈_
    _≈_ : Meaning -> Meaning -> Set
    m1 ≈ m2 = ∀ env -> (m1 env) == (m2 env)
    
    infixl 6 _+m_
    _+m_ : Meaning -> Meaning -> Meaning
    f +m g = \ env -> (f env) + (g env)

    _*m_ : Meaning -> Meaning -> Meaning
    f *m g = \ env -> (f env) * (g env)
    
  
    ⟦_⟧term : Term -> Meaning
    ⟦ (var i) ⟧term env = lookup env i
    ⟦ t1 ⊗ t2  ⟧term = ⟦ t1  ⟧term *m ⟦ t2 ⟧term


  
    ⟦_⟧terms : List Term -> Meaning
    ⟦ l ⟧terms env = sum (map (\ t -> ⟦ t ⟧term env) l)
  
    terms-eval-inject-++ : 
      {a b : List Term} -> ⟦ a ++ b ⟧terms ≈ ⟦ a ⟧terms +m ⟦ b ⟧terms 
    terms-eval-inject-++ {a} {b} env = sum-map-inject-++ (\ t -> ⟦ t ⟧term env) {a} {b}
  
    terms-eval-inject-map-⊗ : 
      {e : Term} -> {b : List Term} 
      -> ⟦ (map (e ⊗_) b) ⟧terms ≈ ⟦ e ⟧term *m ⟦ b ⟧terms 
    terms-eval-inject-map-⊗ {e} {[]} env = sym (*-right-zero {⟦ e ⟧term env})
    terms-eval-inject-map-⊗ {e} {(e2 :: b)} env = 
      begin
        ⟦ (map (e ⊗_) (e2 :: b)) ⟧terms env 
      ==<>
        ⟦ (map (e ⊗_) (e2 :: [])) ++ (map (e ⊗_) b) ⟧terms env 
      ==< terms-eval-inject-++ {map (e ⊗_) (e2 :: [])} {map (e ⊗_) b} env >
        ⟦ map (e ⊗_) (e2 :: []) ⟧terms env + ⟦ (map (e ⊗_) b) ⟧terms env 
      ==<>
        (⟦ e ⊗ e2 ⟧term env + 0#) + ⟦ (map (e ⊗_) b) ⟧terms env 
      ==< +-left (+-right-zero {⟦ e ⊗ e2 ⟧term env}) >
        ⟦ e ⊗ e2 ⟧term env + ⟦ (map (e ⊗_) b) ⟧terms env 
      ==< +-right {⟦ e ⊗ e2 ⟧term env} (terms-eval-inject-map-⊗ {e} {b} env) >
        ⟦ e ⊗ e2 ⟧term env + ⟦ e ⟧term env * ⟦ b ⟧terms env 
      ==<>
        ⟦ e ⟧term env * ⟦ e2 ⟧term env + ⟦ e ⟧term env * ⟦ b ⟧terms env 
      ==< sym (*-distrib-+-left {⟦ e ⟧term env}) >
        ⟦ e ⟧term env * (⟦ e2 ⟧term env + ⟦ b ⟧terms env )
      ==<>
        ⟦ e ⟧term env * ⟦ (e2 :: b) ⟧terms env 
      end
  
  
    terms-eval-inject-all-pairs : 
      (env : Vec Domain n) -> {a b : List Term} 
      -> ⟦ (all-pairs a b) ⟧terms env == ⟦ a ⟧terms env * ⟦ b ⟧terms env 
    terms-eval-inject-all-pairs env {[]} {b} = sym (*-left-zero {⟦ b ⟧terms env})
    terms-eval-inject-all-pairs env {e :: a} {b} =
      begin
        ⟦ (all-pairs (e :: a) b) ⟧terms env 
      ==<>
        ⟦ (map (e ⊗_) b) ++ (all-pairs a b) ⟧terms env 
      ==< terms-eval-inject-++ {map (e ⊗_) b} {all-pairs a b} env >
        (⟦ (map (e ⊗_) b) ⟧terms env) + (⟦ (all-pairs a b) ⟧terms env )
      ==< +-left (terms-eval-inject-map-⊗ {e} {b} env) > 
        (⟦ e ⟧term env * ⟦ b ⟧terms env) + (⟦ (all-pairs a b) ⟧terms env )
      ==< +-right {(⟦ e ⟧term env * ⟦ b ⟧terms env)} (terms-eval-inject-all-pairs env {a} {b}) > 
        (⟦ e ⟧term env * ⟦ b ⟧terms env) + (⟦ a ⟧terms env * ⟦ b ⟧terms env)
      ==< sym (*-distrib-+-right {⟦ e ⟧term env}) > 
        (⟦ e ⟧term env + ⟦ a ⟧terms env) * ⟦ b ⟧terms env 
      ==<> 
        ⟦ (e :: a) ⟧terms env * ⟦ b ⟧terms env 
      end
  
  
  
    terms-eval-inject-linearize-⊕ :
      (env : Vec Domain n) -> {e1 e2 : Syntax n}
      -> ⟦ linearize (e1 ⊕ e2) ⟧terms env == 
         ⟦ linearize e1 ⟧terms env + ⟦ linearize e2 ⟧terms env
    terms-eval-inject-linearize-⊕ env {e1} {e2} =
      terms-eval-inject-++ {linearize e1} {linearize e2} env
  
    terms-eval-inject-linearize-⊗ :
      (env : Vec Domain n) -> {e1 e2 : Syntax n}
      -> ⟦ linearize (e1 ⊗ e2) ⟧terms env == 
         ⟦ linearize e1 ⟧terms env * ⟦ linearize e2 ⟧terms env
    terms-eval-inject-linearize-⊗ env {e1} {e2} =
      terms-eval-inject-all-pairs env {linearize e1} {linearize e2}
  
  
  
    terms-eval-inject-insertion-sort :
      (env : Vec Domain n) -> {ts : List Term}
      -> ⟦ (insertion-sort term< ts) ⟧terms env == ⟦ ts ⟧terms env 
    terms-eval-inject-insertion-sort env {ts} =
      sym (sum-map-Permutation (\ t -> ⟦ t ⟧term env) (Permutation-insertion-sort term< ts))
  
    ⟦_⇓⟧ : Syntax n -> Meaning
    ⟦ e ⇓⟧ env = ⟦ (insertion-sort term< (linearize e)) ⟧terms env
  
  
    correct : (e : Syntax n) -> (env : Vec Domain n) -> ⟦ e ⇓⟧ env == ⟦ e ⟧ env 
    correct (var i) env = +-right-zero
    correct (l ⊕ r) env = 
      begin
        ⟦ l ⊕ r ⇓⟧ env
      ==<>
        ⟦ insertion-sort term< (linearize (l ⊕ r)) ⟧terms env
      ==< terms-eval-inject-insertion-sort env {linearize (l ⊕ r)} >
        ⟦ linearize (l ⊕ r) ⟧terms env
      ==< terms-eval-inject-linearize-⊕ env {l} {r} >
        ⟦ linearize l ⟧terms env + ⟦ linearize r ⟧terms env
      ==< (+-cong 
              (sym (terms-eval-inject-insertion-sort env {linearize l}))
              (sym (terms-eval-inject-insertion-sort env {linearize r}))) >
        ⟦ insertion-sort term< (linearize l) ⟧terms env + 
        ⟦ insertion-sort term< (linearize r) ⟧terms env
      ==< +-cong (correct l env) (correct r env) >
        ⟦ l ⟧ env + ⟦ r ⟧ env 
      ==<>
        ⟦ l ⊕ r ⟧ env 
      end
    correct (l ⊗ r) env = 
      begin
        ⟦ l ⊗ r ⇓⟧ env
      ==<>
        ⟦ insertion-sort term< (linearize (l ⊗ r)) ⟧terms env
      ==< terms-eval-inject-insertion-sort env {linearize (l ⊗ r)} >
        ⟦ linearize (l ⊗ r) ⟧terms env
      ==< terms-eval-inject-linearize-⊗ env {l} {r} >
        ⟦ linearize l ⟧terms env * ⟦ linearize r ⟧terms env
      ==< (*-cong 
              (sym (terms-eval-inject-insertion-sort env {linearize l}))
              (sym (terms-eval-inject-insertion-sort env {linearize r}))) >
        ⟦ insertion-sort term< (linearize l) ⟧terms env * 
        ⟦ insertion-sort term< (linearize r) ⟧terms env
      ==< *-cong (correct l env) (correct r env) >
        ⟦ l ⟧ env * ⟦ r ⟧ env 
      ==<>
        ⟦ l ⊗ r ⟧ env 
      end

    solve : (f : Nary n (Syntax n) ((Syntax n) × (Syntax n)))
            ->  Eqʰ n _==_ (curry n ⟦  (proj₁ (close n f)) ⇓⟧) (curry n ⟦ proj₂ (close n f) ⇓⟧)
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
      prove ρ pr = (sym (correct e₁ ρ)) >=> pr >=> (correct e₂ ρ)
    
      inner-reg-proof : (ρ : (Vec Domain n)) -> (⟦ e₁ ⟧ ρ) == (⟦ e₂ ⟧ ρ)
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

