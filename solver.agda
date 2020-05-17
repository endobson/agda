module solver where

open import equality
open import nat
open import int
open import Level using (Level; _⊔_; Lift)

data Syntax : Nat -> Set where
  _⊕_ : {n : Nat} -> Syntax n -> Syntax n -> Syntax n
  var : {n : Nat} -> Fin n -> Syntax n

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
  
  data List A : Set where
    [] : List A
    _::_  : (a : A) -> List A -> List A
  
  _++_ : List A -> List A -> List A
  [] ++ l2 = l2
  (a :: l1) ++ l2 = a :: (l1 ++ l2)
  
  sum : List Nat -> Nat
  sum [] = 0
  sum (a :: l) = a +' sum l

  sum-inject-++ : {a b : List Nat} -> sum (a ++ b) == sum a +' sum b
  sum-inject-++ {[]} = refl
  sum-inject-++ {e :: a} {b} = 
    begin
      sum ((e :: a) ++ b)
    ==<> 
      e +' (sum (a ++ b))
    ==< +'-right {e} (sum-inject-++ {a} {b}) >
      e +' (sum a +' sum b)
    ==< sym (+'-assoc {e}) >
      (e +' sum a) +' sum b
    ==<> 
      sum (e :: a) +' sum b
    end

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



private

  ⟦_⟧ : {n : Nat} -> Syntax n -> Vec Nat n -> Nat
  ⟦ (var i) ⟧ env = lookup env i
  ⟦ l ⊕ r ⟧ env = ⟦ l ⟧ env +' ⟦ r ⟧ env

  flatten : {n : Nat} -> Syntax n -> Vec Nat n -> List Nat
  flatten (var i) env = (lookup env i) :: []
  flatten (l ⊕ r) env = (flatten l env) ++ (flatten r env)

  sum-inject-flatten : {n : Nat} -> {e1 e2 : Syntax n} -> {env : Vec Nat n}
                        -> sum (flatten (e1 ⊕ e2) env) == 
                           sum (flatten e1 env) +' sum (flatten e2 env)
  sum-inject-flatten {_} {e1} {e2} {env} = sum-inject-++ {flatten e1 env}



  ⟦_⇓⟧ : {n : Nat} -> Syntax n -> Vec Nat n -> Nat
  ⟦ e ⇓⟧ env = sum (flatten e env)

private

  correct : {n : Nat} -> (e : Syntax n) -> (env : Vec Nat n) -> ⟦ e ⇓⟧ env == ⟦ e ⟧ env 
  correct (var i) env = +'-right-zero
  correct {n} (l ⊕ r) env = sum-inject-flatten {n} {l} {r}
                            >=> (+'-cong (correct l env) (correct r env))
  
  prove : {n : Nat} -> (e1 : Syntax n) -> (e2 : Syntax n) -> (env : Vec Nat n)
                    -> ⟦ e1 ⇓⟧ env == ⟦ e2 ⇓⟧ env -> ⟦ e1 ⟧ env == ⟦ e2 ⟧ env
  prove {n} e1 e2 env pr = (sym (correct e1 env)) >=> pr >=> (correct e2 env)

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

solve : (n : Nat) -> (f : Nary n (Syntax n) ((Syntax n) × (Syntax n)))
        ->  Eqʰ n _==_ (curry n ⟦ proj₁ (close n f) ⇓⟧) (curry n ⟦ proj₂ (close n f) ⇓⟧)
        ->  Eq n _==_ (curry n ⟦ proj₁ (close n f) ⟧) (curry n ⟦ proj₂ (close n f) ⟧)
solve n f hidden-normal-proof = full-reg-proof
  where
  e₁ : Syntax n
  e₁ = proj₁ (close n f)
  e₂ : Syntax n
  e₂ = proj₂ (close n f)

  full-normal-proof : Eq n _==_ (curry n ⟦ e₁ ⇓⟧) (curry n ⟦ e₂ ⇓⟧)
  full-normal-proof = unhide-∀ⁿ n hidden-normal-proof

  inner-normal-proof : (ρ : (Vec Nat n)) -> (⟦ e₁ ⇓⟧ ρ) == (⟦ e₂ ⇓⟧ ρ)
  inner-normal-proof = cong-curry⁻¹ n (⟦ e₁ ⇓⟧) (⟦ e₂ ⇓⟧) full-normal-proof

  inner-reg-proof : (ρ : (Vec Nat n)) -> (⟦ e₁ ⟧ ρ) == (⟦ e₂ ⟧ ρ)
  inner-reg-proof v = (prove e₁ e₂ v (inner-normal-proof v))

  full-reg-proof : Eq n _==_ (curry n ⟦ e₁ ⟧) (curry n ⟦ e₂ ⟧)
  full-reg-proof = cong-curry n (⟦ e₁ ⟧) (⟦ e₂ ⟧) inner-reg-proof

