{-# OPTIONS --cubical --safe --exact-split #-}

module equality where

open import base
open import cubical

open cubical public using (PathP; ~_)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A A1 A2 : Type ℓ
    B : A -> Type ℓ
    C : (a : A) -> (B a) -> Type ℓ


abstract
  cong : (f : (a : A) -> (B a)) -> {x y : A} -> (p : x == y) -> PathP (\i -> (B (p i))) (f x) (f y)
  cong f p i = f (p i)

  cong2 : {A : Type ℓ₁} -> {B : Type ℓ₂} -> {C : Type ℓ₃} ->
          (f : A -> B -> C) -> {a c : A} -> {b d : B} -> a == c -> b == d -> f a b == f c d
  cong2 f p1 p2 i = f (p1 i) (p2 i)

  cong2-dep : (f : (a : A) -> (b : B a) -> C a b)
              {x y : A} (p : x == y)
              {u : B x} {v : B y} (q : PathP (\i -> B (p i)) u v)
              -> PathP (\i -> C (p i) (q i)) (f x u) (f y v)
  cong2-dep f p q i = f (p i) (q i)

  sym : {x y : A} -> x == y -> y == x
  sym p i = p (~ i)

  transport : {A B : Type ℓ} -> A == B -> A -> B
  transport p a = transp (\i -> p i) i0 a

  transportRefl : (x : A) -> transport refl x == x
  transportRefl {A = A} x i = transp (λ _ -> A) i x

  transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A == B) (x : A)
                     -> PathP (\ i -> p i) x (transport p x)
  transport-filler p x i = transp (\j -> p (i ∧ j)) (~ i) x

  module _ {x : A} (P : ∀ y -> x == y -> Type ℓ) (d : P x refl) where

    J : {y : A} -> (p : x == y) -> P y p
    J p = transport (\i -> P (p i) (\j -> p (i ∧ j))) d

    JRefl : J refl == d
    JRefl = transportRefl d

  _∙∙_∙∙_ : {w x y z : A} -> w == x -> x == y -> y == z -> w == z
  (p ∙∙ q ∙∙ r) i =
    hcomp (\ j -> \ { (i = i0) -> p (~ j)
                    ; (i = i1) -> r j})
          (q i)

  doubleCompPath-filler :
    {ℓ : Level} {A : Type ℓ} {w x y z : A}
    (p : w == x) (q : x == y) (r : y == z)
    -> PathP (\i -> p (~ i) == r i) q (p ∙∙ q ∙∙ r)
  doubleCompPath-filler p q r j i =
    hfill (\ j -> (\ { (i = i0) -> (p (~ j))
                     ; (i = i1) -> r j }))
          (inS (q i)) j

  trans : {x y z : A} -> x == y -> y == z -> x == z
  trans p1 p2 = refl ∙∙ p1 ∙∙ p2

  infixl 20 _>=>_
  _>=>_ : {x y z : A} -> x == y -> y == z -> x == z
  p1 >=> p2 = trans p1 p2

  private
    _∙_ : {x y z : A} -> x == y -> y == z -> x == z
    _∙_ = trans

  compPath-filler : {x y z : A} (p : x == y) (q : y == z) -> PathP (\i -> x == (q i)) p (p ∙ q)
  compPath-filler p q = doubleCompPath-filler refl p q


-- Path identies with refl
abstract
  compPath-refl-right : {x y : A} (p : x == y) -> (p >=> refl) == p
  compPath-refl-right p = sym (compPath-filler p refl)

  compPath-refl-left : {x y : A} (p : x == y) -> (refl >=> p) == p
  compPath-refl-left p = swap-sides >=> compPath-refl-right p
    where
    swap-sides : (refl >=> p) == (p >=> refl)
    swap-sides j = (\i -> p (i ∧ j)) >=> (\i -> p (i ∨ j))

  compPath-sym : {x y : A} (p : x == y) -> (p >=> sym p) == refl
  compPath-sym p = contract >=> compPath-refl-right refl
    where
    contract : (p >=> sym p) == (refl >=> refl)
    contract j = (\i -> p (i ∧ (~ j))) >=> (\i -> p (~ i ∧ (~ j)))

-- Path composition with transport
abstract
  transport-twice : ∀ {A B C : Type ℓ} (p : B == C) (q : A == B) (x : A)
                    -> transport p (transport q x) == (transport (q >=> p) x)
  transport-twice p q x =
    (\i -> transport p (transport (compPath-refl-right q (~ i)) x))
    >=> (\i -> transport (\j -> p (i ∨ j)) (transport (q >=> (\j -> p (i ∧ j))) x))
    >=> transportRefl (transport (q >=> p) x)

-- Path composition on PathP

abstract
  transP : {A : I -> Type ℓ} {a0 : A i0} {a1 : A i1} {B_i1 : Type ℓ} {B : A i1 == B_i1}
           {b1 : B_i1} (p : PathP A a0 a1) (q : PathP (\i -> B i) a1 b1)
           -> PathP (\j -> ((\k -> A k) ∙ B) j) a0 b1
  transP {A = A} {a0 = a0} {B = B} p q i =
    comp (\j -> compPath-filler (\k -> A k) B j i)
         (\j -> (\ { (i = i0) -> a0
                   ; (i = i1) -> q j}))
         (p i)

  transP-left : {A : I -> Type ℓ} {a0 : A i0} {a1 : A i1} {b1 : A i1}
                (p : PathP A a0 a1) (q : Path (A i1) a1 b1)
                -> PathP A a0 b1
  transP-left {A = A} {a0} {a1} {b1} p q =
    transport (\k -> PathP (\j -> (compPath-refl-right (\k -> A k) k) j) a0 b1)
              (transP p q)

  transP-right : {A : I -> Type ℓ} {a0 : A i0} {b0 : A i0} {b1 : A i1}
                 (p : Path (A i0) a0 b0) (q : PathP A b0 b1)
                 -> PathP A a0 b1
  transP-right {A = A} {a0} {b0} {b1} p q =
    transport (\k -> PathP (\j -> (compPath-refl-left (\k -> A k) k) j) a0 b1)
              (transP p q)

  transP-mid : {A : I -> Type ℓ} {a0 : A i0} {b0 : A i0} {b1 : A i1} {a1 : A i1}
               (p : Path (A i0) a0 b0) (q : PathP A b0 b1) (r : Path (A i1) b1 a1) ->
               PathP A a0 a1
  transP-mid p q r = transP-right p (transP-left q r)

-- Path reversal on PathP
abstract
  symP : {A : I -> Type ℓ} -> {a0 : A i0} {a1 : A i1} -> PathP A a0 a1 -> PathP (\k -> A (~ k)) a1 a0
  symP p k = p (~ k)

-- Substitution
substᵉ : {x y : A} -> (P : A → Type ℓ) -> x == y -> P x -> P y
substᵉ P path = transport (\ i -> (P (path i)))

abstract
  subst : {x y : A} -> (P : A → Type ℓ) -> x == y -> P x -> P y
  subst = substᵉ

  subst2 : {a11 a12 : A1} {a21 a22 : A2} -> (P : A1 -> A2 -> Type ℓ) ->
           a11 == a12 -> a21 == a22 -> P a11 a21 -> P a12 a22
  subst2 P path1 path2 = transport (\ i -> (P (path1 i) (path2 i)))

  subst-filler : {x y : A} -> (Q : A -> Type ℓ) -> (p : x == y) -> (qx : (Q x))
               -> PathP (\i -> Q (p i)) qx (substᵉ Q p qx)
  subst-filler Q p qx = transport-filler (cong Q p) qx

  subst-filler2 :  {x y : A} -> (Q : A -> Type ℓ) (p1 p2 : x == y) (pp : p1 == p2)
                   (qx : Q x) -> PathP (\k -> Q (p1 k)) qx (substᵉ Q p2 qx)
  subst-filler2 Q p1 p2 pp qx = transP-left (subst-filler Q p1 qx) (\k -> subst Q (pp k) qx)

  subst-refl : {x : A} -> {P : A → Type ℓ} -> {px : P x} -> subst P refl px == px
  subst-refl {px = px} = transportRefl px

-- True identity

path->id : {x y : A} -> x == y -> x === y
path->id {x = x} {y = y} path = (subst (x ===_) path refl-===)

id->path : {x y : A} -> x === y -> x == y
id->path refl-=== = refl


module EqReasoning where
  -- Equational reasoning
  infix  1 begin_
  infixr 2 _==<>_ _==<_>_
  infix  3 _end

  begin_ : {x y : A} -> x == y -> x == y
  begin x==y  =  x==y

  _==<>_ : (x : A) {y : A} -> x == y -> x == y
  x ==<> x==y  =  x==y

  _==<_>_ : (x : A) {y z : A} -> x == y -> y == z -> x == z
  x ==< x==y > y==z  =  trans x==y y==z

  _end : (x : A) -> x == x
  x end  =  refl

_!=_ : A -> A -> Type _
x != y = ¬ (x == y)

_!==_ : A -> A -> Type _
x !== y = ¬ (x === y)
