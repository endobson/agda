{-# OPTIONS --cubical #-}

module equality where

open import Level
open import base

cong : {a b : Level} {A : Set a} {B : Set b} -> (f : A -> B) -> {x y : A} -> x == y -> f x == f y  
cong f p i = f (p i)

cong2 : {i1 i2 i3 : Level} -> {A : Set i1} -> {B : Set i2} -> {C : Set i3} -> 
        (f : A -> B -> C) -> {a c : A} -> {b d : B} -> a == c -> b == d -> f a b == f c d
cong2 f p1 p2 i = f (p1 i) (p2 i)

cong2-dep : ∀ {l} {A : Set l} {B : A -> Set l} {x y} {C : (a : A) → (b : B a) → Set l} →
            (f : (a : A) → (b : B a) → C a b) →
            (p : x == y) →
            {u : B x} {v : B y} (q : PathP (λ i → B (p i)) u v) →
            PathP (λ i → C (p i) (q i)) (f x u) (f y v)
cong2-dep f p q i = f (p i) (q i)

sym : {a : Level} {A : Set a} -> {x y : A} -> x == y -> y == x 
sym p i = p (~ i)

transport : ∀ {i} {A B : Set i} -> A == B -> A -> B
transport p a = transp (\ i -> p i) i0 a

J : ∀ {i} {A : Set i} {x : A} (P : ∀ y → x == y → Set i)
      (d : P x refl) {y : A} (p : x ≡ y)
    → P y p
J P d p = transport (\ i -> P (p i) (\ j -> p (i ∧ j))) d


_∙∙_∙∙_ : ∀ {a} {A : Set a} {w x y z : A} -> w == x -> x == y -> y == z -> w == z
(p ∙∙ q ∙∙ r) i =
  hcomp (\ j -> \ { (i = i0) -> p (~ j)
                  ; (i = i1) -> r j})
        (q i)

trans : {a : Level} {A : Set a} -> {x y z : A} -> x == y -> y == z -> x == z
trans p1 p2 = refl ∙∙ p1 ∙∙ p2


subst : {a p : Level} -> {A : Set a} -> {x y : A} -> (P : A → Set p) -> x == y -> P x -> P y
subst P path = transport (\ i -> (P (path i)))

-- Σ-types
infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

idfun : ∀ {ℓ} → (A : Set ℓ) → A → A
idfun _ x = x

idIsEquiv : ∀ {ℓ} (A : Set ℓ) → isEquiv (idfun A)
equiv-proof (idIsEquiv A) y =
  ((y , refl) , λ z i → z .snd (~ i) , λ j → z .snd (~ i ∨ j))

idEquiv : ∀ {ℓ} (A : Set ℓ) → A ≃ A
idEquiv A .fst = idfun A
idEquiv A .snd = idIsEquiv A

Glue : ∀ {i j} (A : Set i) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Set j ] T ≃ A))
       → Set j
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

ua : ∀ {i} {A B : Set i} -> A ≃ B -> A == B
ua {A = A} {B = B} e i = Glue B (\ { (i = i0) -> (A , e)
                                   ; (i = i1) -> (B , idEquiv B) })



path->id : ∀ {i} {A : Set i} {x y : A} -> x == y -> x === y
path->id {x = x} {y = y} path = (subst (\ z -> x === z) path refl-===)

id->path : ∀ {i} {A : Set i} {x y : A} -> x === y -> x == y
id->path refl-=== = refl


infix  1 begin_
infixr 2 _==<>_ _==<_>_
infix  3 _end

begin_ : {a : Level} -> {A : Set a} -> {x y : A} -> x == y -> x == y
begin x==y  =  x==y
 
_==<>_ : {a : Level} {A : Set a} -> (x : A) {y : A} -> x == y -> x == y
x ==<> x==y  =  x==y
 
_==<_>_ : {a : Level} {A : Set a} (x : A) {y z : A} -> x == y -> y == z -> x == z
x ==< x==y > y==z  =  trans x==y y==z

_end : {a : Level} {A : Set a} (x : A) -> x == x
x end  =  refl

_!=_ : {a : Level} -> {A : Set a} -> A -> A -> Set a
x != y = ¬ (x == y)

_!==_ : {a : Level} -> {A : Set a} -> A -> A -> Set a
x !== y = ¬ (x === y)


infixl 20 _>=>_
_>=>_ : {a : Level} {A : Set a} -> {x y z : A} -> x == y -> y == z -> x == z
p1 >=> p2 = trans p1 p2

