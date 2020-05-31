{-# OPTIONS --cubical --safe --exact-split #-}

module equality where

open import Level
open import base

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Type ℓ
    B : A -> Type ℓ
    C : (a : A) -> (B a) -> Type ℓ

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

J : {x : A} (P : ∀ y -> x == y -> Type ℓ)
    (d : P x refl) {y : A} (p : x == y)
    -> P y p
J P d p = transport (\ i -> P (p i) (\ j -> p (i ∧ j))) d


_∙∙_∙∙_ : {w x y z : A} -> w == x -> x == y -> y == z -> w == z
(p ∙∙ q ∙∙ r) i =
  hcomp (\ j -> \ { (i = i0) -> p (~ j)
                  ; (i = i1) -> r j})
        (q i)

trans : {x y z : A} -> x == y -> y == z -> x == z
trans p1 p2 = refl ∙∙ p1 ∙∙ p2


subst : {x y : A} -> (P : A → Type ℓ) -> x == y -> P x -> P y
subst P path = transport (\ i -> (P (path i)))

-- Σ-types
infix 2 Σ-syntax

Σ-syntax : ∀ (A : Type ℓ₁) (B : A → Type ℓ₂) → Type (ℓ-max ℓ₁ ℓ₂)
Σ-syntax = Σ

syntax Σ-syntax A (\x -> B) = Σ[ x ∈ A ] B

idfun : (A : Type ℓ) → A → A
idfun _ x = x


idIsEquiv : (A : Type ℓ) → isEquiv (idfun A)
equiv-proof (idIsEquiv A) y =
  ((y , refl) , \ z i -> z .snd (~ i) , \ j -> z .snd (~ i ∨ j))

idEquiv : (A : Type ℓ) → A ≃ A
idEquiv A .fst = idfun A
idEquiv A .snd = idIsEquiv A

Glue : ∀ (A : Type ℓ₁) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Type ℓ₂ ] T ≃ A))
       → Type ℓ₂
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

ua : ∀ {A B : Type ℓ} -> A ≃ B -> A == B
ua {A = A} {B = B} e i = Glue B (\ { (i = i0) -> (A , e)
                                   ; (i = i1) -> (B , idEquiv B) })



path->id : {x y : A} -> x == y -> x === y
path->id {x = x} {y = y} path = (subst (x ===_) path refl-===)

id->path : {x y : A} -> x === y -> x == y
id->path refl-=== = refl


module _ {f g : (a : A) -> B a} where

  funExt : ((x : A) -> f x == g x) -> f == g
  funExt p i x = p x i
  funExt⁻ : f == g -> ((x : A) -> f x == g x)
  funExt⁻ eq a i = eq i a

  private
    fib : (p : f == g) -> fiber funExt p
    fib p = ((\x i -> (p i) x) , refl)
    funExt-fiber-isContr : (p : f == g) -> (fi : fiber funExt p) -> fib p == fi
    funExt-fiber-isContr p (h , eq) i = (funExt⁻ (eq (~ i)) , \j -> eq (~ i ∨ j))


  funExt-isEquiv : isEquiv funExt
  equiv-proof funExt-isEquiv p = (fib p , funExt-fiber-isContr p)

  funExtEquiv : ((x : A) -> f x == g x) ≃ (f == g)
  funExtEquiv = (funExt , funExt-isEquiv)

  funExtPath : ((x : A) -> f x == g x) == (f == g)
  funExtPath = ua funExtEquiv




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


infixl 20 _>=>_
_>=>_ : {x y z : A} -> x == y -> y == z -> x == z
p1 >=> p2 = trans p1 p2

