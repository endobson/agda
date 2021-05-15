{-# OPTIONS --cubical --safe --exact-split #-}

module type-algebra where

open import base
open import commutative-monoid
open import equality
open import equivalence
open import functions
open import isomorphism
open import monoid
open import sum
open import univalence
open import vec

open Iso

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ

-- Product

×-Bot : (A : Type ℓ) -> (Bot × A) == Lift ℓ Bot
×-Bot {ℓ} A = ua (isoToEquiv i)
  where
  i : Iso (Bot × A) (Lift ℓ Bot)
  i .fun (b , _)  = bot-elim b
  i .inv (lift b) = bot-elim b
  i .rightInv (lift b) = bot-elim b
  i .leftInv (b , _)   = bot-elim b

×-Bot₀ : (A : Type₀) -> (Bot × A) == Bot
×-Bot₀ A = ua (isoToEquiv i)
  where
  i : Iso (Bot × A) Bot
  i .fun (b , _) = bot-elim b
  i .inv b       = bot-elim b
  i .rightInv b      = bot-elim b
  i .leftInv (b , _) = bot-elim b


×-Top : (A : Type ℓ) -> (Top × A) == A
×-Top A = ua (isoToEquiv i)
  where
  i : Iso (Top × A) A
  i .fun (tt , a)  = a
  i .inv a         = (tt , a)
  i .rightInv _ = refl
  i .leftInv _ = refl

×-flip : {A B : Type ℓ} -> (A × B) == (B × A)
×-flip {A = A} {B} = ua (isoToEquiv i)
  where
  i : Iso (A × B) (B × A)
  i .fun (a , b) = (b , a)
  i .inv (b , a) = (a , b)
  i .rightInv _ = refl
  i .leftInv _ = refl

×-assoc : (A B C : Type ℓ) -> ((A × B) × C) == (A × (B × C))
×-assoc A B C = ua (isoToEquiv i)
  where
  i : Iso ((A × B) × C) (A × (B × C))
  i .fun ((a , b) , c) = (a , (b , c))
  i .inv (a , (b , c)) = ((a , b) , c)
  i .rightInv _ = refl
  i .leftInv _ = refl

instance
  ×-Monoid : Monoid (Type ℓ-zero)
  ×-Monoid = record
    { ε = Top
    ; _∙_ = _×_
    ; ∙-assoc = \{A B C} -> ×-assoc A B C
    ; ∙-left-ε = \{A} -> ×-Top A
    ; ∙-right-ε = \{A} -> ×-flip >=> ×-Top A
    }

  ×-CommMonoid : CommMonoid (Type ℓ-zero)
  ×-CommMonoid = record
    { ∙-commute = ×-flip
    }

-- Disjoint Sum

⊎-Bot : (A : Type ℓ) -> (Bot ⊎ A) == A
⊎-Bot A = ua (isoToEquiv i)
  where
  i : Iso (Bot ⊎ A) A
  i .fun (inj-r a) = a
  i .fun (inj-l ())
  i .inv a = (inj-r a)
  i .rightInv a = refl
  i .leftInv (inj-r a) = refl
  i .leftInv (inj-l ())

⊎-flip : {A : Type ℓ₁} {B : Type ℓ₂} -> (A ⊎ B) == (B ⊎ A)
⊎-flip {A = A} {B} = ua (isoToEquiv i)
  where
  i : Iso (A ⊎ B) (B ⊎ A)
  i .fun (inj-l a) = inj-r a
  i .fun (inj-r b) = inj-l b
  i .inv (inj-l b) = inj-r b
  i .inv (inj-r a) = inj-l a
  i .rightInv (inj-l _) = refl
  i .rightInv (inj-r _) = refl
  i .leftInv  (inj-l _) = refl
  i .leftInv  (inj-r _) = refl


⊎-Top : {A B : Type ℓ} -> (Top ⊎ A) == (Top ⊎ B) -> A == B
⊎-Top {A = A} {B = B} ⊎path = ua (isoToEquiv new-iso)
  where
  iso' : Iso (Top ⊎ A) (Top ⊎ B)
  iso' = pathToIso ⊎path

  f : (Top ⊎ A) -> (Top ⊎ B)
  g : (Top ⊎ B) -> (Top ⊎ A)
  f = iso' .fun
  g = iso' .inv

  module both-left
           (f-Left : (f (inj-l tt)) == (inj-l tt))
           (g-Left : (g (inj-l tt)) == (inj-l tt))  where
    f-Right' : (a : A) -> Σ[ b ∈ B ] (inj-r b) == f (inj-r a)
    f-Right' a = handle (f (inj-r a)) refl
      where
      handle : (s2 : Top ⊎ B) -> s2 == (f (inj-r a)) -> Σ[ b ∈ B ] (inj-r b) == (f (inj-r a))
      handle (inj-r b) p = b , p
      handle (inj-l _) p = bot-elim (inj-l!=inj-r path)
        where
        path : (inj-l tt) == (inj-r a)
        path = sym g-Left >=> cong g p >=> (iso' .leftInv (inj-r a))

    g-Right' : (b : B) -> Σ[ a ∈ A ] (inj-r a) == g (inj-r b)
    g-Right' b = handle (g (inj-r b)) refl
      where
      handle : (s2 : Top ⊎ A) -> s2 == (g (inj-r b)) -> Σ[ a ∈ A ] (inj-r a) == (g (inj-r b))
      handle (inj-r a) p = a , p
      handle (inj-l _) p = bot-elim (inj-l!=inj-r path)
        where
        path : (inj-l tt) == (inj-r b)
        path = sym f-Left >=> cong f p >=> (iso' .rightInv (inj-r b))

    f' : A -> B
    f' a = fst (f-Right' a)
    f'-path : (a : A) -> inj-r (f' a) == f (inj-r a)
    f'-path a = snd (f-Right' a)

    g' : B -> A
    g' b = fst (g-Right' b)
    g'-path : (b : B) -> inj-r (g' b) == g (inj-r b)
    g'-path b = snd (g-Right' b)

    fg' : (b : B) -> Path B (f' (g' b)) b
    fg' b = inj-r-injective
      (f'-path (g' b)
       >=> cong f (g'-path b)
       >=> iso' .rightInv (inj-r b))

    gf' : (a : A) -> Path A (g' (f' a)) a
    gf' a = inj-r-injective
      (g'-path (f' a)
       >=> cong g (f'-path a)
       >=> iso' .leftInv (inj-r a))

    new-iso : Iso A B
    new-iso .fun = f'
    new-iso .inv = g'
    new-iso .rightInv = fg'
    new-iso .leftInv = gf'

  module f-left-g-right
           (f-Left : (f (inj-l tt)) == (inj-l tt))
           {a : A}
           (g-Left : (g (inj-l tt)) == (inj-r a))  where

    absurd : Bot
    absurd = inj-l!=inj-r (sym (iso' .leftInv (inj-l tt)) >=> cong g f-Left >=> g-Left)

  module f-right-g-left
           {b : B}
           (f-Left : (f (inj-l tt)) == (inj-r b))
           (g-Left : (g (inj-l tt)) == (inj-l tt))  where

    absurd : Bot
    absurd = inj-l!=inj-r (sym (iso' .rightInv (inj-l tt)) >=> cong f g-Left >=> f-Left)

  module both-right
           {b-base : B}
           (f-Left : (f (inj-l tt)) == (inj-r b-base))
           {a-base : A}
           (g-Left : (g (inj-l tt)) == (inj-r a-base)) where

    f'-base : (Top ⊎ B) -> B
    f'-base (inj-l _) = b-base
    f'-base (inj-r b) = b

    f' : A -> B
    f' a = (f'-base (f (inj-r a)))


    g'-base : (Top ⊎ A) -> A
    g'-base (inj-l _) = a-base
    g'-base (inj-r a) = a

    g' : B -> A
    g' b = (g'-base (g (inj-r b)))

    fg' : (b : B) -> (f' (g' b)) == b
    fg' b = handle (g (inj-r b)) refl
      where
      handle : (a : (Top ⊎ A)) -> a == g (inj-r b) -> (f' (g' b)) == b
      handle (inj-l _) p =
        begin
          f' (g' b)
        ==<>
          f' (g'-base (g (inj-r b)))
        ==< cong f' (cong g'-base (sym p)) >
          f' a-base
        ==<>
          f'-base (f (inj-r a-base))
        ==< cong f'-base (cong f (sym g-Left)) >
          f'-base (f (g (inj-l tt)))
        ==< cong f'-base (iso' .rightInv (inj-l tt)) >
          b-base
        ==< b-path >
          b
        end
        where
        b-path : b-base == b
        b-path = inj-r-injective
          (sym f-Left
           >=> cong f p
           >=> iso' .rightInv (inj-r b))
      handle (inj-r a) p =
        begin
          f' (g' b)
        ==<>
          f' (g'-base (g (inj-r b)))
        ==< cong f' (cong g'-base (sym p)) >
          f' a
        ==<>
          f'-base (f (inj-r a))
        ==< cong f'-base (cong f p) >
          f'-base (f (g (inj-r b)))
        ==< cong f'-base (iso' .rightInv (inj-r b)) >
          f'-base (inj-r b)
        ==<>
          b
        end

    gf' : (a : A) -> (g' (f' a)) == a
    gf' a = handle (f (inj-r a)) refl
      where
      handle : (b : (Top ⊎ B)) -> b == f (inj-r a) -> (g' (f' a)) == a
      handle (inj-l _) p =
        begin
          g' (f' a)
        ==<>
          g' (f'-base (f (inj-r a)))
        ==< cong g' (cong f'-base (sym p)) >
          g' b-base
        ==<>
          g'-base (g (inj-r b-base))
        ==< cong g'-base (cong g (sym f-Left)) >
          g'-base (g (f (inj-l tt)))
        ==< cong g'-base (iso' .leftInv (inj-l tt)) >
          a-base
        ==< a-path >
          a
        end
        where
        a-path : a-base == a
        a-path = inj-r-injective
          (sym g-Left
           >=> cong g p
           >=> iso' .leftInv (inj-r a))
      handle (inj-r b) p =
        begin
          g' (f' a)
        ==<>
          g' (f'-base (f (inj-r a)))
        ==< cong g' (cong f'-base (sym p)) >
          g' b
        ==<>
          g'-base (g (inj-r b))
        ==< cong g'-base (cong g p) >
          g'-base (g (f (inj-r a)))
        ==< cong g'-base (iso' .leftInv (inj-r a)) >
          g'-base (inj-r a)
        ==<>
          a
        end

    new-iso : Iso A B
    new-iso .fun = f'
    new-iso .inv = g'
    new-iso .rightInv = fg'
    new-iso .leftInv = gf'


  new-iso : Iso A B
  new-iso = handle (f (inj-l tt)) refl (g (inj-l tt)) refl
    where
    handle : (b : Top ⊎ B) -> (f (inj-l tt)) == b -> (a : Top ⊎ A) -> (g (inj-l tt)) == a -> Iso A B
    handle (inj-l _) f-p (inj-l _) g-p = both-left.new-iso f-p g-p
    handle (inj-l _) f-p (inj-r _) g-p = bot-elim (f-left-g-right.absurd f-p g-p)
    handle (inj-r _) f-p (inj-l _) g-p = bot-elim (f-right-g-left.absurd f-p g-p)
    handle (inj-r _) f-p (inj-r _) g-p = both-right.new-iso f-p g-p

⊎-assoc : (A B C : Type ℓ) -> ((A ⊎ B) ⊎ C) == (A ⊎ (B ⊎ C))
⊎-assoc A B C = ua (isoToEquiv i)
  where
  i : Iso ((A ⊎ B) ⊎ C) (A ⊎ (B ⊎ C))
  i .fun (inj-l (inj-l a)) = inj-l a
  i .fun (inj-l (inj-r b)) = inj-r (inj-l b)
  i .fun (inj-r c)         = inj-r (inj-r c)
  i .inv (inj-l a)         = inj-l (inj-l a)
  i .inv (inj-r (inj-l b)) = inj-l (inj-r b)
  i .inv (inj-r (inj-r c)) = inj-r c
  i .rightInv (inj-l a)         = refl
  i .rightInv (inj-r (inj-l b)) = refl
  i .rightInv (inj-r (inj-r c)) = refl
  i .leftInv (inj-l (inj-l a)) = refl
  i .leftInv (inj-l (inj-r b)) = refl
  i .leftInv (inj-r c)         = refl

instance
  ⊎-Monoid : Monoid (Type ℓ-zero)
  ⊎-Monoid = record
    { ε = Bot
    ; _∙_ = _⊎_
    ; ∙-assoc = \{A B C} -> ⊎-assoc A B C
    ; ∙-left-ε = \{A} -> ⊎-Bot A
    ; ∙-right-ε = \{A} -> ⊎-flip >=> ⊎-Bot A
    }

  ⊎-CommMonoid : CommMonoid (Type ℓ-zero)
  ⊎-CommMonoid = record
    { ∙-commute = ⊎-flip
    }

×-distrib-⊎ : {A B C : Type ℓ} -> ((A ⊎ B) × C) == ((A × C) ⊎ (B × C))
×-distrib-⊎ {A = A} {B} {C} = ua (isoToEquiv i)
  where
  i : Iso ((A ⊎ B) × C) ((A × C) ⊎ (B × C))
  i .fun (inj-l a , c) = inj-l (a , c)
  i .fun (inj-r b , c) = inj-r (b , c)
  i .inv (inj-l (a , c)) = (inj-l a , c)
  i .inv (inj-r (b , c)) = (inj-r b , c)
  i .leftInv ((inj-l _) , _) = refl
  i .leftInv ((inj-r _) , _) = refl
  i .rightInv (inj-l _) = refl
  i .rightInv (inj-r _) = refl


Vec-Top : (A : Type₀) -> Vec A 0 == Top
Vec-Top A = ua (isoToEquiv i)
  where
  i : Iso (Vec A 0) Top
  i .fun _ = tt
  i .inv _ = []
  i .rightInv tt = refl
  i .leftInv [] = refl


Vec-Id : (A : Type₀) -> Vec A 1 == A
Vec-Id A = ua (isoToEquiv i)
  where
  i : Iso (Vec A 1) A
  i .fun (a :: []) = a
  i .inv a = (a :: [])
  i .rightInv _ = refl
  i .leftInv (a :: []) = refl

Vec-× : {n : Nat} -> (A : Type₀) -> (Vec A (suc n)) == (A × Vec A n)
Vec-× {n} A = ua (isoToEquiv i)
  where
  i : Iso (Vec A (suc n)) (A × (Vec A n))
  i .fun (a :: as) = (a , as)
  i .inv (a , as) = (a :: as)
  i .rightInv (_ , _) = refl
  i .leftInv (_ :: _) = refl

Bot-Fun : (A : Type₀) -> ((Bot -> A) == Top)
Bot-Fun A = ua (isoToEquiv i)
  where
  i : Iso (Bot -> A) Top
  i .fun f = tt
  i .inv tt = \()
  i .rightInv _ = refl
  i .leftInv f i ()

Top-Fun : (A : Type₀) -> ((Top -> A) == A)
Top-Fun A = ua (isoToEquiv i)
  where
  i : Iso (Top -> A) A
  i .fun f = f tt
  i .inv a _ = a
  i .rightInv _ = refl
  i .leftInv _ = refl

⊎-Fun : (A B C : Type₀) -> ((A ⊎ B) -> C) == ((A -> C) × (B -> C))
⊎-Fun A B C = ua (isoToEquiv i)
  where
  i : Iso ((A ⊎ B) -> C) ((A -> C) × (B -> C))
  i .fun f = (f ∘ inj-l , f ∘ inj-r)
  i .inv (f , g) (inj-l a) = f a
  i .inv (f , g) (inj-r b) = g b
  i .rightInv (f , g) = refl
  i .leftInv f i (inj-l a) = f (inj-l a)
  i .leftInv f i (inj-r b) = f (inj-r b)
