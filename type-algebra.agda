{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module type-algebra where

open import base
open import cubical
open import equality-path
open import equality.square
open import equivalence
open import functions
open import funext
open import hlevel
open import infinity-monoid
open import isomorphism
open import maybe
open import monoid
open import sigma.base
open import sum
open import truncation
open import univalence
open import vec

open Iso

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Type ℓ

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

×-LiftBot : (A : Type ℓ) -> (Lift ℓ Bot × A) == Lift ℓ Bot
×-LiftBot {ℓ} A = ua (isoToEquiv i)
  where
  i : Iso (Lift ℓ Bot × A) (Lift ℓ Bot)
  i .fun (lift b , _)  = bot-elim b
  i .inv (lift b) = bot-elim b
  i .rightInv (lift b) = bot-elim b
  i .leftInv (lift b , _)   = bot-elim b

×-Top-eq : (A : Type ℓ) -> (Top × A) ≃ A
×-Top-eq A = (isoToEquiv i)
  where
  i : Iso (Top × A) A
  i .fun (tt , a)  = a
  i .inv a         = (tt , a)
  i .rightInv _ = refl
  i .leftInv _ = refl

×-Top : (A : Type ℓ) -> (Top × A) == A
×-Top A = ua (×-Top-eq A)


×-LiftTop : (A : Type ℓ) -> (Lift ℓ Top × A) == A
×-LiftTop A = ua (isoToEquiv i)
  where
  i : Iso (Lift ℓ Top × A) A
  i .fun (lift tt , a)  = a
  i .inv a         = (lift tt , a)
  i .rightInv _ = refl
  i .leftInv _ = refl


×-flip-eq : {A : Type ℓ₁} {B : Type ℓ₂} -> (A × B) ≃ (B × A)
×-flip-eq {A = A} {B} = (isoToEquiv i)
  where
  i : Iso (A × B) (B × A)
  i .fun (a , b) = (b , a)
  i .inv (b , a) = (a , b)
  i .rightInv _ = refl
  i .leftInv _ = refl

×-flip : {A : Type ℓ₁} {B : Type ℓ₂} -> (A × B) == (B × A)
×-flip {A = A} {B} = ua ×-flip-eq

×-assoc : (A B C : Type ℓ) -> ((A × B) × C) == (A × (B × C))
×-assoc A B C = ua (isoToEquiv i)
  where
  i : Iso ((A × B) × C) (A × (B × C))
  i .fun ((a , b) , c) = (a , (b , c))
  i .inv (a , (b , c)) = ((a , b) , c)
  i .rightInv _ = refl
  i .leftInv _ = refl

instance
  ×-InfinityMonoid : InfinityMonoid (Type ℓ-zero)
  ×-InfinityMonoid = record
    { ε = Top
    ; _∙_ = _×_
    ; ∙-assoc = \{A B C} -> ×-assoc A B C
    ; ∙-left-ε = \{A} -> ×-Top A
    ; ∙-right-ε = \{A} -> ×-flip >=> ×-Top A
    }

-- Disjoint Sum

⊎-Bot-eq : (A : Type ℓ) -> (Bot ⊎ A) ≃ A
⊎-Bot-eq A = (isoToEquiv i)
  where
  i : Iso (Bot ⊎ A) A
  i .fun (inj-r a) = a
  i .fun (inj-l ())
  i .inv a = (inj-r a)
  i .rightInv a = refl
  i .leftInv (inj-r a) = refl
  i .leftInv (inj-l ())

⊎-Bot : (A : Type ℓ) -> (Bot ⊎ A) == A
⊎-Bot A = ua (⊎-Bot-eq A)

⊎-LiftBot : (A : Type ℓ) -> (Lift ℓ Bot ⊎ A) == A
⊎-LiftBot {ℓ} A = ua (isoToEquiv i)
  where
  i : Iso (Lift ℓ Bot ⊎ A) A
  i .fun (inj-r a) = a
  i .fun (inj-l (lift ()))
  i .inv a = (inj-r a)
  i .rightInv a = refl
  i .leftInv (inj-r a) = refl
  i .leftInv (inj-l (lift ()))


⊎-flip-eq : {A : Type ℓ₁} {B : Type ℓ₂} -> (A ⊎ B) ≃ (B ⊎ A)
⊎-flip-eq {A = A} {B} = (isoToEquiv i)
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

⊎-flip : {A : Type ℓ₁} {B : Type ℓ₂} -> (A ⊎ B) == (B ⊎ A)
⊎-flip {A = A} {B} = ua ⊎-flip-eq

⊎-Top-eq : (Top ⊎ A) ≃ Maybe A
⊎-Top-eq = isoToEquiv i
  where
  i : Iso (Top ⊎ A) (Maybe A)
  i .fun (inj-l tt) = nothing
  i .fun (inj-r a) = just a
  i .inv nothing = (inj-l tt)
  i .inv (just a) = (inj-r a)
  i .leftInv (inj-l tt) = refl
  i .leftInv (inj-r a) = refl
  i .rightInv nothing = refl
  i .rightInv (just a) = refl


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
    open EqReasoning

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

⊎-assoc-eq : {ℓa ℓb ℓc : Level} (A : Type ℓa) (B : Type ℓb) (C : Type ℓc) ->
             ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
⊎-assoc-eq A B C = (isoToEquiv i)
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

⊎-assoc : {ℓa ℓb ℓc : Level} (A : Type ℓa) (B : Type ℓb) (C : Type ℓc) ->
          ((A ⊎ B) ⊎ C) == (A ⊎ (B ⊎ C))
⊎-assoc A B C = ua (⊎-assoc-eq A B C)

instance
  ⊎-InfinityMonoid : InfinityMonoid (Type ℓ-zero)
  ⊎-InfinityMonoid = record
    { ε = Bot
    ; _∙_ = _⊎_
    ; ∙-assoc = \{A B C} -> ⊎-assoc A B C
    ; ∙-left-ε = \{A} -> ⊎-Bot A
    ; ∙-right-ε = \{A} -> ⊎-flip >=> ⊎-Bot A
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

LeftRight-Top : (x : (A ⊎ B)) -> (Left x ⊎ Right x) == Top
LeftRight-Top (inj-r _) = ⊎-Bot Top
LeftRight-Top (inj-l _) = ⊎-flip >=> ⊎-Bot Top


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


¬-Bot-eq : {A : Type ℓ} -> ¬ A -> A ≃ Bot
¬-Bot-eq {A = A} ¬A = (isoToEquiv i)
  where
  i : Iso A Bot
  i .fun a = ¬A a
  i .inv ()
  i .rightInv ()
  i .leftInv a = bot-elim (¬A a)

¬-eq : {A : Type ℓ₁} {B : Type ℓ₂} -> A ≃ B -> ¬ A ≃ ¬ B
¬-eq {A = A} {B} eq = (isoToEquiv i)
  where
  i : Iso (¬ A) (¬ B)
  i .fun ¬a b = ¬a (eqInv eq b)
  i .inv ¬b a = ¬b (eqFun eq a)
  i .rightInv _ = isProp¬ _ _
  i .leftInv _ = isProp¬ _ _


¬-Bot : {A : Type ℓ} -> ¬ A -> A == Lift ℓ Bot
¬-Bot {A = A} ¬A = ua (isoToEquiv i)
  where
  i : Iso A (Lift ℓ Bot)
  i .fun a = lift (¬A a)
  i .inv (lift ())
  i .rightInv (lift ())
  i .leftInv a = bot-elim (¬A a)

∥-Top-eq : {A : Type ℓ} -> A -> ∥ A ∥ ≃ Top
∥-Top-eq {A = A} a = (isoToEquiv i)
  where
  i : Iso ∥ A ∥ Top
  i .fun _ = tt
  i .inv _ = ∣ a ∣
  i .rightInv _ = isPropTop _ _
  i .leftInv _ = squash _ _

∥-Top : {A : Type ℓ} -> A -> ∥ A ∥ == Lift ℓ Top
∥-Top {A = A} a = ua (isoToEquiv i)
  where
  i : Iso ∥ A ∥ (Lift ℓ Top)
  i .fun _ = (lift tt)
  i .inv _ = ∣ a ∣
  i .rightInv (lift _) = cong lift (isPropTop _ _)
  i .leftInv _ = squash _ _

∥-Bot-eq : {A : Type ℓ} -> ¬ A -> ∥ A ∥ ≃ Bot
∥-Bot-eq {A = A} ¬A = (isoToEquiv i)
  where
  i : Iso ∥ A ∥ Bot
  i .fun a = unsquash isPropBot (∥-map ¬A a)
  i .inv ()
  i .rightInv ()
  i .leftInv _ = squash _ _

∥-Bot : {A : Type ℓ} -> ¬ A -> ∥ A ∥ == Lift ℓ Bot
∥-Bot {A = A} ¬A = ua (isoToEquiv i)
  where
  i : Iso ∥ A ∥ (Lift ℓ Bot)
  i .fun a = bot-elim (unsquash isPropBot (∥-map ¬A a))
  i .inv (lift ())
  i .rightInv (lift ())
  i .leftInv _ = squash _ _

∥-Prop-eq : {A : Type ℓ} -> isProp A -> ∥ A ∥ ≃ A
∥-Prop-eq {A = A} isPropA = (isoToEquiv i)
  where
  forward : ∥ A ∥ -> A
  forward ∣ a ∣ = a
  forward (squash x y i) = isPropA (forward x) (forward y) i

  i : Iso ∥ A ∥ A
  i .fun = forward
  i .inv a = ∣ a ∣
  i .rightInv _ = isPropA _ _
  i .leftInv _ = squash _ _

∥-Prop : {A : Type ℓ} -> isProp A -> ∥ A ∥ == A
∥-Prop {A = A} isPropA = ua (∥-Prop-eq isPropA)

∥-eq : {A : Type ℓ₁} {B : Type ℓ₂} -> A ≃ B -> ∥ A ∥ ≃ ∥ B ∥
∥-eq {A = A} {B} eq = (isoToEquiv i)
  where
  i : Iso ∥ A ∥ ∥ B ∥
  i .fun = ∥-map (eqFun eq)
  i .inv = ∥-map (eqInv eq)
  i .rightInv _ = squash _ _
  i .leftInv _ = squash _ _


∥-⊎-left-eq : {A : Type ℓ₁} {B : Type ℓ₂}  -> (∥ (∥ A ∥) ⊎ B ∥) ≃ (∥ A ⊎ B ∥)
∥-⊎-left-eq = isoToEquiv (isProp->iso (∥-bind forward) (∥-map backward) squash squash)
  where
  forward : (∥ A ∥) ⊎ B -> (∥ A ⊎ B ∥)
  forward (inj-l a) = ∥-map inj-l a
  forward (inj-r b) = ∣ inj-r b ∣

  backward : (A ⊎ B) -> (∥ A ∥) ⊎ B
  backward (inj-l a) = inj-l ∣ a ∣
  backward (inj-r b) = inj-r b


∥-⊎-right-eq : {A : Type ℓ₁} {B : Type ℓ₂}  -> (∥ A ⊎ (∥ B ∥) ∥) ≃ (∥ A ⊎ B ∥)
∥-⊎-right-eq = ∥-eq ⊎-flip-eq >eq> ∥-⊎-left-eq >eq> ∥-eq ⊎-flip-eq


Σ-distrib-⊎ : {A : Type ℓ₁} {B : A -> Type ℓ₂} {C : A -> Type ℓ₃} ->
              (Σ[ a ∈ A ] (B a ⊎ C a)) ≃ (Σ A B ⊎ Σ A C)
Σ-distrib-⊎ {A = A} {B} {C} = isoToEquiv i
  where
  i : Iso (Σ[ a ∈ A ] (B a ⊎ C a)) (Σ A B ⊎ Σ A C)
  i .fun (a , (inj-l b)) = (inj-l (a , b))
  i .fun (a , (inj-r c)) = (inj-r (a , c))
  i .inv (inj-l (a , b)) = (a , (inj-l b))
  i .inv (inj-r (a , c)) = (a , (inj-r c))
  i .rightInv (inj-l (_ , _)) = refl
  i .rightInv (inj-r (_ , _)) = refl
  i .leftInv (_ , (inj-l _)) = refl
  i .leftInv (_ , (inj-r _)) = refl

Maybe-eq : (A ≃ B) -> Maybe A ≃ Maybe B
Maybe-eq {A = A} {B = B} eq = isoToEquiv i
  where
  i : Iso (Maybe A) (Maybe B)
  i .fun nothing = nothing
  i .fun (just a) = just (eqFun eq a)
  i .inv nothing = nothing
  i .inv (just b) = just (eqInv eq b)
  i .rightInv nothing = refl
  i .rightInv (just b) = cong just (eqSec eq b)
  i .leftInv nothing = refl
  i .leftInv (just a) = cong just (eqRet eq a)

⊎-left-Maybe-eq : (Maybe A ⊎ B) ≃ Maybe (A ⊎ B)
⊎-left-Maybe-eq = isoToEquiv (iso f b fb bf)
  where
  f : Maybe A ⊎ B -> Maybe (A ⊎ B)
  f (inj-l nothing)  = nothing
  f (inj-l (just a)) = (just (inj-l a))
  f (inj-r b)        = (just (inj-r b))
  b : Maybe (A ⊎ B) -> Maybe A ⊎ B
  b nothing          = (inj-l nothing)
  b (just (inj-l a)) = (inj-l (just a))
  b (just (inj-r b)) = (inj-r b)
  fb : ∀ x -> f (b x) == x
  fb nothing          = refl
  fb (just (inj-l a)) = refl
  fb (just (inj-r b)) = refl
  bf : ∀ x -> b (f x) == x
  bf (inj-l nothing)  = refl
  bf (inj-l (just a)) = refl
  bf (inj-r b)        = refl

⊎-right-Maybe-eq : (A ⊎ Maybe B) ≃ Maybe (A ⊎ B)
⊎-right-Maybe-eq = ⊎-flip-eq >eq> ⊎-left-Maybe-eq >eq> Maybe-eq ⊎-flip-eq

Σ-Bot-eq : {ℓ : Level} {A : Bot -> Type ℓ} ->
           Σ Bot A ≃ Bot
Σ-Bot-eq {A = A} = isoToEquiv i
  where
  i : Iso (Σ Bot A) Bot
  i .fun (b , _)   = bot-elim b
  i .inv b         = bot-elim b
  i .rightInv b      = bot-elim b
  i .leftInv (b , _) = bot-elim b

Σ-Maybe-eq : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Maybe A -> Type ℓ₂} ->
             Σ (Maybe A) B ≃ (B nothing ⊎ Σ A (B ∘ just))
Σ-Maybe-eq {A = A} {B = B} = isoToEquiv i
  where
  i : Iso (Σ (Maybe A) B) (B nothing ⊎ Σ A (B ∘ just))
  i .fun (nothing , b)   = inj-l b
  i .fun (just a , b)    = inj-r (a , b)
  i .inv (inj-l b)       = nothing , b
  i .inv (inj-r (a , b)) = just a , b
  i .rightInv (inj-l _) = refl
  i .rightInv (inj-r _) = refl
  i .leftInv (nothing , b) = refl
  i .leftInv (just a , b)  = refl

Contr-Top-eq : {A : Type ℓ} -> (isContr A) -> A ≃ Top
Contr-Top-eq {A = A} isContrA = isoToEquiv i
  where
  i : Iso A Top
  i .fun _ = tt
  i .inv _ = isContrA .fst
  i .rightInv _ = refl
  i .leftInv y = isContrA .snd y

Σ-isContr-eq : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A -> Type ℓ₂} ->
               ((a : A) -> isContr (B a)) -> A ≃ Σ A B
Σ-isContr-eq {A = A} {B} f = isoToEquiv i
  where
  i : Iso A (Σ A B)
  i .fun a       = a , fst (f a)
  i .inv (a , b) = a
  i .leftInv _ = refl
  i .rightInv (a , b) = ΣProp-path (\{a} -> (isContr->isProp (f a))) refl

Σ-swap-eq : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {C : A -> B -> Type ℓ₃} ->
            (Σ[ a ∈ A ] Σ[ b ∈ B ] (C a b)) ≃ (Σ[ b ∈ B ] Σ[ a ∈ A ] (C a b))
Σ-swap-eq {A = A} {B} {C} = isoToEquiv i
  where
  i : Iso (Σ[ a ∈ A ] Σ[ b ∈ B ] (C a b)) (Σ[ b ∈ B ] Σ[ a ∈ A ] (C a b))
  i .fun (a , b , c) = (b , a , c)
  i .inv (b , a , c) = (a , b , c)
  i .rightInv _ = refl
  i .leftInv _ = refl


reindexΠ : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : Type ℓ₂}
           (eq : B ≃ A) (C : A -> Type ℓ₃) -> ((a : A) -> C a) ≃ ((b : B) -> (C (eqFun eq b)))
reindexΠ {A = A} {B} eq C = isoToEquiv i
  where
  i : Iso ((a : A) -> C a) ((b : B) -> (C (eqFun eq b)))
  i .fun f b = f (eqFun eq b)
  i .inv g a = substᵉ C (eqSec eq a) (g (eqInv eq a))
  i .leftInv f = funExt ans
    where
    ans : (a : A) -> substᵉ C (eqSec eq a) (f (eqFun eq (eqInv eq a))) == f a
    ans a = transP-sym p1 p2
      where
      p1 : PathP (\i -> C (eqSec eq a (~ i))) (substᵉ C (eqSec eq a) (f (eqFun eq (eqInv eq a))))
                                              (f (eqFun eq (eqInv eq a)))
      p1 = symP (subst-filler C (eqSec eq a) (f (eqFun eq (eqInv eq a))))

      p2 : PathP (\i -> C (eqSec eq a i)) (f (eqFun eq (eqInv eq a))) (f a)
      p2 i = f (eqSec eq a i)


  i .rightInv g = funExt ans
    where
    ans : (b : B) -> substᵉ C (eqSec eq (eqFun eq b)) (g (eqInv eq (eqFun eq b))) == g b
    ans b = transP-sym p1 p2
      where
      p1 : PathP (\i -> C (eqSec eq (eqFun eq b) (~ i)))
                 (substᵉ C (eqSec eq (eqFun eq b)) (g (eqInv eq (eqFun eq b))))
                 (g (eqInv eq (eqFun eq b)))
      p1 = symP (subst-filler C (eqSec eq (eqFun eq b)) (g (eqInv eq (eqFun eq b))))

      pp : (cong (eqFun eq) (eqRet eq b)) == (eqSec eq (eqFun eq b))
      pp = rotate-square-ABCR->CARB (eqComm eq b)

      p2 : PathP (\i -> C (eqSec eq (eqFun eq b) i))
                 (g (eqInv eq (eqFun eq b)))
                 (g b)
      p2 = subst (\P -> PathP (\i -> C (P i)) (g (eqInv eq (eqFun eq b))) (g b))
                 pp (\i -> g (eqRet eq b i))
