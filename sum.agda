{-# OPTIONS --cubical --safe --exact-split #-}

module sum where

open import base
open import equality
open import equivalence
open import functions
open import hlevel.base
open import isomorphism
open import relation

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B C D : Type ℓ

open Iso

⊎-map : (A -> C) -> (B -> D) -> (A ⊎ B) -> (C ⊎ D)
⊎-map f g (inj-l a) = inj-l (f a)
⊎-map f g (inj-r b) = inj-r (g b)

⊎-map-left : (f : A -> C) -> (A ⊎ B) -> (C ⊎ B)
⊎-map-left f = ⊎-map f (\x -> x)

⊎-map-right : (g : B -> D) -> (A ⊎ B) -> (A ⊎ D)
⊎-map-right g = ⊎-map (\x -> x) g

⊎-iso : ∀ {ℓ} {A B C D : Type ℓ} -> Iso A C -> Iso B D -> Iso (A ⊎ B) (C ⊎ D)
(⊎-iso f g) .fun = ⊎-map (f .fun) (g .fun)
(⊎-iso f g) .inv = ⊎-map (f .inv) (g .inv)
(⊎-iso f g) .rightInv (inj-l c) = cong inj-l (f .rightInv c)
(⊎-iso f g) .rightInv (inj-r d) = cong inj-r (g .rightInv d)
(⊎-iso f g) .leftInv  (inj-l a) = cong inj-l (f .leftInv a)
(⊎-iso f g) .leftInv  (inj-r b) = cong inj-r (g .leftInv b)

Left : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} -> A ⊎ B -> Type₀
Left (inj-l _) = Top
Left (inj-r _) = Bot

Right : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} -> A ⊎ B -> Type₀
Right (inj-l _) = Bot
Right (inj-r _) = Top

proj-l : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} -> (s : A ⊎ B) -> Left s -> A
proj-l (inj-l a) _ = a
proj-l (inj-r _) ()

proj-r : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} -> (s : A ⊎ B) -> Right s -> B
proj-r (inj-r b) _ = b
proj-r (inj-l _) ()

inj-l!=inj-r : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {a : A} {b : B}
               -> ¬(Path (A ⊎ B) (inj-l a) (inj-r b))
inj-l!=inj-r p = transport (\i -> Left (p i)) tt

module _ {A : Type ℓ₁} {B : Type ℓ₂} where
  ⊎Cover : (A ⊎ B) -> (A ⊎ B) -> Type (ℓ-max ℓ₁ ℓ₂)
  ⊎Cover (inj-l a1) (inj-l a2) = Lift (ℓ-max ℓ₁ ℓ₂) (a1 == a2)
  ⊎Cover (inj-l _)  (inj-r _) = Lift (ℓ-max ℓ₁ ℓ₂) Bot
  ⊎Cover (inj-r _)  (inj-l _) = Lift (ℓ-max ℓ₁ ℓ₂) Bot
  ⊎Cover (inj-r b1) (inj-r b2) = Lift (ℓ-max ℓ₁ ℓ₂) (b1 == b2)

  private
    reflCode : (s : (A ⊎ B)) -> ⊎Cover s s
    reflCode (inj-l s) = lift refl
    reflCode (inj-r s) = lift refl

    encode : (s1 s2 : (A ⊎ B)) -> s1 == s2 -> ⊎Cover s1 s2
    encode s1 _ = J (\ s2 _ -> ⊎Cover s1 s2) (reflCode s1)

    encodeRefl : (s : (A ⊎ B)) -> encode s s refl == reflCode s
    encodeRefl s = JRefl (\ s2 _ -> ⊎Cover s s2) (reflCode s)

    decode : (s1 s2 : (A ⊎ B)) -> ⊎Cover s1 s2 -> s1 == s2
    decode (inj-l _) (inj-l _) (lift p) = cong inj-l p
    decode (inj-r _) (inj-r _) (lift p) = cong inj-r p

    decodeRefl : (s : (A ⊎ B)) -> decode s s (reflCode s) == refl
    decodeRefl (inj-l _) = refl
    decodeRefl (inj-r _) = refl

    decodeEncode : (s1 s2 : (A ⊎ B)) -> (p : s1 == s2) -> decode s1 s2 (encode s1 s2 p) == p
    decodeEncode s1 _ =
      J (\ s2 p -> decode s1 s2 (encode s1 s2 p) ≡ p)
        (cong (decode s1 s1) (encodeRefl s1) >=> decodeRefl s1)

    encodeDecode : (s1 s2 : (A ⊎ B)) -> (c : ⊎Cover s1 s2) → encode s1 s2 (decode s1 s2 c) ≡ c
    encodeDecode (inj-l a1) (inj-l _) (lift a-p) =
      J (\ a2 p -> encode (inj-l a1) (inj-l a2) (cong inj-l p) == lift p) (encodeRefl (inj-l a1)) a-p
    encodeDecode (inj-r b1) (inj-r _) (lift b-p) =
      J (\ b2 p -> encode (inj-r b1) (inj-r b2) (cong inj-r p) == lift p) (encodeRefl (inj-r b1)) b-p

  ⊎-cover==path : (s1 s2 : (A ⊎ B)) -> ⊎Cover s1 s2 == (s1 == s2)
  ⊎-cover==path s1 s2 = ua (isoToEquiv (record
    { fun = decode s1 s2
    ; inv = encode s1 s2
    ; rightInv = decodeEncode s1 s2
    ; leftInv = encodeDecode s1 s2
    }))

inj-l-injective : {a1 a2 : A} -> Path (A ⊎ B) (inj-l a1) (inj-l a2) -> a1 == a2
inj-l-injective {a1 = a1} {a2 = a2} p =
  Lift.lower (transport (sym (⊎-cover==path (inj-l a1) (inj-l a2))) p)
inj-r-injective : {b1 b2 : B} -> Path (A ⊎ B) (inj-r b1) (inj-r b2) -> b1 == b2
inj-r-injective {b1 = b1} {b2 = b2} p =
  Lift.lower (transport (sym (⊎-cover==path (inj-r b1) (inj-r b2))) p)





Discrete⊎ : Discrete A -> Discrete B -> Discrete (A ⊎ B)
Discrete⊎ da db (inj-l a1) (inj-l a2) with (da a1 a2)
... | yes a-path = yes (cong inj-l a-path)
... | no ¬a-path = no (¬a-path ∘ f)
  where
  f : (inj-l a1) == (inj-l a2) -> a1 == a2
  f p i = proj-l (p i) (Left-path i)
    where
    Left-path : PathP (\i -> Left (p i)) tt tt
    Left-path i = transport-filler (\i -> Left (p i)) tt i
Discrete⊎ da db (inj-l a1) (inj-r b2) = no inj-l!=inj-r
Discrete⊎ da db (inj-r b1) (inj-l a2) = no (inj-l!=inj-r ∘ sym)
Discrete⊎ da db (inj-r b1) (inj-r b2) with (db b1 b2)
... | yes b-path = yes (cong inj-r b-path)
... | no ¬b-path = no (¬b-path ∘ f)
  where
  f : (inj-r b1) == (inj-r b2) -> b1 == b2
  f p i = proj-r (p i) (Right-path i)
    where
    Right-path : PathP (\i -> Right (p i)) tt tt
    Right-path i = transport-filler (\i -> Right (p i)) tt i

-- Properties about the type
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
