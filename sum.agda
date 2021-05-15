{-# OPTIONS --cubical --safe --exact-split #-}

module sum where

open import base
open import cubical
open import equality
open import equivalence
open import functions
open import hlevel.base
open import isomorphism
open import univalence
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

⊎-iso : Iso A C -> Iso B D -> Iso (A ⊎ B) (C ⊎ D)
(⊎-iso f g) .fun = ⊎-map (f .fun) (g .fun)
(⊎-iso f g) .inv = ⊎-map (f .inv) (g .inv)
(⊎-iso f g) .rightInv (inj-l c) = cong inj-l (f .rightInv c)
(⊎-iso f g) .rightInv (inj-r d) = cong inj-r (g .rightInv d)
(⊎-iso f g) .leftInv  (inj-l a) = cong inj-l (f .leftInv a)
(⊎-iso f g) .leftInv  (inj-r b) = cong inj-r (g .leftInv b)

⊎-equiv : A ≃ C -> B ≃ D -> (A ⊎ B) ≃ (C ⊎ D)
⊎-equiv f g = isoToEquiv (⊎-iso (equivToIso f) (equivToIso g))

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

⊎-swap : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} -> A ⊎ B -> B ⊎ A
⊎-swap (inj-l a) = (inj-r a)
⊎-swap (inj-r b) = (inj-l b)

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
      J (\ s2 p -> decode s1 s2 (encode s1 s2 p) == p)
        (cong (decode s1 s1) (encodeRefl s1) >=> decodeRefl s1)

    encodeDecode : (s1 s2 : (A ⊎ B)) -> (c : ⊎Cover s1 s2) → encode s1 s2 (decode s1 s2 c) == c
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
