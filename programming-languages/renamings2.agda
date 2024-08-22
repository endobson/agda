{-# OPTIONS --cubical --safe --exact-split #-}

module programming-languages.renamings2 where

open import base
open import container.finmap.v3
open import cubical
open import discrete
open import dominance
open import equality-path
open import equivalence
open import fin
open import finset
open import functions
open import hlevel
open import isomorphism
open import nat
open import partial-map
open import relation
open import truncation
open import type-algebra
open import univalence

private
  variable
    ℓ : Level
    A : Type ℓ

  Atom : Type₀
  Atom = Nat

  isSet-Atom : isSet Atom
  isSet-Atom = isSetNat

  DiscreteAtom : Discrete Atom
  DiscreteAtom = decide-nat

private
  DDec : Dominance ℓ-zero
  DDec = Dominance-Dec

isRenaming : Pred (FinMap Atom Atom) ℓ-one
isRenaming = isInvertibleFinMap

Renaming : Type₁
Renaming = Σ (FinMap Atom Atom) isRenaming

InverseRenamings : Rel Renaming ℓ-zero
InverseRenamings (m1 , _) (m2 , _) = InverseFinMaps m1 m2

invert-renaming' : ∀ r -> isContr (Σ Renaming (InverseRenamings r))
invert-renaming' r@((m , fin) , inv) = ans , center-ans
  where
  unique-m' : isContr (Σ (PartialMap DDec Atom Atom) (InversePartialMaps DDec m))
  unique-m' = setPartialMap-unique-inverse DDec m inv isSet-Atom
  m' = fst (fst unique-m')
  inverse-m' : InversePartialMaps DDec m m'
  inverse-m' = snd (fst unique-m')
  invertible-m' : isInvertibleMap DDec m'
  invertible-m' = ∣ m , Symmetric-InversePartialMaps DDec m m' inverse-m' ∣

  fin' : isFinMap m'
  fin' = inverse-isFinMap m m' inverse-m' fin

  ans = (((m' , fin') , invertible-m') , inverse-m')

  center-ans : ∀ (r' : (Σ Renaming (InverseRenamings r))) -> ans == r'
  center-ans (((m2 , fin2) , invertible2) , inverse2) i =
    ((m-path i , fin-path i) , invertible-path i) , snd (path i)
    where
    path : (m' , inverse-m') == (m2 , inverse2)
    path = snd unique-m' (m2 , inverse2)
    m-path : m' == m2
    m-path = cong fst path
    fin-path : PathP (\i -> isFinREL ⟨ m-path i ⟩) fin' fin2
    fin-path = isProp->PathP (\_ -> isProp-isFinSetΣ)
    invertible-path : PathP (\i -> isInvertibleMap DDec (m-path i)) invertible-m' invertible2
    invertible-path = isProp->PathP (\_ -> squash)


invert-renaming : Renaming -> Renaming
invert-renaming r = fst (fst (invert-renaming' r))

empty-renaming : Renaming
empty-renaming = empty-finmap , ∣ fst (empty-finmap) , (\_ _ -> idEquiv (Lift ℓ-zero Bot)) ∣

apply-renaming/Atom : Renaming -> Atom -> Atom
apply-renaming/Atom (((m , l) , _) , _) a with (l a)
... | (_ , (yes (a2 , _))) = a2
... | (_ , (no  _))        = a


-- Overt : {ℓ : Level} -> Dominance ℓ -> Type ℓ -> Type (ℓ-suc ℓ)
-- Overt {ℓ} (D , _) T = ∀ (F : T -> Type ℓ) -> ((t : T) -> D (F t)) -> D (∃ T F)
--
--   (invert-renaming'P : ∀ r -> isProp (Σ Renaming (InverseRenamings r)))
--   (Overt-Dec-FinΣ : ∀ {ℓ : Level} (I : FinSetΣ ℓ) -> Overt Dominance-Dec ⟨ I ⟩)




  -- invert-renaming' : ∀ r -> isContr (Σ Renaming (InverseRenamings r))
  -- invert-renaming' r@(((R1 , D1) , F1) , Rename1) =
  --   ((((R2 , D2) , F2) , ? ) , inverse) , invert-renaming'P r _
  --
  --
  --   where
  --   R2 : Rel Atom ℓ-zero
  --   R2 y x = R1 x y
  --
  --   D2 : ∀ y -> ⟨ Dominance-Dec ⟩ (Σ Atom (R2 y))
  --   D2 y = subst ⟨ DDec ⟩ eq use-overt
  --     where

  --     use-overt : ⟨ DDec ⟩ (∃[ t ∈ TotalSpace R1 ] (fst (snd t) == y))
  --     use-overt = Overt-Dec-FinΣ (_ , F1) _ handle
  --       where
  --       handle : (t : TotalSpace R1) -> ⟨ DDec ⟩ (fst (snd t) == y)
  --       handle (x , y' , r) = isSetNat _ _ , DiscreteAtom _ _

  --     eq1 : (Σ[ t ∈ TotalSpace R1 ] (fst (snd t) == y)) ==
  --           (Σ Atom (R2 y))
  --     eq1 = ua (isoToEquiv (iso f g fg gf))
  --       where
  --       f : (Σ[ t ∈ TotalSpace R1 ] (fst (snd t) == y)) ->
  --           (Σ Atom (R2 y))
  --       f ((x , y' , r) , p) = x , substᵉ (R1 x) p r
  --       g : (Σ Atom (R2 y)) ->
  --           (Σ[ t ∈ TotalSpace R1 ] (fst (snd t) == y))
  --       g (x , r) = (x , y , r) , refl
  --       fg : ∀ t -> f (g t) == t
  --       fg t = transportRefl t
  --       gf : ∀ t -> g (f t) == t
  --       gf ((x , y' , r) , p) i = (x , p (~ i) , subst-filler (R1 x) p r (~ i)) , (\j -> p (j ∨ ~ i))

  --     eq : (∃[ t ∈ TotalSpace R1 ] (fst (snd t) == y)) ==
  --          (Σ Atom (R2 y))
  --     eq =  -- cong ∥_∥ eq1 >=> ∥-Prop (Rename1 y)

  --
  --   F2 : isFinREL R2
  --   F2 = fst F1 , ∥-map (Σ-swap-eq >eq>_) (snd F1)

  --
  --   --Rename2 : isRenamingRel R2
  --   --Rename2 x = proj₁ (D1 x)
  --
  --   inverse : InverseRelations R1 R2
  --   inverse x y = idEquiv _

