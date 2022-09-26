{-# OPTIONS --cubical --safe --exact-split #-}

module container.finmap.v3 where

open import base
open import cubical
open import dominance
open import equality-path
open import equivalence
open import fin
open import finset
open import functions
open import functions.embedding
open import funext
open import hlevel
open import isomorphism
open import nat
open import partial-map
open import relation
open import sigma.base
open import sigma
open import truncation
open import type-algebra
open import univalence

private
  variable
    ℓ ℓA ℓB ℓC ℓK ℓV : Level
    A B C K V : Type ℓ

module _ {ℓ : Level} {K V : Type ℓ} where
  TotalSpace : REL K V ℓ -> Type ℓ
  TotalSpace R = (Σ[ k ∈ K ] Σ[ v ∈ V ] (R k v))

  isFinREL : Pred (REL K V ℓ) ℓ
  isFinREL R = isFinSetΣ (TotalSpace R)
  
private
  DecPartialMap : {ℓ : Level} -> (K V : Type ℓ) -> Type (ℓ-suc ℓ)
  DecPartialMap K V = (PartialMap Dominance-Dec K V)

isFinMap : {ℓ : Level} -> {K V : Type ℓ} -> Pred (DecPartialMap K V) ℓ
isFinMap (R , _)= isFinREL R

FinMap : {ℓ : Level} -> (K V : Type ℓ) -> Type (ℓ-suc ℓ)
FinMap K V = Σ (DecPartialMap K V) isFinMap 

private
  module _ {ℓ : Level} {K V : Type ℓ} where
    lift-PMap-path : {m1 m2 : FinMap K V} -> fst m1 == fst m2 -> m1 == m2
    lift-PMap-path p = ΣProp-path isProp-isFinSetΣ p

    lift-Rel-path : {m1 m2 : FinMap K V} -> fst (fst m1) == fst (fst m2) -> m1 == m2
    lift-Rel-path p =
      lift-PMap-path (ΣProp-path (isPropΠ (\x -> isDominance.isProp-D (snd Dominance-Dec) _)) p)


module _ {ℓ : Level} {K V : Type ℓ} where
  finmap-size : FinMap K V -> Nat
  finmap-size (PM , fin) = fst fin

  empty-finmap : FinMap K V
  empty-finmap = (R , \_ -> DVBot) , isFin
    where
    Botℓ = Lift ℓ Bot
    R : K -> V -> Type ℓ
    R = (\_ _ -> Botℓ)

    D : Type ℓ -> Type ℓ 
    D X = isProp X × Dec X

    DVBot : D (Σ V (\_ -> Botℓ))
    DVBot = (\ (_ , (lift b)) -> bot-elim b) , no (\ (_ , (lift b)) ->  b)

    isFin : isFinREL R
    isFin = 0 , ∣ eq ∣
      where
      eq : TotalSpace R ≃ Fin 0
      eq = isoToEquiv (iso f b fb bf)
        where
        f : TotalSpace R -> Fin 0
        f (_ , _ , (lift b)) = bot-elim b
        b : Fin 0 -> TotalSpace R
        b z = bot-elim (¬fin-zero z)
        fb : ∀ z -> f (b z) == z
        fb z = bot-elim (¬fin-zero z)
        bf : ∀ t -> b (f t) == t
        bf (_ , _ , (lift b)) = bot-elim b

  private
    empty-finmap-size : finmap-size empty-finmap == 0
    empty-finmap-size = refl

  isProp-empty-finmap : isProp (Σ[ m ∈ FinMap K V ] (finmap-size m == 0))
  isProp-empty-finmap (((r1 , v1) , f1) , s1) (((r2 , v2) , f2) , s2) = 
    ΣProp-path (isSetNat _ _) (lift-Rel-path r-path)
    where
    f1' : ∥ TotalSpace r1 ≃ Fin 0 ∥
    f1' = subst (\ s -> ∥ TotalSpace r1 ≃ Fin s ∥) s1 (snd f1)
    f2' : ∥ TotalSpace r2 ≃ Fin 0 ∥
    f2' = subst (\ s -> ∥ TotalSpace r2 ≃ Fin s ∥) s2 (snd f2)

    r1->Bot : ∀ {x y} -> r1 x y -> Bot 
    r1->Bot r = unsquash isPropBot (∥-map (\eq -> ¬fin-zero (eqFun eq (_ , _ , r))) f1')
    r2->Bot : ∀ {x y} -> r2 x y -> Bot 
    r2->Bot r = unsquash isPropBot (∥-map (\eq -> ¬fin-zero (eqFun eq (_ , _ , r))) f2')

    r-eq : ∀ x y -> r1 x y ≃ r2 x y
    r-eq x y = ¬-Bot-eq r1->Bot >eq> (equiv⁻¹ (¬-Bot-eq r2->Bot))

    r-path : r1 == r2
    r-path = funExt2 (\x y -> ua (r-eq x y))

  isContr-empty-finmap : isContr (Σ[ m ∈ FinMap K V ] (finmap-size m == 0))
  isContr-empty-finmap = (empty-finmap , refl) , isProp-empty-finmap _

module _ {ℓ : Level} {K V : Type ℓ} where
  MapDisjointUnion : (A B C : DecPartialMap K V) -> Type ℓ
  MapDisjointUnion (AR , AD) (BR , BD) (CR , CD) = 
    ∀ x y -> (AR x y ⊎ BR x y) ≃ CR x y
  FinMapDisjointUnion : (A B C : FinMap K V) -> Type ℓ
  FinMapDisjointUnion (AM , _) (BM , _) (CM , _) = MapDisjointUnion AM BM CM
  

module _ {ℓ : Level} {K V : Type ℓ} where
  isInvertibleFinMap : Pred (FinMap K V) (ℓ-suc ℓ)
  isInvertibleFinMap (m , _) = isInvertibleMap Dominance-Dec m

module _ {ℓ : Level} {A B : Type ℓ} where
  InverseFinMaps : REL (FinMap A B) (FinMap B A) ℓ
  InverseFinMaps (m1 , _) (m2 , _) = InversePartialMaps Dominance-Dec m1 m2

inverse-isFinMap : ∀ {ℓ : Level} {X Y : Type ℓ}
                     (m1 : PartialMap Dominance-Dec X Y) -> 
                     (m2 : PartialMap Dominance-Dec Y X) ->
                     InversePartialMaps Dominance-Dec m1 m2 ->
                     isFinMap m1 -> isFinMap m2
inverse-isFinMap (R1 , m1) (R2 , m2) inv (n , ∣eq∣) = n , ∥-map handle ∣eq∣
  where
  same-space : (TotalSpace R1) ≃ (TotalSpace R2)
  same-space = Σ-swap-eq >eq> (existential-eq (\ y -> existential-eq (\ x -> inv x y)))

  handle : (TotalSpace R1) ≃ Fin n -> (TotalSpace R2) ≃ Fin n 
  handle eq = equiv⁻¹ same-space >eq> eq

