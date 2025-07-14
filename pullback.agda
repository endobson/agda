{-# OPTIONS --cubical --safe --exact-split #-}

module pullback where

open import base
open import functions
open import equivalence
open import equality-path
open import funext
open import pushout.flattening
open import hlevel
open import sigma.base
open import isomorphism
open import univalence

module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (f : A -> C) (g : B -> C) where
  Cone : {ℓD : Level} (D : Type ℓD) -> Type (ℓ-max* 4 ℓA ℓB ℓC ℓD)
  Cone D = 
    Σ[ p₁ ∈ (D -> A) ] Σ[ p₂ ∈ (D -> B) ] ((f ∘ p₁) == (g ∘ p₂))


module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (f : A -> C) (g : B -> C) where
  Pullback : Type (ℓ-max* 3 ℓA ℓB ℓC)
  Pullback = Σ[ a ∈ A ] (Σ[ b ∈ B ] (f a == g b))

module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         {f : A -> C} {g : B -> C} where
  pullback-projˡ : Pullback f g -> A
  pullback-projˡ (a , b , s) = a
  pullback-projʳ : Pullback f g -> B
  pullback-projʳ (a , b , s) = b
  pullback-htpy : (p : Pullback f g) -> f (pullback-projˡ p) == g (pullback-projʳ p)
  pullback-htpy (a , b , s) = s

  gap : {ℓD : Level} {D : Type ℓD} -> Cone f g D -> D -> Pullback f g
  gap (p₁ , p₂ , s) d = (p₁ d , p₂ d , \i -> s i d)

  isPullbackCone : {ℓD : Level} {D : Type ℓD} -> Cone f g D -> Type (ℓ-max* 4 ℓA ℓB ℓC ℓD)
  isPullbackCone cone = isEquiv (gap cone)

  isProp-ΣisPullbackCone : (ℓD : Level)-> isProp (Σ[ (_ , c) ∈ Σ (Type ℓD) (Cone f g) ] (isPullbackCone c))
  isProp-ΣisPullbackCone ℓD ((D₁ , c₁@(p₁ , q₁ , s₁)) , P₁) ((D₂ , c₂@(p₂ , q₂ , s₂)) , P₂) = 
    ΣProp-path isProp-isEquiv (\i -> pD i , path-c i)
    where
    e₁ : Iso D₁ (Pullback f g)
    e₁ = equivToIso (_ , P₁)
    e₂ : Iso (Pullback f g) D₂
    e₂ = iso⁻¹ (equivToIso (_ , P₂))

    e : Iso D₁ D₂
    e = e₁ >iso> e₂

    path-p : ∀ x -> p₂ (Iso.fun e x) == p₁ x
    path-p x = cong (\ (p , q , s) -> p) (Iso.leftInv e₂ (Iso.fun e₁ x))
    path-q : ∀ x -> q₂ (Iso.fun e x) == q₁ x
    path-q x = cong (\ (p , q , s) -> q) (Iso.leftInv e₂ (Iso.fun e₁ x))
    path-s : ∀ x i -> s₂ i (Iso.fun e x) == s₁ i x
    path-s x i = cong (\ (p , q , s) -> s i) (Iso.leftInv e₂ (Iso.fun e₁ x))

    pD : D₁ == D₂
    pD = isoToPath e

    path-c1 : Path (Cone f g D₁)
              c₁
              (p₂ ∘ Iso.fun e , q₂ ∘ Iso.fun e , (\i x -> s₂ i (Iso.fun e x))) 
    path-c1 i = funExt path-p (~ i) , funExt path-q (~ i) , \j x -> path-s x j (~ i)

    path-c2 : PathP (\i -> Cone f g (pD i))
              (p₂ ∘ Iso.fun e , q₂ ∘ Iso.fun e , (\i x -> s₂ i (Iso.fun e x))) 
              c₂
    path-c2 i = path-p2 i , path-q2 i , path-s2 i
      where
      path-p2 : PathP (\i -> pD i -> A) (p₂ ∘ Iso.fun e) p₂
      path-p2 = (\i x -> p₂ (ua-unglue (isoToEquiv e) i x))
      path-q2 : PathP (\i -> pD i -> B) (q₂ ∘ Iso.fun e) q₂
      path-q2 = (\i x -> q₂ (ua-unglue (isoToEquiv e) i x))
      path-s2 : PathP (\i -> Path (pD i -> C) (f ∘ (path-p2 i)) (g ∘ (path-q2 i))) (\i x -> s₂ i (Iso.fun e x)) s₂
      path-s2 = (\i j x -> s₂ j (ua-unglue (isoToEquiv e) i x))

    path-c : PathP (\i -> Cone f g (pD i)) c₁ c₂
    path-c = transP-right path-c1 path-c2
             


    


module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (f : A -> C) (g : B -> C) where
  cone-map : {ℓD ℓE : Level} {D : Type ℓD} -> Cone f g D -> 
             {E : Type ℓE} -> (E -> D) -> Cone f g E
  cone-map (p₁ , p₂ , s) h = 
    (p₁ ∘ h) , (p₂ ∘ h) , (\i -> s i ∘ h)


module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (f : A -> C) (g : B -> C) where
  isPullbackConeLarge : {ℓD : Level} {D : Type ℓD} -> Cone f g D -> Agda.Primitive.Setω
  isPullbackConeLarge {D = D} c = 
    {ℓE : Level} -> (E : Type ℓE) -> isEquiv (cone-map f g c {E})

module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (f : A -> C) (g : B -> C) where
  standard-PullbackCone : Cone f g (Pullback f g)
  standard-PullbackCone = pullback-projˡ , pullback-projʳ , funExt pullback-htpy

  isPullbackConeLarge-standard : isPullbackConeLarge f g standard-PullbackCone
  isPullbackConeLarge-standard E =
    isoToIsEquiv (iso _ gap (\_ -> refl) (\_ -> refl))

  isPullbackCone-standard : isPullbackCone {f = f} {g} standard-PullbackCone
  isPullbackCone-standard = idIsEquiv _


