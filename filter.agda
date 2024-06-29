{-# OPTIONS --cubical --safe --exact-split #-}

module filter where

open import base
open import subset
open import functions
open import equality
open import hlevel
open import relation
open import truncation

Subtype-∩ : {ℓD ℓS₁ ℓS₂ : Level} -> {D : Type ℓD} ->
  Subtype D ℓS₁ -> Subtype D ℓS₂ -> Subtype D (ℓ-max ℓS₁ ℓS₂)
Subtype-∩ S₁ S₂ d = (⟨ S₁ d ⟩ × ⟨ S₂ d ⟩) , isProp× (snd (S₁ d)) (snd (S₂ d))

Subtype-∪ : {ℓD ℓS₁ ℓS₂ : Level} -> {D : Type ℓD} ->
  Subtype D ℓS₁ -> Subtype D ℓS₂ -> Subtype D (ℓ-max ℓS₁ ℓS₂)
Subtype-∪ S₁ S₂ d = ∥ ⟨ S₁ d ⟩ ⊎ ⟨ S₂ d ⟩ ∥ , squash



record Filter {ℓD : Level} (D : Type ℓD) (ℓS ℓF : Level) : Type (ℓ-max* 3 ℓD (ℓ-suc ℓS) (ℓ-suc ℓF)) where
  field
    P : Pred (Subtype D ℓS) ℓF
    isProp-P : isPropValuedPred P
    inhabited : ∃ (Subtype D ℓS) P
    upward-closed : ∀ S1 S2 -> (∀ d -> ⟨ S1 d ⟩ -> ⟨ S2 d ⟩) -> P S1 -> P S2
    downward-directed : ∀ S1 S2 -> P S1 -> P S2 ->
      ∃[ S3 ∈ (Subtype D ℓS) ]
        (P S3 × (∀ d -> ⟨ S3 d ⟩ -> ⟨ S1 d ⟩) × (∀ d -> ⟨ S3 d ⟩ -> ⟨ S2 d ⟩))

  ∈ : Type (ℓ-max* 3 ℓD (ℓ-suc ℓS) ℓF)
  ∈ = Σ (Subtype D ℓS) P

module _ {ℓD : Level} {D : Type ℓD} where
  record ConvergesTo {ℓS ℓF : Level} (f : Filter D ℓS ℓF) (d : D) :
                     Type (ℓ-max* 4 ℓD (ℓ-suc ℓS) ℓF ℓ-one) where
    no-eta-equality
    field
      contains : ∀ S -> ⟨ S d ⟩ -> Filter.P f S

  record isLimit {ℓS ℓF : Level} (f : Filter D ℓS ℓF) (d : D) :
                 Type (ℓ-max* 4 ℓD (ℓ-suc ℓS) ℓF ℓ-one) where
    no-eta-equality
    field
      converges : ConvergesTo f d
      unique : isProp (Σ D (ConvergesTo f))


  record isPrime {ℓS ℓF : Level} (F : Filter D ℓS ℓF) :
                 Type (ℓ-max* 4 ℓD (ℓ-suc ℓS) ℓF ℓ-one) where
    no-eta-equality
    private
      module F = Filter F

    field
      intersect : ∀ S1 S2 -> F.P (Subtype-∩ S1 S2) -> ∥ F.P S1 ⊎ F.P S2 ∥



module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} {ℓS ℓF : Level}
         (g : A -> B) (F : Filter A ℓS ℓF) where
  private
    module F = Filter F

  Filter-map : Filter B ℓS (ℓ-max* 3 ℓA (ℓ-suc ℓS) ℓF)
  Filter-map .Filter.P S =
    ∃[ S' ∈ Subtype A ℓS ] (F.P S' × (∀ a -> ⟨ S' a ⟩ -> ⟨ S (g a) ⟩))
  Filter-map .Filter.isProp-P _ = squash
  Filter-map .Filter.inhabited = ∣ (UnivS' B ℓS) , ∥-map handle F.inhabited ∣
    where
    handle : Σ (Subtype A ℓS) F.P -> _
    handle (S' , PS') = S' , PS' , (\ _ _ -> lift tt)
  Filter-map .Filter.upward-closed S1 S2 S1->S2 = ∥-map handle
    where
    handle : Σ[ S' ∈ Subtype A ℓS ] (F.P S' × (∀ a -> ⟨ S' a ⟩ -> ⟨ S1 (g a) ⟩)) ->
             Σ[ S' ∈ Subtype A ℓS ] (F.P S' × (∀ a -> ⟨ S' a ⟩ -> ⟨ S2 (g a) ⟩))
    handle (S' , P' , im) = S' , P' , \a s' -> S1->S2 (g a) (im a s')
  Filter-map .Filter.downward-directed S1 S2 = ∥-bind2 handle
    where
    handle : Σ[ S' ∈ Subtype A ℓS ] (F.P S' × (∀ a -> ⟨ S' a ⟩ -> ⟨ S1 (g a) ⟩)) ->
             Σ[ S' ∈ Subtype A ℓS ] (F.P S' × (∀ a -> ⟨ S' a ⟩ -> ⟨ S2 (g a) ⟩)) ->
             _
    handle (S1' , P1' , S1'->S1) (S2' , P2' , S2'->S1) =
      ∥-map handle2 (F.downward-directed S1' S2' P1' P2')
      where
      handle2 : _ -> _
      handle2 (S3' , P3' , S3'->S1' , S3'->S2') =
        S3 , ∣ (S3' , P3' , (\a s3' -> (S1'->S1 _ (S3'->S1' _ s3')) ,
                                       (S2'->S1 _ (S3'->S2' _ s3')))) ∣ ,
        (\a -> proj₁) , (\a -> proj₂)
        where
        S3 : Subtype B ℓS
        S3 = Subtype-∩ S1 S2


module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} {ℓS ℓF : Level}
         (g : A -> B) (F : Filter B ℓS ℓF) where
  private
    module F = Filter F

  Filter-map' : Filter A ℓS (ℓ-max* 4 ℓA ℓB (ℓ-suc ℓS) ℓF)
  Filter-map' .Filter.P S =
    ∃[ S' ∈ Subtype B ℓS ] (F.P S' × (∀ a -> ⟨ S' (g a) ⟩ -> ⟨ S a ⟩))
  Filter-map' .Filter.isProp-P _ = squash
  Filter-map' .Filter.inhabited = ∣ (UnivS' A ℓS) , ∥-map handle F.inhabited ∣
    where
    handle : Σ (Subtype B ℓS) F.P -> _
    handle (S' , PS') = S' , PS' , (\ _ _ -> lift tt)
  Filter-map' .Filter.upward-closed S1 S2 S1->S2 = ∥-map handle
    where
    handle : Σ[ S' ∈ Subtype B ℓS ] (F.P S' × (∀ a -> ⟨ S' (g a) ⟩ -> ⟨ S1 a ⟩)) ->
             Σ[ S' ∈ Subtype B ℓS ] (F.P S' × (∀ a -> ⟨ S' (g a) ⟩ -> ⟨ S2 a ⟩))
    handle (S' , P' , im) = S' , P' , \a s' -> S1->S2 a (im a s')
  Filter-map' .Filter.downward-directed S1 S2 = ∥-bind2 handle
    where
    handle : Σ[ S' ∈ Subtype B ℓS ] (F.P S' × (∀ a -> ⟨ S' (g a) ⟩ -> ⟨ S1 a ⟩)) ->
             Σ[ S' ∈ Subtype B ℓS ] (F.P S' × (∀ a -> ⟨ S' (g a) ⟩ -> ⟨ S2 a ⟩)) ->
             _
    handle (S1' , P1' , S1'->S1) (S2' , P2' , S2'->S1) =
      ∥-map handle2 (F.downward-directed S1' S2' P1' P2')
      where
      handle2 : _ -> _
      handle2 (S3' , P3' , S3'->S1' , S3'->S2') =
        S3 , ∣ (S3' , P3' , (\a s3' -> (S1'->S1 _ (S3'->S1' _ s3')) ,
                                       (S2'->S1 _ (S3'->S2' _ s3')))) ∣ ,
        (\a -> proj₁) , (\a -> proj₂)
        where
        S3 : Subtype A ℓS
        S3 = Subtype-∩ S1 S2


module _ {ℓA : Level} {A : Type ℓA} {ℓP : Level} (P : Pred A ℓP) (ℓS : Level) where
  predicate-filter : Filter A ℓS (ℓ-max* 3 ℓA ℓP ℓS)
  predicate-filter .Filter.P S = ∀ a -> P a -> ⟨ S a ⟩
  predicate-filter .Filter.isProp-P S = isPropΠ2 (\a _ -> snd (S a))
  predicate-filter .Filter.inhabited = ∣ (UnivS' A ℓS) , (\_ _ -> lift tt) ∣
  predicate-filter .Filter.upward-closed S1 S2 S1->S2 P1 a Pa = S1->S2 a (P1 a Pa)
  predicate-filter .Filter.downward-directed S1 S2 P1 P2 =
    ∣ Subtype-∩ S1 S2 , (\a p -> P1 a p , P2 a p) , (\_ -> proj₁) , (\_ -> proj₂) ∣

module _ {ℓA : Level} {A : Type ℓA} (a : A) (ℓS : Level) where
  principal-filter : Filter A ℓS (ℓ-max ℓA ℓS)
  principal-filter = predicate-filter (\x -> a == x) ℓS

module _ {ℓA : Level} {A : Type ℓA} (a : A) (ℓS : Level) where
  ConvergesTo-principal-filter : ConvergesTo (principal-filter a ℓS) a
  ConvergesTo-principal-filter .ConvergesTo.contains S Sa b a=b = subst (fst ∘ S) a=b Sa

-- module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} {ℓS ℓF : Level}
--          (g : A -> B) (F : Filter B ℓS ℓF) where
--   private
--     module F = Filter F
--
--   Filter-map'-preserves-ConvergesTo : {a : A} -> ConvergesTo F (g a) -> ConvergesTo (Filter-map' g F) a
--   Filter-map'-preserves-ConvergesTo converge-ga .ConvergesTo.contains S Sa =
--     ? -- ∥-map handle (ConvergesTo.contains converge-ga ? ?)
--     where
--     handle : _ -> _
--     handle = ?


module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} {ℓS ℓF : Level}
         (g : A -> B) {F : Filter A ℓS ℓF} where
  private
    module F = Filter F

  Filter-map-preserves-ConvergesTo :
    {a : A} -> ConvergesTo F a -> ConvergesTo (Filter-map g F) (g a)
  Filter-map-preserves-ConvergesTo converge-a .ConvergesTo.contains S Sga =
    ∣ S' , ConvergesTo.contains converge-a S' Sga , (\b Sgb -> Sgb) ∣
    where
    S' : Subtype A ℓS
    S' a = S (g a)



record PreFilter {ℓD : Level} (D : Type ℓD) (ℓS ℓF : Level) :
       Type (ℓ-max* 3 ℓD (ℓ-suc ℓS) (ℓ-suc ℓF)) where
  field
    P : Pred (Subtype D ℓS) ℓF
    isProp-P : isPropValuedPred P
    inhabited : ∃ (Subtype D ℓS) P
    downward-directed : ∀ S1 S2 -> P S1 -> P S2 ->
      ∃[ S3 ∈ (Subtype D ℓS) ]
        (P S3 × (∀ d -> ⟨ S3 d ⟩ -> ⟨ S1 d ⟩) × (∀ d -> ⟨ S3 d ⟩ -> ⟨ S1 d ⟩))

-- module _ {ℓD : Level} {D : Type ℓD} {ℓS ℓF : Level} (PF : PreFilter D ℓS ℓF) where
--   private
--     module PF = PreFilter PF
--   PreFilter->Filter : Filter D ℓS ℓF
--   PreFilter->Filter .Filter.P =
--     ∃[ s ∈ Subtype D ℓS ] (PF
