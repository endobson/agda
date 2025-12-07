{-# OPTIONS --cubical --safe --exact-split #-}

module graph.simple.decidable-path where

open import base
open import decision
open import discrete
open import equality-path
open import equivalence
open import fin
open import finset
open import finset.detachable
open import finset.instances
open import finset.instances.pi
open import finset.instances.sigma
open import finset.order
open import finset.search
open import functions
open import functions.embedding
open import functions.embedding.finset
open import graph.simple
open import graph.simple.finite-walk
open import hlevel.base
open import hlevel.sigma
open import isomorphism
open import order
open import order.instances.nat
open import sigma
open import sum
open import truncation
open import univalence


module _ {ℓV ℓE : Level} {G : Graph ℓV ℓE} where
 open Graph G
 private
   FV : FinSet ℓV
   FV = V , isFinSet-V

   #V : Nat
   #V = cardinality FV

   Skeleton : (n : Nat) -> Type ℓV
   Skeleton n = Fin (suc n) -> V

   isFinSet-Skeleton : (n : Nat) -> isFinSet (Skeleton n)
   isFinSet-Skeleton n = isFinSet-Π isFinSetⁱ (\_ -> isFinSet-V)

   isGoodSkeleton : {n : Nat} -> (s : Skeleton n) -> Type ℓE
   isGoodSkeleton s = ∀ i -> E (s (inc-fin i)) (s (suc-fin i))

   Dec-isGoodSkeleton : {n : Nat} -> (s : Skeleton n) -> Dec (isGoodSkeleton s)
   Dec-isGoodSkeleton s = either (no ∘ unsquash isProp¬ ∘ ∥-map convert) yes search-result
     where
     search-result : (∃[ i ∈ _ ] _) ⊎ isGoodSkeleton s
     search-result =
       finite-search-dec' (_  , isFinSetⁱ)
         (\i -> dec-E (s (inc-fin i)) (s (suc-fin i)))

     convert : _ -> ¬ (isGoodSkeleton s)
     convert (i , ¬e) g = ¬e (g i)

   GPath≃GoodPathSkeleton : GPath G ≃ (Σ[ n ∈ Nat ] (Σ[ s ∈ (Skeleton n) ] (isGoodSkeleton s × isEmbedding s)))
   GPath≃GoodPathSkeleton = isoToEquiv (iso for back (\_ -> refl) (\_ -> refl))
     where
     for : GPath G -> (Σ[ n ∈ Nat ] (Σ[ s ∈ (Skeleton n) ] (isGoodSkeleton s × isEmbedding s)))
     for (w , p) = N , vs , (es , p)
       where
       open FiniteWalk w
     back : (Σ[ n ∈ Nat ] (Σ[ s ∈ (Skeleton n) ] (isGoodSkeleton s × isEmbedding s))) -> GPath G
     back (N , vs , (es , p)) = record { N = N ; vs = vs ; es = es } , p


   path-length≤cardinality : ∀ ((w , _) : GPath G) -> FiniteWalk.length w ≤ cardinality FV
   path-length≤cardinality (w , emb-vs) =
     isInjective->FinSet≤ (_ , isFinSetⁱ) FV (FiniteWalk.vs w) (isEqInv (emb-vs _ _))

   emb->short : {n : Nat} -> {s : Skeleton n} -> isEmbedding s -> n < #V
   emb->short {n} {s} e =
     isInjective->FinSet≤ (_ , isFinSetⁱ) FV s (isEqInv (e _ _))


   ShortSkeleton-eq :
     (Σ[ n ∈ Nat ] (Σ[ s ∈ (Skeleton n) ] (isGoodSkeleton s × isEmbedding s))) ≃
     (Σ[ (n , _) ∈ Fin #V ] (Σ[ s ∈ (Skeleton n) ] (isGoodSkeleton s × isEmbedding s)))
   ShortSkeleton-eq = isoToEquiv (iso for back fb (\_ -> refl))
     where
     for : _ -> _
     for (n , s , g , e) = ((n , emb->short e) , s , g , e)
     back : _ -> _
     back ((n , lt) , s , g , e) = (n , s , g , e)

     fb : ∀ x -> _
     fb ((n , lt) , s , g , e) i = (n , isProp-< (emb->short e) lt i) , s , g , e

   isFinSet-ShortSkeleton :
     isFinSet (Σ[ (n , _) ∈ Fin #V ] (Σ[ s ∈ (Skeleton n) ] (isGoodSkeleton s × isEmbedding s)))
   isFinSet-ShortSkeleton =
     isFinSet-Σ isFinSetⁱ
       (\ (n , _) -> isFinSet-Detachable
         (\s -> (_ , isProp× (isPropΠ (\_ -> isProp-E _ _)) isProp-isEmbedding))
         (isFinSet-Skeleton n)
         (Decidable-∩ Dec-isGoodSkeleton (decide-isEmbedding (_ , isFinSetⁱ)))
         )

 opaque
   isFinSet-GPath : isFinSet (GPath G)
   isFinSet-GPath = subst isFinSet (sym (ua (GPath≃GoodPathSkeleton >eq> ShortSkeleton-eq))) isFinSet-ShortSkeleton

   decide-∥GPath∥ : ∀ v₁ v₂ -> Dec (∃[ (w , _) ∈ GPath G ] (FiniteWalk-StartsWith w v₁ × FiniteWalk-EndsWith w v₂))
   decide-∥GPath∥ v₁ v₂ =
     either yes (\ ¬e -> no (unsquash isPropBot ∘ ∥-map (\ (p , e) -> ¬e p e))) search-result
     where
     search-result : (∃[ (w , _) ∈ GPath G ] (FiniteWalk-StartsWith w v₁ × FiniteWalk-EndsWith w v₂)) ⊎
                     (∀ ((w , _) : GPath G) -> ¬ (FiniteWalk-StartsWith w v₁ × FiniteWalk-EndsWith w v₂))
     search-result =
       finite-search-dec (GPath G , isFinSet-GPath)
         (Decidable-∩ (\_ -> decide-= _ _) (\_ -> decide-= _ _))
