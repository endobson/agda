{-# OPTIONS --cubical --safe --exact-split #-}

module direct-product.standard-basis where

open import apartness
open import base
open import commutative-monoid
open import commutative-monoid.pi
open import direct-product
open import equality hiding (J)
open import fin
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset
open import finset.detachable
open import finset.search
open import funext
open import functions
open import group
open import heyting-field
open import hlevel
open import monoid
open import nat.order
open import relation
open import ring
open import semiring
open import sigma
open import subset
open import sum
open import truncation
open import type-algebra
open import vector-space

private
  variable
    ℓ ℓD ℓK ℓI : Level
    D K I : Type ℓ

  DP = DirectProduct

  wrap-dp : (I -> D) -> DP D I
  wrap-dp f = direct-product-cons f

  unwrap-dp : DP D I -> I -> D
  unwrap-dp (direct-product-cons f) = f

  i-coord : I -> DP D I -> D
  i-coord i (direct-product-cons f) = f i




module _ {ℓK ℓI : Level} {K : Type ℓK} {S : Semiring K}
         {R : Ring S} {A : TightApartnessStr K} (F : Field R A) (I : FinSet ℓI) where
  private
    instance
      IS = S
      IR = R

    I' = ⟨ I ⟩
    isFinSet-I = snd I
    isSet-I = isFinSet->isSet isFinSet-I
    discrete-I = isFinSet->Discrete isFinSet-I

    isSet-K = Semiring.isSet-Domain S

    VS = (VectorSpaceStr-DirectProduct F I')
    MS = VectorSpaceStr.module-str VS
    V = (DP K I')

    instance
      IMS = MS


    -- Show that unwrap is a CommMonoidʰ
    CM-V = ModuleStr.CommMonoid-V+ MS
    CM-K+ = Semiring.+-CommMonoid S
    CM-ΠK+ : CommMonoid (I' -> K)
    CM-ΠK+ = CommMonoidStr-Π (\_ -> CM-K+)
    module CM-V = CommMonoid CM-V
    module CM-ΠK+ = CommMonoid CM-ΠK+

    unwrap-dpʰ : CommMonoidʰᵉ CM-V CM-ΠK+ unwrap-dp
    unwrap-dpʰ = record
      { preserves-ε = refl
      ; preserves-∙ = \x y -> refl
      }


    indicator' : {i1 i2 : I'} -> Dec (i1 == i2) -> K
    indicator' (yes _) = 1#
    indicator' (no _) = 0#

    indicator : I' -> I' -> K
    indicator i1 i2 = indicator' (discrete-I i1 i2)

    -- The family of vectors that are the standard basis.
    standard-basis' : I' -> V
    standard-basis' i1 = wrap-dp (indicator i1)


    module _ (S : FinSubset I' ℓI) (f : ⟨ ⟨ S ⟩ ⟩ -> K) where
      private
        S' = ⟨ ⟨ S ⟩ ⟩
        isFinSet-S' = snd ⟨ S ⟩
        inc : S' -> I'
        inc = fst (snd S)
        inj-inc : Injective inc
        inj-inc = snd (snd S)

      ΣS' : Pred I' ℓI
      ΣS' i = (Σ[ s ∈ S' ] (inc s == i))

      isProp-ΣS' : isPropValuedPred ΣS'
      isProp-ΣS' _ (s1 , p1) (s2 , p2) =
        ΣProp-path (isSet-I _ _) (inj-inc (p1 >=> (sym p2)))

      SubS : Subtype I' ℓI
      SubS i = ΣS' i , isProp-ΣS' i

      ΣI : Pred S' ℓI
      ΣI s = (Σ[ i ∈ I' ] (inc s == i))

      isProp-ΣI : (s : S') -> isProp (ΣI s)
      isProp-ΣI s (i1 , p1) (i2 , p2) = ΣProp-path (isSet-I _ _) (sym p1 >=> p2)

      isContr-ΣI : (s : S') -> isContr (ΣI s)
      isContr-ΣI s = (inc s , refl) , isProp-ΣI s _

      find-s : Decidable ΣS'
      find-s i = handle find-or
        where
        find-or : Inhabited (\s -> inc s == i) ⊎ Universal (\s -> inc s != i)
        find-or = finite-search' ⟨ S ⟩ (\s -> handle (discrete-I (inc s) i))
          where
          handle : {s : S'} -> Dec (inc s == i) -> (inc s == i) ⊎ (inc s != i)
          handle (yes p) = inj-l p
          handle (no p) = inj-r p

        handle : (Inhabited (\s -> inc s == i) ⊎ Universal (\s -> inc s != i)) -> Dec (ΣS' i)
        handle (inj-r f) = no (\(s , p) -> f s p)
        handle (inj-l p) = yes (unsquash (isProp-ΣS' i) p)

      detachable-S : Detachable SubS
      detachable-S = find-s

      extend' : {i : I'} -> Dec (ΣS' i) -> K
      extend' (yes (s , _)) = f s
      extend' (no _) = 0#

      extend : I' -> K
      extend i = extend' (find-s i)

      extend-support' : (s : S') -> extend (inc s) == f s
      extend-support' s = handle (find-s (inc s)) refl
        where
        handle : (d : Dec (Σ[ s2 ∈ S' ] (inc s2 == inc s))) -> d == find-s (inc s) ->
                 extend (inc s) == f s
        handle (yes (s2 , p)) path =
          cong extend' (sym path) >=> cong f (inj-inc p)
        handle (no ¬s2) path = bot-elim (¬s2 (s , refl))

      extend-support : (i : I') -> (s : ΣS' i) -> extend i == f ⟨ s ⟩
      extend-support i (s , p) = cong extend (sym p) >=> extend-support' s

      extend-no-support : (i : I') -> (¬s : ¬ (ΣS' i)) -> extend i == 0#
      extend-no-support i ¬s = handle (find-s i) refl
        where
        handle : (d : Dec (ΣS' i)) -> d == find-s i ->
                 extend i == 0#
        handle (yes s) p = bot-elim (¬s s)
        handle (no s) p = cong extend' (sym p)

      private
        scale-up : (s : S') -> V
        scale-up s = (f s) v* (standard-basis' (inc s))

        extended-scale-up : (i : I') -> V
        extended-scale-up i = extend i v* (standard-basis' i)

        vsum' = vector-sum VS

        extended-scale-up-no-support : Path (∉-Subtype SubS -> V) (extended-scale-up ∘ fst) (\_ -> 0v)
        extended-scale-up-no-support = funExt (\ (i , ¬s) -> path i ¬s)
          where
          path : (i : I') -> ¬(ΣS' i) -> extended-scale-up i == 0v
          path i ¬s = cong (_v* (standard-basis' i)) (extend-no-support i ¬s) >=> v*-left-zero

        extended-scale-up-support :
          Path (∈-Subtype SubS -> V) (extended-scale-up ∘ fst)
                                     (\ (i , s , _) -> scale-up s)
        extended-scale-up-support = funExt (\ (i , Σs) -> path i Σs)
          where
          path : (i : I') -> (s : ΣS' i) -> extended-scale-up i == scale-up ⟨ s ⟩
          path i s@(_ , p) =
            cong2 (\a b -> a v* (standard-basis' b)) (extend-support i s) (sym p)

        fs-ΣIS : isFinSet (∈-Subtype SubS)
        fs-ΣIS = (snd (FinSet-Detachable I SubS detachable-S))
        fs-ΣIS' : isFinSet (∉-Subtype SubS)
        fs-ΣIS' = (snd (FinSet-DetachableComp I SubS detachable-S))

        fs-ΣSI : isFinSet (Σ[ s ∈ S' ] Σ[ i ∈ I' ] (inc s == i))
        fs-ΣSI = isFinSet-equiv Σ-swap-eq fs-ΣIS


        sum1 : scaled-vector-sum VS standard-basis' S f ==
               vector-sum VS scale-up isFinSet-S'
        sum1 = refl

        sum2 : vsum' extended-scale-up isFinSet-I ==
               vsum' (extended-scale-up ∘ fst) fs-ΣIS v+
               vsum' (extended-scale-up ∘ fst) fs-ΣIS'
        sum2 = vector-sum-Detachable VS I SubS detachable-S extended-scale-up

        sum3 : vsum' (extended-scale-up ∘ fst) fs-ΣIS'  == 0v
        sum3 = cong (\f -> vsum' f fs-ΣIS') extended-scale-up-no-support >=>
               vector-sum-0v VS fs-ΣIS'

        sum4 : vsum' (extended-scale-up ∘ fst) fs-ΣIS
               == vsum' scale-up isFinSet-S'
        sum4 = cong (\f -> vsum' f fs-ΣIS) extended-scale-up-support >=>
               vector-sum-convert VS (_ , fs-ΣIS) (_ , fs-ΣSI) Σ-swap-eq
                                  (\ (i , s , _) -> scale-up s) >=>
               vector-sum-convert VS (_ , fs-ΣSI) (_ , isFinSet-S') (Σ-isContr-eq isContr-ΣI)
                                  (scale-up ∘ fst)

        sum5 : scaled-vector-sum VS standard-basis' S f ==
               vsum' extended-scale-up isFinSet-I
        sum5 = sym (sum2 >=> cong2 _v+_ sum4 sum3 >=> v+-right-zero)

      private
        sum6 : unwrap-dp (vsum' extended-scale-up isFinSet-I) ==
               finiteMerge CM-ΠK+ (isSetΠ (\_ -> isSet-K)) I (unwrap-dp ∘ extended-scale-up)
        sum6 = sym (finiteMerge-homo-inject _ _ _ _ _ unwrap-dpʰ)


        module _ (i : I') where

          sum7 : finiteMerge CM-ΠK+ (isSetΠ (\_ -> isSet-K)) I
                             (unwrap-dp ∘ extended-scale-up) i  ==
                 finiteMerge CM-K+ isSet-K I (app-to i ∘ unwrap-dp ∘ extended-scale-up)
          sum7  = sym (finiteMerge-homo-inject _ _ _ _ _ (app-toʰ _ i))

          P : Subtype I' ℓI
          P i2 = (i == i2) , isSet-I i i2

          detachable-P : Detachable P
          detachable-P = discrete-I i

          fs-ΣIP : isFinSet (∈-Subtype P)
          fs-ΣIP = (snd (FinSet-Detachable I P detachable-P))
          fs-ΣIP' : isFinSet (∉-Subtype P)
          fs-ΣIP' = (snd (FinSet-DetachableComp I P detachable-P))

          isProp-ΣIP : isProp (∈-Subtype P)
          isProp-ΣIP (i1 , p1) (i2 , p2) = ΣProp-path (isSet-I _ _) (sym p1 >=> p2)

          isContr-ΣIP : isContr (∈-Subtype P)
          isContr-ΣIP = (i , refl) , isProp-ΣIP _


          sum8 : finiteMerge CM-K+ isSet-K I (app-to i ∘ unwrap-dp ∘ extended-scale-up) ==
                 finiteMerge CM-K+ isSet-K (_ , fs-ΣIP)
                             (app-to i ∘ unwrap-dp ∘ extended-scale-up ∘ fst) +
                 finiteMerge CM-K+ isSet-K (_ , fs-ΣIP')
                             (app-to i ∘ unwrap-dp ∘ extended-scale-up ∘ fst)
          sum8 = finiteMerge-Detachable CM-K+ isSet-K I P detachable-P
                   (app-to i ∘ unwrap-dp ∘ extended-scale-up)


          path9 : (ip : (∉-Subtype P)) ->
                  (app-to i ∘ unwrap-dp ∘ extended-scale-up ∘ fst) ip == 0#
          path9 ip@(i2 , i!=i2) = handle (discrete-I i2 i) refl
            where
            handle : (d : Dec (i2 == i)) -> d == (discrete-I i2 i) ->
                     (app-to i ∘ unwrap-dp ∘ extended-scale-up ∘ fst) ip == 0#
            handle (yes i2=i) = bot-elim (i!=i2 (sym i2=i))
            handle (no _) path = ans
              where
              ans : extend i2 * indicator i2 i == 0#
              ans = cong (extend i2 *_) (cong indicator' (sym path)) >=>
                    *-right-zero

          path10 : (ip : (∈-Subtype P)) ->
                   (app-to i ∘ unwrap-dp ∘ extended-scale-up ∘ fst) ip == extend i
          path10 ip@(i2 , i=i2) = handle (discrete-I i2 i) refl
            where
            handle : (d : Dec (i2 == i)) -> d == (discrete-I i2 i) ->
                     (app-to i ∘ unwrap-dp ∘ extended-scale-up ∘ fst) ip == extend i
            handle (no i2!=i) = bot-elim (i2!=i (sym i=i2))
            handle (yes _) path = ans
              where
              ans : extend i2 * indicator i2 i == extend i
              ans = cong2 _*_ (cong extend (sym i=i2)) (cong indicator' (sym path)) >=>
                    *-right-one

          sum11 : finiteMerge CM-K+ isSet-K I (app-to i ∘ unwrap-dp ∘ extended-scale-up) ==
                  extend i
          sum11 = sum8 >=>
                  cong2 _+_ (cong (finiteMerge CM-K+ isSet-K (_ , fs-ΣIP))
                                  (funExt path10))
                            (cong (finiteMerge CM-K+ isSet-K (_ , fs-ΣIP'))
                                  (funExt path9) >=>
                             finiteMerge-ε CM-K+ isSet-K (_ , fs-ΣIP'))
                  >=> +-right-zero
                  >=> finiteMerge-isContr CM-K+ isSet-K (_ , fs-ΣIP) isContr-ΣIP (\_ -> extend i)



        sum12 : finiteMerge CM-ΠK+ (isSetΠ (\_ -> isSet-K)) I (unwrap-dp ∘ extended-scale-up) ==
                extend
        sum12 = funExt (\i -> (sum7 i >=> sum11 i))

      standard-basis'-sum' : scaled-vector-sum VS standard-basis' S f == wrap-dp extend
      standard-basis'-sum' = sum5 >=> cong wrap-dp (sum6 >=> sum12)

  private

    -- The improper subset of I
    J : FinSubset I' ℓI
    J = I , (\x -> x) , (\p -> p)

    extend-J : (f : I' -> K) -> extend J f == f
    extend-J f k i = extend-support J f i (i , refl) k

    standard-basis'-sum : (f : I' -> K) -> scaled-vector-sum VS standard-basis' J f == wrap-dp f
    standard-basis'-sum f = standard-basis'-sum' J f >=> cong wrap-dp (extend-J f)

    isSpanning-standard-basis' : isSpanning VS standard-basis' ℓI
    isSpanning-standard-basis' v = ∣ J , unwrap-dp v , standard-basis'-sum _ ∣

    LinearlyIndependent-standard-basis' : LinearlyIndependent VS standard-basis' ℓI
    LinearlyIndependent-standard-basis' S a path s =
      sym (extend-support' S a s) >=>
      cong (\x -> unwrap-dp x (fst (snd S) s)) (sym (standard-basis'-sum' S a) >=> path)

    abstract
      isBasis-standard-basis' : isBasis VS standard-basis' ℓI
      isBasis-standard-basis' = isSpanning-standard-basis' , LinearlyIndependent-standard-basis'

  standard-basis : Basis VS ℓI
  standard-basis = I' , standard-basis' , isBasis-standard-basis'
