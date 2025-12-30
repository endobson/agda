{-# OPTIONS --cubical --safe --exact-split #-}

module vector-space.finite where

open import additive-group
open import apartness
open import base
open import equality hiding (J)
open import equivalence
open import fin
open import finset
open import finsum
open import finsum.arithmetic
open import finite-commutative-monoid.instances
open import functions
open import funext
open import heyting-field
open import hlevel
open import ring
open import relation
open import semiring
open import sigma.base
open import subset
open import truncation
open import vector-space

private
  variable
    ℓ : Level

module _ {ℓK ℓV : Level}
         {K : Type ℓK} {K# : Rel K ℓK}
         {V : Type ℓV} {V# : Rel V ℓV}
         {ACM-K : AdditiveCommMonoid K} {AG-K : AdditiveGroup ACM-K}
         {S-K : Semiring ACM-K} {R-K : Ring S-K AG-K}
         {ACM-V : AdditiveCommMonoid V} {AG-V : AdditiveGroup ACM-V}
         {A-K : isTightApartness K#}
         {A-V : isTightApartness V#}
         {MS : ModuleStr R-K AG-V}
         {{AMS : ApartModuleStr MS A-K A-V}}
         {{F : Field R-K A-K}}
         where

  private
    instance
      IMS = MS
      IACM-K = ACM-K
      IS = S-K
      IACM-V = ACM-V
      IA-K = A-K
      IA-V = A-V


  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    scaled-vector-sum : (I -> K) -> (I -> V) -> V
    scaled-vector-sum ks vs = finiteSum (\i -> (ks i) v* (vs i))



  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} (vs : I -> V) where
    LinearlyDependent :  Type (ℓ-max* 3 ℓK ℓV ℓI)
    LinearlyDependent =
      ∃[ a ∈ (I -> K) ] ((scaled-vector-sum a vs == 0#) × (Σ[ i ∈ I ] (a i # 0#)))

    LinearlyIndependent : Type (ℓ-max* 3 ℓK ℓV ℓI)
    LinearlyIndependent =
      (a : I -> K) ->
      scaled-vector-sum a vs == 0# ->
      (i : I) -> a i == 0#

    LinearlyFree : Type (ℓ-max* 3 ℓK ℓV ℓI)
    LinearlyFree =
      (a : I -> K) ->
      ∃[ i ∈ I ] ((a i) # 0#) ->
      scaled-vector-sum a vs # 0#


    LinearlyFree->LinearlyIndependent : LinearlyFree -> LinearlyIndependent
    LinearlyFree->LinearlyIndependent free a sum0 i =
      tight-# (\ai#0 -> irrefl-path-# sum0 (free a ∣ (i , ai#0) ∣))

    LinearlyIndependent->¬LinearlyDependent : LinearlyIndependent -> ¬ LinearlyDependent
    LinearlyIndependent->¬LinearlyDependent indep dep =
      unsquash isPropBot (∥-map handle dep)
      where
      handle : Σ[ a ∈ (I -> K) ] (scaled-vector-sum a vs == 0# ×
                                  Σ[ i ∈ I ] (a i # 0#)) -> Bot
      handle (a , sum0 , i , ai#0) = irrefl-path-# (indep a sum0 i) ai#0

    ¬LinearlyDependent->LinearlyIndependent : ¬ LinearlyDependent -> LinearlyIndependent
    ¬LinearlyDependent->LinearlyIndependent ¬dep a sum0 i =
      tight-# (\ai#0 -> ¬dep ∣ a , sum0 , i , ai#0 ∣)

    LinearlyDependent->¬LinearlyIndependent : LinearlyDependent -> ¬ LinearlyIndependent
    LinearlyDependent->¬LinearlyIndependent dep indep =
      LinearlyIndependent->¬LinearlyDependent indep dep

    ¬LinearlyIndependent->¬LinearlyFree : ¬ LinearlyIndependent -> ¬ LinearlyFree
    ¬LinearlyIndependent->¬LinearlyFree ¬indep free =
      ¬indep (LinearlyFree->LinearlyIndependent free)

    isLinearCombination' : Pred V _
    isLinearCombination' v =
      Σ[ a ∈ (I -> K) ] (scaled-vector-sum a vs == v)

    isLinearCombination : Pred V _
    isLinearCombination v = ∥ isLinearCombination' v ∥

    LinearSpan : Subtype V (ℓ-max* 3 ℓK ℓV ℓI)
    LinearSpan v = isLinearCombination v , squash


    isAffineCombination : Pred V _
    isAffineCombination v =
      ∃[ a ∈ (I -> K) ] (scaled-vector-sum a vs == v × finiteSum a == 1#)

    AffineSpan : Subtype V (ℓ-max* 3 ℓK ℓV ℓI)
    AffineSpan v = isAffineCombination v , squash

    isSpanning : Type (ℓ-max* 3 ℓK ℓV ℓI)
    isSpanning = isFullSubtype LinearSpan

    isBasis : Type (ℓ-max* 3 ℓK ℓV ℓI)
    isBasis = isSpanning × LinearlyIndependent



module _ {ℓK ℓV : Level}
         {K : Type ℓK} {K# : Rel K ℓK}
         {V : Type ℓV} {V# : Rel V ℓV}
         {ACM-K : AdditiveCommMonoid K} {AG-K : AdditiveGroup ACM-K}
         {S-K : Semiring ACM-K} {R-K : Ring S-K AG-K}
         {ACM-V : AdditiveCommMonoid V} {AG-V : AdditiveGroup ACM-V}
         {A-K : isTightApartness K#}
         {A-V : isTightApartness V#}
         {MS : ModuleStr R-K AG-V}
         {{AMS : ApartModuleStr MS A-K A-V}}
         {{F : Field R-K A-K}}
         where
  private
    instance
      IACM-K = ACM-K
      IAG-K = AG-K
      IACM-V = ACM-V
      IAG-V = AG-V
      IMS = MS

    isSet-V = AdditiveCommMonoid.isSet-Domain ACM-V

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    opaque
      linearlyIndependent->isProp-isLinearCombination :
        {vs : I -> V} -> LinearlyIndependent vs -> {v : V} -> isProp (isLinearCombination' vs v)
      linearlyIndependent->isProp-isLinearCombination {vs} li {v} (a1 , p1) (a2 , p2) =
        ΣProp-path (isSet-V _ _) a1=a2
        where
        da : I -> K
        da i = diff (a1 i) (a2 i)

        d1-path : scaled-vector-sum a1 vs == scaled-vector-sum a2 vs
        d1-path = p1 >=> sym p2

        d2-path : scaled-vector-sum a2 vs + (- scaled-vector-sum a1 vs) == 0#
        d2-path = cong (_+ (- scaled-vector-sum a1 vs)) (sym d1-path) >=> +-inverse

        d3-path : scaled-vector-sum a2 vs + (- scaled-vector-sum a1 vs) ==
                  scaled-vector-sum da vs
        d3-path =
          +-right (sym finiteSum--) >=>
          sym (finiteMerge-split _) >=>
          cong finiteSum (funExt (\i -> +-right (sym v*-minus-extract-left) >=>
                                        sym v*-distrib-+-right))

        d-path : scaled-vector-sum da vs == 0#
        d-path = sym d3-path >=> d2-path

        a1=a2 : a1 == a2
        a1=a2 = funExt (\ i -> diff-zero (li da d-path i))

    basis-decomposition-full : {b : I -> V} -> isBasis b -> (v : V) ->
                               isContr (isLinearCombination' b v)
    basis-decomposition-full {b} (span , li) v =
      combo , (isProp-lc combo)
      where
        isProp-lc : isProp (isLinearCombination' b v)
        isProp-lc = (linearlyIndependent->isProp-isLinearCombination li)
        combo : isLinearCombination' b v
        combo = unsquash isProp-lc (span v)

    basis-decomposition : {b : I -> V} -> isBasis b -> V -> (I -> K)
    basis-decomposition b v = fst (fst (basis-decomposition-full b v))

    basis-decomposition-path :
      {b : I -> V} {v : V} -> (isBasis-b : isBasis b) ->
      scaled-vector-sum (basis-decomposition isBasis-b v) b == v
    basis-decomposition-path {_} {v} b =
      snd (fst (basis-decomposition-full b v))

    basis-decomposition-unique :
      {vs : I -> V} {v : V} {f : I -> K} (b : isBasis vs) ->
      scaled-vector-sum f vs == v -> f == basis-decomposition b v
    basis-decomposition-unique {vs} {v} {f} b p =
      cong fst (sym (snd (basis-decomposition-full b  v) (f , p)))


module _ {ℓK ℓV₁ ℓV₂ : Level}
         {K : Type ℓK} {V₁ : Type ℓV₁} {V₂ : Type ℓV₂}
         {K# : Rel K ℓK}
         {V₁# : Rel V₁ ℓV₁}
         {V₂# : Rel V₂ ℓV₂}
         {ACM-K : AdditiveCommMonoid K}
         {AG-K : AdditiveGroup ACM-K}
         {S-K : Semiring ACM-K}
         {R-K : Ring S-K AG-K}
         {ACM-V₁ : AdditiveCommMonoid V₁} {AG-V₁ : AdditiveGroup ACM-V₁}
         {ACM-V₂ : AdditiveCommMonoid V₂} {AG-V₂ : AdditiveGroup ACM-V₂}
         {MS₁ : ModuleStr R-K AG-V₁}
         {MS₂ : ModuleStr R-K AG-V₂}
         {A-K : isTightApartness K#}
         {A-V₁ : isTightApartness V₁#}
         {A-V₂ : isTightApartness V₂#}
         {{F : Field R-K A-K}}
         {{AMS₁ : ApartModuleStr MS₁ A-K A-V₁}}
         {{AMS₂ : ApartModuleStr MS₂ A-K A-V₂}}
  where

  private
    instance
      IACM-V₁ = ACM-V₁
      IACM-V₂ = ACM-V₂
      IMS₁ = MS₁
      IMS₂ = MS₂
      IA-V₁ = A-V₁
      IA-V₂ = A-V₂

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    transform-isSpanning : {f : V₁ -> V₂} {vs : I -> V₁} ->
                           isLinearTransformation f -> isEquiv f -> isSpanning vs -> isSpanning (f ∘ vs)
    transform-isSpanning {f} {vs} lt isEq-f vs-span = fvs-span
      where
      fvs-span : isSpanning (f ∘ vs)
      fvs-span v2 = ∥-map handle (vs-span v1)
        where
        v1 : V₁
        v1 = isEqInv isEq-f v2
        handle : isLinearCombination' vs v1 -> isLinearCombination' (f ∘ vs) v2
        handle (a , p) = (a , path)
          where
          path : scaled-vector-sum a (f ∘ vs) == v2
          path = cong finiteSum (funExt (\i -> sym (lt-preserves-* lt (a i) (vs i)))) >=>
                 sym (lt-preserves-finiteSum lt) >=>
                 cong f p >=>
                 isEqSec isEq-f v2

    transform-isSpanning-path :
      {vs1 : I -> V₁} {vs2 : I -> V₁} -> vs1 == vs2 ->
      isSpanning vs1 -> isSpanning vs2
    transform-isSpanning-path {vs1} {vs2} p1 vs1-span v = ∥-map handle (vs1-span v)
      where
      handle : isLinearCombination' vs1 v -> isLinearCombination' vs2 v
      handle (a , p2) = (a , cong (scaled-vector-sum a) (sym p1) >=> p2)

    transform-LinearlyIndependent :
      {f : V₁ -> V₂} {vs : I -> V₁} ->
      isLinearTransformation f -> isEquiv f -> LinearlyIndependent vs -> LinearlyIndependent (f ∘ vs)
    transform-LinearlyIndependent {f} {vs} lt isEq-f vs-ind a p i = vs-ind a path i
      where
      f-path : f (scaled-vector-sum a vs) == f 0#
      f-path = lt-preserves-finiteSum lt >=>
               cong finiteSum (funExt (\i -> (lt-preserves-* lt (a i) (vs i)))) >=>
               p >=>
               sym (lt-preserves-0v lt)

      path : scaled-vector-sum a vs == 0#
      path = sym (isEqRet isEq-f (scaled-vector-sum a vs)) >=>
             (cong (isEqInv isEq-f) f-path) >=>
             (isEqRet isEq-f 0#)

    transform-LinearlyFree :
      {f : V₁ -> V₂} {vs : I -> V₁} ->
      isLinearTransformation f -> StronglyInjective f -> LinearlyFree vs -> LinearlyFree (f ∘ vs)
    transform-LinearlyFree {f} {vs} lt inj-f vs-free a a#0 =
      subst2 _#_ (sym path1) (sym path2) (inj-f (vs-free a a#0))
      where
      path1 : scaled-vector-sum a (f ∘ vs) == f (scaled-vector-sum a vs)
      path1 = cong finiteSum (funExt (\i -> sym (lt-preserves-* lt (a i) (vs i)))) >=>
              sym (lt-preserves-finiteSum lt)

      path2 : 0# == f 0#
      path2 = sym (lt-preserves-0v lt)


    transform-basis : {f : V₁ -> V₂} {vs : I -> V₁} ->
                      isLinearTransformation f -> isEquiv f ->
                      isBasis vs -> isBasis (f ∘ vs)
    transform-basis lt isEq-f =
      ×-map (transform-isSpanning lt isEq-f) (transform-LinearlyIndependent lt isEq-f)
