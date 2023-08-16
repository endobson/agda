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

module _ {ℓK ℓV : Level} {K : Type ℓK} {K# : Rel K ℓK}
         {ACM : AdditiveCommMonoid K} {AG : AdditiveGroup ACM}
         {S : Semiring ACM} {R : Ring S AG}
         {A : isTightApartness K#} {F : Field R A} {V : Type ℓV}
         {{VS : VectorSpaceStr F V}} where


  private
    module VS = VectorSpaceStr VS

    instance
      IS = S
      IA = A
      IM = VS.module-str
      IACM = ACM
      IVA = ModuleStr.isTightApartness-v# IM


  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    scaled-vector-sum : (I -> K) -> (I -> V) -> V
    scaled-vector-sum ks vs = vector-sum (\i -> (ks i) v* (vs i))


  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} (vs : I -> V) where
    LinearlyDependent :  Type (ℓ-max* 3 ℓK ℓV ℓI)
    LinearlyDependent =
      ∃[ a ∈ (I -> K) ] ((scaled-vector-sum a vs == 0v) × (Σ[ i ∈ I ] (a i # 0#)))

    LinearlyIndependent : Type (ℓ-max* 3 ℓK ℓV ℓI)
    LinearlyIndependent =
      (a : I -> K) ->
      scaled-vector-sum a vs == 0v ->
      (i : I) -> a i == 0#

    LinearlyFree : Type (ℓ-max* 3 ℓK ℓV ℓI)
    LinearlyFree =
      (a : I -> K) ->
      ∃[ i ∈ I ] ((a i) # 0#) ->
      scaled-vector-sum a vs # 0v


    LinearlyFree->LinearlyIndependent : LinearlyFree -> LinearlyIndependent
    LinearlyFree->LinearlyIndependent free a sum0 i =
      tight-# (\ai#0 -> irrefl-path-# sum0 (free a ∣ (i , ai#0) ∣))

    LinearlyIndependent->¬LinearlyDependent : LinearlyIndependent -> ¬ LinearlyDependent
    LinearlyIndependent->¬LinearlyDependent indep dep =
      unsquash isPropBot (∥-map handle dep)
      where
      handle : Σ[ a ∈ (I -> K) ] (scaled-vector-sum a vs == 0v ×
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


module _ {ℓK ℓV : Level} {K : Type ℓK} {K# : Rel K ℓK}
         {ACM : AdditiveCommMonoid K} {AG : AdditiveGroup ACM}
         {S : Semiring ACM} {R : Ring S AG}
         {A : isTightApartness K#} {F : Field R A} {V : Type ℓV}
         {{VS : VectorSpaceStr F V}}
         where
  private
    instance
      M = VectorSpaceStr.module-str VS
      IACM = ACM
      IAG = AG

    isSet-V = ModuleStr.isSet-V M

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    linearlyIndependent->isProp-isLinearCombination :
      {vs : I -> V} -> LinearlyIndependent vs -> {v : V} -> isProp (isLinearCombination' vs v)
    linearlyIndependent->isProp-isLinearCombination {vs} li {v} (a1 , p1) (a2 , p2) =
      ΣProp-path (isSet-V _ _) a1=a2
      where
      da : I -> K
      da i = diff (a1 i) (a2 i)

      d1-path : scaled-vector-sum a1 vs == scaled-vector-sum a2 vs
      d1-path = p1 >=> sym p2

      d2-path : scaled-vector-sum a2 vs v+ (v- scaled-vector-sum a1 vs) == 0v
      d2-path = cong (_v+ (v- scaled-vector-sum a1 vs)) (sym d1-path) >=> v+-inverse

      d3-path : scaled-vector-sum a2 vs v+ (v- scaled-vector-sum a1 vs) ==
                scaled-vector-sum da vs
      d3-path =
        v+-right (sym (finiteMerge-homo-inject v-ʰ)) >=>
        sym (finiteMerge-split _) >=>
        cong vector-sum (funExt (\i -> v+-right (sym v*-minus-extract-left) >=>
                                       sym v*-distrib-+))

      d-path : scaled-vector-sum da vs == 0v
      d-path = sym d3-path >=> d2-path

      a1=a2 : a1 == a2
      a1=a2 = funExt (\ i -> diff-zero (li da d-path i))

    basis-decomposition-full : {b : I -> V} -> isBasis b -> (v : V) ->
                               isContr (isLinearCombination' b v)
    basis-decomposition-full {b} (span , li) v =
      combo , (isProp-lc combo)
      where
      abstract
        isProp-lc : isProp (isLinearCombination' b v)
        isProp-lc = (linearlyIndependent->isProp-isLinearCombination li)
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



module _ {ℓK ℓV1 ℓV2 : Level} {K : Type ℓK} {K# : Rel K ℓK}
         {ACM : AdditiveCommMonoid K} {AG : AdditiveGroup ACM}
         {S : Semiring ACM} {R : Ring S AG}
         {A : isTightApartness K#} {F : Field R A} {V1 : Type ℓV1} {V2 : Type ℓV2}
         {{VS1 : VectorSpaceStr F V1}} {{VS2 : VectorSpaceStr F V2}}
         where

  private
    instance
      IS = S
      IM1 = VectorSpaceStr.module-str VS1
      IM2 = VectorSpaceStr.module-str VS2
      IACM = ACM
      IVA1 = ModuleStr.isTightApartness-v# IM1
      IVA2 = ModuleStr.isTightApartness-v# IM2


  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    transform-isSpanning : {f : V1 -> V2} {vs : I -> V1} ->
                           isLinearTransformation f -> isEquiv f -> isSpanning vs -> isSpanning (f ∘ vs)
    transform-isSpanning {f} {vs} lt isEq-f vs-span = fvs-span
      where
      fvs-span : isSpanning (f ∘ vs)
      fvs-span v2 = ∥-map handle (vs-span v1)
        where
        v1 = isEqInv isEq-f v2
        handle : isLinearCombination' vs v1 -> isLinearCombination' (f ∘ vs) v2
        handle (a , p) = (a , path)
          where
          path : scaled-vector-sum a (f ∘ vs) == v2
          path = cong vector-sum (funExt (\i -> sym (lt-preserves-* lt (a i) (vs i)))) >=>
                 sym (lt-preserves-vector-sum lt) >=>
                 cong f p >=>
                 isEqSec isEq-f v2

    transform-isSpanning-path :
      {vs1 : I -> V1} {vs2 : I -> V1} -> vs1 == vs2 ->
      isSpanning vs1 -> isSpanning vs2
    transform-isSpanning-path {vs1} {vs2} p1 vs1-span v = ∥-map handle (vs1-span v)
      where
      handle : isLinearCombination' vs1 v -> isLinearCombination' vs2 v
      handle (a , p2) = (a , cong (scaled-vector-sum a) (sym p1) >=> p2)

    transform-LinearlyIndependent :
      {f : V1 -> V2} {vs : I -> V1} ->
      isLinearTransformation f -> isEquiv f -> LinearlyIndependent vs -> LinearlyIndependent (f ∘ vs)
    transform-LinearlyIndependent {f} {vs} lt isEq-f vs-ind a p i = vs-ind a path i
      where
      f-path : f (scaled-vector-sum a vs) == f 0v
      f-path = lt-preserves-vector-sum lt >=>
               cong vector-sum (funExt (\i -> (lt-preserves-* lt (a i) (vs i)))) >=>
               p >=>
               sym (lt-preserves-0v lt)

      path : scaled-vector-sum a vs == 0v
      path = sym (isEqRet isEq-f (scaled-vector-sum a vs)) >=>
             (cong (isEqInv isEq-f) f-path) >=>
             (isEqRet isEq-f 0v)

    transform-LinearlyFree :
      {f : V1 -> V2} {vs : I -> V1} ->
      isLinearTransformation f -> StronglyInjective f -> LinearlyFree vs -> LinearlyFree (f ∘ vs)
    transform-LinearlyFree {f} {vs} lt inj-f vs-free a a#0 =
      subst2 _v#_ (sym path1) (sym path2) (inj-f (vs-free a a#0))
      where
      path1 : scaled-vector-sum a (f ∘ vs) == f (scaled-vector-sum a vs)
      path1 = cong vector-sum (funExt (\i -> sym (lt-preserves-* lt (a i) (vs i)))) >=>
              sym (lt-preserves-vector-sum lt)

      path2 : 0v == f 0v
      path2 = sym (lt-preserves-0v lt)


    transform-basis : {f : V1 -> V2} {vs : I -> V1} ->
                      isLinearTransformation f -> isEquiv f ->
                      isBasis vs -> isBasis (f ∘ vs)
    transform-basis lt isEq-f =
      ×-map (transform-isSpanning lt isEq-f) (transform-LinearlyIndependent lt isEq-f)
