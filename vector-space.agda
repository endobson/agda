{-# OPTIONS --cubical --safe --exact-split #-}

module vector-space where

open import apartness
open import base
open import commutative-monoid
open import equivalence
open import fin
open import finset
open import finset.partition
open import finsum
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.partition
open import functions
open import group
open import heyting-field
open import hlevel
open import monoid
open import ring
open import relation
open import semiring
open import subset
open import truncation

private
  variable
    ℓ : Level

module _ {ℓK ℓV : Level} {K : Type ℓK} {S : Semiring K} (R : Ring S) (V : Type ℓV) where
  private
    instance
      IS = S
      IR = R

  record ModuleStr : Type (ℓ-max ℓK (ℓ-suc ℓV)) where
    field
      GroupStr-V : GroupStr V
      TightApartnessStr-V : TightApartnessStr V

    _v#_ = TightApartnessStr._#_ TightApartnessStr-V

    _v+_ = GroupStr._∙_ GroupStr-V
    0v = GroupStr.ε GroupStr-V

    isSet-V = GroupStr.isSet-Domain GroupStr-V

    field
      _v*_ : K -> V -> V
      v*-distrib-v+ : {k : K} -> {v1 v2 : V} -> k v* (v1 v+ v2) == (k v* v1) v+ (k v* v2)
      v*-distrib-+ : {k1 k2 : K} -> {v : V} -> (k1 + k2) v* v == (k1 v* v) v+ (k2 v* v)
      v*-assoc : {k1 k2 : K} -> {v : V} -> (k1 * k2) v* v == k1 v* (k2 v* v)
      v*-left-one : {v : V} -> 1# v* v == v


module _  {ℓK ℓV : Level} {K : Type ℓK} {S : Semiring K} {R : Ring S} {V : Type ℓV}
          {{M : ModuleStr R V}} where
  open ModuleStr M public using
    ( _v+_
    ; 0v
    ; _v*_
    ; v*-distrib-v+
    ; v*-distrib-+
    ; v*-assoc
    ; v*-left-one
    ; _v#_
    )


module _ {ℓK ℓV : Level} {K : Type ℓK} {S : Semiring K} {R : Ring S}
         (F : Field R) (V : Type ℓV)  where
  private
    instance
      IS = S
      IF = F
      IFA = Field.TightApartnessStr-f# F

  record VectorSpaceStr : Type (ℓ-max ℓK (ℓ-suc ℓV)) where
    constructor vector-space-str
    field
      module-str : ModuleStr R V

    private
      module MS = ModuleStr module-str

    field
      v*-apart-zero : {k : K} {v : V} -> (k MS.v* v) MS.v# MS.0v -> (k # 0#) × (v MS.v# MS.0v)
      v*-apart-args : {k1 k2 : K} {v1 v2 : V} ->
                      (k1 MS.v* v1) MS.v# (k2 MS.v* v2) ->
                      ∥ (k1 # k2) ⊎ (v1 MS.v# v2) ∥


module _ {ℓK ℓV : Level} {K : Type ℓK} {S : Semiring K} {R : Ring S} {F : Field R} {V : Type ℓV}
         (VS : VectorSpaceStr F V) where

  private
    module VS = VectorSpaceStr VS
    module M = ModuleStr VS.module-str

    instance
      IM = VS.module-str
      IS = S
      IF = F
      IVA = ModuleStr.TightApartnessStr-V IM
      IFA = Field.TightApartnessStr-f# F

  private
    variable
      I : Type ℓ

  private
    CommMonoid-V+ : CommMonoid V
    CommMonoid-V+ = GroupStr.comm-monoid M.GroupStr-V

  vector-sum : (I -> V) -> isFinSet I -> V
  vector-sum vs fs = finiteMerge CommMonoid-V+ M.isSet-V (_ , fs) vs

  vector-sum-⊎ : {ℓ₁ ℓ₂ : Level} (FI₁ : FinSet ℓ₁) (FI₂ : FinSet ℓ₂) ->
                 (f : (⟨ FI₁ ⟩ ⊎ ⟨ FI₂ ⟩) -> V) ->
                 vector-sum f (snd (FinSet-⊎ FI₁ FI₂)) ==
                 (vector-sum (f ∘ inj-l) (snd FI₁)) v+ (vector-sum (f ∘ inj-r) (snd FI₂))
  vector-sum-⊎ FI₁ FI₂ = finiteMerge-⊎ CommMonoid-V+ M.isSet-V (snd FI₁) (snd FI₂)

  vector-sum-binary-partition :
    {ℓI ℓP : Level} (FI : FinSet ℓI) (partition : BinaryPartition ⟨ FI ⟩ ℓP) ->
    (f : ⟨ FI ⟩ -> V) ->
    vector-sum f (snd FI) ==
    (vector-sum (f ∘ fst) (snd (FinSet-partition FI (2 , partition) zero-fin))) v+
    (vector-sum (f ∘ fst) (snd (FinSet-partition FI (2 , partition) (suc-fin zero-fin))))
  vector-sum-binary-partition =
    finiteMerge-binary-partition CommMonoid-V+ M.isSet-V



  private
    module _ {ℓI₁ : Level} {I₁ : Type ℓI₁} where
      Carrier : {ℓI₂ : Level} -> FinSubset I₁ ℓI₂ -> Type ℓI₂
      Carrier ((T , _) , _) = T

      isFinSet-Carrier : {ℓI₂ : Level} -> (S : FinSubset I₁ ℓI₂) -> isFinSet (Carrier S)
      isFinSet-Carrier ((_ , fs) , _) = fs

      include : {ℓI₂ : Level} -> (S : FinSubset I₁ ℓI₂) -> Carrier S -> I₁
      include (_ , f , _) = f

  module _ {ℓI₁ ℓI₂ : Level} {I₁ : Type ℓI₁} (family : I₁ -> V) (S : FinSubset I₁ ℓI₂) where
    scaled-vector-sum-inner : (a : Carrier S -> K) -> Carrier S -> V
    scaled-vector-sum-inner a = (\i -> (a i) v* (family (include S i)))

    scaled-vector-sum : (a : Carrier S -> K) -> V
    scaled-vector-sum a = vector-sum (scaled-vector-sum-inner a) (isFinSet-Carrier S)

  module _ {ℓI₁ : Level} {I₁ : Type ℓI₁} (family : I₁ -> V) where

    LinearlyDependent : (ℓI₂ : Level) -> Type (ℓ-max* 4 ℓK ℓV ℓI₁ (ℓ-suc ℓI₂))
    LinearlyDependent ℓI₂ =
      ∃[ S ∈ FinSubset I₁ ℓI₂ ]
      Σ[ a ∈ (Carrier S -> K) ] (scaled-vector-sum family S a == 0v ×
                                 Σ[ i ∈ Carrier S ] (a i # 0#))

    LinearlyIndependent : (ℓI₂ : Level) -> Type (ℓ-max* 4 ℓK ℓV ℓI₁ (ℓ-suc ℓI₂))
    LinearlyIndependent ℓI₂ =
      (S : FinSubset I₁ ℓI₂) -> (a : Carrier S -> K) ->
      scaled-vector-sum family S a == 0v ->
      (i : Carrier S) -> a i == 0#

    LinearlyFree : (ℓI₂ : Level) -> Type (ℓ-max* 4 ℓK ℓV ℓI₁ (ℓ-suc ℓI₂))
    LinearlyFree ℓI₂ =
      (S : FinSubset I₁ ℓI₂) -> (a : Carrier S -> K) ->
      ∃[ i ∈ Carrier S ] ((a i) # 0#) ->
      scaled-vector-sum family S a # 0v


    LinearlyFree->LinearlyIndependent : {ℓI₂ : Level} -> LinearlyFree ℓI₂ -> LinearlyIndependent ℓI₂
    LinearlyFree->LinearlyIndependent free S a sum0 i =
      tight-# (\ai#0 -> irrefl-path-# sum0 (free S a ∣ (i , ai#0) ∣))

    LinearlyIndependent->¬LinearlyDependent :
      {ℓI₂ : Level} -> LinearlyIndependent ℓI₂ -> ¬ (LinearlyDependent ℓI₂)
    LinearlyIndependent->¬LinearlyDependent {ℓI₂} indep dep =
      unsquash isPropBot (∥-map handle dep)
      where
      handle : Σ[ S ∈ FinSubset I₁ ℓI₂ ]
               Σ[ a ∈ (Carrier S -> K) ] (scaled-vector-sum family S a == 0v ×
                                          Σ[ i ∈ Carrier S ] (a i # 0#)) -> Bot
      handle (S , a , sum0 , i , ai#0) = irrefl-path-# (indep S a sum0 i) ai#0

    ¬LinearlyDependent->LinearlyIndependent :
      {ℓI₂ : Level} -> ¬(LinearlyDependent ℓI₂) -> LinearlyIndependent ℓI₂
    ¬LinearlyDependent->LinearlyIndependent ¬dep S a sum0 i =
      tight-# (\ai#0 -> ¬dep ∣ S , a , sum0 , i , ai#0 ∣)

    LinearlyDependent->¬LinearlyIndependent :
      {ℓI₂ : Level} -> (LinearlyDependent ℓI₂) -> ¬ (LinearlyIndependent ℓI₂)
    LinearlyDependent->¬LinearlyIndependent dep indep =
      LinearlyIndependent->¬LinearlyDependent indep dep

    ¬LinearlyIndependent->¬LinearlyFree :
      {ℓI₂ : Level} -> ¬ (LinearlyIndependent ℓI₂) -> ¬ (LinearlyFree ℓI₂)
    ¬LinearlyIndependent->¬LinearlyFree ¬indep free =
      ¬indep (LinearlyFree->LinearlyIndependent free)

    module _ (ℓI₂ : Level) where
      isLinearCombination : Pred V _
      isLinearCombination v =
        ∃[ S ∈ FinSubset I₁ ℓI₂ ]
        Σ[ a ∈ (Carrier S -> K) ] (scaled-vector-sum family S a == v)

      LinearSpan : Subtype V (ℓ-max* 4 ℓK ℓV ℓI₁ (ℓ-suc ℓI₂))
      LinearSpan v = isLinearCombination v , squash

      isAffineCombination : Pred V _
      isAffineCombination v =
        ∃[ S ∈ FinSubset I₁ ℓI₂ ]
        Σ[ a ∈ (Carrier S -> K) ] (scaled-vector-sum family S a == v ×
                                   finiteSum ⟨ S ⟩ a == 1#)

      AffineSpan : Subtype V (ℓ-max* 4 ℓK ℓV ℓI₁ (ℓ-suc ℓI₂))
      AffineSpan v = isLinearCombination v , squash

      isSpanning : Type _
      isSpanning = isFullSubtype LinearSpan

      isBasis : Type _
      isBasis = isSpanning × LinearlyIndependent ℓI₂

  Basis : (ℓI : Level) -> Type _
  Basis ℓI = Σ[ I ∈ Type ℓI ] Σ[ family ∈ (I -> V) ] (isBasis family ℓI)
