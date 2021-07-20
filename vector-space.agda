{-# OPTIONS --cubical --safe --exact-split #-}

module vector-space where

open import apartness
open import apartness.instances.heyting-field
open import base
open import commutative-monoid
open import finset
open import finite-commutative-monoid
open import functions
open import group
open import heyting-field
open import hlevel
open import monoid
open import ring
open import semiring
open import truncation

private
  variable
    ℓ : Level

module _ {ℓK ℓV : Level} {K : Type ℓK} {S : Semiring K} (R : Ring S) (V : Type ℓV) (ℓA : Level) where
  private
    instance
      IS = S
      IR = R

  record ModuleStr : Type (ℓ-max (ℓ-max ℓK ℓV) (ℓ-suc ℓA)) where
    field
      GroupStr-V : GroupStr V
      TightApartnessStr-V : TightApartnessStr V ℓA

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


module _  {ℓK ℓV ℓA : Level} {K : Type ℓK} {S : Semiring K} {R : Ring S} {V : Type ℓV}
          {{M : ModuleStr R V ℓA}} where
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
         (F : Field R) (V : Type ℓV) (ℓA : Level)  where
  private
    instance
      IS = S
      IF = F

  record VectorSpaceStr : Type (ℓ-max (ℓ-max ℓK ℓV) (ℓ-suc ℓA)) where
    constructor vector-space-str
    field
      module-str : ModuleStr R V ℓA

    private
      module MS = ModuleStr module-str

    field
      v*-apart-zero : {k : K} {v : V} -> (k MS.v* v) MS.v# MS.0v -> (k # 0#) × (v MS.v# MS.0v)
      v*-apart-args : {k1 k2 : K} {v1 v2 : V} ->
                      (k1 MS.v* v1) MS.v# (k2 MS.v* v2) ->
                      ∥ (k1 # k2) ⊎ (v1 MS.v# v2) ∥


module _ {ℓK ℓV ℓA : Level} {K : Type ℓK} {S : Semiring K} {R : Ring S} {F : Field R} {V : Type ℓV}
         (VS : VectorSpaceStr F V ℓA) where

  private
    module VS = VectorSpaceStr VS
    module M = ModuleStr VS.module-str

    instance
      IM = VS.module-str
      IS = S
      IF = F
      IVA = ModuleStr.TightApartnessStr-V IM

  private
    variable
      I : Type ℓ

  private
    CommMonoid-V+ : CommMonoid V
    CommMonoid-V+ = GroupStr.comm-monoid M.GroupStr-V

  vector-sum : (I -> V) -> isFinSet I -> V
  vector-sum vs fs = finiteMerge CommMonoid-V+ M.isSet-V (_ , fs) vs

  private

    module _ {ℓI₁ : Level} {I₁ : Type ℓI₁} (family : I₁ -> V) where
      FinSubset : (ℓI₂ : Level) -> Type (ℓ-max (ℓ-suc ℓI₂) ℓI₁)
      FinSubset ℓI₂ =
        Σ[ I₂ ∈ (FinSet ℓI₂) ] Σ[ f ∈ (⟨ I₂ ⟩ -> I₁) ] (Injective f)


  module _ {ℓI₁ : Level} {I₁ : Type ℓI₁} (family : I₁ -> V) where
    private
      Carrier : {ℓI₂ : Level} -> FinSubset family ℓI₂ -> Type ℓI₂
      Carrier ((T , _) , _) = T

      isFinSet-Carrier : {ℓI₂ : Level} -> (S : FinSubset family ℓI₂) -> isFinSet (Carrier S)
      isFinSet-Carrier ((_ , fs) , _) = fs

      include : {ℓI₂ : Level} -> (S : FinSubset family ℓI₂) -> Carrier S -> I₁
      include (_ , f , _) = f

      scaled-vector-sum : {ℓI₂ : Level} -> (S : FinSubset family ℓI₂) -> (a : Carrier S -> K) -> V
      scaled-vector-sum S a = vector-sum (\i -> (a i) v* (family (include S i))) (isFinSet-Carrier S)

    LinearlyDependent : (ℓI₂ : Level) -> Type (ℓ-max (ℓ-max ℓK (ℓ-max ℓI₁ ℓV)) (ℓ-suc ℓI₂))
    LinearlyDependent ℓI₂ =
      ∃[ S ∈ FinSubset family ℓI₂ ]
      Σ[ a ∈ (Carrier S -> K) ] (scaled-vector-sum S a == 0v ×
                                 Σ[ i ∈ Carrier S ] (a i # 0#))

    LinearlyIndependent : (ℓI₂ : Level) -> Type (ℓ-max (ℓ-max ℓK (ℓ-max ℓI₁ ℓV)) (ℓ-suc ℓI₂))
    LinearlyIndependent ℓI₂ =
      (S : FinSubset family ℓI₂) -> (a : Carrier S -> K) ->
      scaled-vector-sum S a == 0v ->
      (i : Carrier S) -> a i == 0#

    LinearlyFree : (ℓI₂ : Level) -> Type (ℓ-max (ℓ-max ℓK (ℓ-max ℓI₁ ℓA)) (ℓ-suc ℓI₂))
    LinearlyFree ℓI₂ =
      (S : FinSubset family ℓI₂) -> (a : Carrier S -> K) ->
      ∃[ i ∈ Carrier S ] (a i # 0#) ->
      scaled-vector-sum S a # 0v

    LinearlyFree->LinearlyIndependent : {ℓI₂ : Level} -> LinearlyFree ℓI₂ -> LinearlyIndependent ℓI₂
    LinearlyFree->LinearlyIndependent free S a sum0 i =
      tight-# (\ai#0 -> irrefl-path-# sum0 (free S a ∣ (i , ai#0) ∣))

    LinearlyIndependent->¬LinearlyDependent :
      {ℓI₂ : Level} -> LinearlyIndependent ℓI₂ -> ¬ (LinearlyDependent ℓI₂)
    LinearlyIndependent->¬LinearlyDependent {ℓI₂} indep dep =
      unsquash isPropBot (∥-map handle dep)
      where
      handle : Σ[ S ∈ FinSubset family ℓI₂ ]
               Σ[ a ∈ (Carrier S -> K) ] (scaled-vector-sum S a == 0v ×
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
