{-# OPTIONS --cubical --safe --exact-split #-}

module finset.injective where

open import base
open import equality-path
open import equivalence
open import fin
open import finset
open import functions
open import functions.embedding
open import hlevel.base
open import isomorphism
open import nat
open import new-permutation
open import truncation

private
  opaque
    fin-isInjective->isEquiv :
      {n₁ n₂ : ℕ} {f : Fin n₁ -> Fin n₂} -> (n₁ == n₂) ->
      isInjective f -> isEquiv f
    fin-isInjective->isEquiv {n₁} {n₂} {f} p isInjective-f =
      subst isEquiv f''=f isEquiv-f''
      where
      e : Fin n₁ ≃ Fin n₂
      e = pathToEquiv (cong Fin p)

      f' : Fin n₁ -> Fin n₁
      f' = eqInv e ∘ f

      f'' : Fin n₁ -> Fin n₂
      f'' = eqFun e ∘ eqInv e ∘ f

      f''=f : f'' == f
      f''=f i x = eqSec e (f x) i

      isInjective-f' : isInjective f'
      isInjective-f' = ∘-isInjective (isEmbedding->isInjective (isEquiv->isEmbedding (snd (equiv⁻¹ e))))
                                     isInjective-f

      isEquiv-f' : isEquiv f'
      isEquiv-f' = snd (isoToEquiv (fin-injective->permutation f' isInjective-f'))


      isEquiv-f'' : isEquiv f''
      isEquiv-f'' = ∘-isEquiv (snd e) isEquiv-f'



module _ {ℓA ℓB : Level}
  (FA@(A , fsA) : FinSet ℓA)
  (FB@(B , fsB) : FinSet ℓB)
  (cp : cardinality FA == cardinality FB)
  {f : A -> B}
  (inj-f : isInjective f)
  where
  private
    fsA' : isFinSetΣ A
    fsA' = isFinSet->isFinSetΣ fsA
    fsB' : isFinSetΣ B
    fsB' = isFinSet->isFinSetΣ fsB

    cA : ℕ
    cA = fst fsA'
    cB : ℕ
    cB = fst fsB'

    module _ (eqA : A ≃ Fin cA) (eqB : B ≃ Fin cB) where

      g : Fin cA -> Fin cB
      g = eqFun eqB ∘ f ∘ eqInv eqA

      f' : A -> B
      f' = eqInv eqB ∘ eqFun eqB ∘ f ∘ eqInv eqA ∘ eqFun eqA

      f'=f : f' == f
      f'=f i x = eqRet eqB (f (eqRet eqA x i)) i

      isInjective-eqBf : isInjective (eqFun eqB)
      isInjective-eqBf = isEmbedding->isInjective (isEquiv->isEmbedding (snd eqB))
      isInjective-eqAi : isInjective (eqInv eqA)
      isInjective-eqAi = isEmbedding->isInjective (isEquiv->isEmbedding (snd (equiv⁻¹ eqA)))

      isInjective-g : isInjective g
      isInjective-g = ∘-isInjective isInjective-eqBf (∘-isInjective inj-f isInjective-eqAi)

      isEquiv-g : isEquiv g
      isEquiv-g = fin-isInjective->isEquiv cp isInjective-g

      isEquiv-f' : isEquiv f'
      isEquiv-f' = ∘-isEquiv (snd (equiv⁻¹ eqB)) (∘-isEquiv isEquiv-g (snd eqA))

      isEquiv-f : isEquiv f
      isEquiv-f = subst isEquiv f'=f isEquiv-f'




  opaque
    FinSet-isInjective->isEquiv : isEquiv f
    FinSet-isInjective->isEquiv = unsquash isProp-isEquiv (∥-map2 isEquiv-f (snd fsA') (snd fsB'))
