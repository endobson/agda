{-# OPTIONS --cubical --safe --exact-split #-}

module functions.embedding.fin where

open import base
open import equality-path
open import equivalence
open import equivalence.injective-surjective
open import fin
open import fin-algebra
open import functions
open import functions.embedding
open import functions.embedding.sum
open import funext
open import hlevel
open import nat
open import sum

module _ {ℓA : Level} {A : Type ℓA} where
  opaque
    isEmbedding-fin-rec : {n : Nat} {a : A} {f : Fin n -> A} ->
      isProp (a == a) -> isEmbedding f -> ¬ (fiber f a) -> isEmbedding (fin-rec a f)
    isEmbedding-fin-rec {n} {a} {f} isProp-=a embed-f ¬fib-a =
      subst isEmbedding (sym f'-path2) isEmbed-f'
      where
      Top->a : Top -> A
      Top->a _ = a

      hasPropFibers-Top->a : ∀ a2 -> isProp (fiber Top->a a2)
      hasPropFibers-Top->a a2 (tt , p1) (tt , p2) = \i -> tt , (\j -> ans j i)
        where
        ans : PathP (\i -> (p1 i) == (p2 i)) (reflᵉ a) (reflᵉ a2)
        ans = transP-right (isProp-=a _ _)
                           (symP (doubleCompPath-filler p1 (reflᵉ a2) (sym p2)))
      isEmbedding-Top->a : isEmbedding Top->a
      isEmbedding-Top->a = eqInv isEmbedding-eq-hasPropFibers hasPropFibers-Top->a

      f1 : Top ⊎ Fin n -> A
      f1 = either (\_ -> a) f
      isEmbed-f1 : isEmbedding f1
      isEmbed-f1 =
        isEmbedding-either isEmbedding-Top->a embed-f
          (\_ i p -> ¬fib-a (i , sym p))


      f2 : Fin (suc n) -> Top ⊎ Fin n
      f2 = eqFun (Fin-suc-⊎-eq n)
      isEmbed-f2 : isEmbedding f2
      isEmbed-f2 = isEquiv->isEmbedding (snd (Fin-suc-⊎-eq n))

      f' : Fin (suc n) -> A
      f' = f1 ∘ f2

      isEmbed-f' : isEmbedding f'
      isEmbed-f' = ∘-isEmbedding isEmbed-f1 isEmbed-f2

      f'-path1 : f == f' ∘ suc-fin
      f'-path1 = funExt (\i -> cong f (fin-i-path refl))

      f'-path2 : fin-rec a f == f'
      f'-path2 = cong (fin-rec a) f'-path1 >=> fin-rec-reduce f'

opaque
  isEmbedding-suc-fin : {n : Nat} -> isEmbedding (suc-fin {n = n})
  isEmbedding-suc-fin {n} = isSet-isInjective->isEmbedding isSetFin isInjective-suc-fin
    where
    isInjective-suc-fin : isInjective (suc-fin {n = n})
    isInjective-suc-fin path = fin-i-path (cong pred (cong Fin.i path))
