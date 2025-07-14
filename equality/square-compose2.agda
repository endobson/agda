{-# OPTIONS --cubical --safe --exact-split #-}

module equality.square-compose2 where


open import base
open import pointed.base
open import cubical
open import equality-path
open import equality.square
open import base
open import funext
open import isomorphism
open import sigma

open import additive-group
open import additive-group.instances.nat
open import cubical
open import equality-path
open import equality.square
open import equality.square-compose
open import equality.path-composition-equivalence
open import connected
open import hlevel.base
open import hlevel.pi
open import pointed.base
open import pointed.loop-space
open import truncation.generic
open import truncation.generic.map
open import equivalence.base
open import equivalence
open import connected.wedge




module square-path1 {ℓ : Level} {A : Type ℓ} {n s : A} (p q : n == s) where
  private
    pq : n == n
    pq = p ∙∙ refl ∙∙ sym q


    sq₁ : Square (reflᵉ n) pq (reflᵉ n) pq
    sq₁ i j = pq (i ∧ j)

    sq₃ : Square refl pq refl pq
    sq₃ = ▪comp (\i j -> (p ∙∙ refl ∙∙ sym q) (i ∧ j))
                (\i j -> n)
                (\i j -> (p ∙∙ refl ∙∙ sym q) j)
                (\i j -> n)
                (\i j -> (p ∙∙ refl ∙∙ sym q) i)


    sq₂ : Square refl pq refl pq
    sq₂ = ▪comp (reflᵉ (reflᵉ s))
                (\i j -> p i)
                (\i j -> doubleCompPath-filler p refl (sym q) i j)
                (\i j -> p j)
                (\i j -> doubleCompPath-filler p refl (sym q) j i)

    west-sideP :
      PathP (\k -> Square (reflᵉ n) (reflᵉ (p k)) (\i -> p (i ∧ k)) (\i -> p (i ∧ k)))
            (\i j -> n) (\i j -> p i)
    west-sideP k i j = p (i ∧ k)


    south-sideP :
      PathP (\k -> Square (\j -> p (j ∧ k)) (\j -> p (j ∧ k)) (reflᵉ n) (reflᵉ (p k)))
            (\i j -> n) (\i j -> p j)
    south-sideP k i j = p (j ∧ k)

    north-sideP :
      PathP (\k -> Square (\j -> p (~ j ∧ k)) (\j -> q (~ j ∧ k))
                   (\i -> doubleCompPath-filler p refl (sym q) (~ k) i)
                   pq)
        (\i j -> pq i)
        (\i j -> doubleCompPath-filler p refl (sym q) j i)
    north-sideP k i j = doubleCompPath-filler p refl (sym q) (~ k ∨ j) i

    east-sideP :
      PathP (\k -> Square (\j -> doubleCompPath-filler p refl (sym q) (~ k) j) pq
                          (\i -> p (~ i ∧ k)) (\i -> q (~ i ∧ k)) )
        (\i j -> (p ∙∙ refl ∙∙ sym q) j)
        (\i j -> doubleCompPath-filler p refl (sym q) i j)
    east-sideP k i j = north-sideP k j i



    centerP : PathP (\k -> Square (\j -> (p k))
                                   (\j -> doubleCompPath-filler p refl (sym q) (~ k) j)
                                   (\i -> p k)
                                   (\i -> doubleCompPath-filler p refl (sym q) (~ k) i))
                    (\i j -> (p ∙∙ refl ∙∙ sym q) (i ∧ j))
                    (\i j -> s)
    centerP =
      transP-mid
        (sym (rotate-square-ABCR->RBCA/reflᵉ (p ∙∙ refl ∙∙ sym q)))
        (\k -> (rotate-square-ABCR->RBCA (centerP'₂ k)))
        (rotate-square-ABCR->RBCA/reflᵉ (reflᵉ s))
      where
      centerP'₂ : PathP (\k -> Square (\j -> doubleCompPath-filler p refl (sym q) (~ k) j)
                                      (\j -> doubleCompPath-filler p refl (sym q) (~ k) j)
                                      (\i -> p k)
                                      (\i -> q k))
                      (\i j -> (p ∙∙ refl ∙∙ sym q) j)
                      (\i j -> s)
      centerP'₂ k i j = doubleCompPath-filler p refl (sym q) (~ k) j





    sq₁=sq₃ : sq₁ == sq₃
    sq₁=sq₃ = sym (▪comp-refl sq₁)

    sq₃=sq₂ : Path (Square refl pq refl pq) sq₃ sq₂
    sq₃=sq₂ k =
      ▪comp (\i j -> centerP k i j)
            (\i j -> west-sideP k i j)
            (\i j -> east-sideP k i j)
            (\i j -> south-sideP k i j)
            (\i j -> north-sideP k i j)


  lemma : sq₁ == sq₂
  lemma = sq₁=sq₃ >=> sq₃=sq₂





module square-path2 {ℓ : Level} {A : Type ℓ} {n s : A} (p : n == s) (magic : Magic) where
  private
    sq₁ : Square p (p >=> (reflᵉ s)) (reflᵉ n) (reflᵉ s)
    sq₁ i j = compPath-refl-right p (~ i) j


    sq₂ : Square (reflᵉ s) (p >=> (reflᵉ s)) (sym p) (reflᵉ s)
    sq₂ i j = doubleCompPath-filler p refl refl i j


  lemma : PathP (\k -> Square (\j -> p (j ∨ k)) (p >=> (reflᵉ s)) (\i -> p (~ i ∧ k)) (reflᵉ s)) sq₁ sq₂
  lemma = magic
