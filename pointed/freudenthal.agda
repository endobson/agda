{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.freudenthal where

open import base
open import additive-group
open import additive-group.instances.nat
open import cubical
open import equality-path
open import equality.square
open import connected
open import hlevel.base
open import hlevel.pi
open import pointed.base
open import pointed.loop-space
open import pointed.suspension
open import truncation.generic
open import equivalence.base
open import univalence
open import connected.wedge


module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) where
  ΩΣf : A -> ⟨ Ω (Susp∙ A∙) ⟩
  ΩΣf a = meridian a >=> sym (meridian ★A)


module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) {n : Nat} (cA : isConnectedₙ n A) (magic : Magic) where


  private
    encode : ∀ (s : Susp A) -> (north == s) -> Type ℓ
    encode north p = Squashₙ (suc (suc (n + n))) (fiber (ΩΣf A∙) p)
    encode south p = Squashₙ (suc (suc (n + n))) (fiber meridian p)
    encode (meridian a₁ i) = ans i
      where
      tp : PathP (\i -> (north == meridian a₁ i) -> Type ℓ)
                 (encode north)
                 (\q -> encode north (transport (\i -> north == meridian a₁ (~ i)) q))
      tp j q = encode north (transp (\i -> north == meridian a₁ (~ i ∧ j)) (~ j) q)

      step₁ : ∀ (q : (north == south)) ->
        Path (Type ℓ)
          (encode north (transport (\i -> north == meridian a₁ (~ i)) q))
          (encode south q)
      step₁ q = ua eq
        where
        eq : (encode north (transport (\i -> north == meridian a₁ (~ i)) q)) ≃
             (encode south q)
        eq = magic
          where
          for' : (fiber (ΩΣf A∙) (transport (\i -> north == meridian a₁ (~ i)) q)) ->
                 (encode south q)
          for' (a₂ , sq) = f sq₂
            where
            sq₂ : (meridian a₂ >=> sym (meridian ★A)) ==
                  q >=> sym (meridian a₁)
            sq₂ = sq >=> sq-p
              where
              sq-p : (transport (\i -> north == meridian a₁ (~ i)) q) ==
                     q >=> sym (meridian a₁)
              sq-p =
                (transP-sym (symP (transport-filler (\i -> north == (meridian a₁ (~ i))) q))
                            (doubleCompPath-filler refl q (sym (meridian a₁)))) >=>
                (\j -> (\i -> q (i ∧ j)) ∙∙ (\i -> q (i ∨ j)) ∙∙ sym (meridian a₁))

            P : A -> A -> Type ℓ
            P a₁ a₂ =
              ((meridian a₂ >=> sym (meridian ★A)) == q >=> sym (meridian a₁)) ->
              (encode south q)

            hP : ∀ a₁ a₂ -> isOfHLevel (suc (suc (n + n))) (P a₁ a₂)
            hP a₁ a₂ =
              isOfHLevelΠ (suc (suc (n + n))) (\_ -> isOfHLevel-Squashₙ (suc (suc (n + n))))

            f₁ : ∀ a -> P a ★A
            f₁ a p = ∣ a , ma=q ∣
              where
              p' : refl == q >=> sym (meridian a)
              p' = sym (compPath-sym (meridian ★A)) >=> p

              ma=q : (meridian a) == q
              ma=q = sym (▪ᵀ (transP-right p' (symP (doubleCompPath-filler _ _ _))))

            f₂ : ∀ a -> P ★A a
            f₂ a p = ∣ a , ma=q ∣
              where
              p' : (meridian a >=> sym (meridian ★A)) >=> meridian ★A ==
                   (q >=> sym (meridian ★A)) >=> meridian ★A
              p' = (\i -> p i >=> meridian ★A)

              ma=q : meridian a == q
              ma=q =
                sym (compPath-assoc _ _ _ >=>
                     cong (meridian a >=>_) (compPath-sym _) >=>
                     compPath-refl-right _) ∙∙
                p' ∙∙
                (compPath-assoc _ _ _ >=>
                 cong (q >=>_) (compPath-sym _) >=>
                 compPath-refl-right _)

            fp' : ∀ p -> f₁ ★A p == f₂ ★A p
            fp' p = \i -> ∣ ★A , l=r i ∣
              where

              check-p : (meridian ★A >=> sym (meridian ★A)) ==
                        (q >=> sym (meridian ★A))
              check-p = p

              left : meridian ★A == q
              left =
                sym (▪ᵀ (transP-right (sym (compPath-sym (meridian ★A)) >=> p)
                                      (symP (doubleCompPath-filler q refl (sym (meridian ★A))))))

              right : meridian ★A == q
              right =
                sym (compPath-assoc _ _ _ >=>
                     cong (meridian ★A >=>_) (compPath-sym (sym (meridian ★A))) >=>
                     compPath-refl-right _) ∙∙
                (\i -> p i >=> meridian ★A) ∙∙
                (compPath-assoc _ _ _ >=>
                 cong (q >=>_) (compPath-sym (sym (meridian ★A))) >=>
                 compPath-refl-right _)





              l=r : left == right
              l=r = magic


            fp : f₁ ★A == f₂ ★A
            fp i p = fp' p i





            f : ((meridian a₂ >=> sym (meridian ★A)) == q >=> sym (meridian a₁)) ->
                (encode south q)
            f = fst (extend-raw-wedge A∙ A∙ cA cA P hP f₁ f₂ fp) a₁ a₂








          for : (encode north (transport (\i -> north == meridian a₁ (~ i)) q)) ->
                (encode south q)
          for = ∥ₙ-elim (\_ -> isOfHLevel-Squashₙ (suc (suc (n + n)))) for'



      ans : PathP (\i -> (north == meridian a₁ i) -> Type ℓ) (encode north) (encode south)
      ans = transP-left tp (\i q -> step₁ q i)
