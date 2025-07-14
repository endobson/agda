{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.pullback where

open import base
open import cubical
open import equivalence
open import functions
open import equality-path
open import equality.square
open import equality.null-homotopic
open import pullback
open import isomorphism
open import pointed.base
open import pointed.function
open import pointed.loop-space


module _ {ℓA ℓB ℓC : Level}
  {A∙@(A , ★A) : Type∙ ℓA} {B∙@(B , ★B) : Type∙ ℓB} {C∙ : Type∙ ℓC}
  (f∙@(->∙-cons f fp) : A∙ ->∙ C∙)
  (g∙@(->∙-cons g gp) : B∙ ->∙ C∙)
  where

  Pullback∙ : Type∙ (ℓ-max* 3 ℓA ℓB ℓC)
  Pullback∙ = Pullback f g , (★A , ★B , fp >=> sym gp)

-- Pullback∙ : {ℓA ℓB : Level} -> (A : Type∙ ℓA) (B : Type∙ ℓB) -> Type∙ (ℓ-max ℓA ℓB)
-- PullBack∙ (A , ★A) (B , ★B) = Pull


point->∙ᵉ : {ℓA : Level} -> (A∙ : Type∙ ℓA) -> (Top∙ ->∙ A∙)
point->∙ᵉ _ = const->∙

point->∙ : {ℓA : Level} -> {A∙ : Type∙ ℓA} -> (Top∙ ->∙ A∙)
point->∙ = const->∙

module _ {ℓA ℓB : Level}
  {A∙@(A , ★A) : Type∙ ℓA} {B∙@(B , ★B) : Type∙ ℓB}
  (f∙@(->∙-cons f fp) : A∙ ->∙ B∙)
  where

  fiber∙-Pullback-eq∙ : fiber∙ f∙ ≃∙ Pullback∙ f∙ point->∙
  fiber∙-Pullback-eq∙ = isoToEquiv (iso for back (\_ -> refl) (\_ -> refl)) , for-path
    where
    for : ⟨ fiber∙ f∙ ⟩ -> ⟨ Pullback∙ f∙ point->∙ ⟩
    for (a , fa=b) = (a , tt , fa=b)

    back : ⟨ Pullback∙ f∙ point->∙ ⟩ -> ⟨ fiber∙ f∙ ⟩
    back (a , _ , fa=b) = (a , fa=b)

    for-path : for (snd (fiber∙ f∙)) == snd (Pullback∙ f∙ point->∙)
    for-path k = ★A , tt , compPath-refl-right fp (~ k)


module _ {ℓA : Level} (A∙@(A , ★A) : Type∙ ℓA)
  where
  Ω-Pullback-eq∙ : Ω A∙ ≃∙ Pullback∙ (point->∙ᵉ A∙) (point->∙ᵉ A∙)
  Ω-Pullback-eq∙ = isoToEquiv (iso for back (\_ -> refl) (\_ -> refl)) ,
                   for-path
    where
    P : Type ℓA
    P = ⟨ Pullback∙ (point->∙ᵉ A∙) (point->∙ᵉ A∙) ⟩

    for : ⟨ Ω A∙ ⟩ -> P
    for a=a = (tt , tt , a=a)
    back : P -> ⟨ Ω A∙ ⟩
    back (_ , _ , a=a) = a=a

    for-path : (tt , tt , refl) == (tt , tt , refl >=> refl)
    for-path k = tt , tt , compPath-refl-right refl (~ k)


{-

module _ {ℓA ℓB : Level} {A∙@(A , ★A) : Type∙ ℓA} {B∙@(B , ★B) : Type∙ ℓB} (magic : Magic) where
  fiber∙-Ωf-eq∙₂ : (f : A∙ ->∙ B∙) -> fiber∙ (Ωf f) ≃∙ Ω (fiber∙ f)
  fiber∙-Ωf-eq∙₂ f∙@(->∙-cons f fp) =
    (step₁ >≃∙> (step₃ >≃∙> step₂'))
    where
    step₁ : fiber∙ (Ωf f∙) ≃∙ Pullback∙ (Ωf f∙) point->∙
    step₁ = fiber∙-Pullback-eq∙ (Ωf f∙)

    step₂ : Ω (fiber∙ f∙) ≃∙ Pullback∙ (point->∙ᵉ (fiber∙ f∙)) (point->∙ᵉ (fiber∙ f∙))
    step₂ = Ω-Pullback-eq∙ (fiber∙ f∙)

    step₂' : Pullback∙ (point->∙ᵉ (fiber∙ f∙)) (point->∙ᵉ (fiber∙ f∙)) ≃∙ Ω (fiber∙ f∙)
    step₂' = equiv⁻¹ eq , cong (eqInv eq) (sym (snd step₂)) >=> eqRet eq _
      where
      eq = (fst step₂)

    P₁ = Pullback∙ (Ωf f∙) point->∙
    P₂ = Pullback∙ (point->∙ᵉ (fiber∙ f∙)) (point->∙ᵉ (fiber∙ f∙))

    rotate-for : ⟨ P₁ ⟩ -> ⟨ P₂ ⟩
    rotate-for (a=a , tt , p) = (tt , tt , (\i -> a=a i , p₃ i))
      where
      p₂ : Square (cong f a=a) (sym fp ∙∙ cong f a=a ∙∙ fp) (\i -> fp i) (\i -> fp i)
      p₂ = doubleCompPath-filler (sym fp) (cong f a=a) fp

      p₃ : Square fp fp (cong f a=a) refl
      p₃ = ▪ᵀ (transP-left p₂ p)


    rotate-back : ⟨ P₂ ⟩ -> ⟨ P₁ ⟩
    rotate-back (tt , tt , q) = q₁ , tt , q₂
      where
      q₁ : ★A == ★A
      q₁ = cong fst q

      q₂ : (sym fp ∙∙ cong f q₁ ∙∙ fp) == refl
      q₂ = transP-sym (symP (doubleCompPath-filler (sym fp) (cong f q₁) fp))
                      (▪ᵀ (\i -> snd (q i)))

    fb : ∀ x -> rotate-for (rotate-back x) == x
    fb = magic
    bf : ∀ x -> rotate-back (rotate-for x) == x
    bf = magic

    step₃ : Pullback∙ (Ωf f∙) point->∙ ≃∙ Pullback∙ (point->∙ᵉ (fiber∙ f∙)) (point->∙ᵉ (fiber∙ f∙))
    step₃ = isoToEquiv (iso rotate-for rotate-back fb bf) , magic
-}


private
  module _ {ℓA : Level} {A : I -> Type ℓA} {a₀ : A i0} {a₁ a₁' : A i1}
    (p : PathP A a₀ a₁) (q : a₁ == a₁') where

    transP-lemma₁ : transP-sym (symP p) (transP-left p q) == q
    transP-lemma₁ =
      (\k -> transP-sym (\i -> (p (~ i ∨ k)))
               (transP-left (\i -> (p (i ∨ k))) q)) >=>
      cong (transP-sym refl) (compPath-refl-left q) >=>
      (\k -> transP-sides refl (\i -> q (i ∧ k)) (\i -> q (i ∨ k))) >=>
      transP-sides-filler refl q refl

  module _ {ℓA : Level} {A : I -> Type ℓA} {a₀ : A i0} {a₁ a₁' : A i1}
    (p : PathP A a₀ a₁) (q : PathP A a₀ a₁') where

    transP-lemma₂ : (transP-left p (transP-sym (symP p) q)) == q
    transP-lemma₂ = check₄
      where
      invert : PathP (\j -> p (~ j) == q (~ j)) (transP-sym (symP p) q) (reflᵉ a₀)
      invert = transP-sides-filler (symP p) refl q

      check₂ : PathP (\j -> PathP (\i -> A (i ∧ ~ j)) a₀ (q (~ j)))
                     (transP-mid refl p (transP-sym (symP p) q))
                     (transP-mid refl refl refl)
      check₂ j = (transP-mid refl (\i -> p (i ∧ ~ j)) (invert j))

      check₃ : PathP (\j -> PathP (\i -> A (i ∧ j)) a₀ (q j))
                     (transP-mid refl refl refl)
                     (transP-mid refl q refl)
      check₃ j = (transP-mid refl (\i -> q (i ∧ j)) refl)

      check₄ : (transP-mid refl p (transP-sym (symP p) q)) ==
               q
      check₄ = transP-sym check₂ check₃ >=> sym (transP-mid-filler refl q refl)


module _ {ℓA ℓB : Level} {A∙@(A , ★A) : Type∙ ℓA} {B∙@(B , ★B) : Type∙ ℓB}
         (f∙@(->∙-cons f fp) : A∙ ->∙ B∙) where
  private
    for : ⟨ fiber∙ (Ωf f∙) ⟩ -> ⟨ Ω (fiber∙ f∙) ⟩
    for (a=a , p) = \i -> a=a i , p₃ i
      where
      p₂ : Square (cong f a=a) (sym fp ∙∙ cong f a=a ∙∙ fp) (\i -> fp i) (\i -> fp i)
      p₂ = doubleCompPath-filler (sym fp) (cong f a=a) fp

      p₃ : Square fp fp (cong f a=a) refl
      p₃ = ▪ᵀ (transP-left p₂ p)

    back : ⟨ Ω (fiber∙ f∙) ⟩ -> ⟨ fiber∙ (Ωf f∙) ⟩
    back q = q₁ , q₂
      where
      q₁ : ★A == ★A
      q₁ = cong fst q

      q₂ : (sym fp ∙∙ cong f q₁ ∙∙ fp) == refl
      q₂ = transP-sym (symP (doubleCompPath-filler (sym fp) (cong f q₁) fp))
                      (▪ᵀ (\i -> snd (q i)))

    bf : ∀ x -> back (for x) == x
    bf (a=a , p) k = a=a , transP-lemma₁ (doubleCompPath-filler (sym fp) (cong f a=a) fp) p k
    fb : ∀ x -> for (back x) == x
    fb q k = \i -> q₁ i , lemma k i
      where
      q₁ : ★A == ★A
      q₁ = cong fst q

      q₂ : PathP (\i -> f (q₁ i) == ★B) fp fp
      q₂ = cong snd q
      dp = (doubleCompPath-filler (sym fp) (cong f q₁) fp)

      lemma : ▪ᵀ (transP-left dp (transP-sym (symP dp) (▪ᵀ q₂))) == q₂
      lemma = cong ▪ᵀ (transP-lemma₂ (doubleCompPath-filler (sym fp) (cong f q₁) fp) (▪ᵀ q₂))

    for★ : for (refl , compPath-sym (sym fp)) == refl
    for★ = \k i -> ★A , ans k i
      where

      Ans : ∀ {ℓ : Level} {A : Type ℓ} {a₀} (a₁ : A) (q : a₀ == a₁) -> Type ℓ
      Ans {a₀ = a₀} a₁ q =
        Path (PathP (\i -> q i == q i) (reflᵉ a₀) (reflᵉ a₁))
         (transP-left
           (doubleCompPath-filler (sym q) refl q)
           (compPath-sym (sym q)))
         (\j i -> q j)

      ans-refl : ∀ {ℓ : Level} {A : Type ℓ} (a₀ : A) -> Ans a₀ refl
      ans-refl a₀ = sub-ans
        where
        q = reflᵉ a₀
        left : PathP (\i -> q i == q i) (reflᵉ a₀) (reflᵉ a₀)
        left =
          (transP-left
            (doubleCompPath-filler (sym q) refl q)
            (compPath-sym (sym q)))

        left₂ : Path (a₀ == a₀) (reflᵉ a₀) (reflᵉ a₀)
        left₂ =
          ((doubleCompPath-filler (sym q) refl q) ∙∙
           refl ∙∙
           (compPath-sym (sym q)))

        step : left == left₂
        step k =
          ((\i -> doubleCompPath-filler (sym q) refl q (i ∧ k)) ∙∙
           (\i -> doubleCompPath-filler (sym q) refl q (i ∨ k)) ∙∙
           (compPath-sym (sym q)))

        left₂-refl : left₂ == refl
        left₂-refl = compPath-sym _

        sub-ans : left == refl
        sub-ans = step >=> left₂-refl


      step₁ : ∀ {ℓ : Level} {A : Type ℓ} {a₀ a₁ : A} (q : a₀ == a₁) ->
        Path (PathP (\i -> q i == q i) (reflᵉ a₀) (reflᵉ a₁))
         (transP-left
           (doubleCompPath-filler (sym q) refl q)
           (compPath-sym (sym q)))
         (\j i -> q j)
      step₁ {ℓ} {A} {a₀} {a₁} q = J Ans (ans-refl a₀) q


      ans : Path (fp == fp)
             (▪ᵀ (transP-left
                    (doubleCompPath-filler (sym fp) refl fp)
                    (compPath-sym (sym fp))))
             refl
      ans = cong ▪ᵀ (step₁ fp)

    back★ : back refl == (refl , compPath-sym (sym fp))
    back★ = \k -> refl , ans k
      where
      Ans : ∀ {ℓ : Level} {A : Type ℓ} {a₀} (a₁ : A) (p : a₀ == a₁) -> Type ℓ
      Ans {a₀ = a₀} a₁ p =
        Path ((sym p ∙∙ refl ∙∙ p) == refl)
          (transP-sym (symP (doubleCompPath-filler (sym p) refl p))
                      (\i j -> p i))
          (compPath-sym (sym p))

      Ans-refl : ∀ {ℓ : Level} {A : Type ℓ} (a : A) -> Ans a refl
      Ans-refl _ =
        transP-sides->∙∙ ∙∙-refl refl refl >=>
        compPath-refl-right ∙∙-refl

      ans : Ans _ fp
      ans = J Ans (Ans-refl _) fp




  fiber∙-Ωf-eq∙₃ : fiber∙ (Ωf f∙) ≃∙ Ω (fiber∙ f∙)
  fiber∙-Ωf-eq∙₃ = isoToEquiv (iso for back fb bf) , for★

  fiber∙-Ωf-eq∙₄ : Ω (fiber∙ f∙) ≃∙ fiber∙ (Ωf f∙)
  fiber∙-Ωf-eq∙₄ = isoToEquiv (iso back for bf fb) , back★

  fiber∙-Ωf-eq∙₄-∙Tri :
    ->∙Tri (->∙-cons (fst (fst fiber∙-Ωf-eq∙₄))
                     (snd fiber∙-Ωf-eq∙₄))
           (Ωf (->∙-cons fst refl))
           (->∙-cons fst refl)
  fiber∙-Ωf-eq∙₄-∙Tri = [ ans ]
    where
    left : Ω (fiber∙ f∙) ->∙ Ω A∙
    left = (Ωf (->∙-cons fst refl))

    left' : Ω (fiber∙ f∙) ->∙ Ω A∙
    left' = ->∙-cons (\ap -> sym refl ∙∙ cong fst ap ∙∙ refl)
                     ∙∙-refl

    center : Ω (fiber∙ f∙) ->∙ Ω A∙
    center = ->∙-cons (\ap -> cong fst ap) refl

    left-path : left == center
    left-path k =
      ->∙-cons (\ap -> doubleCompPath-filler refl (cong fst ap) refl (~ k))
               (\i -> ∙∙-refl (i ∨ k))

    right : Ω (fiber∙ f∙) ->∙ Ω A∙
    right =
      (->∙-cons (fst (fst fiber∙-Ωf-eq∙₄))
                     (snd fiber∙-Ωf-eq∙₄)) >∙>
      (->∙-cons fst refl)

    right-path : center == right
    right-path k = ->∙-cons (\ap -> cong fst ap) (∙∙-refl (~ k))


    right' : Ω (fiber∙ f∙) ->∙ Ω A∙
    right' =
      ->∙-cons
        (\ap -> cong fst ap)
        (refl >=> refl)

    check-right : right == right'
    check-right = refl
    check-left : left == left'
    check-left = refl

    ans : left == right
    ans = left-path >=> right-path
