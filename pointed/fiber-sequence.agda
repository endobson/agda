{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.fiber-sequence where

open import base
open import cubical
open import equality-path
open import equivalence
open import pointed.base
open import univalence
open import isomorphism
open import pointed.loop-space


module FiberSequence 
  {ℓ : Level} {A∙@(A , ★A) : Type∙ ℓ} {B∙@(B , ★B) : Type∙ ℓ} 
  (f0∙ : A∙ ->∙ B∙)
  where

  Ty∙ : Nat -> Type∙ ℓ
  Ty : Nat -> Type ℓ
  ★ⁿ : (n : Nat) -> Ty n
  private
    Σf : Nat -> Σ[ X∙ ∈ Type∙ ℓ ] Σ[ Y∙ ∈ Type∙ ℓ ] (X∙ ->∙ Y∙)
    Ty∙' : Nat -> Type∙ ℓ
    f∙' : (n : Nat) -> (Ty∙' n ->∙ Ty∙ n)

  Ty∙' n = fst (Σf n)
  Ty∙ n = fst (snd (Σf n))
  Ty n = ⟨ Ty∙ n ⟩
  ★ⁿ n = snd (Ty∙ n)
  f∙' n = snd (snd (Σf n))

  Σf 0 = A∙ , B∙ , f0∙
  Σf (suc n) =
    ((fiber (app∙ (f∙' n)) (★ⁿ n)) , (_ , ->∙-path (f∙' n))) , 
    (Ty∙' n) , 
    ->∙-cons fst refl

  f∙ : (n : Nat) -> (Ty∙ (suc n) ->∙ Ty∙ n)
  f∙ = f∙'
  f : (n : Nat) -> (Ty (suc n) -> Ty n)
  f n = app∙ (f∙ n)

  twice-const : ∀ n x -> f n (f (suc n) x) == (★ⁿ n)
  twice-const _ (x , p) = p


  fiber-f1 : fiber (f 1) (★ⁿ 1) == ⟨ Ω (Ty∙ 0) ⟩
  fiber-f1 = isoToPath (iso fwd bkw fb bf)
    where
    fwd : fiber (f 1) (★ⁿ 1) -> ⟨ Ω (Ty∙ 0) ⟩
    fwd ((a , f₀a=★) , p) = (sym (->∙-path f0∙) ∙∙ cong (f 0) (sym p) ∙∙ f₀a=★)

    bkw : ⟨ Ω (Ty∙ 0) ⟩ -> fiber (f 1) (★ⁿ 1)
    bkw p = (★A , ->∙-path f0∙ >=> p) , (reflᵉ ★A)

    fb : ∀ x -> fwd (bkw x) == x
    fb p =
      sym (compPath-assoc _ _ _ ) >=> 
      cong (_>=> p) (compPath-sym _) >=>
      compPath-refl-left _

    bf : ∀ x -> bkw (fwd x) == x
    bf ((a , p) , q) = ans
      where
      step1 : (->∙-path f0∙ >=> (sym (->∙-path f0∙) ∙∙ cong (f 0) (sym q) ∙∙ p)) ==
              (refl >=> (refl ∙∙ cong (f 0) (sym q) ∙∙ p))
      step1 k =
        ((\i -> ->∙-path f0∙ (i ∧ ~ k)) >=> ((\i -> (->∙-path f0∙ (~ i ∧ ~ k))) ∙∙ cong (f 0) (sym q) ∙∙ p))
      step2 : (refl >=> (refl ∙∙ cong (f 0) (sym q) ∙∙ p)) ==
              (refl ∙∙ cong (f 0) (sym q) ∙∙ p)
      step2 = compPath-refl-left _
      step3 : (refl ∙∙ cong (f 0) (sym q) ∙∙ p) ==
              (cong (f 0) (sym q) ∙∙ refl ∙∙ p)
      step3 k = ((\i -> f 0 (q (~ (i ∧ k)))) ∙∙ (\i -> f 0 (q (~ (i ∨ k)))) ∙∙ p)


      ans1 : ((★A , (->∙-path f0∙ >=> (sym (->∙-path f0∙) ∙∙ cong (f 0) (sym q) ∙∙ p))) , refl) ==
             ((★A , cong (f 0) (sym q) >=> p) , refl)
      ans1 k = (★A , (step1 ∙∙ step2 ∙∙ step3) k) , refl

      ans2 : ((★A , cong (f 0) (sym q) >=> p) , refl) ==
             ((a , refl >=> p) , q)
      ans2 k = (q (~ k) , (\i -> f 0 (q (~ i ∧ ~ k))) >=> p) , (\i -> q (i ∨ ~ k))


      ans3 : ((a , refl >=> p) , q) == ((a , p) , q)
      ans3 k = (a , compPath-refl-left p k) , q


      ans : ((★A , (->∙-path f0∙ >=> (sym (->∙-path f0∙) ∙∙ cong (f 0) (sym q) ∙∙ p))) , refl) ==
            ((a , p) , q)
      ans = ans1 ∙∙ ans2 ∙∙ ans3






