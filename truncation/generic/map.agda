{-# OPTIONS --cubical --safe --exact-split #-}

module truncation.generic.map where

open import base
open import equality-path
open import equality.square
open import equivalence.base
open import equivalence
open import funext
open import functions
open import functions.embedding
open import hlevel
open import hlevel.base
open import hlevel.pi
open import pointed.base
open import pointed.loop-space
open import pointed.loop-space.hlevel
open import pointed.spheres
open import pointed.suspension
open import pointed.suspension-loop-eq
open import truncation.generic
open import truncation.generic.path



-- module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} where
--   ∥ₙ-map-preserves-isEquiv : (n : Nat) -> {f : A -> B} -> isEquiv f -> isEquiv (∥ₙ-map f {n})
--   ∥ₙ-map-preserves-isEquiv zero {f} isEq .equiv-proof _ = (lift tt , refl) , (\_ -> refl)
--   ∥ₙ-map-preserves-isEquiv (suc n) {f} isEq .equiv-proof =
--     ∥ₙ-elim
--       (\b -> isProp->isOfHLevelSuc n isProp-isContr)
--       ctr-fibers
--     where
--     ctr-fibers : ∀ b -> isContr (fiber (∥ₙ-map f) ∣ b ∣)
--     ctr-fibers b = transform (fst ctr-base-fibers) , back _
--       where
--       ctr-base-fibers : isContr (fiber f b)
--       ctr-base-fibers = isEq .equiv-proof b
--
--       transform : fiber f b -> fiber (∥ₙ-map f {suc n}) ∣ b ∣
--       transform (a , p) = ∣ a ∣ , (\i -> ∣ p i ∣)
--
--       back : ∀ (c₁ c₂ : fiber (∥ₙ-map f {suc n}) ∣ b ∣) -> c₁ == c₂
--       back (a₁ , p₁) (a₂ , p₂) = ∥ₙ-elim2 {P = P} hP ans a₁ a₂ p₁ p₂
--         where
--         P : Squashₙ (suc n) A -> Squashₙ (suc n) A -> Type (ℓ-max ℓA ℓB)
--         P a₁ a₂ = (p₁ : ∥ₙ-map f a₁ == ∣ b ∣) -> (p₂ : ∥ₙ-map f a₂ == ∣ b ∣) -> (a₁ , p₁) == (a₂ , p₂)
--
--         hP : ∀ a₁ a₂ -> isOfHLevel (suc n) (P a₁ a₂)
--         hP a₁ a₂ = isOfHLevelΠ (suc n) (\_ -> isOfHLevelΠ (suc n) (\_ ->
--                      isOfHLevelPath (suc n) (isOfHLevelΣ (suc n)
--                        (isOfHLevel-Squashₙ (suc n))
--                          (\_ -> isOfHLevelPath (suc n) (isOfHLevel-Squashₙ (suc n)) _ _)) _ _))
--
--         ans : ∀ a₁ a₂ ->
--                (p₁ : ∣ f a₁ ∣ == ∣ b ∣) ->
--                (p₂ : ∣ f a₂ ∣ == ∣ b ∣) ->
--                (∣ a₁ ∣ , p₁) == (∣ a₂ ∣ , p₂)
--         ans a₁ a₂ p₁ p₂ = ?
--           where
--           step₁ : Squashₙ n (f a₁ == b)
--           step₁ = eqInv (squashed-path-eq n (f a₁) b) p₁
--           step₂ : Squashₙ n (f a₂ == b)
--           step₂ = eqInv (squashed-path-eq n (f a₂) b) p₂
--
--           step₁' : Squashₙ n (fiber f b)
--           step₁' = ∥ₙ-map (a₁ ,_) step₁
--           step₂' : Squashₙ n (fiber f b)
--           step₂' = ∥ₙ-map (a₂ ,_) step₂
--
--           step-path : step₁' == step₂'
--           step-path = ?
--
--           a₁-path : ∥ₙ-map fst step₁' == squashₙ n a₁
--           a₁-path = ?
--
--           -- a-path : squashₙ n a₁ == squashₙ n a₂
--           -- a-path i = ∥ₙ-map fst (step-path i)

∥ₙ-map-squashₙ : ∀ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} (n : Nat) (f : A -> B) (a : A) ->
                 ∥ₙ-map f (squashₙ n a) == squashₙ n (f a)
∥ₙ-map-squashₙ zero _ _ = refl
∥ₙ-map-squashₙ (suc _) _ _ = refl

∥ₙ-map-preserves-isEquiv :
  {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} (n : Nat) ->
  {f : A -> B} -> isEquiv f -> isEquiv (∥ₙ-map f {n})
∥ₙ-map-preserves-isEquiv zero _ .equiv-proof _ = (lift tt , refl) , (\_ -> refl)
∥ₙ-map-preserves-isEquiv {ℓA} {ℓB} {A} {B} (suc n) {f} isEq-f =
  record { equiv-proof = \b -> ans₂ b , ans₁ _ _ }
  where
  f' : ∀ (x y : A) -> x == y -> f x == f y
  f' x y = cong f

  fₙ : Squashₙ (suc n) A -> Squashₙ (suc n) B
  fₙ = ∥ₙ-map f

  isEmb-f : isEmbedding f
  isEmb-f x y = isEquiv->isEmbedding isEq-f x y


  step₁ : (b : B) -> isProp (fiber fₙ ∣ b ∣)
  step₁ b = \ (a₁ , p₁) (a₂ , p₂) -> (∥ₙ-elim2 hP step₂ a₁ a₂ p₁ p₂)
    where
    P : Squashₙ (suc n) A -> Squashₙ (suc n) A -> Type (ℓ-max ℓA ℓB)
    P a₁ a₂ = (p₁ : ∥ₙ-map f a₁ == ∣ b ∣) -> (p₂ : ∥ₙ-map f a₂ == ∣ b ∣) -> (a₁ , p₁) == (a₂ , p₂)

    hP : ∀ a₁ a₂ -> isOfHLevel (suc n) (P a₁ a₂)
    hP a₁ a₂ = isOfHLevelΠ (suc n) (\_ -> isOfHLevelΠ (suc n) (\_ ->
                 isOfHLevelPath (suc n) (isOfHLevelΣ (suc n)
                   (isOfHLevel-Squashₙ (suc n))
                     (\_ -> isOfHLevelPath (suc n) (isOfHLevel-Squashₙ (suc n)) _ _)) _ _))


    step₂ : (a₁ a₂ : A) ->
            (p₁ : ∣ f a₁ ∣ == ∣ b ∣) ->
            (p₂ : ∣ f a₂ ∣ == ∣ b ∣) ->
            (∣ a₁ ∣ , p₁) == (∣ a₂ ∣ , p₂)
    step₂ a₁ a₂ p₁ p₂ = ans
      where
      pfa₁ : Path (Squashₙ (suc n) B) (∣ f a₁ ∣) (∣ f a₂ ∣)
      pfa₁ = p₁ >=> sym p₂

      pfa₁-sq : Square pfa₁ refl p₁ p₂
      pfa₁-sq i j = doubleCompPath-filler p₁ refl (sym p₂) (~ i) j

      eq₁ : Path (Squashₙ (suc n) B) (∣ f a₁ ∣) (∣ f a₂ ∣) ≃
            Squashₙ n (f a₁ == f a₂)
      eq₁ = equiv⁻¹ (squashed-path-eq n (f a₁) (f a₂))

      eq₂ : Squashₙ n (f a₁ == f a₂) ≃ Squashₙ n (a₁ == a₂)
      eq₂ = equiv⁻¹ (∥ₙ-map (cong f) , ∥ₙ-map-preserves-isEquiv n (isEmb-f a₁ a₂))

      eq₃ : Squashₙ n (a₁ == a₂) ≃ Path (Squashₙ (suc n) A) (∣ a₁ ∣) (∣ a₂ ∣)
      eq₃ = squashed-path-eq n a₁ a₂


      p-sfa : Squashₙ n (f a₁ == f a₂)
      p-sfa = eqFun eq₁ pfa₁

      p-sfa-prop : eqInv eq₁ p-sfa == pfa₁
      p-sfa-prop = eqRet eq₁ pfa₁

      p-sa : Squashₙ n (a₁ == a₂)
      p-sa = eqFun eq₂ p-sfa

      p-sa-prop : eqInv eq₁ (∥ₙ-map (cong f) p-sa) == pfa₁
      p-sa-prop = cong (eqInv eq₁) (eqRet eq₂ p-sfa) >=> eqRet eq₁ pfa₁


      P₃ : Squashₙ n (a₁ == a₂) -> Type ℓB
      P₃ sp = eqInv eq₁ (∥ₙ-map (cong f) sp) == pfa₁ ->
              (cong (∥ₙ-map f) (eqFun eq₃ sp) == pfa₁)

      hP₃ : ∀ (sp : Squashₙ n (a₁ == a₂)) -> isOfHLevel n (P₃ sp)
      hP₃ sp =
        isOfHLevelΠ n (\_ -> isOfHLevelPath' n (isOfHLevelPath (suc n) (isOfHLevel-Squashₙ (suc n)) _ _) _ _)


      P₃-squash : ∀ (p : a₁ == a₂) -> P₃ (squashₙ n p)
      P₃-squash a₁=a₂ q = P₃-ans -- fa₁=fa₂ q = P₂-ans
        where
        check-q : eqFun (squashed-path-eq n (f a₁) (f a₂)) (∥ₙ-map (cong f) (squashₙ n a₁=a₂)) == pfa₁
        check-q = q

        P₃-step₁ : (∥ₙ-map (cong f) (squashₙ n a₁=a₂)) == (squashₙ n (cong f a₁=a₂))
        P₃-step₁ = ∥ₙ-map-squashₙ n (cong f) a₁=a₂

        q₂ : cong (squashₙ (suc n) ∘ f) a₁=a₂ == pfa₁
        q₂ = sym (squashed-path-eq-path n (cong f a₁=a₂)) >=>
             cong (eqFun (squashed-path-eq n (f a₁) (f a₂))) (sym P₃-step₁) >=>
             q

        P₃-step₂ : (eqFun eq₃ (squashₙ n a₁=a₂)) ==
                   cong (squashₙ (suc n)) a₁=a₂
        P₃-step₂ = (squashed-path-eq-path n a₁=a₂)

        P₃-ans : cong (∥ₙ-map f) (eqFun eq₃ (squashₙ n a₁=a₂)) == pfa₁
        P₃-ans = cong (cong (∥ₙ-map f)) P₃-step₂ >=> q₂


      eq₁₂₃ : Path (Squashₙ (suc n) B) (∣ f a₁ ∣) (∣ f a₂ ∣) ≃
              Path (Squashₙ (suc n) A) (∣ a₁ ∣) (∣ a₂ ∣)
      eq₁₂₃ = eq₁ >eq> eq₂ >eq> eq₃

      pa : Path (Squashₙ (suc n) A) (∣ a₁ ∣) (∣ a₂ ∣)
      pa = eqFun eq₁₂₃ pfa₁

      pfa₂ : Path (Squashₙ (suc n) B) (∣ f a₁ ∣) (∣ f a₂ ∣)
      pfa₂ = cong (∥ₙ-map f) pa

      ppfa : pfa₂ == pfa₁
      ppfa = ∥ₙ-elim' hP₃ P₃-squash p-sa p-sa-prop


      pfa₂-sq : Square pfa₂ refl p₁ p₂
      pfa₂-sq = transP-right ppfa pfa₁-sq

      ans : Path (fiber (∥ₙ-map f) ∣ b ∣) (∣ a₁ ∣ , p₁) (∣ a₂ ∣ , p₂)
      ans i = pa i , \j -> pfa₂-sq j i


  n-trunc-fib : ∀ bₙ -> isOfHLevel (suc n) (fiber fₙ bₙ)
  n-trunc-fib bₙ =
    isOfHLevelΣ (suc n)
      (isOfHLevel-Squashₙ (suc n))
      (\_ -> isOfHLevelPath (suc n) (isOfHLevel-Squashₙ (suc n)) _ _)


  ans₁ : hasPropFibers fₙ
  ans₁ = ∥ₙ-elim (\_ -> isProp->isOfHLevelSuc n isProp-isProp) step₁

  ans₂ : ∀ bₙ -> fiber fₙ bₙ
  ans₂ = ∥ₙ-elim n-trunc-fib (\b -> convert-fib b (fst (isEquiv.equiv-proof isEq-f b)))
    where
    convert-fib : ∀ b -> fiber f b -> fiber fₙ (∣ b ∣)
    convert-fib b (a , p) = ∣ a ∣ , cong ∣_∣ p





∥ₙ-map-preserves-hasPropFibers : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} (n : Nat) ->
                                 {f : A -> B} -> hasPropFibers f -> hasPropFibers (∥ₙ-map f {n})
∥ₙ-map-preserves-hasPropFibers zero {f} hFib-f (lift tt) (lift tt , p₁) (lift tt , p₂) = refl
∥ₙ-map-preserves-hasPropFibers {ℓA} {ℓB} {A} {B} (suc n) {f} hFib-f = ans₁
  where
  f' : ∀ (x y : A) -> x == y -> f x == f y
  f' x y = cong f

  fₙ : Squashₙ (suc n) A -> Squashₙ (suc n) B
  fₙ = ∥ₙ-map f

  isEmb-f : isEmbedding f
  isEmb-f x y = (eqInv isEmbedding-eq-hasPropFibers hFib-f x y)


  step₁ : (b : B) -> isProp (fiber fₙ ∣ b ∣)
  step₁ b = \ (a₁ , p₁) (a₂ , p₂) -> (∥ₙ-elim2 hP step₂ a₁ a₂ p₁ p₂)
    where
    P : Squashₙ (suc n) A -> Squashₙ (suc n) A -> Type (ℓ-max ℓA ℓB)
    P a₁ a₂ = (p₁ : ∥ₙ-map f a₁ == ∣ b ∣) -> (p₂ : ∥ₙ-map f a₂ == ∣ b ∣) -> (a₁ , p₁) == (a₂ , p₂)

    hP : ∀ a₁ a₂ -> isOfHLevel (suc n) (P a₁ a₂)
    hP a₁ a₂ = isOfHLevelΠ (suc n) (\_ -> isOfHLevelΠ (suc n) (\_ ->
                 isOfHLevelPath (suc n) (isOfHLevelΣ (suc n)
                   (isOfHLevel-Squashₙ (suc n))
                     (\_ -> isOfHLevelPath (suc n) (isOfHLevel-Squashₙ (suc n)) _ _)) _ _))


    step₂ : (a₁ a₂ : A) ->
            (p₁ : ∣ f a₁ ∣ == ∣ b ∣) ->
            (p₂ : ∣ f a₂ ∣ == ∣ b ∣) ->
            (∣ a₁ ∣ , p₁) == (∣ a₂ ∣ , p₂)
    step₂ a₁ a₂ p₁ p₂ = ans
      where
      pfa₁ : Path (Squashₙ (suc n) B) (∣ f a₁ ∣) (∣ f a₂ ∣)
      pfa₁ = p₁ >=> sym p₂

      pfa₁-sq : Square pfa₁ refl p₁ p₂
      pfa₁-sq i j = doubleCompPath-filler p₁ refl (sym p₂) (~ i) j

      eq₁ : Path (Squashₙ (suc n) B) (∣ f a₁ ∣) (∣ f a₂ ∣) ≃
            Squashₙ n (f a₁ == f a₂)
      eq₁ = equiv⁻¹ (squashed-path-eq n (f a₁) (f a₂))

      eq₂ : Squashₙ n (f a₁ == f a₂) ≃ Squashₙ n (a₁ == a₂)
      eq₂ = equiv⁻¹ (∥ₙ-map (cong f) , ∥ₙ-map-preserves-isEquiv n (isEmb-f a₁ a₂))

      eq₃ : Squashₙ n (a₁ == a₂) ≃ Path (Squashₙ (suc n) A) (∣ a₁ ∣) (∣ a₂ ∣)
      eq₃ = squashed-path-eq n a₁ a₂


      p-sfa : Squashₙ n (f a₁ == f a₂)
      p-sfa = eqFun eq₁ pfa₁

      p-sfa-prop : eqInv eq₁ p-sfa == pfa₁
      p-sfa-prop = eqRet eq₁ pfa₁

      p-sa : Squashₙ n (a₁ == a₂)
      p-sa = eqFun eq₂ p-sfa

      p-sa-prop : eqInv eq₁ (∥ₙ-map (cong f) p-sa) == pfa₁
      p-sa-prop = cong (eqInv eq₁) (eqRet eq₂ p-sfa) >=> eqRet eq₁ pfa₁


      P₃ : Squashₙ n (a₁ == a₂) -> Type ℓB
      P₃ sp = eqInv eq₁ (∥ₙ-map (cong f) sp) == pfa₁ ->
              (cong (∥ₙ-map f) (eqFun eq₃ sp) == pfa₁)

      hP₃ : ∀ (sp : Squashₙ n (a₁ == a₂)) -> isOfHLevel n (P₃ sp)
      hP₃ sp =
        isOfHLevelΠ n (\_ -> isOfHLevelPath' n (isOfHLevelPath (suc n) (isOfHLevel-Squashₙ (suc n)) _ _) _ _)


      P₃-squash : ∀ (p : a₁ == a₂) -> P₃ (squashₙ n p)
      P₃-squash a₁=a₂ q = P₃-ans -- fa₁=fa₂ q = P₂-ans
        where
        check-q : eqFun (squashed-path-eq n (f a₁) (f a₂)) (∥ₙ-map (cong f) (squashₙ n a₁=a₂)) == pfa₁
        check-q = q

        P₃-step₁ : (∥ₙ-map (cong f) (squashₙ n a₁=a₂)) == (squashₙ n (cong f a₁=a₂))
        P₃-step₁ = ∥ₙ-map-squashₙ n (cong f) a₁=a₂

        q₂ : cong (squashₙ (suc n) ∘ f) a₁=a₂ == pfa₁
        q₂ = sym (squashed-path-eq-path n (cong f a₁=a₂)) >=>
             cong (eqFun (squashed-path-eq n (f a₁) (f a₂))) (sym P₃-step₁) >=>
             q

        P₃-step₂ : (eqFun eq₃ (squashₙ n a₁=a₂)) ==
                   cong (squashₙ (suc n)) a₁=a₂
        P₃-step₂ = (squashed-path-eq-path n a₁=a₂)

        P₃-ans : cong (∥ₙ-map f) (eqFun eq₃ (squashₙ n a₁=a₂)) == pfa₁
        P₃-ans = cong (cong (∥ₙ-map f)) P₃-step₂ >=> q₂






      eq₁₂₃ : Path (Squashₙ (suc n) B) (∣ f a₁ ∣) (∣ f a₂ ∣) ≃
              Path (Squashₙ (suc n) A) (∣ a₁ ∣) (∣ a₂ ∣)
      eq₁₂₃ = eq₁ >eq> eq₂ >eq> eq₃

      pa : Path (Squashₙ (suc n) A) (∣ a₁ ∣) (∣ a₂ ∣)
      pa = eqFun eq₁₂₃ pfa₁

      pfa₂ : Path (Squashₙ (suc n) B) (∣ f a₁ ∣) (∣ f a₂ ∣)
      pfa₂ = cong (∥ₙ-map f) pa

      ppfa : pfa₂ == pfa₁
      ppfa = ∥ₙ-elim' hP₃ P₃-squash p-sa p-sa-prop


      pfa₂-sq : Square pfa₂ refl p₁ p₂
      pfa₂-sq = transP-right ppfa pfa₁-sq

      ans : Path (fiber (∥ₙ-map f) ∣ b ∣) (∣ a₁ ∣ , p₁) (∣ a₂ ∣ , p₂)
      ans i = pa i , \j -> pfa₂-sq j i



  ans₁ : hasPropFibers fₙ
  ans₁ = ∥ₙ-elim (\_ -> isProp->isOfHLevelSuc n isProp-isProp) step₁
