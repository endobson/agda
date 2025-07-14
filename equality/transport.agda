{-# OPTIONS --cubical --safe --exact-split #-}

module equality.transport where

open import base
open import cubical
open import hlevel.base
open import equality-path
open import equality.square
open import equivalence.base
open import equivalence
open import isomorphism


module _ {ℓ : Level} {A B : Type ℓ} (P : A == B) (a : A) where
  private
    v2 : I -> B
    v2 i = transp (\k -> (P (i ∨ k))) i
            (transp (\k -> (P (i ∧ k))) (~ i) a)
    v2' : transport P a == transport P a
    v2' i = v2 i

    v4 : (j : I) -> P j
    v4 j = transp (\k -> (P (k ∧ j))) (~ j) a


    v3 : (i j : I) -> P j
    v3 i j =
      (transp (\k -> (P ((i ∧ j) ∨ (k ∧ j)))) (~ j ∨ i)
        (transp (\k -> (P ((i0 ∧ ~ k) ∨ (k ∧ (i ∧ j))))) (~ i ∨ ~ j) a))

    v3' : PathP (\j -> v4 j == v4 j) (reflᵉ a) v2'
    v3' i j = v3 j i


  transport-partway-square : v2' == (reflᵉ (transport P a))
  transport-partway-square i j =
    comp (\k -> P k)
      (\k -> \{ (i = i0) -> v3' k j
              ; (i = i1) -> v4 k
              ; (j = i0) -> v4 k
              ; (j = i1) -> v4 k
              })
      a


module _ {ℓ : Level} {A B : Type ℓ} (P : A == B) where

  {-  This upeer triangle is 1 and the lower triangle is 2.

      i --* 1
      |   * |
      |  /  |
      * /   *
      0 --* i
  -}

  opaque
    transport-commuting-triangle₁ : (i : I) (v : P i) ->
      (transport P (transport (\k -> P (i ∧ ~ k)) v)) ==
      (transport (\k -> P (i ∨ k)) v)
    transport-commuting-triangle₁ i v =
      sym (step3 _) >=> cong (transport (\k -> P (i ∨ k))) (sym step2 >=> sym step1)

      where
      step1 : v == (transport refl (transport refl v))
      step1 = sym (transportRefl _) >=> sym (transportRefl _)

      step2 : (transport refl (transport refl v)) ==
              (transport (\k -> P (i ∧ k)) (transport (\k -> P (i ∧ ~ k)) v))
      step2 j =
        transport (\k -> P (i ∧ (k ∨ ~ j)))
          (transport (\k -> P (i ∧ (~ k ∨ ~ j))) v)

      step3 : ∀ a ->
        (transport (\k -> P (i ∨ k)) (transport (\k -> P (i ∧ k)) a)) ==
        (transport P a)
      step3 a j =
        (transp (\k -> P ((i ∨ j) ∨ k)) j (transport (\k -> P ((i ∨ j) ∧ k)) a))

  -- transport-commuting-triangle₂ :
  --   (i : I) (a : A) ->
  --   (transport (\k -> P (i ∨ ~ k)) (transport P a)) ==
  --   (transport (\k -> P (i ∧ k)) a)
  -- transport-commuting-triangle₂ i a = ?


module _ {ℓ : Level} {A B : Type ℓ} (P : A == B) where

  raw-square : (i j : I) -> P i -> P j
  raw-square i j = transport (\k -> P ((i ∧ ~ k) ∨ (j ∧ k)))





module _ {ℓ : Level} {A B : Type ℓ} (P : A == B)
         (i : I) (v : P i) where

  path1 : (j : I) -> P j
  path1 j =
    transport (\k -> (P (j ∧ k))) (transport (\k -> P (i ∧ ~ k)) v)

  path2 : (j : I) -> P j
  path2 j =
    transport (\k -> (P (j ∨ ~ k))) (transport (\k -> P (i ∨ k)) v)


  -- step6 : ∀ a -> (transport (\k -> P (i ∨ k)) (transport (\k -> P (i ∧ k)) v)) ==
  --                (transport P v)
  -- step6 = ?


module _ {ℓ : Level} {A B : Type ℓ} (v : A) (p : A == B) (magic : Magic) where
  trans-sym-mess :
     transport-sym (sym p) (transport p v) ==
     (\i -> transport p (transport-sym p v i))
  trans-sym-mess = magic
    where
    left : transport-sym (sym p) (transport p v) ==
           (\i ->
             transp (\j -> p (j ∨ i)) i
               (transp (\j -> p (~ j ∨ i)) i
                 (transp (\j -> p j) i0 v)))
    left = refl


    right : Path (transport p (transport (sym p) (transport p v)) == transport p v)
            (\i -> transport p (transport-sym p v i))
            (\i ->
              transp (\j -> p j) i0
                (transp (\j -> p (~ j ∧ ~ i)) i
                  (transp (\j -> p (j ∧ ~ i)) i v)))
    right = refl

    isEq-trans : isEquiv (transport p)
    isEq-trans = isoToIsEquiv (iso (transport p) (transport (sym p))
                                   (transport-sym (sym p)) (transport-sym p))

    isEquivTransport : isEquiv (transport p)
    isEquivTransport =
      transport (\ i -> isEquiv (\ x -> transp (λ j → p (i ∧ j)) (~ i) x)) (idIsEquiv A)

    isEquivTransport' : isEquiv (transport p)
    isEquivTransport' .equiv-proof = ans
      where
      ans : ∀ b -> isContr (fiber (transport p) b)
      ans b = (transp (\i -> p (~ i)) i0 b ,
               (\j -> transp (\i -> p (i ∨ j)) j (transp (\i -> p (~ i ∨ j)) j b))) ,
              isProp-fib _
        where
        isProp-fib : isProp (fiber (transport p) b)
        isProp-fib (a₁ , q₁) (a₂ , q₂) = magic
          where
          b₁ b₂ : B
          b₁ = transport p a₁
          b₂ = transport p a₂

          b₁=b₂ : b₁ == b₂
          b₁=b₂ = q₁ >=> sym q₂

          bsq : Square q₁ q₂ b₁=b₂ refl
          bsq i j = square-filler (sym q₁) (sym q₂) refl i (~ j)


          a₁=a₂ : a₁ == a₂
          a₁=a₂ = sym (transport-sym p a₁) ∙∙ cong (transport (sym p)) b₁=b₂ ∙∙ transport-sym p a₂

          module _ (i : I) where
            tsp : transport (sym p) (q₁ i) == transport (sym p) (q₂ i)
            tsp j = transport (sym p) (bsq j i)

            tsp' : (j : I) -> A
            tsp' j = tsp j

            rsp : (j : I) -> transport p (tsp' j) == bsq j i
            rsp j = transport-sym (sym p) (bsq j i)

            bsq' : ∀ j -> bsq j i == b
            bsq' j k = bsq j (i ∨ k)

            fib-sq : ∀ j -> fiber (transport p) b
            fib-sq j = tsp' j , rsp j >=> bsq' j

          check-fib-sq : fib-sq i0 i0 == (tsp' i0 i0 , transport-sym (sym p) (bsq i0 i0) >=> bsq' i0 i0)
            -- transport-sym (sym p) (bsq i0 i0) >=> ?) -- (\j -> bsq' i0 j))
          check-fib-sq = magic








          -- check-q₁ : transport p a₁ == b
          -- check-q₁ = q₁

          -- v₁ : (i : I) -> Σ[ x ∈ p i ] (transp (\j -> p (i ∨ j)) i x == b)
          -- v₁ i = transp (\j -> p (j ∧ i)) (~ i) a₁ , step >=> q₁
          --   where
          --   step : (transp (\j -> p (i ∨ j)) i (transp (\j -> p (j ∧ i)) (~ i) a₁)) ==
          --          transport p a₁
          --   step k =
          --     transp (\j -> p ((i ∨ k) ∨ j)) (i ∨ k)
          --       (transp (\j -> p (j ∧ (i ∨ k))) (~ (i ∨ k)) a₁)

          -- v₂ : (i : I) -> Σ[ x ∈ p i ] (transport p (transp (\j -> p (i ∧ ~ j)) (~ i) x) == b)
          -- v₂ i = x₁ , outS v₂-ans
          --   where
          --   x₁ : p i
          --   x₁ = transp (\j -> p (j ∧ i)) (~ i) a₁

          --   partial : Partial (i ∨ ~ i) (transport p (transp (\j -> p (i ∧ ~ j)) (~ i) x₁) == b)
          --   partial (i = i0) = q₁
          --   -- partial (i = i1) = transport-sym (sym p) (transport p a₁) >=> q₁
          --   partial (i = i1) = cong (transport p) (transport-sym p a₁) >=> q₁

          --   v₂-ans : Sub _ _ partial
          --   v₂-ans = ?




          -- v₂ : (i : I) -> Σ[ x ∈ p i ] (transp (\j -> p (i ∨ j)) i x == b)
          -- v₂ i = transp (\j -> p (j ∧ i)) (~ i) a₁ , step >=> q₁
          --   where
          --   step : (transp (\j -> p (i ∨ j)) i (transp (\j -> p (j ∧ i)) (~ i) a₁)) ==
          --          transport p a₁
          --   step k =
          --     transp (\j -> p ((i ∨ k) ∨ j)) (i ∨ k)
          --       (transp (\j -> p (j ∧ (i ∨ k))) (~ (i ∨ k)) a₁)







    -- check : transport-sym (sym p) (transport p v) ==
    --         (\i -> transport p (transport-sym p v i))
    -- check = rotate-square-ARBC->ABRC ?

    -- check2 : Square _ refl _ refl
    -- check2 = isEqComm isEquivTransport v





