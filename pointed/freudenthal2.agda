{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.freudenthal2 where


open import base
open import pointed.base
open import cubical
open import equality-path
open import equality.square
open import equality.dependent-path
open import base
open import funext
open import isomorphism
open import sigma
open import univalence

open import additive-group
open import order
open import functions
open import nat.order
open import order.instances.nat
open import additive-group.instances.nat
open import cubical
open import equality-path
open import equality.square
open import equality.square-compose
open import equality.square-compose2
open import equality.path-composition-equivalence
open import connected
open import hlevel.base
open import hlevel.pi
open import pointed.base
open import pointed.loop-space
open import truncation.generic
open import truncation.generic.path
open import truncation.generic.map
open import equivalence.base
open import equivalence
open import connected.wedge
open import connected.reduce

open import pointed.suspension

module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) where
  ΩΣf : A -> ⟨ Ω (Susp∙ A∙) ⟩
  ΩΣf a = meridian a >=> sym (meridian ★A)



module freudenthal {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) {n : Nat} (cA : isConnectedₙ n A) where
  south-code : Path (Susp A) north south -> Type ℓ
  south-code p = Squashₙ (suc (suc (n + n))) (fiber meridian p)

  mid-code : A -> Path (Susp A) north south -> Type ℓ
  mid-code a₂ p =
    Squashₙ (suc (suc (n + n)))
      (Σ[ a₁ ∈ A ] (Square p (sym (meridian ★A)) (meridian a₁) (sym (meridian a₂))))

  north-code : Path (Susp A) north north -> Type ℓ
  north-code p = Squashₙ (suc (suc (n + n))) (fiber (ΩΣf A∙) p)

  module _ (q : Path (Susp A) north south) where
    private
      P : A -> A -> Type ℓ
      P a₁ a₂ =
        Square q (sym (meridian ★A)) (meridian a₁) (sym (meridian a₂)) ->
        (south-code q)

      hP : ∀ a₁ a₂ -> isOfHLevel (suc (suc (n + n))) (P a₁ a₂)
      hP a₁ a₂ =
        isOfHLevelΠ (suc (suc (n + n))) (\_ -> isOfHLevel-Squashₙ (suc (suc (n + n))))

      f₁ : ∀ a -> P a ★A
      f₁ a p = ∣ a , sym (case₁.step₂ q (meridian a) (meridian ★A) p) ∣
      f₂ : ∀ a -> P ★A a
      f₂ a p = ∣ a , sym (case₂.step₂ q (meridian ★A) (meridian a) p) ∣

      fp : f₁ ★A == f₂ ★A
      fp i p = ∣ ★A , sym (cases.step₂ q (meridian ★A) p i) ∣

      Σf = (extend-raw-wedge A∙ A∙ cA cA P hP f₁ f₂ fp)


    to-south-raw : ∀ a₁ a₂ -> Square q (sym (meridian ★A)) (meridian a₁) (sym (meridian a₂)) ->
                              south-code q
    to-south-raw = fst Σf

    to-south/★A : mid-code ★A q -> south-code q
    to-south/★A = ∥ₙ-map (\ (a₁ , p) ->  a₁ , sym (case₁.step₂ q (meridian a₁) (meridian ★A) p))

    to-south : ∀ a₂ -> mid-code a₂ q -> south-code q
    to-south a₂ =
      ∥ₙ-elim (\_ -> isOfHLevel-Squashₙ (suc (suc (n + n))))
              (\ (a₁ , p) -> to-south-raw a₁ a₂ p)

    to-south/★A-path : to-south/★A == (to-south ★A)
    to-south/★A-path =
      funExt (∥ₙ-elim (\_ -> isOfHLevelPath (suc (suc (n + n))) (isOfHLevel-Squashₙ (suc (suc (n + n)))) _ _)
                      (\ (a , p) i -> path₂ a (~ i) p))
      where
      path₂ : ∀ a₁ -> to-south-raw a₁ ★A == (\ (p : Square q (sym (meridian ★A)) (meridian a₁) (sym (meridian ★A))) ->
                                              ∣ a₁ , sym (case₁.step₂ q (meridian a₁) (meridian ★A) p) ∣)
      path₂ = fst (snd Σf)

    opaque
      isEquiv-to-south : ∀ a₂ -> isEquiv (to-south a₂)
      isEquiv-to-south a₂ =
        ∥ₙ-elim (\_ -> isProp-isEquiv {f = to-south a₂}) handle ap
        where
        cA₀ : isConnected A
        cA₀ = reduce-isConnectedₙ₋₂ (suc-≤ (suc-≤ zero-≤)) cA

        ap : Squashₙ 1 (a₂ == ★A)
        ap = eqInv (squashed-path-eq 1 _ _) (isContr->isProp cA₀ _ _)

        isEquiv-step₂ : ∀ a₁ -> isEquiv (case₁.step₂ q (meridian a₁) (meridian ★A))
        isEquiv-step₂ a₁ = ∘-isEquiv (isEquiv-▪comp _ _ _ _) (isEquiv-▪comp _ _ _ _)

        module _ where
          isEquiv-step₃ :
            isEquiv (\ (a₁ , p) ->  a₁ , sym (case₁.step₂ q (meridian a₁) (meridian ★A) p))
          isEquiv-step₃ =
            snd (existential-eq (\a -> _ , ∘-isEquiv isEquiv-symP (isEquiv-step₂ a)))

        isEquiv-to-south/★A : isEquiv to-south/★A
        isEquiv-to-south/★A = ∥ₙ-map-preserves-isEquiv _ isEquiv-step₃

        isEquiv-to-south'₂ : isEquiv (to-south ★A)
        isEquiv-to-south'₂ = subst isEquiv to-south/★A-path isEquiv-to-south/★A

        handle : a₂ == ★A -> isEquiv (to-south a₂)
        handle p = transport (\i -> isEquiv (to-south (p (~ i)))) isEquiv-to-south'₂

    to-southΣ : Σ[ a ∈ A ] (mid-code a q) -> A × south-code q
    to-southΣ (a , m) = a , to-south a m

    isEquiv-to-southΣ : isEquiv to-southΣ
    isEquiv-to-southΣ = snd (existential-eq (\a -> to-south a , isEquiv-to-south a))




  module _ (q : Path (Susp A) north south) (a₂ : A) where

    from-north-coherence : (a₁ : A) ->
       (meridian a₁ >=> sym (meridian ★A) == (transport (\i -> north == meridian a₂ (~ i)) q)) ->
       (Square q (sym (meridian ★A)) (meridian a₁) (sym (meridian a₂)))
    from-north-coherence a₁ sq = ans
      where
      y₀-side : Square refl (sym (meridian ★A)) (meridian a₁) ((meridian a₁) >=> (sym (meridian ★A)))
      y₀-side = rotate-square-ABRC->RBAC y₀-side₁
        where
        y₀-side₁ : Square (sym (meridian a₁)) (sym (meridian ★A)) refl ((meridian a₁) >=> (sym (meridian ★A)))
        y₀-side₁ i j = doubleCompPath-filler (meridian a₁) refl (sym (meridian ★A)) j i


      y₁-side :
       Square q refl (transport (\i -> north == meridian a₂ (~ i)) q) (sym (meridian a₂))
      y₁-side = rotate-square-ABCR->ARCB y₁-side₂
        where
        y₁-side₁ :
         Square (reflᵉ north) (meridian a₂) (transport (\i -> north == meridian a₂ (~ i)) q) q
        y₁-side₁ i j = symP (transport-filler (\i -> north == meridian a₂ (~ i)) q) j i

        y₁-side₂ :
         Square q (meridian a₂) (transport (\i -> north == meridian a₂ (~ i)) q) (reflᵉ south)
        y₁-side₂ = rotate-square-RABC->CABR y₁-side₁

      x₀-side : Square q refl refl (sym q)
      x₀-side x y = q (y ∧ ~ x)

      x₁-side : Square refl (sym (meridian ★A)) (meridian ★A) refl
      x₁-side x y = meridian ★A (~ y ∧ x)

      ans : Square q (sym (meridian ★A)) (meridian a₁) (sym (meridian a₂))
      ans = ▪comp (▪ᵀ sq) x₀-side x₁-side y₀-side y₁-side


    module _ {q₂ : north == north} (sq : Square q₂ q refl (meridian a₂)) where
      from-north₃-coherence :
        (a₁ : A) ->
        (meridian a₁ >=> sym (meridian ★A) == q₂) ->
        (Square q (sym (meridian ★A)) (meridian a₁) (sym (meridian a₂)))
      from-north₃-coherence a₁ sq₂ = ans
        where
        y₀-side : Square refl (sym (meridian ★A)) (meridian a₁) ((meridian a₁) >=> (sym (meridian ★A)))
        y₀-side = rotate-square-ABRC->RBAC y₀-side₁
          where
          y₀-side₁ : Square (sym (meridian a₁)) (sym (meridian ★A)) refl ((meridian a₁) >=> (sym (meridian ★A)))
          y₀-side₁ i j = doubleCompPath-filler (meridian a₁) refl (sym (meridian ★A)) j i

        y₁-side : Square q refl q₂ (sym (meridian a₂))
        y₁-side = rotate-square-ABRC->ARBC (symP sq)

        x₀-side : Square q refl refl (sym q)
        x₀-side x y = q (y ∧ ~ x)

        x₁-side : Square refl (sym (meridian ★A)) (meridian ★A) refl
        x₁-side x y = meridian ★A (~ y ∧ x)

        ans : Square q (sym (meridian ★A)) (meridian a₁) (sym (meridian a₂))
        ans = ▪comp (▪ᵀ sq₂) x₀-side x₁-side y₀-side y₁-side

    from-north-coherence₂ : (a₁ : A) ->
       (meridian a₁ >=> sym (meridian ★A) == (q >=> sym (meridian a₂))) ->
       (Square q (sym (meridian ★A)) (meridian a₁) (sym (meridian a₂)))
    from-north-coherence₂ =
      from-north₃-coherence (rotate-square-ARBC->ABRC y₁-side₁)
      where
      y₁-side₁ : Square (q >=> sym (meridian a₂)) refl q (meridian a₂)
      y₁-side₁ i j = doubleCompPath-filler q refl (sym (meridian a₂)) (~ i) j


    from-north :
      north-code (transport (\i -> north == meridian a₂ (~ i)) q) ->
      mid-code a₂ q
    from-north = ∥ₙ-map (\ (a , s) -> a , from-north-coherence a s)


    from-north₂ : north-code (q >=> sym (meridian a₂)) -> mid-code a₂ q
    from-north₂ = ∥ₙ-map (\ (a , s) -> a , from-north-coherence₂ a s)


    from-north₃ : {q₂ : north == north} (sq : Square q₂ q refl (meridian a₂)) ->
                  north-code q₂ -> mid-code a₂ q
    from-north₃ {q₂} sq = ∥ₙ-map (\ (a , s) -> a , from-north₃-coherence sq a s)

    opaque
      isEquiv-from-north : isEquiv from-north
      isEquiv-from-north =
        ∥ₙ-map-preserves-isEquiv _ (snd (existential-eq (\a -> _ ,
          ∘-isEquiv (isEquiv-▪comp _ _ _ _) isEquiv-▪ᵀ)))

      isEquiv-from-north₂ : isEquiv from-north₂
      isEquiv-from-north₂ =
        ∥ₙ-map-preserves-isEquiv _ (snd (existential-eq (\a -> _ ,
          ∘-isEquiv (isEquiv-▪comp _ _ _ _) isEquiv-▪ᵀ)))

      isEquiv-from-north₃ :
        {q₂ : north == north}
        (sq : Square q₂ q refl (meridian a₂)) ->
        isEquiv (from-north₃ sq)
      isEquiv-from-north₃ sq = ∥ₙ-map-preserves-isEquiv _ isEq
        where
        module _ where
          isEq : isEquiv (\ (a , s) -> a , from-north₃-coherence sq a s)
          isEq = (snd (existential-eq (\a -> _ ,
              ∘-isEquiv (isEquiv-▪comp _ _ _ _) isEquiv-▪ᵀ)))




  module _ (q : Path (Susp A) north south) (a₂ : A) where
    ns :
      north-code (transport (\i -> north == meridian a₂ (~ i)) q) ->
      south-code q
    ns c = to-south q a₂ (from-north q a₂ c)

    opaque
      isEquiv-ns : isEquiv ns
      isEquiv-ns = ∘-isEquiv (isEquiv-to-south q a₂) (isEquiv-from-north q a₂)

      isEquiv-ns-inv-path :
        isEqInv isEquiv-ns ==
        isEqInv (isEquiv-from-north q a₂) ∘
        isEqInv (isEquiv-to-south q a₂)
      isEquiv-ns-inv-path = refl

    ns-path :
      Path (Type ℓ)
        (north-code (transport (\i -> north == meridian a₂ (~ i)) q))
        (south-code q)
    ns-path = ua (ns , isEquiv-ns)


  encode : ∀ (s : Susp A) -> (north == s) -> Type ℓ
  encode north = north-code
  encode south = south-code
  encode (meridian a₁ i) = ans i
    where
    tp : PathP (\i -> (north == meridian a₁ i) -> Type ℓ)
               (encode north)
               (\q -> encode north (transport (\i -> north == meridian a₁ (~ i)) q))
    tp j q = encode north (transp (\i -> north == meridian a₁ (~ i ∧ j)) (~ j) q)

    ans : PathP (\i -> (north == meridian a₁ i) -> Type ℓ) (encode north) (encode south)
    ans = transP-left tp (\i q -> ns-path q a₁ i)

  encode' : (Σ[ s ∈ (Susp A) ] (north == s)) -> Type ℓ
  encode' (s , p) = encode s p

  module encode₂ (a₁ : A) where
    left-edge : Path (north == north -> Type ℓ)
                     (\p -> (mid-code a₁ (p >=> meridian a₁)))
                     (\p -> north-code p)
    left-edge k p =
      (sym (ua (from-north₂ (p >=> meridian a₁) a₁ , isEquiv-from-north₂ (p >=> meridian a₁) a₁)) >=>
       cong north-code ((\i -> p >=> (\j -> meridian a₁ (j ∧ ~ i)) >=> (\j -> meridian a₁ (~ j ∧ ~ i))) >=>
                        compPath-refl-right (p >=> refl) >=>
                        compPath-refl-right p)) k

    right-edge : Path (north == south -> Type ℓ)
                      (\p -> (mid-code a₁ (p >=> refl)))
                      (\p -> south-code p)
    right-edge k p = (cong (mid-code a₁) (compPath-refl-right p) >=>
                      ua (to-south p a₁ , isEquiv-to-south p a₁)) k

    base : PathP (\k -> (north == meridian a₁ k) -> Type ℓ)
                  (\p -> (mid-code a₁ (p >=> meridian a₁)))
                  (\p -> (mid-code a₁ (p >=> refl)))
    base k p = (mid-code a₁ (p >=> (\j -> meridian a₁ (k ∨ j))))

  module encode₃ (a₁ : A) {p₁ : north == north} {p₂ : north == south}
                 (sq : Square p₁ p₂ refl (meridian a₁)) where
    -- left-edge : Path (Type ℓ) (north-code p₁) (mid-code a₁ p₂)
    -- left-edge = (ua (from-north₃ p₂ a₁ sq , isEquiv-from-north₃ p₂ a₁ sq))

    -- right-edge : Path (Type ℓ) (mid-code a₁ p₂) (south-code p₂)
    -- right-edge = ua (to-south p₂ a₁ , isEquiv-to-south p₂ a₁)

    edge : Path (Type ℓ) (north-code p₁) (south-code p₂)
    edge =
      ua (to-south p₂ a₁ ∘ from-north₃ p₂ a₁ sq ,
          ∘-isEquiv (isEquiv-to-south p₂ a₁) (isEquiv-from-north₃ p₂ a₁ sq))

  module encode₃-m (a₁ : A) (i : I) (p : north == meridian a₁ i)
    where
    open encode₃ a₁

    q₁ : north == north
    q₁ = transp (\k -> north == (meridian a₁ (i ∧ ~ k))) (~ i) p

    q₂ : north == south
    q₂ = transp (\k -> north == (meridian a₁ (i ∨ k))) i p


    msq : Square (reflᵉ (meridian a₁ i)) (meridian a₁) (\j -> meridian a₁ (i ∧ ~ j)) (\j -> meridian a₁ (i ∨ j))
    msq ii jj =
      hcomp (\k -> \{ (ii = i0) -> meridian a₁ (k ∧ i)
                    ; (ii = i1) -> meridian a₁ (k ∧ jj)
                    ; (jj = i0) -> meridian a₁ (k ∧ (i ∧ ~ ii))
                    ; (jj = i1) -> meridian a₁ (k ∧ (i ∨ ii))
                    })
        north

    sq : Square q₁ q₂ refl (meridian a₁)
    sq ii jj =
      hcomp (\l -> \{ (ii = i0) -> (transp (\k -> north == meridian a₁ (i ∧ (~ k ∨ ~ l))) (~ i ∨ ~ l) p) jj
                    ; (ii = i1) -> (transp (\k -> north == meridian a₁ (i ∨ (k ∧ l))) (i ∨ ~ l) p) jj
                    ; (jj = i0) -> north
                    ; (jj = i1) -> msq l ii
                    })
        (p jj)


    ans : Sub (Type ℓ) (i ∨ ~ i)
                       (\{ (i = i0) -> north-code p
                         ; (i = i1) -> south-code p
                         })
    ans = inS (encode₃.edge a₁ sq i)


  encode₃ : ∀ (s : Susp A) -> (north == s) -> Type ℓ
  encode₃ north = north-code
  encode₃ south = south-code
  encode₃ (meridian a₁ i) p = outS (encode₃-m.ans a₁ i p)


  encode₃' : Σ[ s ∈ Susp A ] (north == s) -> Type ℓ
  encode₃' (s , p) = encode₃ s p

  module encode₄-m (a₁ : A) (i : I) (p : north == meridian a₁ i)
    where
    n->m : north == meridian a₁ i
    n->m j = meridian a₁ (i ∧ j)
    m->s : meridian a₁ i == south
    m->s j = meridian a₁ (i ∨ j)

    q₁ : north == north
    q₁ = p >=> sym n->m

    q₂ : north == south
    q₂ = p >=> m->s


    msq : Square (sym n->m) m->s (reflᵉ (meridian a₁ i)) (meridian a₁)
    msq jj ii =
      hcomp (\k -> \{ (ii = i0) -> meridian a₁ (k ∧ i)
                    ; (ii = i1) -> meridian a₁ (k ∧ jj)
                    ; (jj = i0) -> meridian a₁ (k ∧ (i ∧ ~ ii))
                    ; (jj = i1) -> meridian a₁ (k ∧ (i ∨ ii))
                    })
        north

    sq : Square q₁ q₂ refl (meridian a₁)
    sq i j = (p >=> msq i) j

    ans : Sub (Type ℓ) (i ∨ ~ i)
                       (\{ (i = i0) -> north-code p
                         ; (i = i1) -> south-code p
                         })
    ans = inS
      (hcomp (\k -> \{ (i = i0) -> north-code (compPath-refl-right p k)
                     ; (i = i1) -> south-code (compPath-refl-right p k)
                     })
         (encode₃.edge a₁ sq i))


  encode₄ : ∀ (s : Susp A) -> (north == s) -> Type ℓ
  encode₄ north = north-code
  encode₄ south = south-code
  encode₄ (meridian a₁ i) p = outS (encode₄-m.ans a₁ i p)


  encode₄' : Σ[ s ∈ Susp A ] (north == s) -> Type ℓ
  encode₄' (s , p) = encode₄ s p





  encode₂ : ∀ (s : Susp A) -> (north == s) -> Type ℓ
  encode₂ north = north-code
  encode₂ south = south-code
  encode₂ (meridian a₁ i) = (transP-mid (sym left-edge) base right-edge) i
    where
    open encode₂ a₁



  encode₂' : Σ[ s ∈ Susp A ] (north == s) -> Type ℓ
  encode₂' (s , p) = encode₂ s p



  encode-center : ∀ s p -> encode s p
  encode-center _ = J (\s p -> (encode s p)) (∣ ★A , compPath-sym (meridian ★A) ∣)

  encode₂-center : ∀ s p -> encode₂ s p
  encode₂-center _ = J (\s p -> (encode₂ s p)) (∣ ★A , compPath-sym (meridian ★A) ∣)

  encode₃-center : ∀ s p -> encode₃ s p
  encode₃-center _ = J (\s p -> (encode₃ s p)) (∣ ★A , compPath-sym (meridian ★A) ∣)

  encode₄-center : ∀ s p -> encode₄ s p
  encode₄-center _ = J (\s p -> (encode₄ s p)) (∣ ★A , compPath-sym (meridian ★A) ∣)



  module _ (magic : Magic) where
    isCenter-encode-north : ∀ (p : north == north) (v : encode north p) -> encode-center north p == v
    isCenter-encode-north =
      (\p -> ∥ₙ-elim (\fib -> isOfHLevelPath (suc (suc (n + n)))
                              (isOfHLevel-Squashₙ (suc (suc (n + n)))) (encode-center north p) fib)
                     (step₁ p))
      where

      step₁ : ∀ (p : north == north) (v : (fiber (ΩΣf A∙) p)) -> encode-center north p == ∣ v ∣
      step₁ p (a , r) = ans
        where
        check-p : north == north
        check-p = p
        check-a : A
        check-a = a
        check-r : meridian a >=> sym (meridian ★A) == p
        check-r = r

        Ans : ∀ p' (r' : meridian a >=> sym (meridian ★A) == p') -> Type _
        Ans p' r' = encode-center north p' == ∣ (a , r') ∣

        base' :
          transport (\i  -> (encode ((meridian a >=> sym (meridian ★A)) i)
                                    (\j -> (meridian a >=> sym (meridian ★A)) (i ∧ j))))
                    (∣ ★A , compPath-sym (meridian ★A) ∣)
             ==
          ∣ (a , refl) ∣
        base' = magic
         where
          t₀ : encode north refl
          t₀ = (∣ ★A , compPath-sym (meridian ★A) ∣)

          t₁ : encode south (meridian a)
          t₁ = transport (\i -> (encode (meridian a i) (\j -> (meridian a) (i ∧ j)))) t₀





          t₂ : encode south (meridian a >=> refl)
          t₂ = transport (\i -> (encode south (\j -> compPath-refl-right (meridian a) (~ i) j))) t₁

          t₃ : encode north (meridian a >=> sym (meridian ★A))
          t₃ = transport (\i -> (encode (meridian ★A (~ i))
                                        (meridian a >=> (\j -> meridian ★A (~ j ∨ ~ i)))))
                         t₂

          t₄ : encode north (meridian a >=> sym (meridian ★A))
          t₄ = transport
            ((\i -> (encode (meridian a i) (\j -> (meridian a) (i ∧ j)))) ∙∙
             (\i -> (encode south (\j -> compPath-refl-right (meridian a) (~ i) j))) ∙∙
             (\i -> (encode (meridian ★A (~ i))
                            (meridian a >=> (\j -> meridian ★A (~ j ∨ ~ i))))))
            t₀


          t₅-p : PathP (\i -> north == (meridian a >=> sym (meridian ★A)) i)
                       refl
                       (meridian a >=> sym (meridian ★A))
          t₅-p = ∙∙dep (\x -> north == x)
                       (\i j -> (meridian a) (i ∧ j))
                       (\i j -> compPath-refl-right (meridian a) (~ i) j)
                       (\i -> meridian a >=> (\j -> meridian ★A (~ j ∨ ~ i)))

          t₅-p' : PathP (\i -> north == (meridian a >=> sym (meridian ★A)) i)
                    refl
                    (meridian a >=> sym (meridian ★A))
          t₅-p' = ▪dep
                    (\i j -> (meridian a) (i ∧ j))
                    (\i j -> compPath-refl-right (meridian a) (~ i) j)
                    (\i -> meridian a >=> (\j -> meridian ★A (~ j ∨ ~ i)))


          t₅ : encode north (meridian a >=> sym (meridian ★A))
          t₅ = transport
            (\i -> encode ((meridian a >=> sym (meridian ★A)) i)
                          (t₅-p i))
            t₀

          t₆-p : PathP (\i -> north == (meridian a >=> sym (meridian ★A)) i)
                       refl
                       (meridian a >=> sym (meridian ★A))
          t₆-p i j = (meridian a >=> sym (meridian ★A)) (i ∧ j)


          t₆ : encode north (meridian a >=> sym (meridian ★A))
          t₆ = transport
            (\i -> encode ((meridian a >=> sym (meridian ★A)) i)
                          (t₆-p i))
            t₀


          t₅-p=t₆-p : t₅-p == t₆-p
          t₅-p=t₆-p = sym t₅-step₁ ∙∙ stage₃=stage-end₁ ∙∙ sym step-end₁
            where


            stage₁ : PathP (\i -> north == (meridian a >=> sym (meridian ★A)) i)
                       refl
                       (meridian a >=> sym (meridian ★A))
            stage₁ = t₅-p

            stage₂ : PathP (\i -> north == (meridian a >=> sym (meridian ★A)) i)
                       refl
                       (meridian a >=> sym (meridian ★A))
            stage₂ = t₅-p'

            t₅-step₁ : stage₂ == stage₁
            t₅-step₁ =
              ▪dep-path
                (\i j -> (meridian a) (i ∧ j))
                (\i j -> compPath-refl-right (meridian a) (~ i) j)
                (\i -> meridian a >=> (\j -> meridian ★A (~ j ∨ ~ i)))

            stage₃ : Square
                       (reflᵉ north)
                       (meridian a >=> sym (meridian ★A))
                       (reflᵉ north)
                       (meridian a >=> sym (meridian ★A))
            stage₃ =
              ▪comp (\i j -> compPath-refl-right (meridian a) (~ i) j)
                    (\i j -> (meridian a) (i ∧ j))
                    (\i -> meridian a >=> (\j -> meridian ★A (~ j ∨ ~ i)))
                    (reflᵉ (reflᵉ north))
                    (\i j -> doubleCompPath-filler (meridian a) refl (sym (meridian ★A)) j i)

            t₅-step₂ : stage₂ == stage₃
            t₅-step₂ = refl

            check-left : t₅-p == stage₁
            check-left = refl


            stage₄ : Square
                       (reflᵉ north)
                       (meridian a >=> sym (meridian ★A))
                       (reflᵉ north)
                       (meridian a >=> sym (meridian ★A))
            stage₄ =
              ▪comp (\i j -> doubleCompPath-filler (meridian a) refl refl i j)
                    (\i j -> meridian a i)
                    (\i -> meridian a >=> (\j -> meridian ★A (~ j ∨ ~ i)))
                    (\i j -> meridian a (~ i ∧ j))
                    (\i j -> doubleCompPath-filler (meridian a) refl (sym (meridian ★A)) j i)

            t₅-step₃ : stage₃ == stage₄
            t₅-step₃ k =
              ▪comp (\i j -> square-path2.lemma (meridian a) magic k i j)
                    (\i j -> meridian a (i ∧ (j ∨ k)))
                    (\i -> meridian a >=> (\j -> meridian ★A (~ j ∨ ~ i)))
                    (\i j -> meridian a ((~ i ∧ j) ∧ k))
                    (\i j -> doubleCompPath-filler (meridian a) refl (sym (meridian ★A)) j i)


            stage₅ : Square
                       (reflᵉ north)
                       (meridian a >=> sym (meridian ★A))
                       (reflᵉ north)
                       (meridian a >=> sym (meridian ★A))
            stage₅ =
              ▪comp (\i j -> doubleCompPath-filler refl (reflᵉ south) refl i j)
                    (\i j -> meridian a i)
                    (\i j ->
                      doubleCompPath-filler (\j -> meridian a (j ∨ ~ i)) refl (\j -> meridian ★A (~ j ∨ ~ i))
                        i1 j)
                    (\i j -> meridian a j)
                    (\i j -> doubleCompPath-filler (meridian a) refl (sym (meridian ★A)) j i)

            t₅-step₅ : stage₄ == stage₅
            t₅-step₅ k =
              ▪comp (\i j -> doubleCompPath-filler (\l -> meridian a (l ∨ k)) refl refl i j)
                    (\i j -> meridian a i)
                    (\i -> ((\j -> meridian a (j ∨ (~ i ∧ k))) >=> (\j -> meridian ★A (~ j ∨ ~ i))))
                    (\i j -> meridian a ((k ∨ ~ i) ∧ j))
                    (\i j -> doubleCompPath-filler (meridian a) refl (sym (meridian ★A)) j i)


            stage₆ : Square
                       (reflᵉ north)
                       (meridian a >=> sym (meridian ★A))
                       (reflᵉ north)
                       (meridian a >=> sym (meridian ★A))
            stage₆ =
              ▪comp (\i j -> south)
                    (\i j -> meridian a i)
                    (\i j ->
                      doubleCompPath-filler (\j -> meridian a (j ∨ ~ i)) refl (\j -> meridian ★A (~ j ∨ ~ i))
                        i j)
                    (\i j -> meridian a j)
                    (\i j -> doubleCompPath-filler (meridian a) refl (sym (meridian ★A)) j i)


            t₅-step₆ : stage₅ == stage₆
            t₅-step₆ k =
              ▪comp (\i j -> doubleCompPath-filler refl (reflᵉ south) refl (i ∧ ~ k) j)
                    (\i j -> meridian a i)
                    (\i j ->
                      doubleCompPath-filler (\j -> meridian a (j ∨ ~ i)) refl (\j -> meridian ★A (~ j ∨ ~ i))
                        (~ k ∨ i) j)
                    (\i j -> meridian a j)
                    (\i j -> doubleCompPath-filler (meridian a) refl (sym (meridian ★A)) j i)


            stage₇ : Square
                       (reflᵉ north)
                       (meridian a >=> sym (meridian ★A))
                       (reflᵉ north)
                       (meridian a >=> sym (meridian ★A))
            stage₇ =
              ▪comp (\i j -> south)
                    (\i j -> meridian a i)
                    (\i j ->
                      doubleCompPath-filler (\j -> meridian a j) refl (\j -> meridian ★A (~ j))
                        i j)
                    (\i j -> meridian a j)
                    (\i j -> doubleCompPath-filler (meridian a) refl (sym (meridian ★A)) j i)

            t₅-step₇ : stage₆ == stage₇
            t₅-step₇ k =
              ▪comp (\i j -> south)
                    (\i j -> meridian a i)
                    (\i j ->
                      doubleCompPath-filler (\j -> meridian a (j ∨ (~ i ∧ k)))
                                            refl
                                            (\j -> meridian ★A (~ j ∨ (~ i ∧ k)))
                        i j)
                    (\i j -> meridian a j)
                    (\i j -> doubleCompPath-filler (meridian a) refl (sym (meridian ★A)) j i)




            stage-end : PathP (\i -> north == (meridian a >=> sym (meridian ★A)) i)
                         refl
                         (meridian a >=> sym (meridian ★A))
            stage-end i j = (meridian a >=> sym (meridian ★A)) (i ∧ j)

            stage-end₁ : Square
                       (reflᵉ north)
                       (meridian a >=> sym (meridian ★A))
                       (reflᵉ north)
                       (meridian a >=> sym (meridian ★A))
            stage-end₁ =
              ▪comp (reflᵉ (reflᵉ south))
                    (\i j -> (meridian a) i)
                    (\i j -> doubleCompPath-filler (meridian a) refl (sym (meridian ★A)) i j)
                    (\i j -> (meridian a) j)
                    (\i j -> doubleCompPath-filler (meridian a) refl (sym (meridian ★A)) j i)





            step-end₁ : stage-end == stage-end₁
            step-end₁ = square-path1.lemma (meridian a) (meridian ★A)


            stage₃=stage-end₁ : stage₃ == stage-end₁
            stage₃=stage-end₁ = t₅-step₃ >=> (t₅-step₅ ∙∙ t₅-step₆ ∙∙ t₅-step₇)




          t₅=t₆ : t₅ == t₆
          t₅=t₆ k = transport
            (\i -> encode ((meridian a >=> sym (meridian ★A)) i)
                          (t₅-p=t₆-p k i))
            t₀





          t₄=t₃ : t₄ == t₃
          t₄=t₃ = transport-∙∙
            (\i -> (encode (meridian a i) (\j -> (meridian a) (i ∧ j))))
            (\i -> (encode south (\j -> compPath-refl-right (meridian a) (~ i) j)))
            (\i -> (encode (meridian ★A (~ i))
                   (meridian a >=> (\j -> meridian ★A (~ j ∨ ~ i)))))
            t₀

          t₄=t₅ : t₄ == t₅
          t₄=t₅ =
            cong (\x -> transport x t₀)
              (sym (cong2-dep-∙∙ encode (meridian a) (\i j -> (meridian a) (i ∧ j))
                                        refl (\i j -> compPath-refl-right (meridian a) (~ i) j)
                                        (sym (meridian ★A))
                                        (\i -> meridian a >=> (\j -> meridian ★A (~ j ∨ ~ i)))))





          end : encode north (meridian a >=> sym (meridian ★A))
          end =
             transport (\i  -> (encode ((meridian a >=> sym (meridian ★A)) i)
                                       (\j -> (meridian a >=> sym (meridian ★A)) (i ∧ j))))
              (∣ ★A , compPath-sym (meridian ★A) ∣)

          t₃=start : t₃ == ∣ (a , refl) ∣
          t₃=start = magic


          t₆=start : t₆ == ∣ (a , refl) ∣
          t₆=start = sym t₅=t₆ >=> sym t₄=t₅ >=> t₄=t₃ >=> t₃=start




        base : encode-center north (meridian a >=> sym (meridian ★A)) == ∣ (a , refl) ∣
        base = base'


        ans : encode-center north p == ∣ (a , r) ∣
        ans = J Ans base r






    isContr-encode-refl : isContr (encode north refl)
    isContr-encode-refl = magic
      where
      ctr : Squashₙ (suc (suc (n + n))) (fiber (ΩΣf A∙) refl)
      ctr = ∣ ★A , compPath-sym (meridian ★A) ∣

--       isCtr' : ∀ fib -> ctr == ∣ fib ∣
--       isCtr' (a , p) = ?
--         where
--         ap : a == ★A
--         ap = ?
--
--       isCtr : ∀ fib -> ctr == fib
--       isCtr =
--         ∥ₙ-elim (\fib -> isOfHLevelPath (suc (suc (n + n)))
--                            (isOfHLevel-Squashₙ (suc (suc (n + n)))) ctr fib)
--                 isCtr'


    isContr-encode : ∀ s p -> isContr (encode s p)
    isContr-encode _ = J (\s p -> isContr (encode s p)) isContr-encode-refl


    isConnectedMap-ΩΣf : isConnectedMapₙ (n + n) (ΩΣf A∙)
    isConnectedMap-ΩΣf = isContr-encode north
