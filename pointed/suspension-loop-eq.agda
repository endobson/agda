{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.suspension-loop-eq where

open import base
open import functions
open import sigma
open import cubical
open import equivalence
open import isomorphism
open import equality-path
open import pointed.base
open import funext
open import pointed.suspension
open import pointed.loop-space
open import univalence

module _ {ℓA ℓB : Level} (A∙@(A , ★A) : Type∙ ℓA) (B∙@(B , ★B) : Type∙ ℓB) where

  private
    iso₁ : Iso (Susp∙ A∙ ->∙ B∙) (Σ B (\b -> A -> ★B == b))
    iso₁ = iso forward backward fb bf
      where
      open _->∙_
      forward : (Susp∙ A∙ ->∙ B∙) -> (Σ B (\b -> A -> ★B == b))
      forward (->∙-cons f p) = f south , \a -> sym p >=> cong f (meridian a)
      backward : (Σ B (\b -> A -> ★B == b)) -> (Susp∙ A∙ ->∙ B∙)
      backward (b , ps) .f north = ★B
      backward (b , ps) .f south = b
      backward (b , ps) .f (meridian a i) = ps a i
      backward (b , ps) .preserves-★ = refl

      fb : ∀ p -> forward (backward p) == p
      fb (b , ps) = cong (b ,_) (funExt (\a -> compPath-refl-left (ps a)))

      bf : ∀ f -> backward (forward f) == f
      bf (->∙-cons f p) i .f north = p (~ i)
      bf (->∙-cons f p) i .f south = (f south)
      bf (->∙-cons f p) i .f (meridian a j) = path i j
        where
        path : PathP (\i -> p (~ i) == f south) (sym p >=> cong f (meridian a)) (cong f (meridian a))
        path =
          transP-left
            (\i -> (\j -> p (~ j ∧ (~ i))) >=> cong f (meridian a))
            (compPath-refl-left (cong f (meridian a)))
      bf (->∙-cons f p) i .preserves-★ j = p (j ∨ (~ i))

    T₂ : Type _
    T₂ = Σ[ b ∈ B ] Σ[ p ∈ (★B == b) ] Σ[ ps ∈ (∀ a -> ★B == b) ] (ps ★A == p)

    iso₂ : Iso (Σ B (\b -> A -> ★B == b)) T₂
    iso₂ = iso f b fb bf
      where
      f : (Σ B (\b -> A -> ★B == b)) -> T₂
      f (b , ps) = (b , ps ★A , ps , refl)
      b : T₂ -> (Σ B (\b -> A -> ★B == b))
      b (b , p , ps , pp) = (b , ps)
      fb : ∀ x -> f (b x) == x
      fb (b , p , ps , pp) = (\ i -> b , pp i , ps , (\j -> pp (j ∧ i)))
      bf : ∀ x -> b (f x) == x
      bf _ = refl

    -- module _ (Q : B -> Type ℓB) where
    --   iso-Q : Iso (Σ[ b ∈ B ] Σ[ p ∈ (★B == b) ] (Q b)) (Q ★B)
    --   iso-Q = iso f b fb bf
    --     where
    --     b : (Q ★B) -> (Σ[ b ∈ B ] Σ[ p ∈ (★B == b) ] (Q b))
    --     b q = (★B , refl , q)
    --     f : Σ[ b ∈ B ] Σ[ p ∈ (★B == b) ] (Q b) -> Q ★B
    --     f (b , p , q) = transport (\i -> Q (p (~ i))) q

    --     bf : ∀ x -> b (f x) == x
    --     bf (b , p , q) i =
    --       p i , (\j -> p (i ∧ j)) , (transp (\j -> Q (p (~ j ∨ i))) i q)
    --
    --     fb : ∀ x -> f (b x) == x
    --     fb q j = transp (\i -> Q ★B) j q

    module _ {ℓ : Level} (Q : (b : B) -> ★B == b -> Type ℓ) where
      iso-Q : Iso (Σ[ b ∈ B ] Σ[ p ∈ (★B == b) ] (Q b p)) (Q ★B refl)
      iso-Q = iso f b fb bf
        where
        b : (Q ★B refl) -> (Σ[ b ∈ B ] Σ[ p ∈ (★B == b) ] (Q b p))
        b q = (★B , refl , q)
        f : Σ[ b ∈ B ] Σ[ p ∈ (★B == b) ] (Q b p) -> Q ★B refl
        f (b , p , q) = transport (\i -> Q (p (~ i)) (\j -> p (~ i ∧ j))) q

        bf : ∀ x -> b (f x) == x
        bf (b , p , q) i =
          p i , (\j -> p (i ∧ j)) ,
                (transp (\j -> Q (p (~ j ∨ i)) (\k -> p ((~ j ∨ i) ∧ k))) i q)

        fb : ∀ x -> f (b x) == x
        fb q j = transp (\i -> Q ★B refl) j q

    iso₃ : Iso T₂ (Σ[ ps ∈ (∀ a -> ★B == ★B) ] (ps ★A == refl))
    iso₃ = iso-Q (\b p -> Σ[ ps ∈ (∀ a -> ★B == b) ] (ps ★A == p))

    iso4 : Iso (Σ[ ps ∈ (∀ a -> ★B == ★B) ] (ps ★A == refl)) (A∙ ->∙ Ω B∙)
    iso4 = iso (\ (ps , p) -> ->∙-cons ps p) (\ (->∙-cons ps p) -> ps , p)
             (\_ -> refl) (\_ -> refl)

  Susp∙-Ω-map-eq : (Susp∙ A∙ ->∙ B∙) ≃ (A∙ ->∙ Ω B∙)
  Susp∙-Ω-map-eq =
    isoToEquiv ((iso₁ >iso> iso₂) >iso> (iso₃ >iso> iso4))

  Susp∙-Ω-map-path : (Susp∙ A∙ ->∙∙ B∙) == (A∙ ->∙∙ Ω B∙)
  Susp∙-Ω-map-path =
    sigmaPath->pathSigma _ _ (ua Susp∙-Ω-map-eq , path)
    where
    f1 = Iso.fun iso₁
    f2 = Iso.fun iso₂
    f3 = Iso.fun iso₃
    f4 = Iso.fun iso4

    path-f1 : f1 (->∙-cons (\_ -> ★B) refl) == (★B , \a -> refl)
    path-f1 i = (★B , \a -> compPath-refl-right refl i)
    path-f3 : f3 (★B , refl , (\_ -> refl) , refl) == ((\_ -> refl) , refl)
    path-f3 = transportRefl _

    path₂ : (f4 (f3 (f2 (f1 (->∙-cons (\_ -> ★B) refl))))) ==
            (->∙-cons (\_ -> reflᵉ ★B) refl)
    path₂ = cong (f4 ∘ f3 ∘ f2) path-f1 >=> cong f4 path-f3

    path : _ == _
    path = (\i -> transport-isoToPath ((iso₁ >iso> iso₂) >iso> (iso₃ >iso> iso4)) i
                                      (->∙-cons (\_ -> ★B) refl)) >=> path₂



{-
  iso₃ : Iso T₁ (A∙ ->∙ Ω B∙)
  iso₃ = ?
    where


    b : (A∙ ->∙ Ω B∙) -> T₁
    b (->∙-cons ps pp) = (★B , ps , refl , pp)


    where
    f : T₁ -> (A∙ ->∙ Ω B∙)
    f (b , ps , p , pp) = ->∙-cons f' (f'★₁ >=> f'★₂)
      where
      f' : A -> ⟨ Ω B∙ ⟩
      f' a = (transport (\i -> ★B == p (~ i)) (ps a))

      f'★₁ : f' ★A == (transport (\i -> ★B == p (~ i)) p)
      f'★₁ j = (transport (\i -> ★B == p (~ i)) (pp j))
      f'★₂ : (transport (\i -> ★B == p (~ i)) p) == refl
      f'★₂ j = (transp (\i -> ★B == p (~ i ∧ ~ j)) j (\i -> p (i ∧ ~ j)))

    b : (A∙ ->∙ Ω B∙) -> T₁
    b (->∙-cons ps pp) = (★B , ps , refl , pp)

    fb : ∀ x -> f (b x) == x
    fb (->∙-cons ps pp) = \i -> ->∙-cons (\a -> ps-path a i) (pp-path i)
      where
      ps-path : ∀ a -> (transport (\i -> ★B == ★B) (ps a)) == ps a
      ps-path a i = transp (\i -> ★B == ★B) i (ps a)

      pp-path :
        PathP (\i -> ps-path ★A i == refl)
          ((\j -> transport (\i -> ★B == ★B) (pp j)) >=>
           (\j -> transp (\i -> ★B == ★B) j (\i -> ★B))) pp
      pp-path = ?
        where
        f'★₂ : (transport (\i -> ★B == ★B) (\i -> ★B)) == refl
        f'★₂ = (\j -> transp (\i -> ★B == ★B) j (\i -> ★B))
        s₁ : ∀ i j -> f'★₂ i j == ★B
        s₁ j i k = (transp (\i -> ★B == ★B) (j ∨ k) (\i -> ★B)) i

    bf : ∀ x -> b (f x) == x
    bf (b , ps , p , pp) = \i -> p i , (\a -> ps-path a i) , ? , ?
      where
      ps-path : ∀ a ->
        PathP (\i -> ★B == p i)
              (transport (\i -> ★B == p (~ i)) (ps a))
              (ps a)
      ps-path a = symP (transport-filler (\i -> ★B == p (~ i)) (ps a))
-}




    -- fb : ∀ x -> f (b x) == x
    -- fb (->∙-cons ps pp) i =
    --   ->∙-cons (\a -> compPath-refl-right (ps a) i) ans
    --   where
    --   ans : ?
    --   ans = ?


    -- f₂ : Σ B T₁ -> (A∙ ->∙ Ω B∙)
    -- f₂ = ?


{-
  iso₂ : Iso (Σ B (\b -> A -> ★B == b)) (A∙ ->∙ Ω B∙)
  iso₂ = iso forward' backward fb' bf'
    where
    forward : (Σ B (\b -> A -> ★B == b)) -> (A∙ ->∙ Ω B∙)
    forward (b , ps) = ->∙-cons f (compPath-sym (ps ★A))
      where
      f : A -> ⟨ Ω B∙ ⟩
      f a = ps a >=> sym (ps ★A)

    forward'-f : (Σ B (\b -> A -> ★B == b)) -> A -> ⟨ Ω B∙ ⟩
    forward'-f (b , ps) a =
      transport (\i -> ★B == (ps ★A (~ i))) (ps a)

    forward'-★A : ∀ (p : (Σ B (\b -> A -> ★B == b))) -> forward'-f p ★A == refl
    forward'-★A (b , ps) j =
      transp (\i -> ★B == (ps ★A (~ i ∧ ~ j))) j (\k -> ps ★A (k ∧ ~ j))

    forward' : (Σ B (\b -> A -> ★B == b)) -> (A∙ ->∙ Ω B∙)
    forward' p = ->∙-cons (forward'-f p) (forward'-★A p)

    backward : (A∙ ->∙ Ω B∙) -> (Σ B (\b -> A -> ★B == b))
    backward (->∙-cons f p) = ★B , f

    bf' : ∀ p -> backward (forward' p) == p
    bf' (b , ps) = \i -> p₁ i , p₂ i
      where
      p₁ : ★B == b
      p₁ = ps ★A
      p₂ : PathP (\i -> A -> ★B == p₁ i)
                 (\a -> (transport (\i -> ★B == (ps ★A (~ i))) (ps a)))
                 ps
      p₂ i a = transp (\j -> ★B == (ps ★A (~ j ∨ i))) i (ps a)

    fb' : ∀ f -> forward' (backward f) == f
    fb' (->∙-cons f p) = \i -> ->∙-cons (f-path i) (p-path i)
      where
      f-path₁ :
        Path (A -> _)
          (\a -> transport (\i -> ★B == (f ★A (~ i))) (f a))
          (\a -> transport (\i -> ★B == ★B) (f a))
      f-path₁ j a = transport (\i -> ★B == p j (~ i)) (f a)

      f-path₂ : (\a -> transport (\i -> ★B == ★B) (f a)) == f
      f-path₂ = (\i a -> transportRefl (f a) i)

      f-path : forward'-f (backward (->∙-cons f p)) == f
      f-path = f-path₁ >=> f-path₂

      p-path :
        PathP (\i -> f-path i ★A == (reflᵉ ★B))
          (forward'-★A (★B , f))
          p
      p-path = ?



    bf : ∀ p -> (backward (forward p)) == p
    bf (b , ps) = \i -> p₁ i , p₂ i
      where
      p₁ : ★B == b
      p₁ = ps ★A
      p₂ : PathP (\i -> A -> ★B == p₁ i)
                 (\a -> ps a >=> sym (ps ★A))
                 ps
      p₂ = transP-left
             (\i a -> ps a >=> (\j -> ps ★A (~ j ∨ i)))
             (funExt (\a -> compPath-refl-right (ps a)))


    -- fb : ∀ f -> forward (backward f) == f
    -- fb (->∙-cons f p) = f-path
    --   where
    --   c : (A∙ ->∙ Ω B∙)
    --   c = forward (backward (->∙-cons f p))

    --   f-path : app∙ c == f
    --   f-path = funExt (\a -> cong (\b -> f a >=> sym b) p >=> compPath-refl-right (f a))
-}


{-
  Susp∙-Ω-map-path : (Susp∙ A∙ ->∙ B∙) ≃ (A∙ ->∙ Ω B∙)
  Susp∙-Ω-map-path = isoToEquiv (iso forward backward magic magic)
    where
    φ∙ : A∙ ->∙ Ω (Susp∙ A∙)
    φ∙ = ->∙-cons (\a -> meridian a >=> sym (meridian ★A))
                  (compPath-sym (meridian ★A))

    forward : (Susp∙ A∙ ->∙ B∙) -> (A∙ ->∙ Ω B∙)
    forward (->∙-cons f p) = ->∙-cons g q
      where
      g : A -> ⟨ Ω B∙ ⟩
      g a = sym p ∙∙ (cong f (app∙ φ∙ a)) ∙∙ p
      q : g ★A == refl
      q = (\j -> sym p ∙∙ (\i -> f (->∙-path φ∙ j i)) ∙∙ p) >=>
          compPath-sym (sym p)

    ψ : (A -> ⟨ Ω B∙ ⟩) -> (Susp A -> B)
    ψ f north = ★B
    ψ f south = ★B
    ψ f (meridian a i) = f a i

    backward : (A∙ ->∙ Ω B∙) -> (Susp∙ A∙ ->∙ B∙)
    backward (->∙-cons f p) = (->∙-cons (ψ f) refl)

    {-
      fib-backward : ∀ f -> fiber backward f
      fib-backward (->∙-cons f p) = ?
        where
        check-f : Susp A -> B
        check-f = f

        ψ' : (i : I) -> (Susp A -> B)
        ψ' i north = ★B
        ψ' i south = p (~ i)
        ψ' i (meridian a j) = ?
    -}
-}






    {-

    bf : ∀ f -> backward (forward f) == f
    bf (->∙-cons f p) = ?
      where
      c1 : Susp A -> B
      c1 = app∙ (backward (forward (->∙-cons f p)))

      c2 : Susp A -> B
      c2 = ψ (\a -> sym p ∙∙ (cong f (app∙ φ∙ a)) ∙∙ p)

      c1=c2 : c1 == c2
      c1=c2 = refl

      c2=f : c2 == f
      c2=f i north = (sym p ∙∙ refl                 ∙∙ refl) i
      c2=f i south = (sym p ∙∙ cong f (meridian ★A) ∙∙ refl) i
      c2=f i (meridian a j) = ?
        where
        check : c2 (meridian a j) == (sym p ∙∙ (cong f (meridian a >=> sym (meridian ★A))) ∙∙ p) j
        check = refl

        -- path :


      fb : ∀ f -> forward (backward f) == f
      fb (->∙-cons f p) = (\i -> ->∙-cons (ans₁ i) (ans₂ i))
        where
        c : (A∙ ->∙ Ω B∙)
        c = (forward (backward (->∙-cons f p)))

        c15 : (A∙ ->∙ Ω B∙)
        c15 = ->∙-cons (app∙ c) (refl >=> ->∙-path c)

        c=c15 : c == c15
        c=c15 i = ->∙-cons (app∙ c) (compPath-refl-left (->∙-path c) (~ i))


        check' : app∙ c == (\a -> (cong (ψ f) (app∙ φ∙ a)))
        check' = funExt (\a -> sym (doubleCompPath-filler refl _ refl))

        c2 : (A∙ ->∙ Ω B∙)
        c2 = ->∙-cons (\a -> (cong (ψ f) (app∙ φ∙ a)))
                      ((\i -> check' (~ i) ★A) >=> ->∙-path c)

        c15=c2 : c15 == c2
        c15=c2 i = ->∙-cons (check' i) ((\j -> check' (~ j ∧ i) ★A) >=> ->∙-path c)


        check'2 : ∀ a -> (cong (ψ f) (app∙ φ∙ a)) == (f a >=> sym (f ★A))
        check'2 a = cong-trans (ψ f) (meridian a) (sym (meridian ★A))

        check'3 : ∀ a -> (f a >=> sym (f ★A)) == f a
        check'3 a = (\i -> f a >=> (sym (p i))) >=> compPath-refl-right (f a)

        ans₁ : app∙ c == f
        ans₁ = check' >=> (funExt (\a -> check'2 a >=> check'3 a))

        ans₂ : PathP (\i -> ans₁ i ★A == refl) (->∙-path c) p
        ans₂ = ?
    -}
