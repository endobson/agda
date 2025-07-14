{-# OPTIONS --cubical --safe --exact-split #-}

module equality.null-homotopic where

open import base
open import cubical
open import hlevel.base
open import equality-path
open import equality.square

isNull¹ : {ℓ : Level} {A : Type ℓ} {a : A} -> Pred (a == a) ℓ
isNull¹ p = Square p refl refl refl

isNull² : {ℓ : Level} {A : Type ℓ} {a : A} {p₁ p₂ p₃ p₄ : a == a} -> Pred (Square p₁ p₂ p₃ p₄) ℓ
isNull² {a = a} {p₁} {p₂} {p₃} {p₄} s =
  Σ[ (h₁ , h₂ , h₃ , h₄) ∈ (isNull¹ p₁ × isNull¹ p₂ × isNull¹ p₃ × isNull¹ p₄) ]
    PathP (\k -> Square (h₁ k) (h₂ k) (h₃ k) (h₄ k)) s (\i j -> a)

module _ {ℓ : Level} {A : Type ℓ} (a : A) where
  isContr-ΣisNull¹ : isContr (Σ (a == a) isNull¹)
  isContr-ΣisNull¹ =
    (refl , \i j -> a) ,
    (\ (p , n) k -> ((\j -> n (~ k) j) , (\i j -> n (~ k ∨ i) j)))

  isNull¹-refl : isNull¹ (reflᵉ a)
  isNull¹-refl = refl



module _ {ℓ : Level} {A : Type ℓ} {a : A} where

  isNull¹->=> : {p₁ p₂ : a == a} ->
    isNull¹ p₁ -> isNull¹ p₂ ->
    isNull¹ (p₁ >=> p₂)
  isNull¹->=> {p₁} {p₂} s₁ s₂ i j =
    hcomp (\k -> \{ (i = i0) -> doubleCompPath-filler p₁ refl p₂ k j
                  ; (i = i1) -> a
                  ; (j = i0) -> s₁ i (~ k)
                  ; (j = i1) -> s₂ i k
                  })
      a

  isNull¹-∙∙ : {p₁ p₂ p₃ : a == a} ->
    isNull¹ p₁ -> isNull¹ p₂ -> isNull¹ p₃ ->
    isNull¹ (p₁ ∙∙ p₂ ∙∙ p₃)
  isNull¹-∙∙ {p₁} {p₂} {p₃} s₁ s₂ s₃ i j =
    hcomp (\k -> \{ (i = i0) -> (p₁ ∙∙ p₂ ∙∙ p₃) j
                  ; (i = i1) -> s₂ k j
                  ; (j = i0) -> s₁ k i
                  ; (j = i1) -> s₃ k (~ i)
                  })
      (doubleCompPath-filler p₁ p₂ p₃ (~ i) j)


  isNull¹-sym : {p : a == a} -> isNull¹ p -> isNull¹ (sym p)
  isNull¹-sym s i j = s i (~ j)

module _ {ℓ : Level} {A : Type ℓ} {a₁ a₂ : A} where
  private
    isNull¹-∙∙-sym' : (p₁ : a₁ == a₂) ->
      isNull¹ (p₁ ∙∙ refl ∙∙ sym p₁)
    isNull¹-∙∙-sym' p₁ i j =
      hcomp (\k -> \{ (i = i0) -> (p₁ ∙∙ refl ∙∙ (sym p₁)) j
                    ; (i = i1) -> p₁ (~ k)
                    ; (j = i0) -> p₁ (i ∧ ~ k)
                    ; (j = i1) -> p₁ (i ∧ ~ k)
                    })
        (doubleCompPath-filler p₁ refl (sym p₁) (~ i) j)

    isNull¹-∙∙-sym'₂ : (p₁ : a₁ == a₂) ->
      isNull¹ (p₁ ∙∙ refl ∙∙ sym p₁)
    isNull¹-∙∙-sym'₂ = compPath-sym

  isNull¹-∙∙-sym : (p₁ : a₁ == a₂) -> {p₂ : a₂ == a₂} ->
    isNull¹ p₂ -> isNull¹ (p₁ ∙∙ p₂ ∙∙ sym p₁)
  isNull¹-∙∙-sym p₁ {p₂} s₁ =
    cong (p₁ ∙∙_∙∙ (sym p₁)) s₁ >=> isNull¹-∙∙-sym'₂ p₁


module _ {ℓ : Level} {A : Type ℓ} (a : A) where
  isNull¹-∙∙-refl'₁ :
    PathP (\i -> isNull¹ (∙∙-refl-sides (reflᵉ a) i))
      (compPath-sym (reflᵉ a)) (reflᵉ (reflᵉ a))
  isNull¹-∙∙-refl'₁ i j k = ans k
    where
    module _ (k : I) where
      spec : Partial (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k) A
      spec (i = i0) = hfill (\l -> (\ { (k = i0) -> a
                                      ; (k = i1) -> a }))
                       (inS a) (~ j)
      spec (i = i1) = a
      spec (j = i0) = hfill (\l -> (\ { (k = i0) -> a
                                      ; (k = i1) -> a }))
                       (inS a) (~ i)
      spec (j = i1) = a
      spec (k = i0) = a
      spec (k = i1) = a

    ans : (k : I) -> A
    ans k =
      hfill (\l -> (\ { (k = i0) -> a
                      ; (k = i1) -> a }))
       (inS a) (~ j ∧ ~ i)

  isNull¹-∙∙-refl'₂ :
    PathP (\i -> isNull¹ (∙∙-refl-sides (reflᵉ a) i))
      (isNull¹-∙∙-sym (reflᵉ a) (reflᵉ (reflᵉ a))) (reflᵉ (reflᵉ a))
  isNull¹-∙∙-refl'₂ = transP-right (compPath-refl-left _) isNull¹-∙∙-refl'₁


module _ {ℓ : Level} {A : Type ℓ} {a : A} {p : a == a} where
  isNull¹-∙∙-refl : (n : isNull¹ p) ->
    PathP (\i -> isNull¹ (∙∙-refl-sides p i))
      (isNull¹-∙∙-sym refl n) n
  isNull¹-∙∙-refl n = subst P path P-refl
    where
    P : Σ (a == a) isNull¹ -> Type ℓ
    P (p , n) = PathP (\i -> isNull¹ (∙∙-refl-sides p i))
                 (isNull¹-∙∙-sym refl n) n

    P-refl : P (refl , refl)
    P-refl = isNull¹-∙∙-refl'₂ a

    path : Path (Σ (a == a) isNull¹) (refl , refl) (p , n)
    path = snd (isContr-ΣisNull¹ a) (p , n)



module _ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (f : A → B)
         {φ : I} (u : ∀ i → Partial φ A)
         (u₀ : Sub A φ \{ (φ = i1) -> u i0 1=1 })
  where
  hcomp-commute :
    f (hcomp u (outS u₀)) == hcomp (\i → \{ (φ = i1) -> f (u i 1=1) }) (f (outS u₀))
  hcomp-commute i =
    hcomp (\j -> \{ (φ = i1) -> f (u j 1=1)
                  ; (i = i0) -> f (hfill u u₀ j)
                  ; (i = i1) -> hfill (\k -> \{ (φ = i1) -> f (u k 1=1) }) (inS (f (outS u₀))) j
                  })
      (f (outS u₀))

module _
  {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} (f : A -> B)
  {a₁ a₂ : A} (p : a₁ == a₂)
  where

  private
    side₁ : cong f (p >=> sym p) == refl
    side₁ = cong (cong f) (compPath-sym p)
    side₂ : cong f (p >=> sym p) == cong f p >=> sym (cong f p)
    side₂ = cong-∙∙ f p refl (sym p)
    side₃ : cong f p >=> sym (cong f p) == refl
    side₃ = compPath-sym (cong f p)




module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} where
  isNull¹-cong : (f : A -> B) {a : A} {p : a == a} -> isNull¹ p -> isNull¹ (cong f p)
  isNull¹-cong f s i j = f (s i j)




private
  module _
    {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} (f : A -> B)
    {a₂ : A} {p₂ : a₂ == a₂} (s : isNull¹ p₂)
    where

    -- make-isNull²-square :
    --   {s₁p₁ s₁p₂ s₁p₃ s₁p₄ : a₂ == a₂} {s₁ : Square s₁p₁ s₁p₂ s₁p₃ s₁p₄} (n₁ : isNull² s₁) ->
    --   {s₂p₁ s₂p₂ s₂p₃ s₂p₄ : a₂ == a₂} {s₂ : Square s₂p₁ s₂p₂ s₂p₃ s₂p₄} (n₂ : isNull² s₂) ->
    --   {s₃p₁ s₃p₂ s₃p₃ s₃p₄ : a₂ == a₂} {s₃ : Square s₃p₁ s₃p₂ s₃p₃ s₃p₄} (n₃ : isNull² s₃) ->
    --   {s₄p₁ s₄p₂ s₄p₃ s₄p₄ : a₂ == a₂} {s₄ : Square s₄p₁ s₄p₂ s₄p₃ s₄p₄} (n₄ : isNull² s₄) ->
    --   Square s₁ s₂ s₃ s₄
    -- make-isNull²-square = ?


    isNull¹-cong-∙∙-sym' :
      PathP (\i -> isNull¹ (cong-∙∙ f refl p₂ refl i))
          (isNull¹-cong f (isNull¹-∙∙-sym refl s))
          (isNull¹-∙∙-sym (cong f refl) (isNull¹-cong f s))
    isNull¹-cong-∙∙-sym' = transP-right step₁ step₂
      where

      stage₀ : isNull¹ (cong f (refl ∙∙ p₂ ∙∙ refl))
      stage₀ = cong (cong f) (cong (refl ∙∙_∙∙ refl) s >=> ∙∙-refl)

      stage₁ : isNull¹ (cong f (refl ∙∙ p₂ ∙∙ refl))
      stage₁ = (cong (\p -> (cong f (refl ∙∙ p ∙∙ refl))) s) >=> (cong (cong f) ∙∙-refl)

      stage₂ : isNull¹ (refl ∙∙ cong f p₂ ∙∙ refl)
      stage₂ = (cong (\p -> (refl ∙∙ cong f p ∙∙ refl)) s) >=> ∙∙-refl


      step₁ : stage₀ == stage₁
      step₁ = cong-∙∙ (cong f) (cong (refl ∙∙_∙∙ refl) s) refl ∙∙-refl

      step₂ : PathP (\i -> cong-∙∙ f refl p₂ refl i == refl) stage₁ stage₂
      step₂ = check₂'1 ▪v check₂'2 ▪v check₂'3
        where
        check : (\(p : (a₂ == a₂)) -> (cong f (refl ∙∙ p ∙∙ refl))) == (\p -> (refl ∙∙ cong f p ∙∙ refl))
        check i p = cong-∙∙ f refl p refl i

        check₂'1 :
          PathP (\i -> cong-∙∙ f refl p₂ refl i == cong-∙∙ f refl refl refl i)
            (cong (\ (p : (a₂ == a₂)) -> (cong f (refl ∙∙ p ∙∙ refl))) s)
            (cong (\ p -> (refl ∙∙ cong f p ∙∙ refl)) s)
        check₂'1 i = cong (check i) s

        check₂'2 :
          PathP (\i -> cong-∙∙ f refl refl refl i == cong-∙∙ f refl refl refl i) refl refl
        check₂'2 i j = cong-∙∙ f refl refl refl i


        check₂'3 :
          Square
            (cong (cong f) ∙∙-refl) ∙∙-refl
            (cong-∙∙ f refl refl refl) refl
        check₂'3 i j k = cong-doubleCompPath-filler f (reflᵉ a₂) refl refl i (~ j) k


      left : (isNull¹-cong f (isNull¹-∙∙-sym refl s)) == stage₀
      left = refl
      right : (isNull¹-∙∙-sym (cong f refl) (isNull¹-cong f s)) == stage₂
      right = refl

module _
  {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} (f : A -> B)
  {a₁ a₂ : A} (p₁ : a₁ == a₂)
  {p₂ : a₂ == a₂} (s : isNull¹ p₂)

  where

  isNull¹-cong-∙∙-sym :
    PathP (\i -> isNull¹ (cong-∙∙ f p₁ p₂ (sym p₁) i))
        (isNull¹-cong f (isNull¹-∙∙-sym p₁ s))
        (isNull¹-∙∙-sym (cong f p₁) (isNull¹-cong f s))
  isNull¹-cong-∙∙-sym =
    J (\a p₁ -> PathP (\i -> isNull¹ (cong-∙∙ f (sym p₁) p₂ p₁ i))
                 (isNull¹-cong f (isNull¹-∙∙-sym (sym p₁) s))
                 (isNull¹-∙∙-sym (cong f (sym p₁)) (isNull¹-cong f s)))
      (isNull¹-cong-∙∙-sym' f s)
      (sym p₁)




module _ {ℓ : Level} {A : Type ℓ} {a : A} where
  isNull¹-path : {p₁ p₂ : a == a} -> isNull¹ p₁ -> isNull¹ p₂ -> p₁ == p₂
  isNull¹-path n₁ n₂ =
    cong fst (isContr->isProp (isContr-ΣisNull¹ a) (_ , n₁) (_ , n₂))
