{-# OPTIONS --cubical --safe --exact-split #-}

module graph.simple.walk-conversion where

open import base
open import decision
open import discrete
open import equality-path
open import equivalence.injective-surjective
open import fin
open import functions
open import graph.simple
open import graph.simple.finite-walk
open import graph.simple.inductive-walk
open import nat
open import nat.order
open import order
open import order.instances.fin
open import order.instances.nat
open import relation

module _ {ℓV ℓE : Level} {G : Graph ℓV ℓE} where
  open Graph G

  module ForwardInductiveWalk->FiniteWalk where
    length : {v₁ v₂ : V} -> ForwardInductiveWalk G v₁ v₂ -> ℕ
    length (walk-end _) = zero
    length (walk-step _ _ _ _ w) = suc (length w)

    vs : {v₁ v₂ : V} -> (w : ForwardInductiveWalk G v₁ v₂) -> Fin (suc (length w)) -> V
    vs (walk-end v) _ = v
    vs (walk-step v₁ v₂ v₃ e w) (zero  , _) = v₁
    vs (walk-step v₁ v₂ v₃ e w) (suc i , si<sl) = vs w (i , pred-≤ si<sl)

    es : {v₁ v₂ : V} -> (w : ForwardInductiveWalk G v₁ v₂) -> (i : Fin (length w)) ->
         E (vs w (inc-fin i)) (vs w (suc-fin i))
    es (walk-end v) i = bot-elim (¬fin-zero i)
    es (walk-step v₁ v₂ v₂ e₁₂ (walk-end v₂)) (zero , _) = e₁₂
    es (walk-step v₁ v₂ v₂ e₁₂ (walk-end v₂)) (suc i , si<l) =
      bot-elim (zero-≮ (pred-≤ si<l))
    es (walk-step v₁ v₂ v₄ e₁₂ (walk-step v₂ v₃ v₄ e₂₃ _)) (zero , _) = e₁₂
    es (walk-step v₁ v₂ v₄ e₁₂ w@(walk-step v₂ v₃ v₄ e₂₃ _)) (suc i , si<l) =
      subst2 E (cong (vs w) p₁) (cong (vs w) p₂) (es w (i , pred-≤ si<l))
      where
      p₁ : (inc-fin (i , pred-≤ si<l)) == _
      p₁ = fin-i-path refl
      p₂ : (suc-fin (i , pred-≤ si<l)) == _
      p₂ = fin-i-path refl


  ForwardInductiveWalk->FiniteWalk :
    {v₁ v₂ : V} -> ForwardInductiveWalk G v₁ v₂ -> FiniteWalk G
  ForwardInductiveWalk->FiniteWalk w = record
    { N = length w
    ; vs = vs w
    ; es = es w
    }
    where
    open ForwardInductiveWalk->FiniteWalk

  FiniteWalk->ForwardInductiveWalk : (w : FiniteWalk G) ->
    ForwardInductiveWalk G (FiniteWalk.vs w zero-fin) (FiniteWalk.vs w max-fin)
  FiniteWalk->ForwardInductiveWalk =
    \w -> FiniteWalk'->ForwardInductiveWalk _ (FiniteWalk.vs w) (FiniteWalk.es w)
    where

    FiniteWalk'->ForwardInductiveWalk :
      (N : Nat) ->
      (vs : Fin (suc N) -> V) ->
      (es : ∀ i -> E (vs (inc-fin i)) (vs (suc-fin i))) ->
      ForwardInductiveWalk G (vs zero-fin) (vs max-fin)
    FiniteWalk'->ForwardInductiveWalk zero vs es =
      subst (ForwardInductiveWalk G _) (cong vs (fin-i-path refl)) (walk-end (vs zero-fin))
    FiniteWalk'->ForwardInductiveWalk (suc n) vs es =
      (walk-step _ _ _ e' rec')
      where
      rec : ForwardInductiveWalk G (vs (suc-fin zero-fin)) (vs (suc-fin max-fin))
      rec = FiniteWalk'->ForwardInductiveWalk n (vs ∘ suc-fin) es'
        where
        es' : ∀ i -> E (vs (suc-fin (inc-fin i))) (vs (suc-fin (suc-fin i)))
        es' i = subst (\v -> E v (vs (suc-fin (suc-fin i)))) (cong vs (fin-i-path refl)) (es (suc-fin i))

      rec' : ForwardInductiveWalk G (vs (suc-fin zero-fin)) (vs max-fin)
      rec' = subst (ForwardInductiveWalk G (vs (suc-fin zero-fin)))
                   (cong vs (fin-i-path refl)) rec

      e' : E (vs zero-fin) (vs (suc-fin zero-fin))
      e' = subst (\v -> E v (vs (suc-fin zero-fin))) (cong vs (fin-i-path refl)) (es zero-fin)


module _ {ℓV ℓE : Level} {G : Graph ℓV ℓE} where
  open Graph G
  private
    FIW = ForwardInductiveWalk
    isPath = ForwardInductiveWalk-isPath
    AvoidsVertex = ForwardInductiveWalk-AvoidsVertex

  opaque
    ForwardInductiveWalk->FiniteWalk-¬AvoidsVertex :
      {v₁ v₂ : V} ->
      (w : ForwardInductiveWalk G v₁ v₂) ->
      ∀ i -> ¬ (AvoidsVertex w (FiniteWalk.vs (ForwardInductiveWalk->FiniteWalk w) i))
    ForwardInductiveWalk->FiniteWalk-¬AvoidsVertex
      (walk-end _) (zero , _) ¬p = ¬p refl
    ForwardInductiveWalk->FiniteWalk-¬AvoidsVertex
      (walk-end _) (suc i , lt) ¬p = bot-elim (zero-≮ (pred-≤ lt))
    ForwardInductiveWalk->FiniteWalk-¬AvoidsVertex
      (walk-step _ _ _ _ _) (zero , _) (¬p , ¬ps) = ¬p refl
    ForwardInductiveWalk->FiniteWalk-¬AvoidsVertex
      (walk-step _ _ _ _ w) (suc i , lt) (_ , ¬ps) =
      ForwardInductiveWalk->FiniteWalk-¬AvoidsVertex w (i , pred-≤ lt) ¬ps

    ForwardInductiveWalk->FiniteWalk-preserves-Path :
      {v₁ v₂ : V} ->
      (w : ForwardInductiveWalk G v₁ v₂) -> isPath w ->
      FiniteWalk-isPath (ForwardInductiveWalk->FiniteWalk w)
    ForwardInductiveWalk->FiniteWalk-preserves-Path w pw =
      isSet-isInjective->isEmbedding isSet-V inj-vs
      where
      module FW = FiniteWalk (ForwardInductiveWalk->FiniteWalk w)
      inj-vs : isInjective FW.vs
      inj-vs {i₁} {i₂} v₁=v₂ = case (trichotomous-< i₁ i₂) of
        \{ (tri< i₁<i₂ _ _) -> bot-elim (handle w pw _ _ i₁<i₂ v₁=v₂)
         ; (tri= _ i₁=i₂ _) -> i₁=i₂
         ; (tri> _ _ i₂<i₁) -> bot-elim (handle w pw _ _ i₂<i₁ (sym v₁=v₂))
         }
        where
        N' : {v₁ v₂ : V} -> (w : FIW G v₁ v₂) -> Nat
        N' = ForwardInductiveWalk->FiniteWalk.length
        vs' : {v₁ v₂ : V} -> (w : FIW G v₁ v₂) -> (Fin (suc (N' w))) -> V
        vs' = ForwardInductiveWalk->FiniteWalk.vs

        handle :
          {v₁ v₂ : V} -> (w : FIW G v₁ v₂) -> isPath w ->
          (i₁ i₂ : Fin (suc (N' w))) -> (i₁ < i₂) ->
          vs' w i₁ == vs' w i₂ ->
          Bot
        handle (walk-end v) _ (i₁ , i₁<1) (i₂ , i₂<1) (fin< i₁<i₂) _ =
          zero-≮ (trans-<-= i₁<i₂ i₂=0)
          where
          i₂=0 : i₂ == 0
          i₂=0 = zero-≤->zero (pred-≤ i₂<1)
        handle (walk-step v₁ _  _ _ w) (¬v₁∈w , pw) _              (zero   , lt₂) (fin< i<0) _ = zero-≮ i<0
        handle (walk-step v₁ v₂ _ e w) (¬v₁∈w , pw) (zero   , lt)  (suc i₂ , lt₂) (fin< _)   p =
          bot-elim (ForwardInductiveWalk->FiniteWalk-¬AvoidsVertex w (i₂ , pred-≤ lt₂)
                       (subst (AvoidsVertex w) p ¬v₁∈w))
        handle (walk-step v₁ _ _ _ w) (¬v₁∈w , pw) (suc i₁ , lt₁) (suc i₂ , lt₂) (fin< si₁<si₂)   p =
          handle w pw (i₁ , pred-≤ lt₁) (i₂ , pred-≤ lt₂) (fin< (pred-≤ si₁<si₂)) p

    ForwardInductiveWalk->FiniteWalk-StartsWith :
      {v₁ v₂ : V} ->
      (w : ForwardInductiveWalk G v₁ v₂) ->
      FiniteWalk-StartsWith (ForwardInductiveWalk->FiniteWalk w) v₁
    ForwardInductiveWalk->FiniteWalk-StartsWith
      (walk-end v) = refl
    ForwardInductiveWalk->FiniteWalk-StartsWith
      (walk-step _ _ _ _ _) = refl

    ForwardInductiveWalk->FiniteWalk-EndsWith :
      {v₁ v₂ : V} ->
      (w : ForwardInductiveWalk G v₁ v₂) ->
      FiniteWalk-EndsWith (ForwardInductiveWalk->FiniteWalk w) v₂
    ForwardInductiveWalk->FiniteWalk-EndsWith
      (walk-end v) = refl
    ForwardInductiveWalk->FiniteWalk-EndsWith
       w₀@(walk-step _ _ _ _ w) = step >=> (ForwardInductiveWalk->FiniteWalk-EndsWith w)
      where
      step : ForwardInductiveWalk->FiniteWalk.vs w₀ max-fin ==
             ForwardInductiveWalk->FiniteWalk.vs w max-fin
      step = cong (ForwardInductiveWalk->FiniteWalk.vs w) (fin-i-path refl)



module _ {ℓV ℓE : Level} {G : Graph ℓV ℓE} where
  open Graph G
  private
    FIW = ForwardInductiveWalk
    isPath = ForwardInductiveWalk-isPath
    AvoidsVertex = ForwardInductiveWalk-AvoidsVertex

    NoExtraVertices : {v₁ v₂ v₃ v₄ : V} -> FIW G v₁ v₂ -> FIW G v₃ v₄ -> Type ℓV
    NoExtraVertices w₁ w₂ = ∀ v -> AvoidsVertex w₁ v -> AvoidsVertex w₂ v

  private
    -- For any path `p` and any vertex `v`, either:
    --   * `p` avoids `v`, or
    --   * Ther is a second path from `v` the that only uses vertices in `p`.
    FIP-vertex-case : {v₁ v₂ : V} ->
      (w₁ : FIW G v₁ v₂ ) -> (isPath w₁) -> (v : V) ->
      (AvoidsVertex w₁ v ⊎
       Σ[ w₂ ∈ FIW G v v₂ ] (isPath w₂ × NoExtraVertices w₁ w₂))
    FIP-vertex-case w₀@(walk-end v₁) pw₀ v = handle (decide-= v₁ v)
      where
      handle : Dec (v₁ == v) -> _
      handle (no v₁!=v) = (inj-l v₁!=v)
      handle (yes v₁=v) =
        inj-r (subst (\v -> (Σ[ w₁ ∈ FIW G v v₁ ] (isPath w₁ × NoExtraVertices w₀ w₁)))
                     v₁=v
                     (w₀ , pw₀ , \_ p -> p))
    FIP-vertex-case w₀@(walk-step v₁ v₂ v₃ _ w₁) pw₀@(v1∈w₁ , pw₁) v = handle (decide-= v₁ v)
      where
      handle : Dec (v₁ == v) -> _
      handle (yes v₁=v) =
        inj-r (subst (\v -> (Σ[ w₂ ∈ FIW G v v₃ ] (isPath w₂ × NoExtraVertices w₀ w₂)))
                     v₁=v
                     (w₀ , pw₀ , \_ p -> p))
      handle (no v₁!=v) = handle2 (FIP-vertex-case w₁ pw₁ v)
        where
        handle2 : (AvoidsVertex w₁ v ⊎ Σ[ w₂ ∈ FIW G v v₃ ] (isPath w₂ × NoExtraVertices w₁ w₂)) ->
                  (AvoidsVertex w₀ v ⊎ Σ[ w₃ ∈ FIW G v v₃ ] (isPath w₃ × NoExtraVertices w₀ w₃))
        handle2 (inj-l av₁) = inj-l (v₁!=v , av₁)
        handle2 (inj-r (w₂ , pw₂ , ex₂)) = inj-r (w₂ , pw₂ , \v (p , ps) -> ex₂ v ps)

    FIW->Path' : {v₁ v₂ : V} ->
      (w : FIW G v₁ v₂) -> (Σ[ w₂ ∈ FIW G v₁ v₂ ] (isPath w₂ × NoExtraVertices w w₂))
    FIW->Path' (walk-end v) = (walk-end v) , lift tt , (\_ p -> p)
    FIW->Path' w₀@(walk-step v₁ v₂ v₃ e w₁) = handle (FIP-vertex-case w₂ pw₂ v₁)
      where
      Σw₂ : Σ[ w₂ ∈ FIW G v₂ v₃ ] (isPath w₂ × NoExtraVertices w₁ w₂)
      Σw₂ = FIW->Path' w₁

      w₂ = fst Σw₂
      pw₂ = fst (snd Σw₂)
      ex₂ = snd (snd Σw₂)

      handle : (AvoidsVertex w₂ v₁ ⊎
                Σ[ w₃ ∈ FIW G v₁ v₃ ] (isPath w₃ × NoExtraVertices w₂ w₃)) ->
               Σ[ w₄ ∈ FIW G v₁ v₃ ] (isPath w₄ × NoExtraVertices w₀ w₄)
      handle (inj-r (w₃ , pw₃ , ex₃)) = (w₃ , pw₃ , (\v (p , ps) -> ex₃ v (ex₂ v ps)))
      handle (inj-l ¬v₁∈w₂) = (w₃ , (¬v₁∈w₂ , pw₂) , ex₃)
        where
        w₃ : FIW G v₁ v₃
        w₃ = (walk-step v₁ v₂ v₃ e w₂)
        ex₃ : NoExtraVertices w₀ w₃
        ex₃ v₄ (v₁!=v₄ , ¬v₄∈w₁) = v₁!=v₄ , ex₂ v₄ ¬v₄∈w₁

  ForwardInductiveWalk->ForwardInductivePath : {v₁ v₂ : V} ->
    (w : FIW G v₁ v₂) -> (Σ[ w₂ ∈ FIW G v₁ v₂ ] (isPath w₂))
  ForwardInductiveWalk->ForwardInductivePath w = fst w' , fst (snd w')
    where
    w' = FIW->Path' w
