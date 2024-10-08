{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.instances where

open import base
open import commutative-monoid
open import commutative-monoid.pi
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finite-commutative-monoid
open import finite-commutative-monoid.small
open import finset
open import finset.instances
open import finset.instances.base
open import finset.instances.boolean
open import finset.instances.sum
open import functions
open import funext
open import hlevel
open import maybe
open import sum
open import truncation
open import type-algebra
open import type-algebra.boolean

open EqReasoning

private
  variable
    ℓ : Level

module _ {D : Type ℓ} (CM : CommMonoid D) where
  open CommMonoid CM

  private
    finiteMerge' = finiteMerge CM
    equivMerge' = equivMerge CM
    finiteMerge-convert' = finiteMerge-convert CM
    enumerationMerge' = enumerationMerge CM
    eval = finiteMerge-eval CM

  abstract
    finiteMerge-FinSuc :
      {n : Nat} (f : (Fin (suc n)) -> D) ->
      finiteMerge' f == (f zero-fin) ∙ (finiteMerge' (f ∘ suc-fin))
    finiteMerge-FinSuc f =
      eval (idEquiv _) f >=> cong (f zero-fin ∙_) (sym (eval (idEquiv _) (f ∘ suc-fin)))


  module _ {ℓB : Level} {B : Type ℓB} {{FB : FinSetStr B}} where
    private
      finB = FinSetStr.isFin FB

    abstract
      finiteMerge-Maybe :
        (f : (Maybe B) -> D) ->
        (finiteMerge' f) == (f nothing) ∙ finiteMerge' (f ∘ just)
      finiteMerge-Maybe f = unsquash (isSet-Domain _ _) (∥-map handle finB)
        where
        handle : Σ[ n ∈ Nat ] (B ≃ Fin n) ->
                 (finiteMerge' f)
                 == (f nothing) ∙ finiteMerge' (f ∘ just)
        handle (n , eq) =
          begin
            finiteMerge' f
          ==< eval eq' f >
            equivMerge' eq' f
          ==<>
            enumerationMerge' (eqInv eq') f
          ==<>
            (f nothing) ∙ (enumerationMerge' (eqInv eq' ∘ suc-fin) f)
          ==< cong (\x -> (f nothing) ∙ (enumerationMerge' x f)) path2 >
            (f nothing) ∙ (enumerationMerge' (just ∘ eqInv eq) f)
          ==<>
            (f nothing) ∙ (enumerationMerge' (eqInv eq) (f ∘ just))
          ==< cong (f nothing ∙_) (sym (eval eq _)) >
            (f nothing) ∙ finiteMerge' (f ∘ just)
          end
          where
          eq' : Maybe B ≃ Fin (suc n)
          eq' = (Maybe-eq eq >eq> (equiv⁻¹ (Fin-Maybe-eq n)))

          path3 : (eqFun (Fin-Maybe-eq n) ∘ suc-fin) == just
          path3 = funExt (\i -> cong just (fin-i-path refl))

          path2 : (eqInv eq' ∘ suc-fin) == (eqInv (Maybe-eq eq) ∘ just)
          path2 = cong (eqInv (Maybe-eq eq) ∘_) path3

  module _ {ℓB : Level} {B : Type ℓB} {{FB : FinSetStr B}} where
    private
      finB = FinSetStr.isFin FB

      finiteMerge-split-Fin0 : {f g : Fin 0 -> D} ->
                         finiteMerge' (\i -> (f i) ∙ (g i))
                         == finiteMerge' f ∙ finiteMerge' g
      finiteMerge-split-Fin0 =
        finiteMerge-Fin0 CM _
        >=> (sym ∙-right-ε)
        >=> cong2 _∙_ (sym (finiteMerge-Fin0 CM _)) (sym (finiteMerge-Fin0 CM _))


      finiteMerge-split' : {n : Nat} {f g : Fin n -> D} ->
                           finiteMerge' (\i -> (f i) ∙ (g i))
                           == finiteMerge' f ∙ finiteMerge' g
      finiteMerge-split' {n = zero} = finiteMerge-split-Fin0
      finiteMerge-split' {n = suc n} {f} {g} =
        finiteMerge-convert' (equiv⁻¹ (Fin-Maybe-eq n)) _
        >=> finiteMerge-Maybe _
        >=> cong ((f zero-fin ∙ g zero-fin) ∙_) finiteMerge-split'
        -- (f + g) + (F + G)
        >=> ∙-assoc
        -- f + (g + (F + G))
        >=> cong (_ ∙_) (sym ∙-assoc)
        -- f + ((g + F) + G)
        >=> cong (((f zero-fin) ∙_) ∘ (_∙ (finiteMerge' (g ∘ suc-fin))))
                 ∙-commute
        -- f + ((F + g) + G)
        >=> cong (_ ∙_) ∙-assoc
        -- f + (F + (g + G))
        >=> sym ∙-assoc
        -- (f + F) + (g + G)
        >=> cong2 _∙_ (sym ((finiteMerge-convert' (equiv⁻¹ (Fin-Maybe-eq n)) _)
                            >=> finiteMerge-Maybe _))
                      (sym ((finiteMerge-convert' (equiv⁻¹ (Fin-Maybe-eq n)) _)
                            >=> finiteMerge-Maybe _))

      finiteMerge-ε' : {n : Nat} ->
                       finiteMerge' (\ (_ : Fin n) -> ε)
                       == ε
      finiteMerge-ε' {zero} = finiteMerge-Fin0 CM (\_ -> ε)
      finiteMerge-ε' {suc n} =
        finiteMerge-convert' (equiv⁻¹ (Fin-Maybe-eq n)) _
        >=> finiteMerge-Maybe _
        >=> ∙-left-ε
        >=> finiteMerge-ε'

    abstract
      finiteMerge-ε : {f : B -> D} -> (∀ (b : B) -> f b == ε) ->
                      finiteMerge' f == ε
      finiteMerge-ε {f} paths = unsquash (isSet-Domain _ _) (∥-map handle finB)
        where
        handle : Σ[ n ∈ Nat ] (B ≃ Fin n) -> finiteMerge' f == ε
        handle (n , eq) =
          cong (finiteMerge _) (funExt paths) >=>
          finiteMerge-convert' (equiv⁻¹ eq) _ >=>
          finiteMerge-ε'

      finiteMerge-split : {f g : B -> D} ->
        finiteMerge' (\b -> (f b) ∙ (g b)) == finiteMerge' f ∙ finiteMerge' g
      finiteMerge-split {f} {g} = unsquash (isSet-Domain _ _) (∥-map handle finB)
        where
        handle : Σ[ n ∈ Nat ] (B ≃ Fin n) ->
                 finiteMerge' (\b -> (f b) ∙ (g b)) == finiteMerge' f ∙ finiteMerge' g
        handle (n , eq) =
          finiteMerge-convert' (equiv⁻¹ eq) _
          >=> finiteMerge-split'
          >=> cong2 _∙_
                    (sym (finiteMerge-convert' (equiv⁻¹ eq) _))
                    (sym (finiteMerge-convert' (equiv⁻¹ eq) _))

    finiteMergeʰ : CommMonoidʰᵉ (CommMonoidStr-Π (\_ -> CM)) CM finiteMerge'
    finiteMergeʰ = record
      { monoidʰ = record
        { preserves-ε = finiteMerge-ε (\_ -> refl)
        ; preserves-∙ = \f g -> finiteMerge-split {f} {g}
        }
      }



  private
    module _ {ℓB : Level} {B : Type ℓB} {{FB : FinSetStr B}} where
      finiteMerge-⊎'-zero' :
        (f : (Fin 0 ⊎ B) -> D) ->
        (finiteMerge' f)
        == (finiteMerge' (f ∘ inj-r))
      finiteMerge-⊎'-zero' f =
        finiteMerge-convert'
          ((equiv⁻¹ (⊎-Bot-eq B)) >eq> (⊎-equiv (equiv⁻¹ Fin-Bot-eq) (idEquiv _)))
          f

      finiteMerge-⊎'-zero :
        (f : (Fin 0 ⊎ B) -> D) ->
        (finiteMerge' f)
        == (finiteMerge' (f ∘ inj-l)) ∙
           (finiteMerge' (f ∘ inj-r))
      finiteMerge-⊎'-zero f =
        finiteMerge-⊎'-zero' f
        >=> (sym ∙-left-ε)
        >=> (cong (_∙ (finiteMerge' (f ∘ inj-r)))
                  (sym (finiteMerge-Fin0 CM (f ∘ inj-l))))

      finiteMerge-⊎'-suc' : {n : Nat}
        (f : (Fin (suc n) ⊎ B) -> D) ->
        (finiteMerge' f)
        == f (inj-l zero-fin) ∙
           (finiteMerge' (f ∘ (⊎-map suc-fin (idfun B))))
      finiteMerge-⊎'-suc' {n} f =
        begin
          (finiteMerge' f)
        ==< finiteMerge-convert' eq f >
          (finiteMerge' (f ∘ (eqFun eq)))
        ==< finiteMerge-Maybe (f ∘ (eqFun eq)) >
          (f (eqFun eq nothing)) ∙
          (finiteMerge' (f ∘ (eqFun eq) ∘ just))
        ==< path >
          (f (inj-l zero-fin)) ∙
          (finiteMerge' (f ∘ (⊎-map suc-fin (idfun B))))
        end
        where
        eq : Maybe (Fin n ⊎ B) ≃ (Fin (suc n) ⊎ B)
        eq = equiv⁻¹ (⊎-equiv (Fin-suc-⊎-eq n) (idEquiv B)
                      >eq> ⊎-assoc-eq Top (Fin n) B
                      >eq> ⊎-Top-eq)

        path1 : Path D (f (eqFun eq nothing)) (f (inj-l zero-fin))
        path1 = refl

        path3 : (x : (Fin n ⊎ B)) -> (f ∘ (eqFun eq) ∘ just) x == (f ∘ (⊎-map suc-fin (idfun B))) x
        path3 (inj-l _) = refl
        path3 (inj-r _) = refl

        path4 : (f ∘ (eqFun eq) ∘ just) == (f ∘ (⊎-map suc-fin (idfun B)))
        path4 = funExt path3


        path : Path D
                 ((f (eqFun eq nothing)) ∙
                  (finiteMerge' (f ∘ (eqFun eq) ∘ just)))
                 ((f (inj-l zero-fin)) ∙
                  (finiteMerge' (f ∘ (⊎-map suc-fin (idfun B)))))
        path i = (f (eqFun eq nothing)) ∙
                 (finiteMerge' (path4 i))


      finiteMerge-⊎' : {n : Nat}
        (f : (Fin n ⊎ B) -> D) ->
        (finiteMerge' f)
        == (finiteMerge' (f ∘ inj-l)) ∙
           (finiteMerge' (f ∘ inj-r))
      finiteMerge-⊎' {zero} f = finiteMerge-⊎'-zero f
      finiteMerge-⊎' {suc n} f =
        step
        >=> cong (f (inj-l zero-fin) ∙_) rec
        >=> (sym ∙-assoc)
        >=> (cong (_∙ (finiteMerge' (f ∘ inj-r))) (sym step2))
        where
        f' = f ∘ (⊎-map suc-fin (idfun B))
        rec : (finiteMerge' f')
              == (finiteMerge' (f ∘ inj-l ∘ suc-fin)) ∙
                 (finiteMerge' (f ∘ inj-r))
        rec = finiteMerge-⊎' f'

        step : (finiteMerge' f) == f (inj-l zero-fin) ∙ (finiteMerge' f')
        step = finiteMerge-⊎'-suc' f

        step2 : (finiteMerge' (f ∘ inj-l))
                == f (inj-l zero-fin) ∙ (finiteMerge' (f ∘ inj-l ∘ suc-fin))
        step2 =
          finiteMerge-convert' (equiv⁻¹ (Fin-Maybe-eq n)) (f ∘ inj-l)
          >=> finiteMerge-Maybe _

  module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
           {{FA : FinSetStr A}} {{FB : FinSetStr B}} where
    private
      finA = FinSetStr.isFin FA

    abstract
      finiteMerge-⊎ :
        (f : (A ⊎ B) -> D) ->
        (finiteMerge' f)
        == (finiteMerge' (f ∘ inj-l)) ∙ (finiteMerge' (f ∘ inj-r))
      finiteMerge-⊎ f = unsquash (isSet-Domain _ _) (∥-map handle finA)
        where
        handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
                 (finiteMerge' f)
                 == (finiteMerge' (f ∘ inj-l)) ∙ (finiteMerge' (f ∘ inj-r))
        handle (n , eq) =
          begin
            finiteMerge' f
          ==< finiteMerge-convert' (⊎-equiv (equiv⁻¹ eq) (idEquiv B)) f >
            finiteMerge' _
          ==< finiteMerge-⊎' _ >
            (finiteMerge' _) ∙ (finiteMerge' (f ∘ inj-r))
          ==< cong
               (_∙ (finiteMerge' (f ∘ inj-r)))
               (sym (finiteMerge-convert' (equiv⁻¹ eq) (f ∘ inj-l))) >
            (finiteMerge' (f ∘ inj-l)) ∙ (finiteMerge' (f ∘ inj-r))
          end

  module _ {ℓA ℓB : Level} (FA@(A , finA) : FinSet ℓA) (FB@(B , finB) : FinSet ℓB) where
    private
      instance
        IFA : FinSetStr A
        IFA = record { isFin = finA }
        IFB : FinSetStr B
        IFB = record { isFin = finB }

    opaque
      finiteMergeᵉ-⊎ :
        (f : (A ⊎ B) -> D) ->
        finiteMergeᵉ CM (FinSet-⊎ FA FB) f ==
        (finiteMergeᵉ CM FA (f ∘ inj-l)) ∙ (finiteMergeᵉ CM FB (f ∘ inj-r))
      finiteMergeᵉ-⊎ = finiteMerge-⊎



module _ {ℓA ℓB ℓD : Level} {A : Type ℓA} {B : Type ℓB} {D : Type ℓD}
         {CM-B : CommMonoid B} {CM-D : CommMonoid D} {{FA : FinSetStr A}}
  where
    module CM-D = CommMonoid CM-D
    module CM-B = CommMonoid CM-B
    module _ {f : B  -> D} (fʰ : (CommMonoidʰᵉ CM-B CM-D f)) where
      module fʰ = CommMonoidʰ fʰ
      private
        finiteMerge-homo-inject' : {n : Nat} {g : Fin n -> B} ->
          finiteMerge CM-D (\i -> (f (g i))) ==
          f (finiteMerge CM-B g)
        finiteMerge-homo-inject' {zero} {g} =
          finiteMerge-Fin0 CM-D (f ∘ g) >=>
          sym fʰ.preserves-ε >=>
          cong f (sym (finiteMerge-Fin0 CM-B g))
        finiteMerge-homo-inject' {suc n} {g} =
          finiteMerge-convert CM-D (equiv⁻¹ (Fin-Maybe-eq n)) (f ∘ g)
          >=> finiteMerge-Maybe CM-D _
          >=> cong (f (g zero-fin) CM-D.∙_) finiteMerge-homo-inject'
          >=> sym (fʰ.preserves-∙ _ _)
          >=> cong f ((sym (finiteMerge-Maybe CM-B _)) >=>
                      (sym (finiteMerge-convert CM-B (equiv⁻¹ (Fin-Maybe-eq n)) g)))

      abstract
        finiteMerge-homo-inject : {g : A -> B} ->
          finiteMerge CM-D (f ∘ g) ==
          f (finiteMerge CM-B g)
        finiteMerge-homo-inject {g} = unsquash (CM-D.isSet-Domain _ _) (∥-map handle (FinSetStr.isFin FA))
          where
          handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
                   finiteMerge CM-D (f ∘ g) ==
                   f (finiteMerge CM-B g)
          handle (n , eq) =
           finiteMerge-convert CM-D (equiv⁻¹ eq) _
           >=> finiteMerge-homo-inject'
           >=> cong f (sym (finiteMerge-convert CM-B (equiv⁻¹ eq) _))
