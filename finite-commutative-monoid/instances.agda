{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.instances where

open import base
open import commutative-monoid
open import commutative-monoid.pi
open import hlevel
open import finite-commutative-monoid
open import finset.instances
open import equivalence
open import isomorphism
open import type-algebra
open import fin-algebra
open import finsum
open import sum
open import equality
open import finset
open import maybe
open import functions
open import cubical
open import fin
open import sigma
open import nat.order
open import truncation
open import funext

private
  variable
    ℓ : Level

module _ {D : Type ℓ} (CM : CommMonoid D) (isSetD : isSet D) where
  open CommMonoid CM

  private
    finiteMerge' = finiteMerge CM isSetD
    equivMerge' = equivMerge CM
    finiteMerge-convert' = finiteMerge-convert CM isSetD
    enumerationMerge' = enumerationMerge CM
    eval = finiteMerge-eval CM isSetD

  abstract
    finiteMerge-Bot : (f : Bot -> D) -> finiteMerge' FinSet-Bot f == ε
    finiteMerge-Bot = eval FinSet-Bot (equiv⁻¹ Fin-Bot-eq)

    finiteMerge-Top : (f : Top -> D) -> finiteMerge' FinSet-Top f == f tt
    finiteMerge-Top f = eval FinSet-Top (equiv⁻¹ Fin-Top-eq) f >=> ∙-right-ε

    finiteMerge-Fin0 : (f : (Fin 0) -> D) -> finiteMerge' (FinSet-Fin 0) f == ε
    finiteMerge-Fin0 = eval (FinSet-Fin 0) (idEquiv _)


  module _ {ℓB : Level} (FB : FinSet ℓB) where
    private
      B = fst FB
      finB = snd FB

    abstract
      finiteMerge-Maybe :
        (f : (Maybe B) -> D) ->
        (finiteMerge' (FinSet-Maybe FB) f)
        == (f nothing) ∙ finiteMerge' FB (f ∘ just)
      finiteMerge-Maybe f = unsquash (isSetD _ _) (∥-map handle finB)
        where
        handle : Σ[ n ∈ Nat ] (B ≃ Fin n) ->
                 (finiteMerge' (FinSet-Maybe FB) f)
                 == (f nothing) ∙ finiteMerge' FB (f ∘ just)
        handle (n , eq) =
          begin
            finiteMerge' (FinSet-Maybe FB) f
          ==< eval _ eq' f >
            equivMerge' eq' f
          ==<>
            enumerationMerge' (eqInv eq') f
          ==<>
            (f nothing) ∙ (enumerationMerge' (eqInv eq' ∘ suc-fin) f)
          ==< cong (\x -> (f nothing) ∙ (enumerationMerge' x f)) path2 >
            (f nothing) ∙ (enumerationMerge' (just ∘ eqInv eq) f)
          ==<>
            (f nothing) ∙ (enumerationMerge' (eqInv eq) (f ∘ just))
          ==< cong (f nothing ∙_) (sym (eval _ eq _)) >
            (f nothing) ∙ finiteMerge' FB (f ∘ just)
          end
          where
          eq' : Maybe B ≃ Fin (suc n)
          eq' = (Maybe-eq eq >eq> (equiv⁻¹ (Fin-Maybe-eq n)))

          path3 : (eqFun (Fin-Maybe-eq n) ∘ suc-fin) == just
          path3 = funExt (\i -> cong just (ΣProp-path isProp≤ refl))

          path2 : (eqInv eq' ∘ suc-fin) == (eqInv (Maybe-eq eq) ∘ just)
          path2 = cong (eqInv (Maybe-eq eq) ∘_) path3

  module _ {ℓB : Level} (FB : FinSet ℓB) where
    private
      B = fst FB
      finB = snd FB

      finiteMerge-split-Fin0 : {f g : Fin 0 -> D} ->
                         finiteMerge' (FinSet-Fin 0) (\i -> (f i) ∙ (g i))
                         == finiteMerge' (FinSet-Fin 0) f ∙ finiteMerge' (FinSet-Fin 0) g
      finiteMerge-split-Fin0 =
        finiteMerge-Fin0 _
        >=> (sym ∙-right-ε)
        >=> cong2 _∙_ (sym (finiteMerge-Fin0 _)) (sym (finiteMerge-Fin0 _))


      finiteMerge-split' : {n : Nat} {f g : Fin n -> D} ->
                           finiteMerge' (FinSet-Fin n) (\i -> (f i) ∙ (g i))
                           == finiteMerge' (FinSet-Fin n) f ∙ finiteMerge' (FinSet-Fin n) g
      finiteMerge-split' {n = zero} = finiteMerge-split-Fin0
      finiteMerge-split' {n = suc n} {f} {g} =
        finiteMerge-convert' _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _
        >=> finiteMerge-Maybe _ _
        >=> cong ((f zero-fin ∙ g zero-fin) ∙_) finiteMerge-split'
        -- (f + g) + (F + G)
        >=> ∙-assoc
        -- f + (g + (F + G))
        >=> cong (_ ∙_) (sym ∙-assoc)
        -- f + ((g + F) + G)
        >=> cong (((f zero-fin) ∙_) ∘ (_∙ (finiteMerge' (FinSet-Fin n) (g ∘ suc-fin))))
                 ∙-commute
        -- f + ((F + g) + G)
        >=> cong (_ ∙_) ∙-assoc
        -- f + (F + (g + G))
        >=> sym ∙-assoc
        -- (f + F) + (g + G)
        >=> cong2 _∙_ (sym ((finiteMerge-convert' _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _)
                            >=> finiteMerge-Maybe _ _))
                      (sym ((finiteMerge-convert' _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _)
                            >=> finiteMerge-Maybe _ _))

      finiteMerge-ε' : {n : Nat} ->
                       finiteMerge' (FinSet-Fin n) (\_ -> ε)
                       == ε
      finiteMerge-ε' {zero} = finiteMerge-Fin0 _
      finiteMerge-ε' {suc n} =
        finiteMerge-convert' _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _
        >=> finiteMerge-Maybe _ _
        >=> ∙-left-ε
        >=> finiteMerge-ε'

      finiteMerge-ε : finiteMerge' FB (\_ -> ε) == ε
      finiteMerge-ε = unsquash (isSetD _ _) (∥-map handle finB)
        where
        handle : Σ[ n ∈ Nat ] (B ≃ Fin n) -> finiteMerge' FB (\_ -> ε) == ε
        handle (n , eq) = finiteMerge-convert' _ _ (equiv⁻¹ eq) _ >=> finiteMerge-ε'

    finiteMerge-split : {f g : B -> D} ->
      finiteMerge' FB (\b -> (f b) ∙ (g b)) == finiteMerge' FB f ∙ finiteMerge' FB g
    finiteMerge-split {f} {g} = unsquash (isSetD _ _) (∥-map handle (snd FB))
      where
      handle : Σ[ n ∈ Nat ] (B ≃ Fin n) ->
               finiteMerge' FB (\b -> (f b) ∙ (g b)) == finiteMerge' FB f ∙ finiteMerge' FB g
      handle (n , eq) =
        finiteMerge-convert' _ _ (equiv⁻¹ eq) _
        >=> finiteMerge-split'
        >=> cong2 _∙_
                  (sym (finiteMerge-convert' _ _ (equiv⁻¹ eq) _))
                  (sym (finiteMerge-convert' _ _ (equiv⁻¹ eq) _))

    finiteMergeʰ : CommMonoidʰᵉ (CommMonoidStr-Π (\_ -> CM)) CM (finiteMerge' FB)
    finiteMergeʰ = record
      { preserves-ε = finiteMerge-ε
      ; preserves-∙ = \f g -> finiteMerge-split {f} {g}
      }



  module _ {ℓB : Level} {B : Type ℓB} (finB : isFinSet B) where

    finiteMerge-⊎'-zero' :
      (f : (Fin 0 ⊎ B) -> D) ->
      (finiteMerge' (FinSet-⊎ (FinSet-Fin 0) (B , finB)) f)
      == (finiteMerge' (B , finB) (f ∘ inj-r))
    finiteMerge-⊎'-zero' f =
      finiteMerge-convert'
        (FinSet-⊎ (FinSet-Fin 0) (B , finB)) (B , finB)
        ((equiv⁻¹ (⊎-Bot-eq B)) >eq> (⊎-equiv (equiv⁻¹ Fin-Bot-eq) (idEquiv _)))
        f

    finiteMerge-⊎'-zero :
      (f : (Fin 0 ⊎ B) -> D) ->
      (finiteMerge' (FinSet-⊎ (FinSet-Fin 0) (B , finB)) f)
      == (finiteMerge' (FinSet-Fin 0) (f ∘ inj-l)) ∙
         (finiteMerge' (B , finB) (f ∘ inj-r))
    finiteMerge-⊎'-zero f =
      finiteMerge-⊎'-zero' f
      >=> (sym ∙-left-ε)
      >=> (cong (_∙ (finiteMerge' (B , finB) (f ∘ inj-r)))
                (sym (finiteMerge-Fin0 (f ∘ inj-l))))

    finiteMerge-⊎'-suc' : {n : Nat}
      (f : (Fin (suc n) ⊎ B) -> D) ->
      (finiteMerge' (FinSet-⊎ (FinSet-Fin (suc n)) (B , finB)) f)
      == f (inj-l zero-fin) ∙
         (finiteMerge' (FinSet-⊎ (FinSet-Fin n) (B , finB))
                       (f ∘ (⊎-map suc-fin (idfun B))))
    finiteMerge-⊎'-suc' {n} f =
      begin
        (finiteMerge' (FinSet-⊎ (FinSet-Fin (suc n)) (B , finB)) f)
      ==< finiteMerge-convert'
            (FinSet-⊎ (FinSet-Fin (suc n)) (B , finB))
            (FinSet-Maybe (FinSet-⊎ (FinSet-Fin n) (B , finB)))
            eq f >
        (finiteMerge' (FinSet-Maybe (FinSet-⊎ (FinSet-Fin n) (B , finB))) (f ∘ (eqFun eq)))
      ==< finiteMerge-Maybe (FinSet-⊎ (FinSet-Fin n) (B , finB)) (f ∘ (eqFun eq)) >
        (f (eqFun eq nothing)) ∙
        (finiteMerge' (FinSet-⊎ (FinSet-Fin n) (B , finB)) (f ∘ (eqFun eq) ∘ just))
      ==< path >
        (f (inj-l zero-fin)) ∙
        (finiteMerge' (FinSet-⊎ (FinSet-Fin n) (B , finB))
                      (f ∘ (⊎-map suc-fin (idfun B))))
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
                (finiteMerge' (FinSet-⊎ (FinSet-Fin n) (B , finB)) (f ∘ (eqFun eq) ∘ just)))
               ((f (inj-l zero-fin)) ∙
                (finiteMerge' (FinSet-⊎ (FinSet-Fin n) (B , finB))
                           (f ∘ (⊎-map suc-fin (idfun B)))))
      path i = (f (eqFun eq nothing)) ∙
               (finiteMerge' (FinSet-⊎ (FinSet-Fin n) (B , finB)) (path4 i))


    finiteMerge-⊎' : {n : Nat}
      (f : (Fin n ⊎ B) -> D) ->
      (finiteMerge' (FinSet-⊎ (FinSet-Fin n) (B , finB)) f)
      == (finiteMerge' (FinSet-Fin n) (f ∘ inj-l)) ∙
         (finiteMerge' (B , finB) (f ∘ inj-r))
    finiteMerge-⊎' {zero} f = finiteMerge-⊎'-zero f
    finiteMerge-⊎' {suc n} f =
      step
      >=> cong (f (inj-l zero-fin) ∙_) rec
      >=> (sym ∙-assoc)
      >=> (cong (_∙ (finiteMerge' (B , finB) (f ∘ inj-r))) (sym step2))
      where
      f' = f ∘ (⊎-map suc-fin (idfun B))
      rec : (finiteMerge' (FinSet-⊎ (FinSet-Fin n) (B , finB)) f')
            == (finiteMerge' (FinSet-Fin n) (f ∘ inj-l ∘ suc-fin)) ∙
               (finiteMerge' (B , finB) (f ∘ inj-r))
      rec = finiteMerge-⊎' f'

      step : (finiteMerge' (FinSet-⊎ (FinSet-Fin (suc n)) (B , finB)) f)
             == f (inj-l zero-fin) ∙
                (finiteMerge' (FinSet-⊎ (FinSet-Fin n) (B , finB)) f')
      step = finiteMerge-⊎'-suc' f

      step2 : (finiteMerge' (FinSet-Fin (suc n)) (f ∘ inj-l))
              == f (inj-l zero-fin) ∙
                 (finiteMerge' (FinSet-Fin n) (f ∘ inj-l ∘ suc-fin))
      step2 =
        finiteMerge-convert' (FinSet-Fin (suc n)) (FinSet-Maybe (FinSet-Fin n))
                             (equiv⁻¹ (Fin-Maybe-eq n)) (f ∘ inj-l)
        >=> finiteMerge-Maybe (FinSet-Fin n) _

  module _ {ℓA : Level} {A : Type ℓA} (finA : isFinSet A)
           {ℓB : Level} {B : Type ℓB} (finB : isFinSet B) where

    finiteMerge-⊎ :
      (f : (A ⊎ B) -> D) ->
      (finiteMerge' (FinSet-⊎ (A , finA) (B , finB)) f)
      == (finiteMerge' (A , finA) (f ∘ inj-l)) ∙ (finiteMerge' (B , finB) (f ∘ inj-r))
    finiteMerge-⊎ f = unsquash (isSetD _ _) (∥-map handle finA)
      where
      handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
               (finiteMerge' (FinSet-⊎ (A , finA) (B , finB)) f)
               == (finiteMerge' (A , finA) (f ∘ inj-l)) ∙ (finiteMerge' (B , finB) (f ∘ inj-r))
      handle (n , eq) =
        begin
          finiteMerge' (FinSet-⊎ (A , finA) (B , finB)) f
        ==< finiteMerge-convert'
              (FinSet-⊎ (A , finA) (B , finB))
              (FinSet-⊎ (FinSet-Fin n) (B , finB))
              (⊎-equiv (equiv⁻¹ eq) (idEquiv B)) f >
          finiteMerge' (FinSet-⊎ (FinSet-Fin n) (B , finB)) _
        ==< finiteMerge-⊎' finB _ >
          (finiteMerge' (FinSet-Fin n) _) ∙ (finiteMerge' (B , finB) (f ∘ inj-r))
        ==< cong
             (_∙ (finiteMerge' (B , finB) (f ∘ inj-r)))
             (sym (finiteMerge-convert' (A , finA) (FinSet-Fin n) (equiv⁻¹ eq) (f ∘ inj-l))) >
          (finiteMerge' (A , finA) (f ∘ inj-l)) ∙ (finiteMerge' (B , finB) (f ∘ inj-r))
        end


module _ {ℓD : Level} {D : Type ℓD} (CM-D : CommMonoid D) (isSetD : isSet D) where
  module CM-D = CommMonoid CM-D

  module _ {ℓA ℓB : Level} (FA : FinSet ℓA) {B : Type ℓB} (CM-B : CommMonoid B) (isSetB : isSet B) where
    private
      A = ⟨ FA ⟩
    module CM-B = CommMonoid CM-B
    module _ {f : B  -> D} (fʰ : (CommMonoidʰᵉ CM-B CM-D f)) where
      module fʰ = CommMonoidʰ fʰ
      private
        finiteMerge-homo-inject' : {n : Nat} {g : Fin n -> B} ->
          finiteMerge CM-D isSetD (FinSet-Fin n) (\i -> (f (g i))) ==
          f (finiteMerge CM-B isSetB (FinSet-Fin n) g)
        finiteMerge-homo-inject' {zero} {g} =
          finiteMerge-Fin0 CM-D isSetD (f ∘ g) >=>
          sym fʰ.preserves-ε >=>
          cong f (sym (finiteMerge-Fin0 CM-B isSetB g))
        finiteMerge-homo-inject' {suc n} {g} =
          finiteMerge-convert CM-D isSetD _ _ (equiv⁻¹ (Fin-Maybe-eq n)) (f ∘ g)
          >=> finiteMerge-Maybe CM-D isSetD _ _
          >=> cong (f (g zero-fin) CM-D.∙_) finiteMerge-homo-inject'
          >=> sym (fʰ.preserves-∙ _ _)
          >=> cong f ((sym (finiteMerge-Maybe CM-B isSetB _ _)) >=>
                      (sym (finiteMerge-convert CM-B isSetB _ _ (equiv⁻¹ (Fin-Maybe-eq n)) g)))

      finiteMerge-homo-inject : {g : A -> B} ->
        finiteMerge CM-D isSetD FA (f ∘ g) ==
        f (finiteMerge CM-B isSetB FA g)
      finiteMerge-homo-inject {g} = unsquash (isSetD _ _) (∥-map handle (snd FA))
        where
        handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
                 finiteMerge CM-D isSetD FA (f ∘ g) ==
                 f (finiteMerge CM-B isSetB FA g)
        handle (n , eq) =
         finiteMerge-convert CM-D isSetD _ _ (equiv⁻¹ eq) _
         >=> finiteMerge-homo-inject'
         >=> cong f (sym (finiteMerge-convert CM-B isSetB _ _ (equiv⁻¹ eq) _))
