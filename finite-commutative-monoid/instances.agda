{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.instances where

open import base
open import commutative-monoid
open import commutative-monoid.pi
open import cubical
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finite-commutative-monoid
open import finset
open import finset.detachable
open import finset.instances
open import finsum
open import functions
open import funext
open import hlevel
open import isomorphism
open import maybe
open import nat.order
open import sigma
open import subset
open import sum
open import truncation
open import type-algebra

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
    finiteMerge-Bot : (f : Bot -> D) -> finiteMerge' f == ε
    finiteMerge-Bot = eval FinSet-Bot (equiv⁻¹ Fin-Bot-eq)

    finiteMerge-Top : (f : Top -> D) -> finiteMerge' f == f tt
    finiteMerge-Top f = eval FinSet-Top (equiv⁻¹ Fin-Top-eq) f >=> ∙-right-ε

    finiteMerge-Fin0 : (f : (Fin 0) -> D) -> finiteMerge' f == ε
    finiteMerge-Fin0 = eval (FinSet-Fin 0) (idEquiv _)

    finiteMerge-Fin1 : (f : (Fin 1) -> D) -> finiteMerge' f == f zero-fin
    finiteMerge-Fin1 f = eval (FinSet-Fin 1) (idEquiv _) f >=> ∙-right-ε

    finiteMerge-Fin2 : (f : (Fin 2) -> D) -> finiteMerge' f ==
                                             (f zero-fin) ∙ (f (suc-fin zero-fin))
    finiteMerge-Fin2 f = eval (FinSet-Fin 2) (idEquiv _) f >=> sym ∙-assoc >=> ∙-right-ε


  module _ {ℓB : Level} (FB : FinSet ℓB) where
    private
      B = fst FB
      finB = snd FB
      instance
        FinSetStr-B : FinSetStr B
        FinSetStr-B = record { isFin = finB }

    abstract
      finiteMerge-isContr :
        (isContr-B : isContr B) -> (f : B -> D) -> finiteMerge' f == f ⟨ isContr-B ⟩
      finiteMerge-isContr isContr-B f = path
        where
        b = fst (isContr-B)

        B≃Top : B ≃ Top
        B≃Top = Contr-Top-eq isContr-B

        path : finiteMerge' f == f b
        path =
          finiteMerge-convert' FB FinSet-Top (equiv⁻¹ B≃Top) f >=>
          finiteMerge-Top (\_ -> f b)

      finiteMerge-isProp : (isProp B) -> (b : B) -> (f : B -> D) -> finiteMerge' f == f b
      finiteMerge-isProp isProp-B b f = finiteMerge-isContr (b , isProp-B b) f

      finiteMerge-Uninhabited : (¬ B) -> (f : B -> D) -> finiteMerge' f == ε
      finiteMerge-Uninhabited ¬b f =
        finiteMerge-convert' FB FinSet-Bot (equiv⁻¹ (¬-Bot-eq ¬b)) f >=>
        finiteMerge-Bot _

  module _ {ℓB : Level} (FB : FinSet ℓB) where
    private
      B = fst FB
      finB = snd FB
      instance
        FinSetStr-B : FinSetStr B
        FinSetStr-B = record { isFin = finB }

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
            (f nothing) ∙ finiteMerge' (f ∘ just)
          end
          where
          eq' : Maybe B ≃ Fin (suc n)
          eq' = (Maybe-eq eq >eq> (equiv⁻¹ (Fin-Maybe-eq n)))

          path3 : (eqFun (Fin-Maybe-eq n) ∘ suc-fin) == just
          path3 = funExt (\i -> cong just (fin-i-path refl))

          path2 : (eqInv eq' ∘ suc-fin) == (eqInv (Maybe-eq eq) ∘ just)
          path2 = cong (eqInv (Maybe-eq eq) ∘_) path3


  module _ {ℓB : Level} (FB : FinSet ℓB) where
    private
      B = fst FB
      finB = snd FB
      instance
        FinSetStr-B : FinSetStr B
        FinSetStr-B = record { isFin = finB }

      finiteMerge-split-Fin0 : {f g : Fin 0 -> D} ->
                         finiteMerge' (\i -> (f i) ∙ (g i))
                         == finiteMerge' f ∙ finiteMerge' g
      finiteMerge-split-Fin0 =
        finiteMerge-Fin0 _
        >=> (sym ∙-right-ε)
        >=> cong2 _∙_ (sym (finiteMerge-Fin0 _)) (sym (finiteMerge-Fin0 _))


      finiteMerge-split' : {n : Nat} {f g : Fin n -> D} ->
                           finiteMerge' (\i -> (f i) ∙ (g i))
                           == finiteMerge' f ∙ finiteMerge' g
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
        >=> cong (((f zero-fin) ∙_) ∘ (_∙ (finiteMerge' (g ∘ suc-fin))))
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
                       finiteMerge' (\ (_ : Fin n) -> ε)
                       == ε
      finiteMerge-ε' {zero} = finiteMerge-Fin0 (\_ -> ε)
      finiteMerge-ε' {suc n} =
        finiteMerge-convert' _ _ (equiv⁻¹ (Fin-Maybe-eq n)) _
        >=> finiteMerge-Maybe _ _
        >=> ∙-left-ε
        >=> finiteMerge-ε'

    finiteMerge-ε : finiteMerge' (\_ -> ε) == ε
    finiteMerge-ε = unsquash (isSet-Domain _ _) (∥-map handle finB)
      where
      handle : Σ[ n ∈ Nat ] (B ≃ Fin n) -> finiteMerge' (\_ -> ε) == ε
      handle (n , eq) = finiteMerge-convert' _ _ (equiv⁻¹ eq) _ >=> finiteMerge-ε'

    finiteMerge-split : {f g : B -> D} ->
      finiteMerge' (\b -> (f b) ∙ (g b)) == finiteMerge' f ∙ finiteMerge' g
    finiteMerge-split {f} {g} = unsquash (isSet-Domain _ _) (∥-map handle (snd FB))
      where
      handle : Σ[ n ∈ Nat ] (B ≃ Fin n) ->
               finiteMerge' (\b -> (f b) ∙ (g b)) == finiteMerge' f ∙ finiteMerge' g
      handle (n , eq) =
        finiteMerge-convert' _ _ (equiv⁻¹ eq) _
        >=> finiteMerge-split'
        >=> cong2 _∙_
                  (sym (finiteMerge-convert' _ _ (equiv⁻¹ eq) _))
                  (sym (finiteMerge-convert' _ _ (equiv⁻¹ eq) _))

    finiteMergeʰ : CommMonoidʰᵉ (CommMonoidStr-Π (\_ -> CM)) CM finiteMerge'
    finiteMergeʰ = record
      { preserves-ε = finiteMerge-ε
      ; preserves-∙ = \f g -> finiteMerge-split {f} {g}
      }



  module _ {ℓB : Level} {B : Type ℓB} (finB : isFinSet B) where
    private
      instance
        FinSetStr-B : FinSetStr B
        FinSetStr-B = record { isFin = finB }

    finiteMerge-⊎'-zero' :
      (f : (Fin 0 ⊎ B) -> D) ->
      (finiteMerge' f)
      == (finiteMerge' (f ∘ inj-r))
    finiteMerge-⊎'-zero' f =
      finiteMerge-convert'
        (FinSet-⊎ (FinSet-Fin 0) (B , finB)) (B , finB)
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
                (sym (finiteMerge-Fin0 (f ∘ inj-l))))

    finiteMerge-⊎'-suc' : {n : Nat}
      (f : (Fin (suc n) ⊎ B) -> D) ->
      (finiteMerge' f)
      == f (inj-l zero-fin) ∙
         (finiteMerge' (f ∘ (⊎-map suc-fin (idfun B))))
    finiteMerge-⊎'-suc' {n} f =
      begin
        (finiteMerge' f)
      ==< finiteMerge-convert'
            (FinSet-⊎ (FinSet-Fin (suc n)) (B , finB))
            (FinSet-Maybe (FinSet-⊎ (FinSet-Fin n) (B , finB)))
            eq f >
        (finiteMerge' (f ∘ (eqFun eq)))
      ==< finiteMerge-Maybe (FinSet-⊎ (FinSet-Fin n) (B , finB)) (f ∘ (eqFun eq)) >
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
        finiteMerge-convert' (FinSet-Fin (suc n)) (FinSet-Maybe (FinSet-Fin n))
                             (equiv⁻¹ (Fin-Maybe-eq n)) (f ∘ inj-l)
        >=> finiteMerge-Maybe (FinSet-Fin n) _

  module _ {ℓA : Level} {A : Type ℓA} (finA : isFinSet A)
           {ℓB : Level} {B : Type ℓB} (finB : isFinSet B) where
    private
      instance
        FinSetStr-A : FinSetStr A
        FinSetStr-A = record { isFin = finA }
        FinSetStr-B : FinSetStr B
        FinSetStr-B = record { isFin = finB }

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
        ==< finiteMerge-convert'
              (FinSet-⊎ (A , finA) (B , finB))
              (FinSet-⊎ (FinSet-Fin n) (B , finB))
              (⊎-equiv (equiv⁻¹ eq) (idEquiv B)) f >
          finiteMerge' _
        ==< finiteMerge-⊎' finB _ >
          (finiteMerge' _) ∙ (finiteMerge' (f ∘ inj-r))
        ==< cong
             (_∙ (finiteMerge' (f ∘ inj-r)))
             (sym (finiteMerge-convert' (A , finA) (FinSet-Fin n) (equiv⁻¹ eq) (f ∘ inj-l))) >
          (finiteMerge' (f ∘ inj-l)) ∙ (finiteMerge' (f ∘ inj-r))
        end

  module _ {ℓA ℓS : Level} (FA : FinSet ℓA) (S : Subtype ⟨ FA ⟩ ℓS) (d-S : Detachable S) where
    private
      A = ⟨ FA ⟩
      fs-A = snd FA
      fs-S = isFinSet-Detachable S fs-A d-S
      fs-S' = isFinSet-DetachableComp S fs-A d-S
      FS : FinSet (ℓ-max ℓA ℓS)
      FS = _ , fs-S
      FS' : FinSet(ℓ-max ℓA ℓS)
      FS' = _ , fs-S'

      instance
        FinSetStr-A : FinSetStr A
        FinSetStr-A = record { isFin = fs-A }
        FinSetStr-S : FinSetStr _
        FinSetStr-S = record { isFin = fs-S }
        FinSetStr-S' : FinSetStr _
        FinSetStr-S' = record { isFin = fs-S' }

    finiteMerge-Detachable :
      (f : A -> D) ->
      finiteMerge' f ==
      (finiteMerge' (f ∘ fst)) ∙
      (finiteMerge' (f ∘ fst))
    finiteMerge-Detachable f =
      finiteMerge-convert' FA (FinSet-⊎ FS FS') (equiv⁻¹ (Detachable-eq S d-S)) f
      >=> finiteMerge-⊎ fs-S fs-S' (f ∘ eqFun (equiv⁻¹ (Detachable-eq S d-S)))



module _ {ℓD : Level} {D : Type ℓD} (CM-D : CommMonoid D) where
  module CM-D = CommMonoid CM-D

  module _ {ℓA ℓB : Level} (FA : FinSet ℓA) {B : Type ℓB} (CM-B : CommMonoid B) where
    private
      A = ⟨ FA ⟩
      instance
        FinSetStr-A : FinSetStr A
        FinSetStr-A = record { isFin = snd FA }

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
          finiteMerge-convert CM-D _ _ (equiv⁻¹ (Fin-Maybe-eq n)) (f ∘ g)
          >=> finiteMerge-Maybe CM-D _ _
          >=> cong (f (g zero-fin) CM-D.∙_) finiteMerge-homo-inject'
          >=> sym (fʰ.preserves-∙ _ _)
          >=> cong f ((sym (finiteMerge-Maybe CM-B _ _)) >=>
                      (sym (finiteMerge-convert CM-B _ _ (equiv⁻¹ (Fin-Maybe-eq n)) g)))

      finiteMerge-homo-inject : {g : A -> B} ->
        finiteMerge CM-D (f ∘ g) ==
        f (finiteMerge CM-B g)
      finiteMerge-homo-inject {g} = unsquash (CM-D.isSet-Domain _ _) (∥-map handle (snd FA))
        where
        handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
                 finiteMerge CM-D (f ∘ g) ==
                 f (finiteMerge CM-B g)
        handle (n , eq) =
         finiteMerge-convert CM-D _ _ (equiv⁻¹ eq) _
         >=> finiteMerge-homo-inject'
         >=> cong f (sym (finiteMerge-convert CM-B _ _ (equiv⁻¹ eq) _))
