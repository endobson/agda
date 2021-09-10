{-# OPTIONS --cubical --safe --exact-split #-}

module finsum where

open import base
open import equality
open import equivalence
open import cubical
open import fin
open import fin-algebra
open import finset
open import finite-commutative-monoid
open import finset.instances
open import functions
open import hlevel
open import isomorphism
open import maybe
open import nat
open import permutation.insert
open import permutation.swap
open import relation
open import ring
open import ring.implementations
open import semiring
open import sigma
open import sum
open import truncation
open import type-algebra
open import univalence
open import funext

private
  variable
    ℓ : Level
    A : Type ℓ

module _ {D : Type ℓ} {{S : Semiring D}} where
  private
    CM = +-CommMonoid

  finSumDep : (n : Nat) -> (f : (Fin n) -> D) -> D
  finSumDep = finMergeDep CM

  enumerationSum : {n : Nat} -> (Fin n -> A) -> (A -> D) -> D
  enumerationSum = enumerationMerge CM

  equivSum : {n : Nat} -> (A ≃ Fin n) -> (A -> D) -> D
  equivSum = equivMerge CM

  abstract
    finiteSum : {ℓ : Level} -> (s : FinSet ℓ) -> (⟨ s ⟩ -> D) -> D
    finiteSum (_ , f) = finiteMerge CM {{FI = record {isFin = f} }}

    finiteSum-eval : {ℓ : Level} (A : FinSet ℓ) {n : Nat}
                     -> (eq : (⟨ A ⟩ ≃ Fin n)) -> (f : ⟨ A ⟩ -> D)
                     -> finiteSum A f == equivSum eq f
    finiteSum-eval = finiteMergeᵉ-eval CM

    finiteSum-convert : {ℓ₁ ℓ₂ : Level} -> (A : FinSet ℓ₁) (B : FinSet ℓ₂)
                        (eq : (⟨ B ⟩ ≃ ⟨ A ⟩) ) (f : ⟨ A ⟩ -> D)
                        -> finiteSum A f == finiteSum B (f ∘ (eqFun eq))
    finiteSum-convert = finiteMergeᵉ-convert CM

    finiteSum-convert-iso : {ℓ₁ ℓ₂ : Level} -> (A : FinSet ℓ₁) (B : FinSet ℓ₂)
                            (i : Iso ⟨ B ⟩ ⟨ A ⟩) (f : ⟨ A ⟩ -> D)
                            -> finiteSum A f == finiteSum B (f ∘ (Iso.fun i))
    finiteSum-convert-iso = finiteMergeᵉ-convert-iso CM


private
  module _ {D : Type ℓ} {{S : Semiring D}} where
    i<nSum : (n : Nat) -> (f : Nat -> D) -> D
    i<nSum n f = finSumDep n (\ (x , _) -> f x)


  i<nSum-zero : {n : Nat} -> i<nSum n (\i -> 0) == 0
  i<nSum-zero {n = zero}  = refl
  i<nSum-zero {n = suc n} = i<nSum-zero {n}

  i<nSum-one : {n : Nat} -> i<nSum n (\i -> 1) == n
  i<nSum-one {n = zero}  = refl
  i<nSum-one {n = suc n} = cong suc (i<nSum-one {n})

finiteSum-one : (n : Nat) -> finiteSum (FinSet-Fin n) (\i -> 1) == n
finiteSum-one n = finiteSum-eval _ (idEquiv _) (\i -> 1) >=> i<nSum-one {n}


ΣFin-suc-eq' : (n : Nat) (P : (Fin (suc n)) -> Type ℓ) ->
               (Σ[ i ∈ Fin (suc n) ] (P i)) ≃ (P zero-fin ⊎  Σ[ i ∈ Fin n ] (P (suc-fin i)))
ΣFin-suc-eq' n P = (isoToEquiv i)
  where

  forward : (Σ[ i ∈ Fin (suc n) ] (P i)) -> (P zero-fin ⊎ Σ[ i ∈ Fin n ] (P (suc-fin i)))
  forward ((0 , lt) , p) = inj-l (substᵉ P (fin-i-path refl) p)
  forward ((suc i , lt) , p) = inj-r ((i , pred-≤ lt) , (substᵉ P (fin-i-path refl) p))

  backward : (P zero-fin ⊎ Σ[ i ∈ Fin n ] (P (suc-fin i))) -> (Σ[ i ∈ Fin (suc n) ] (P i))
  backward (inj-l p) = (zero-fin , p)
  backward (inj-r (i , p)) = (suc-fin i , p)

  module _ (i : Fin n) (p : (P (suc-fin i))) where
    fst-path : fst (proj-r (forward (backward (inj-r (i , p)))) tt) == i
    fst-path = fin-i-path refl

    x : Fin (suc n)
    x = suc-fin i
    y : Fin (suc n)
    y = suc-fin (fst-path i0)
    p1 p2 : x == y
    p1 = sym (cong suc-fin fst-path)
    p2 = (fin-i-path refl)

    fb-r-snd : PathP (\k -> P (p1 (~ k))) (substᵉ P p2 p) p
    fb-r-snd = symP (subst-filler2 P p1 p2 (isSetFin x y p1 p2) p)

    fb-r : forward (backward (inj-r (i , p))) == inj-r (i , p)
    fb-r k = inj-r (fst-path k , fb-r-snd k)

  module _ (p : (P zero-fin)) where
    fb-l : forward (backward (inj-l p)) == inj-l p
    fb-l = cong inj-l path
      where
      path-i : zero-fin == zero-fin
      path-i = fin-i-path refl

      path : (substᵉ P path-i p) == p
      path = sym (subst-filler2 P refl path-i (isSetFin _ _ _ _) p)

  bf-zero : (lt : 0 < (suc n)) (p : P (0 , lt)) ->
            backward (forward ((0 , lt) , p)) == ((0 , lt) , p)
  bf-zero lt p = (\i -> path1 (~ i) , path2 (~ i))
    where
    path1 : (0 , lt) == zero-fin
    path1 = fin-i-path refl
    path2 : PathP (\i -> P (path1 i)) p (substᵉ P path1 p)
    path2 = subst-filler P path1 p

  bf-suc : (i : Nat) (lt : (suc i) < (suc n)) (p : P (suc i , lt)) ->
            backward (forward ((suc i , lt) , p)) == ((suc i , lt) , p)
  bf-suc i lt p = (\i -> path1 (~ i) , path2 (~ i))
    where
    path1 : (suc i , lt) == _
    path1 = fin-i-path refl
    path2 : PathP (\i -> P (path1 i)) p (substᵉ P path1 p)
    path2 = subst-filler P path1 p


  open Iso
  i : Iso (Σ[ i ∈ Fin (suc n) ] (P i)) (P zero-fin ⊎ Σ[ i ∈ Fin n ] (P (suc-fin i)))
  i .fun = forward
  i .inv = backward
  i .rightInv (inj-l p) = fb-l p
  i .rightInv (inj-r (i , p)) = fb-r i p
  i .leftInv ((0 , lt) , p) = bf-zero lt p
  i .leftInv ((suc i , lt) , p) = bf-suc i lt p




isFinSetΣ-⊎ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} -> isFinSetΣ A -> isFinSetΣ B
              -> isFinSetΣ (A ⊎ B)
isFinSetΣ-⊎ {A = A} {B} (na , eq-a) (nb , eq-b) = (na +' nb , ∥-map2 handle eq-a eq-b)
  where
  handle : (A ≃ Fin na) -> (B ≃ Fin nb) -> (A ⊎ B) ≃ Fin (na +' nb)
  handle eq-a eq-b = ∘-equiv (pathToEquiv (\i -> (sym (Fin-+ na nb)) i)) (⊎-equiv eq-a eq-b)

abstract
  isFinSet-⊎ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} -> isFinSet A -> isFinSet B
               -> isFinSet (A ⊎ B)
  isFinSet-⊎ FA FB = isFinSetΣ->isFinSet (isFinSetΣ-⊎ (isFinSet->isFinSetΣ FA) (isFinSet->isFinSetΣ FB))

FinSet-⊎ : {ℓ₁ ℓ₂ : Level} -> (A : FinSet ℓ₁) -> (B : FinSet ℓ₂) -> FinSet (ℓ-max ℓ₁ ℓ₂)
FinSet-⊎ (A , finA) (B , finB) = (A ⊎ B) , isFinSet-⊎ finA finB

instance
  FinSetStr-⊎ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {{FA : FinSetStr A}}
                {{FB : FinSetStr B}} -> FinSetStr (A ⊎ B)
  FinSetStr-⊎ {{FA = FA}} {{FB = FB}} = record
    { isFin = isFinSet-⊎ (FinSetStr.isFin FA) (FinSetStr.isFin FB)
    }

isFinSetΣ-Σ' : {ℓ : Level} {n : Nat} (B : Fin n -> FinSet ℓ) -> isFinSetΣ (Σ[ i ∈ Fin n ] ⟨ B i ⟩)
isFinSetΣ-Σ' {ℓ} {zero} FB = 0 , ∣ isoToEquiv i ∣
  where
  B : Fin 0 -> Type ℓ
  B = fst ∘ FB
  open Iso
  i : Iso (Σ[ i ∈ Fin 0 ] (B i)) (Fin 0)
  i .fun (i , _) = bot-elim (¬fin-zero i)
  i .inv i = bot-elim (¬fin-zero i)
  i .rightInv i = bot-elim (¬fin-zero i)
  i .leftInv (i , _) = bot-elim (¬fin-zero i)
isFinSetΣ-Σ' {ℓ} {suc n} FB = substᵉ isFinSetΣ (sym (ua (ΣFin-suc-eq' n B))) combined
  where
  B : Fin (suc n) -> Type ℓ
  B = fst ∘ FB
  isFinSetΣB : (s : Fin (suc n)) -> isFinSetΣ (B s)
  isFinSetΣB s = isFinSet->isFinSetΣ (snd (FB s))

  rec : isFinSetΣ (Σ[ i ∈ Fin n ] (B (suc-fin i)))
  rec = isFinSetΣ-Σ' (FB ∘ suc-fin)

  zero-case : isFinSetΣ (B zero-fin)
  zero-case = isFinSetΣB zero-fin

  combined : isFinSetΣ (B zero-fin ⊎ (Σ[ i ∈ Fin n ] (B (suc-fin i))))
  combined = isFinSetΣ-⊎ zero-case rec

abstract
  isFinSet-Σ' : {ℓ : Level} {n : Nat} (B : Fin n -> FinSet ℓ) -> isFinSet (Σ[ i ∈ Fin n ] ⟨ B i ⟩)
  isFinSet-Σ' B = isFinSetΣ->isFinSet (isFinSetΣ-Σ' B)

  isFinSet-Σ : {ℓ₁ ℓ₂ : Level} (S : FinSet ℓ₁) (B : ⟨ S ⟩ -> FinSet ℓ₂) ->
               isFinSet (Σ[ s ∈ ⟨ S ⟩ ] ⟨ B s ⟩)
  isFinSet-Σ {ℓ₁} {ℓ₂} (S , n-eq) FB = unsquash isProp-isFinSet (∥-map handle n-eq)
    where
    handle : Σ[ n ∈ Nat ] (S ≃ Fin n) -> isFinSet (Σ[ s ∈ S ] ⟨ FB s ⟩)
    handle (n , eq) = isFinSet-equiv (equiv⁻¹ eqΣ) inner
      where
      eq' = equiv⁻¹ eq
      inner : isFinSet (Σ[ i ∈ Fin n ] (fst (FB (eqFun eq' i))))
      inner = isFinSet-Σ' (\i -> (FB (eqFun eq' i)))
      eqΣ : (Σ[ s ∈ S ] ⟨ FB s ⟩) ≃ (Σ[ i ∈ Fin n ] (fst (FB (eqFun eq' i))))
      eqΣ = reindexΣ eq' (\s -> ⟨ FB s ⟩)

FinSet-Σ : {ℓ₁ ℓ₂ : Level} (S : FinSet ℓ₁) (B : ⟨ S ⟩ -> FinSet ℓ₂) -> FinSet _
FinSet-Σ S B = (Σ[ s ∈ ⟨ S ⟩ ] ⟨ B s ⟩) , isFinSet-Σ S B

FinSet-× : {ℓ₁ ℓ₂ : Level} (A : FinSet ℓ₁) (B : FinSet ℓ₂) -> FinSet _
FinSet-× A B = FinSet-Σ A (\_ -> B)

instance
  FinSetStr-Σ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A -> Type ℓ₂} {{FA : FinSetStr A}}
                {{FB : {a : A} -> FinSetStr (B a)}} -> FinSetStr (Σ A B)
  FinSetStr-Σ {A = A} {B = B} {{FA = FA}} {{FB = FB}} = record
    { isFin = isFinSet-Σ (_ , FinSetStr.isFin FA) (\a -> B a , FinSetStr.isFin (FB {a}))
    }


cardnality-⊎ : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂}
               (finA : isFinSet A) (finB : isFinSet B) ->
               cardnality ((A ⊎ B) , isFinSet-⊎ finA finB) ==
               cardnality (A , finA) +' cardnality (B , finB)
cardnality-⊎ finA finB =
  cardnality-path (_ , (isFinSet-⊎ finA finB))
                  (isFinSetΣ-⊎ (isFinSet->isFinSetΣ finA)
                               (isFinSet->isFinSetΣ finB))

cardnalityΣ-Σ' : {ℓ : Level} {n : Nat} (B : Fin n -> FinSet ℓ) ->
                 cardnalityΣ ((Σ[ i ∈ Fin n ] ⟨ B i ⟩) , isFinSetΣ-Σ' B) ==
                 finSumDep n (\i -> cardnality (B i))
cardnalityΣ-Σ' {n = zero} FB = refl
cardnalityΣ-Σ' {n = suc n} FB = cong (cardnality (FB zero-fin) +'_) rec
  where
  rec : cardnalityΣ ((Σ[ i ∈ Fin n ] ⟨ FB (suc-fin i) ⟩) , isFinSetΣ-Σ' (FB ∘ suc-fin)) ==
        finSumDep n (\i -> cardnality (FB (suc-fin i)))
  rec = cardnalityΣ-Σ' (FB ∘ suc-fin)

cardnality-Σ' : {ℓ : Level} {n : Nat} (B : Fin n -> FinSet ℓ) ->
                cardnality ((Σ[ i ∈ Fin n ] ⟨ B i ⟩) , isFinSet-Σ' B) ==
                finSumDep n (\i -> cardnality (B i))
cardnality-Σ' {n = n} B =
  cardnality-path ((Σ[ i ∈ Fin n ] ⟨ B i ⟩) , isFinSet-Σ' B) (isFinSetΣ-Σ' B)
  >=> cardnalityΣ-Σ' B


cardnality-Σ2 : {ℓ : Level} {n : Nat} (B : Fin n -> FinSet ℓ) ->
                cardnality ((Σ[ i ∈ Fin n ] ⟨ B i ⟩) , isFinSet-Σ' B) ==
                (finiteSum (FinSet-Fin n) (\i -> cardnality (B i)))
cardnality-Σ2 B =
  cardnality-Σ' B >=> sym (finiteSum-eval (FinSet-Fin _) (idEquiv _) (\i -> cardnality (B i)))


-- TODO Make this work with different levels
cardnality-Σ3 : {ℓ : Level} (S : FinSet ℓ) (B : ⟨ S ⟩ -> FinSet ℓ) ->
                cardnality (FinSet-Σ S B) == finiteSum S (\s -> cardnality (B s))
cardnality-Σ3 {ℓ} S@(S' , fin) B = unsquash (isSetNat _ _) (∥-map handle fin)
  where
  handle : (Σ[ n ∈ Nat ] (S' ≃ Fin n)) ->
           cardnality (FinSet-Σ S B) == finiteSum S (\s -> cardnality (B s))
  handle (n , eq) = sym path4 >=> path1 >=> path2
    where
    eq' = equiv⁻¹ eq
    B' : Fin n -> FinSet ℓ
    B' i = B (eqFun eq' i)
    BSet : S' -> Type ℓ
    BSet = fst ∘ B

    path1 : cardnality ((Σ[ i ∈ Fin n ] ⟨ B' i ⟩) , isFinSet-Σ' B') ==
            (finiteSum (FinSet-Fin n) (\i -> cardnality (B' i)))
    path1 = cardnality-Σ2 B'

    path2 : (finiteSum (FinSet-Fin n) (\i -> cardnality (B' i))) ==
            (finiteSum S (\s -> cardnality (B s)))
    path2 = sym (finiteSum-convert S (FinSet-Fin n) eq' (\s -> cardnality (B s)))

    path3 : ((Σ[ i ∈ Fin n ] ⟨ B' i ⟩) , isFinSet-Σ' B') == (FinSet-Σ S B)
    path3 = (ΣProp-path isProp-isFinSet (sym (ua (reindexΣ eq' BSet))))

    path4 : cardnality ((Σ[ i ∈ Fin n ] ⟨ B' i ⟩) , isFinSet-Σ' B') ==
            cardnality (FinSet-Σ S B)
    path4 = cong cardnality path3

finiteSum'-one : {ℓ : Level} {S : FinSet ℓ} -> finiteSum S (\s -> 1) == cardnality S
finiteSum'-one {S = S@(S' , FS)} = unsquash (isSetNat _ _) (∥-map handle FS)
  where
  handle : Σ[ n ∈ Nat ] (S' ≃ Fin n) -> finiteSum S (\s -> 1) == cardnality S
  handle (n , eq) = finiteSum-convert S (FinSet-Fin n) (equiv⁻¹ eq) (\_ -> 1) >=>
                    finiteSum-one n >=> sym (cardnality-path S (n , ∣ eq ∣))


module _ {ℓD : Level} {D : Type ℓD} {{S : Semiring D}} where
  private
    module S = Semiring S

  abstract
    finiteSum-Bot : (f : Bot -> D) -> finiteSum FinSet-Bot f == S.0#
    finiteSum-Bot f = finiteSum-eval FinSet-Bot (equiv⁻¹ Fin-Bot-eq) f

  finiteSum-Fin0 : (f : (Fin 0) -> D) -> finiteSum (FinSet-Fin 0) f == S.0#
  finiteSum-Fin0 f = finiteSum-eval (FinSet-Fin 0) (idEquiv _) f

  module _ {ℓB : Level} {B : Type ℓB} (finB : isFinSet B) where

    finiteSum-Maybe :
      (f : (Maybe B) -> D) ->
      (finiteSum (FinSet-Maybe (B , finB)) f)
      == (f nothing) S.+ finiteSum (B , finB) (f ∘ just)
    finiteSum-Maybe f = unsquash (S.isSet-Domain _ _) (∥-map handle finB)
      where
      handle : Σ[ n ∈ Nat ] (B ≃ Fin n) ->
               (finiteSum (FinSet-Maybe (B , finB)) f)
               == (f nothing) S.+ finiteSum (B , finB) (f ∘ just)
      handle (n , eq) =
        begin
          finiteSum (FinSet-Maybe (B , finB)) f
        ==< finiteSum-eval _ eq' f >
          equivSum eq' f
        ==<>
          enumerationSum (eqInv eq') f
        ==<>
          (f nothing) S.+ (enumerationSum (eqInv eq' ∘ suc-fin) f)
        ==< cong (\x -> (f nothing) S.+ (enumerationSum x f)) path2 >
          (f nothing) S.+ (enumerationSum (just ∘ eqInv eq) f)
        ==<>
          (f nothing) S.+ (enumerationSum (eqInv eq) (f ∘ just))
        ==< cong (f nothing S.+_) (sym (finiteSum-eval _ eq (f ∘ just))) >
          (f nothing) S.+ finiteSum (B , finB) (f ∘ just)
        end
        where
        eq' : Maybe B ≃ Fin (suc n)
        eq' = (Maybe-eq eq >eq> (equiv⁻¹ (Fin-Maybe-eq n)))

        path3 : (eqFun (Fin-Maybe-eq n) ∘ suc-fin) == just
        path3 = funExt (\i -> cong just (fin-i-path refl))

        path4 : (eqInv eq' ∘ suc-fin) == (eqInv (Maybe-eq eq) ∘ eqFun (Fin-Maybe-eq n) ∘ suc-fin)
        path4 = refl

        path5 : (eqInv eq' ∘ suc-fin) == (eqInv (Maybe-eq eq) ∘ just)
        path5 = cong (eqInv (Maybe-eq eq) ∘_) path3


        path2 : (eqInv eq' ∘ suc-fin) == (just ∘ eqInv eq)
        path2 = path5

  module _ {ℓB : Level} {B : Type ℓB} (finB : isFinSet B) where

    finiteSum-⊎'-zero' :
      (f : (Fin 0 ⊎ B) -> D) ->
      (finiteSum (FinSet-⊎ (FinSet-Fin 0) (B , finB)) f)
      == (finiteSum (B , finB) (f ∘ inj-r))
    finiteSum-⊎'-zero' f =
      finiteSum-convert
        (FinSet-⊎ (FinSet-Fin 0) (B , finB)) (B , finB)
        ((equiv⁻¹ (⊎-Bot-eq B)) >eq> (⊎-equiv (equiv⁻¹ Fin-Bot-eq) (idEquiv _)))
        f

    finiteSum-⊎'-zero :
      (f : (Fin 0 ⊎ B) -> D) ->
      (finiteSum (FinSet-⊎ (FinSet-Fin 0) (B , finB)) f)
      == (finiteSum (FinSet-Fin 0) (f ∘ inj-l)) S.+
         (finiteSum (B , finB) (f ∘ inj-r))
    finiteSum-⊎'-zero f =
      finiteSum-⊎'-zero' f
      >=> (sym S.+-left-zero)
      >=> (cong (S._+ (finiteSum (B , finB) (f ∘ inj-r)))
                (sym (finiteSum-Fin0 (f ∘ inj-l))))

    finiteSum-⊎'-suc' : {n : Nat}
      (f : (Fin (suc n) ⊎ B) -> D) ->
      (finiteSum (FinSet-⊎ (FinSet-Fin (suc n)) (B , finB)) f)
      == f (inj-l zero-fin) S.+
         (finiteSum (FinSet-⊎ (FinSet-Fin n) (B , finB))
                    (f ∘ (⊎-map suc-fin (idfun B))))
    finiteSum-⊎'-suc' {n} f =
      begin
        (finiteSum (FinSet-⊎ (FinSet-Fin (suc n)) (B , finB)) f)
      ==< finiteSum-convert
            (FinSet-⊎ (FinSet-Fin (suc n)) (B , finB))
            (FinSet-Maybe (FinSet-⊎ (FinSet-Fin n) (B , finB)))
            eq f >
        (finiteSum (FinSet-Maybe (FinSet-⊎ (FinSet-Fin n) (B , finB))) (f ∘ (eqFun eq)))
      ==< finiteSum-Maybe (snd (FinSet-⊎ (FinSet-Fin n) (B , finB))) (f ∘ (eqFun eq)) >
        (f (eqFun eq nothing)) S.+
        (finiteSum (FinSet-⊎ (FinSet-Fin n) (B , finB)) (f ∘ (eqFun eq) ∘ just))
      ==< path >
        (f (inj-l zero-fin)) S.+
        (finiteSum (FinSet-⊎ (FinSet-Fin n) (B , finB))
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
               ((f (eqFun eq nothing)) S.+
                (finiteSum (FinSet-⊎ (FinSet-Fin n) (B , finB)) (f ∘ (eqFun eq) ∘ just)))
               ((f (inj-l zero-fin)) S.+
                (finiteSum (FinSet-⊎ (FinSet-Fin n) (B , finB))
                           (f ∘ (⊎-map suc-fin (idfun B)))))
      path i = (f (eqFun eq nothing)) S.+
               (finiteSum (FinSet-⊎ (FinSet-Fin n) (B , finB)) (path4 i))


    finiteSum-⊎' : {n : Nat}
      (f : (Fin n ⊎ B) -> D) ->
      (finiteSum (FinSet-⊎ (FinSet-Fin n) (B , finB)) f)
      == (finiteSum (FinSet-Fin n) (f ∘ inj-l)) S.+
         (finiteSum (B , finB) (f ∘ inj-r))
    finiteSum-⊎' {zero} f = finiteSum-⊎'-zero f
    finiteSum-⊎' {suc n} f =
      step
      >=> cong (f (inj-l zero-fin) S.+_) rec
      >=> (sym S.+-assoc)
      >=> (cong (S._+ (finiteSum (B , finB) (f ∘ inj-r))) (sym step2))
      where
      f' = f ∘ (⊎-map suc-fin (idfun B))
      rec : (finiteSum (FinSet-⊎ (FinSet-Fin n) (B , finB)) f')
            == (finiteSum (FinSet-Fin n) (f ∘ inj-l ∘ suc-fin)) S.+
               (finiteSum (B , finB) (f ∘ inj-r))
      rec = finiteSum-⊎' f'

      step : (finiteSum (FinSet-⊎ (FinSet-Fin (suc n)) (B , finB)) f)
             == f (inj-l zero-fin) S.+
                (finiteSum (FinSet-⊎ (FinSet-Fin n) (B , finB)) f')
      step = finiteSum-⊎'-suc' f

      step2 : (finiteSum (FinSet-Fin (suc n)) (f ∘ inj-l))
              == f (inj-l zero-fin) S.+
                 (finiteSum (FinSet-Fin n) (f ∘ inj-l ∘ suc-fin))
      step2 =
        finiteSum-convert (FinSet-Fin (suc n)) (FinSet-Maybe (FinSet-Fin n))
                          (equiv⁻¹ (Fin-Maybe-eq n)) (f ∘ inj-l)
        >=> finiteSum-Maybe (snd (FinSet-Fin n)) _

  module _ {ℓA : Level} {A : Type ℓA} (finA : isFinSet A)
           {ℓB : Level} {B : Type ℓB} (finB : isFinSet B) where

    finiteSum-⊎ :
      (f : (A ⊎ B) -> D) ->
      (finiteSum (FinSet-⊎ (A , finA) (B , finB)) f)
      == (finiteSum (A , finA) (f ∘ inj-l)) S.+ (finiteSum (B , finB) (f ∘ inj-r))
    finiteSum-⊎ f = unsquash (S.isSet-Domain _ _) (∥-map handle finA)
      where
      handle : Σ[ n ∈ Nat ] (A ≃ Fin n) ->
               (finiteSum (FinSet-⊎ (A , finA) (B , finB)) f)
               == (finiteSum (A , finA) (f ∘ inj-l)) S.+ (finiteSum (B , finB) (f ∘ inj-r))
      handle (n , eq) =
        begin
          finiteSum (FinSet-⊎ (A , finA) (B , finB)) f
        ==< finiteSum-convert
              (FinSet-⊎ (A , finA) (B , finB))
              (FinSet-⊎ (FinSet-Fin n) (B , finB))
              (⊎-equiv (equiv⁻¹ eq) (idEquiv B)) f >
          finiteSum (FinSet-⊎ (FinSet-Fin n) (B , finB)) _
        ==< finiteSum-⊎' finB _ >
          (finiteSum (FinSet-Fin n) _) S.+ (finiteSum (B , finB) (f ∘ inj-r))
        ==< cong
             (S._+ (finiteSum (B , finB) (f ∘ inj-r)))
             (sym (finiteSum-convert (A , finA) (FinSet-Fin n) (equiv⁻¹ eq) (f ∘ inj-l))) >
          (finiteSum (A , finA) (f ∘ inj-l)) S.+ (finiteSum (B , finB) (f ∘ inj-r))
        end
