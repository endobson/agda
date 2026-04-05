{-# OPTIONS --cubical --safe --exact-split #-}

module category.instances.simplex where

open import base
open import category.base
open import equality-path
open import equality.square
open import fin
open import hlevel
open import hlevel.base
open import hlevel.pi
open import nat
open import nat.order
open import order
open import order.instances.fin
open import order.instances.nat

module _ (a b : Nat) where
  record OrderPreservingMap : Type₀ where
    constructor order-preserving-map
    field
      f : Fin (suc a) -> Fin (suc b)
      increasing : ∀ {i j} -> i ≤ j -> f i ≤ f j


module _ {a b : Nat} where
  opaque
    isSet-OrderPreservingMap : isSet (OrderPreservingMap a b)
    isSet-OrderPreservingMap (order-preserving-map f₁ i₁) (order-preserving-map f₂ i₂)
      p₁ p₂ = \ii jj -> order-preserving-map (fpp ii jj) (ipp' ii jj)
      where
      fp₁ fp₂ : f₁ == f₂
      fp₁ = cong OrderPreservingMap.f p₁
      fp₂ = cong OrderPreservingMap.f p₂

      fpp : Square fp₁ fp₂ refl refl
      fpp = isSet->Square (isSetΠ (\_ -> isSetFin))

      ipp' : SquareP (\i j -> (∀ {a b} -> a ≤ b -> (fpp i j a) ≤ (fpp i j b)))
        (cong OrderPreservingMap.increasing p₁)
        (cong OrderPreservingMap.increasing p₂)
        refl refl
      ipp' = isSet->SquareP (\_ _ -> isProp->isSet (isPropΠⁱ2 \_ _ -> isPropΠ \_ -> isProp-≤))


SimplexC : PreCategory ℓ-zero ℓ-zero
SimplexC = Laws->Category SimplexLaws
  where
  SimplexSorts : CategorySorts ℓ-zero ℓ-zero
  SimplexSorts = record { Obj = Nat ; Mor = OrderPreservingMap }

  SimplexOps : CategoryOps SimplexSorts
  SimplexOps = record
    { id = record
      { f = \i -> i
      ; increasing = \lt -> lt
      }
    ; _⋆_ = \{ (order-preserving-map f₁ i₁) (order-preserving-map f₂ i₂) -> record
        { f = \x -> f₂ (f₁ x)
        ; increasing = \le -> i₂ (i₁ le)
        }
      }
    }

  opaque
    SimplexLaws : CategoryLaws SimplexOps
    SimplexLaws = record
      { ⋆-left-id = \_ -> refl
      ; ⋆-right-id = \_ -> refl
      ; ⋆-assoc = \_ _ _ -> refl
      ; isSet-Mor = isSet-OrderPreservingMap
      }


face-map : {n : Nat} -> (i : Fin (suc (suc n))) -> SimplexC [ n , suc n ]
face-map {n} (i , i<ssn) = record { f = f ; increasing = inc _ _ }
  where

  handle-split : ∀ ((j , _) : Fin (suc n)) -> j < i ⊎ (i ≤ j) -> Fin (suc (suc n))
  handle-split (j , j<sn) (inj-l j<i) = j , (trans-< j<i i<ssn)
  handle-split (j , j<sn) (inj-r i≤j) = (suc j) , (suc-< j<sn)

  f : Fin (suc n) -> Fin (suc (suc n))
  f fj@(j , j<sn) = handle-split fj (split-< j i)

  inc : ∀ j₁ j₂ -> j₁ ≤ j₂ -> f j₁ ≤ f j₂
  inc fj₁@(j₁ , j₁<sn) fj₂@(j₂ , j₂<sn) (fin≤ j₁≤j₂) =
    handle-split₂ (split-< j₁ i) (split-< j₂ i)
    where
    handle-split₂ : ∀ c₁ c₂ -> handle-split fj₁ c₁ ≤ handle-split fj₂ c₂
    handle-split₂ (inj-l j₁<i) (inj-l j₂<i) = fin≤ j₁≤j₂
    handle-split₂ (inj-l j₁<i) (inj-r i≤j₂) = fin≤ (right-suc-≤ j₁≤j₂)
    handle-split₂ (inj-r i≤j₁) (inj-l j₂<i) =
      bot-elim (irrefl-< (trans-≤-< i≤j₁ (trans-≤-< j₁≤j₂ j₂<i)))
    handle-split₂ (inj-r i≤j₁) (inj-r i≤j₂) = fin≤ (suc-≤ j₁≤j₂)
