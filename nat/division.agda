{-# OPTIONS --cubical --safe --exact-split #-}

module nat.division where

open import additive-group
open import additive-group.instances.nat
open import semiring.division
open import semiring.instances.nat
open import base
open import functions
open import relation
open import equality-path
open import order
open import ordered-semiring
open import ordered-semiring.instances.nat
open import hlevel.base
open import order.instances.nat
open import semiring
open import sigma.base
open import nat
open import nat.order
open import truncation

opaque
  isPropDiv'-ℕ₁ : {d n : ℕ} -> Pos' d -> isProp (d div' n)
  isPropDiv'-ℕ₁ {d} pos-d (_ , p1) (_ , p2) =
    ΣProp-path (isSetNat _ _) (*'-right-injective (d , pos-d) (p1 >=> sym p2))

  isPropDiv'-ℕ₂ : {d n : ℕ} -> Pos' n -> isProp (d div' n)
  isPropDiv'-ℕ₂ {zero}      pos-n (a , p) =
    bot-elim (subst Pos' (sym p >=> *-right-zeroᵉ a) pos-n)
  isPropDiv'-ℕ₂ {d@(suc _)} pos-n = isPropDiv'-ℕ₁ tt

  div-zero->zero : {n : Nat} -> 0 div n -> n == 0
  div-zero->zero 0%n =
    unsquash (isSetNat _ _) (∥-map (\ (x , p) -> sym p >=> *-right-zeroᵉ x) 0%n)

  div-one->one : {d : ℕ} -> d div 1 -> d == 1
  div-one->one d%1 =
    unsquash (isSetNat _ _) (∥-map (\ (x , x*d==1) -> *'-only-one-right {x} x*d==1) d%1)

  div->≤ : {d a : Nat} -> d div a -> Pos' a -> d ≤ a
  div->≤ {d} {a} d%a pos-a = unsquash isProp-≤ (∥-map handle d%a)
    where
    handle : Σ[ x ∈ Nat ] (x * d == a) -> d ≤ a
    handle (zero , x*d=a) = bot-elim (subst Pos' (sym x*d=a) pos-a)
    handle (suc x , x*d=a) = x * d , +-commuteᵉ (x * d) d >=> x*d=a

  div-antisym : {d1 d2 : Nat} -> d1 div d2 -> d2 div d1 -> d1 == d2
  div-antisym {zero}   {zero}   div1 div2 = refl
  div-antisym {suc d1} {suc d2} div1 div2 = antisym-≤ (div->≤ div1 tt) (div->≤ div2 tt)
  div-antisym {zero}   {suc d2} div1 div2 = zero-suc-absurd (sym (div-zero->zero div1))
  div-antisym {suc d1} {zero}   div1 div2 = zero-suc-absurd (sym (div-zero->zero div2))

  div-pos->pos : {d n : Nat} -> d div n -> Pos' n -> Pos' d
  div-pos->pos {zero} div1 n-pos =
    (transport (\i -> (Pos' (div-zero->zero div1 i))) n-pos)
  div-pos->pos {suc _} _ _ = tt

  div->div' : {d n : ℕ} -> d div n -> d div' n
  div->div' {zero} {n} d%n = zero , sym (div-zero->zero d%n)
  div->div' {suc d} {n} = inner (zero-suc-absurd ∘ sym)
    where
    inner : {d n : ℕ} -> d != 0 -> d div n -> d div' n
    inner {d} {n} d!=0 = unsquash (isPropDiv'-ℕ₁ pos-d)
      where
      pos-d : Pos' d
      pos-d = handle d d!=0
        where
        handle : ∀ x -> x != 0 -> Pos' x
        handle zero    ¬p = bot-elim (¬p refl)
        handle (suc _) ¬p = tt


  decide-div : (d n : ℕ) -> Dec (d div n)
  decide-div d n = inner n d
    where
    inner : (n d : ℕ) -> Dec (d div n)
    inner =
      strong-induction' (\{m} rec d -> helper d m rec)
      where
      helper : (d n : ℕ) -> (∀ {n' : Nat} -> n' < n -> (d : ℕ) → Dec (d div n')) ->
                Dec (d div n)
      helper d zero rec = yes (∣ 0 , refl ∣)
      helper zero n@(suc _) rec =
        no (\ 0%n -> zero-suc-absurd (sym (div-zero->zero 0%n)))
      helper d@(suc d') n@(suc _) rec = case (split-< n d) of
        (\{ (inj-l n<d) -> no (\ d%n -> irrefl-< (trans-<-≤ n<d (div->≤ d%n tt)))
          ; (inj-r n≤d@(n' , p)) ->
            helper2 n' p
              (rec (d' , +'-right-suc >=> cong suc (+-commuteᵉ d' n') >=>
                         sym +'-right-suc >=> p) d)
          })
        where
        helper2 : (n' : ℕ) -> n' + d == n -> Dec (d div n') -> Dec (d div n)
        helper2 n' p (yes d%n') =
          yes (∥-map (\ (a , p2) -> suc a , cong (d +_) p2 >=> +-commuteᵉ d n' >=> p) d%n')
        helper2 n' p (no d!%n') =
          no (\ d%n -> d!%n' (∥-map div-step (subst (d div_) (sym p) d%n)))
          where
          div-step : d div' (n' + d) -> d div' n'
          div-step (zero , p) = zero-suc-absurd (p >=> +'-right-suc)
          div-step (suc a , p) = a , +'-right-injective (+-commuteᵉ _ d >=> p)


  private
    div'-+-left : {d a b : Nat} -> d div' a -> d div' (a + b) -> d div' b
    div'-+-left {d@zero}      {a} {b} d%a d%a+b =
      subst (d div'_) (+-left a=0) d%a+b
      where
        a=0 : a == 0
        a=0 = div-zero->zero ∣ d%a ∣
    div'-+-left {d@(suc _)} {a} {b} (x , x*d=a) (y , y*d=a+b) = z , z*d=b
      where
        a≤a+b : a ≤ (a + b)
        a≤a+b = b , +-commuteᵉ b a

        x*d≤y*d : (x * d) ≤ (y * d)
        x*d≤y*d = subst2 _≤_ (sym x*d=a) (sym y*d=a+b) a≤a+b

        x≤y : x ≤ y
        x≤y = *₂-reflects-≤ x*d≤y*d (zero-<)
        z : ℕ
        z = fst x≤y
        z-path : z + x == y
        z-path = snd x≤y

        path1 : a + (z * d) == a + b
        path1 = +-commuteᵉ a (z * d) >=>
                cong ((z * d) +_) (sym x*d=a) >=>
                sym (*-distrib-+-rightᵉ z x d) >=>
                *-left z-path >=> y*d=a+b

        z*d=b : z * d == b
        z*d=b = +'-left-injective path1


  div-+-left : {d a b : Nat} -> d div a -> d div (a + b) -> d div b
  div-+-left = ∥-map2 div'-+-left
  div-+-right : {d a b : Nat} -> d div b -> d div (a + b) -> d div a
  div-+-right {d} {a} {b} d%b d%ab =
    div-+-left d%b (subst (d div_) (+-commuteᵉ a b) d%ab)





-- Lemmas for Nat⁺

_div⁺_ : Nat⁺ -> Nat⁺ -> Type₀
d div⁺ n = ⟨ d ⟩ div ⟨ n ⟩

div'⁺->multiple⁺ : {d n : Nat⁺} -> ⟨ d ⟩ div' ⟨ n ⟩ -> Nat⁺
div'⁺->multiple⁺ {d' , _} {_ , n-pos} (x , pr) =
  x , div-pos->pos ∣ (d' , *'-commute {d'} {x} >=> pr) ∣ n-pos
