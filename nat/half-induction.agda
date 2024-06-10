{-# OPTIONS --cubical --safe --exact-split #-}

module nat.half-induction where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality
open import hlevel
open import nat
open import nat.even-odd
open import nat.order
open import order
open import order.instances.nat

data HalfIndCase (n : Nat) : Type₀ where
  zero-case : n == 0 -> HalfIndCase n
  even-case : (m : Nat) -> HalfIndCase m -> m < n -> n == (m + m) -> Even n -> HalfIndCase n
  odd-case : (m : Nat) -> HalfIndCase m -> m < n -> n == suc (m + m) -> Odd n -> HalfIndCase n

private
  find-half : (n : Nat) -> Σ[ m ∈ Nat ] ((m + m == n) ⊎ (suc (m + m)) == n)
  find-half zero = zero  , inj-l refl
  find-half (suc n) = handle (find-half n)
    where
    handle : Σ[ m ∈ Nat ] ((m + m == n) ⊎ (suc (m + m)) == n) ->
             Σ[ m ∈ Nat ] ((m + m == (suc n)) ⊎ (suc (m + m)) == (suc n))
    handle (m , inj-l p) = (m , inj-r (cong suc p))
    handle (m , inj-r p) = (suc m , inj-l (cong suc (+'-right-suc >=> p)))

  find-smaller-half :
    ((n , _) : Nat⁺) ->
    Σ[ m ∈ Nat ] (m < n) × ((m + m == n) ⊎ (suc (m + m)) == n)
  find-smaller-half (n@(suc n') , _) = handle (find-half n')
    where
    handle : Σ[ m ∈ Nat ] ((m + m == n') ⊎ (suc (m + m)) == n') ->
             Σ[ m ∈ Nat ] (m < n) × ((m + m == n) ⊎ (suc (m + m)) == n)
    handle (m , inj-l p) = m , m<n , inj-r (cong suc p)
      where
      m<n : m < n
      m<n = m , +'-right-suc >=> cong suc p
    handle (m , inj-r p) = suc m , sm<n , inj-l (+'-right-suc {suc m} {m} >=> cong suc p)
      where
      sm<n : suc m < n
      sm<n = m , +'-right-suc >=> cong suc (+'-right-suc >=> p)


  next-case : (n : Nat) -> (∀ m -> m < n -> HalfIndCase m) -> HalfIndCase n
  next-case zero _ = zero-case refl
  next-case n@(suc n') rec = handle (find-smaller-half (suc n' , tt))
    where
    handle : Σ[ m ∈ Nat ] (m < n) × ((m + m == n) ⊎ (suc (m + m)) == n) -> HalfIndCase n
    handle (m , m<n , inj-l p) =
      even-case m (rec m m<n) m<n (sym p) (subst Even p (twice->Even m))
    handle (m , m<n , inj-r p) =
      odd-case m (rec m m<n) m<n (sym p) (subst Odd p (twice->Even m))

  make-case : (n : Nat) -> HalfIndCase n
  make-case = strong-induction' (\r -> next-case _ (\_ -> r))

  twice-injective : (m1 m2 : Nat) -> m1 + m1 == m2 + m2 -> m1 == m2
  twice-injective zero zero _ = refl
  twice-injective (suc m1) zero p = zero-suc-absurd (sym p)
  twice-injective zero (suc m2) p = zero-suc-absurd p
  twice-injective (suc m1) (suc m2) p =
    cong suc (twice-injective m1 m2
      (cong pred (sym +'-right-suc >=> cong pred p >=> +'-right-suc)))

  module _ (n : Nat) (rec : ∀ m -> m < n -> isProp (HalfIndCase m)) where
    isProp-HalfIndCase' : isProp (HalfIndCase n)
    isProp-HalfIndCase' (zero-case p1) (zero-case p2) =
      cong zero-case (isSetNat _ _ p1 p2)
    isProp-HalfIndCase' (even-case m1 cm1 m1<n n=m1+m1 even-n1)
                        (even-case m2 cm2 m2<n n=m2+m2 even-n2) =
      (\i -> even-case (m1=m2 i)
               (cm1=cm2 i)
               (m1<n=m2<n i)
               (isProp->PathPᵉ (\j -> isSetNat _ (m1=m2 j + m1=m2 j)) n=m1+m1 n=m2+m2 i)
               (isProp->PathPᵉ (\j -> isProp-Even n) even-n1 even-n2 i))
      where
      m1=m2 : m1 == m2
      m1=m2 = twice-injective m1 m2 (sym n=m1+m1 >=> n=m2+m2)
      m1<n=m2<n : PathP (\i -> m1=m2 i < n) m1<n m2<n
      m1<n=m2<n = isProp->PathP (\i -> isProp-< {x = m1=m2 i})
      cm1=cm2 : PathP (\i -> HalfIndCase (m1=m2 i)) cm1 cm2
      cm1=cm2 = isProp->PathP (\i -> rec (m1=m2 i) (m1<n=m2<n i))
    isProp-HalfIndCase' (odd-case m1 cm1 m1<n n=sm1+m1 odd-n1)
                        (odd-case m2 cm2 m2<n n=sm2+m2 odd-n2) =
      (\i -> odd-case (m1=m2 i)
               (cm1=cm2 i)
               (m1<n=m2<n i)
               (isProp->PathPᵉ (\j -> isSetNat _ (suc (m1=m2 j + m1=m2 j))) n=sm1+m1 n=sm2+m2 i)
               (isProp->PathPᵉ (\j -> isProp-Odd n) odd-n1 odd-n2 i))
      where
      m1=m2 : m1 == m2
      m1=m2 = twice-injective m1 m2 (cong pred (sym n=sm1+m1 >=> n=sm2+m2))
      m1<n=m2<n : PathP (\i -> m1=m2 i < n) m1<n m2<n
      m1<n=m2<n = isProp->PathP (\i -> isProp-< {x = m1=m2 i})
      cm1=cm2 : PathP (\i -> HalfIndCase (m1=m2 i)) cm1 cm2
      cm1=cm2 = isProp->PathP (\i -> rec (m1=m2 i) (m1<n=m2<n i))

    isProp-HalfIndCase' (zero-case n=0) (odd-case _ _ m<n _ _) =
      bot-elim (zero-≮ (trans-<-= m<n n=0))
    isProp-HalfIndCase' (zero-case n=0) (even-case _ _ m<n _ _) =
      bot-elim (zero-≮ (trans-<-= m<n n=0))
    isProp-HalfIndCase' (odd-case _ _ m<n _ _) (zero-case n=0)  =
      bot-elim (zero-≮ (trans-<-= m<n n=0))
    isProp-HalfIndCase' (even-case _ _ m<n _ _) (zero-case n=0)  =
      bot-elim (zero-≮ (trans-<-= m<n n=0))
    isProp-HalfIndCase' (odd-case _ _ _ _ odd-n) (even-case _ _ _ _ even-n) =
      bot-elim (Even->¬Odd n even-n odd-n)
    isProp-HalfIndCase' (even-case _ _ _ _ even-n) (odd-case _ _ _ _ odd-n) =
      bot-elim (Even->¬Odd n even-n odd-n)

  isProp-HalfIndCase : (n : Nat) -> isProp (HalfIndCase n)
  isProp-HalfIndCase = strong-induction' (\r -> isProp-HalfIndCase' _ (\_ -> r))

opaque
  isContr-HalfIndCase : (n : Nat) -> isContr (HalfIndCase n)
  isContr-HalfIndCase n = make-case n , isProp-HalfIndCase n _

  half-ind-case : (n : Nat) -> HalfIndCase n
  half-ind-case n = fst (isContr-HalfIndCase n)

data HalfIndCase⁺ (n⁺ : Nat⁺) : Type₀ where
  one-case : ⟨ n⁺ ⟩ == 1 -> HalfIndCase⁺ n⁺
  even-case : (m⁺@(m , _) : Nat⁺) -> HalfIndCase⁺ m⁺ ->
              m < ⟨ n⁺ ⟩ -> ⟨ n⁺ ⟩ == (m + m) -> Even ⟨ n⁺ ⟩ -> HalfIndCase⁺ n⁺
  odd-case : (m⁺@(m , _) : Nat⁺) -> HalfIndCase⁺ m⁺ ->
             m < ⟨ n⁺ ⟩ -> ⟨ n⁺ ⟩ == suc (m + m) -> Odd ⟨ n⁺ ⟩ -> HalfIndCase⁺ n⁺

private
  ≠0->Pos' : (n : Nat) -> n != 0 -> Pos' n
  ≠0->Pos' zero n!=0 = n!=0 refl
  ≠0->Pos' (suc n) _ = tt

  HalfIndCase->HalfIndCase⁺ : (n⁺@(n , _) : Nat⁺) -> HalfIndCase n -> HalfIndCase⁺ n⁺
  HalfIndCase->HalfIndCase⁺ (zero , ())
  HalfIndCase->HalfIndCase⁺ (suc zero , _)    _             = one-case refl
  HalfIndCase->HalfIndCase⁺ (suc (suc n) , _) (zero-case p) = zero-suc-absurd (sym p)
  HalfIndCase->HalfIndCase⁺ (suc (suc n) , _) (odd-case m cm1 m<n n=sm+m odd-n) =
    odd-case (m , pos-m) (HalfIndCase->HalfIndCase⁺ (m , pos-m) cm1) m<n n=sm+m odd-n
    where
    pos-m : Pos' m
    pos-m = ≠0->Pos' m (\m=0 ->
      zero-suc-absurd (sym (+-cong m=0 m=0) >=> cong pred (sym n=sm+m)))
  HalfIndCase->HalfIndCase⁺ (suc (suc n) , _) (even-case m cm1 m<n n=m+m even-n) =
    even-case (m , pos-m) (HalfIndCase->HalfIndCase⁺ (m , pos-m) cm1) m<n n=m+m even-n
    where
    pos-m : Pos' m
    pos-m = ≠0->Pos' m (\m=0 ->
      zero-suc-absurd (sym (+-cong m=0 m=0) >=> (sym n=m+m)))

opaque
  half-ind-case⁺ : (n : Nat⁺) -> HalfIndCase⁺ n
  half-ind-case⁺ n⁺@(n , _) = HalfIndCase->HalfIndCase⁺ n⁺ (make-case n)
