{-# OPTIONS --cubical --safe --exact-split #-}

module quotient where

open import base
open import equality
open import nat

quotient : (a : Nat) (b : Nat⁺) -> Nat

private
  quotient-helper : (a : Nat) (x : Nat) (b : Nat⁺) -> Nat
  quotient-helper a       zero    b = suc (quotient a b)
  quotient-helper zero    (suc x) b = zero
  quotient-helper (suc a) (suc x) b = quotient-helper a x b

quotient zero    b              = zero
quotient (suc a) b@(suc b' , _) = quotient-helper a b' b

private
  quotient-helper-+' : {a : Nat} (x : Nat) {b : Nat⁺} -> quotient-helper (x +' a) x b == suc (quotient a b)
  quotient-helper-+' zero    = refl
  quotient-helper-+' (suc x) = quotient-helper-+' x

quotient-+' : (a : Nat) (b : Nat⁺) -> quotient (⟨ b ⟩ +' a) b == suc (quotient a b)
quotient-+' a ((suc b') , _) = (quotient-helper-+' b')

large-quotient : {a : Nat} (b : Nat⁺) (a≥b : a ≥ ⟨ b ⟩ ) -> quotient a b == suc (quotient ⟨ a≥b ⟩ b)
large-quotient {a} b@(b' , _) (k , p) = (\i -> quotient (path i) b) >=> (quotient-+' k b)
  where
  path : a == (b' +' k)
  path = sym p >=> (+'-commute {k} {b'})


quotient-*' : {a : Nat} {b : Nat⁺} -> quotient (a *' ⟨ b ⟩) b == a
quotient-*' {a = zero}        = refl
quotient-*' {a = (suc a)} {b} = (quotient-+' (a *' ⟨ b ⟩) b >=> cong suc (quotient-*'))

remainder : (a : Nat) (b : Nat⁺) -> Nat

private
  remainder-helper : (a : Nat) (x : Nat) (orig : Nat) (b : Nat⁺) -> Nat
  remainder-helper a       zero    orig b = remainder a b
  remainder-helper zero    (suc x) orig b = orig
  remainder-helper (suc a) (suc x) orig b = remainder-helper a x orig b

remainder zero    b              = zero
remainder (suc a) b@(suc b' , _) = (remainder-helper a b' (suc a) b)

private
  small-remainder-helper : (a x o : Nat) (b : Nat⁺)
                           -> (a < x) -> remainder-helper a x o b == o
  small-remainder-helper a       zero    o b a<x = bot-elim (zero-≮ a<x)
  small-remainder-helper zero    (suc x) o b a<x = refl
  small-remainder-helper (suc a) (suc x) o b a<x = small-remainder-helper a x o b (pred-≤ a<x)

small-remainder : {a : Nat} (b : Nat⁺) (a<b : a < ⟨ b ⟩ ) -> remainder a b == a
small-remainder {zero} b a<b = refl
small-remainder {suc a} b@(suc b' , _)  a<b = small-remainder-helper a b' (suc a) b (pred-≤ a<b)


private
  small-quotient-helper : (a x : Nat) (b : Nat⁺)
                           -> (a < x) -> quotient-helper a x b == zero
  small-quotient-helper a       zero    b a<x = bot-elim (zero-≮ a<x)
  small-quotient-helper zero    (suc x) b a<x = refl
  small-quotient-helper (suc a) (suc x) b a<x = small-quotient-helper a x b (pred-≤ a<x)

small-quotient : {a : Nat} (b : Nat⁺) (a<b : a < ⟨ b ⟩ ) -> quotient a b == 0
small-quotient {zero} b a<b = refl
small-quotient {suc a} b@(suc b' , _)  a<b = small-quotient-helper a b' b (pred-≤ a<b)

private

  large-remainder-helper : (a x o : Nat) (b : Nat⁺)
                           -> remainder-helper (x +' a) x o b == remainder a b
  large-remainder-helper a zero    o b = refl
  large-remainder-helper a (suc x) o b = large-remainder-helper a x o b

  remainder-+' : (a : Nat) (b : Nat⁺) -> remainder (⟨ b ⟩ +' a) b == remainder a b
  remainder-+' a b@(suc b' , _) = large-remainder-helper a b' (suc b' +' a) b

large-remainder : {a : Nat} (b : Nat⁺) (a≥b : a ≥ ⟨ b ⟩ ) -> remainder a b == remainder ⟨ a≥b ⟩ b
large-remainder {a} b@(b' , _) (k , p) = (\i -> remainder (path i) b) >=> (remainder-+' k b)
  where
  path : a == (b' +' k)
  path = sym p >=> (+'-commute {k} {b'})


data AddRec (a : Nat) (b : Nat⁺) : Type₀ where
  add-rec-base : (lt : a < ⟨ b ⟩)   -> AddRec a b
  add-rec-step : (gt : (a ≥ ⟨ b ⟩)) -> AddRec ⟨ gt ⟩ b -> AddRec a b

add-rec-exists : (a : Nat) (b : Nat⁺) -> AddRec a b
add-rec-exists a b = add-rec-exists' a b (suc a) (same-≤ (suc a))
  where
  add-rec-exists' : (a : Nat) (b : Nat⁺) (bound : Nat) -> (a < bound) -> AddRec a b
  add-rec-exists' a   (b'           , _) zero        lt = bot-elim (zero-≮ lt)
  add-rec-exists' a b@(b'@(suc b'') , _) (suc bound) lt = handle (split-nat< a b')
    where
    handle : (a < b') ⊎ (a ≥ b') -> AddRec a b
    handle (inj-l a<b) = add-rec-base a<b
    handle (inj-r a≥b) = add-rec-step a≥b (add-rec-exists' k b bound (trans-<-≤ k<a a≤bound))
      where
      k = fst a≥b
      k-path : b'' +' (suc k) == a
      k-path = +'-commute {b''} {suc k} >=> (sym +'-right-suc) >=> snd a≥b

      k<a : k < a
      k<a = b'' , k-path
      a≤bound : a ≤ bound
      a≤bound = pred-≤ lt

quotient-remainder-path : {a : Nat} -> (b : Nat⁺) -> a == quotient a b *' ⟨ b ⟩ +' remainder a b
quotient-remainder-path {a} b = handle (add-rec-exists a b)
  where
  handle : {a : Nat} {b : Nat⁺} -> (AddRec a b) -> a == quotient a b *' ⟨ b ⟩ +' remainder a b
  handle {a} {b@(b' , _)} (add-rec-base a<b) =
    sym (\i -> small-quotient b a<b i *' b' +' small-remainder b a<b i)
  handle {a} {b@(b' , _)} (add-rec-step a≥b rec) =
    begin
      a
    ==< sym k-path >
      b' +' k
    ==< (\i -> b' +' (k-rec-path i)) >
      b' +' (quotient k b *' b' +' remainder k b)
    ==< sym (+'-assoc {b'} {quotient k b *' b'} {remainder k b}) >
      (b' +' quotient k b *' b') +' remainder k b
    ==< (\i -> (quotient-rec-path i) *' b' +' (remainder-rec-path i)) >
      quotient a b *' ⟨ b ⟩ +' remainder a b
    end

    where
    k = ⟨ a≥b ⟩

    k-path : b' +' k  == a
    k-path = +'-commute {b'} {k} >=> snd a≥b

    k-rec-path : k == quotient k b *' b' +' remainder k b
    k-rec-path = handle rec

    remainder-rec-path : remainder k b == remainder a b
    remainder-rec-path =
      (sym (remainder-+' k b)) >=> (\i -> remainder (k-path i) b)
    quotient-rec-path : suc (quotient k b) == quotient a b
    quotient-rec-path =
      (sym (quotient-+' k b)) >=> (\i -> quotient (k-path i) b)
