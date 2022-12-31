{-# OPTIONS --cubical --safe --exact-split #-}

module quotient-remainder where

open import base
open import equality
open import fin
open import hlevel
open import nat
open import order
open import order.instances.nat

record QuotientRemainder (d : Nat⁺) (n : Nat) : Type₀ where
  private
    d' = ⟨ d ⟩

  field
    q : Nat
    r : Fin d'

  private
    r' = Fin.i r

  field
    path : q *' d' +' r' == n

remainder : (n : Nat) (d : Nat⁺) -> Fin ⟨ d ⟩

private
  remainder-helper : (n x y : Nat) (d : Nat⁺) (p : x +' y == ⟨ d ⟩ ) -> Fin ⟨ d ⟩
  remainder-helper n       zero    y d p = remainder n d
  remainder-helper zero    (suc x) y d p = y , (x , +'-right-suc >=> p)
  remainder-helper (suc n) (suc x) y d p = remainder-helper n x (suc y) d (+'-right-suc >=> p)
remainder zero    d@(suc d' , _) = zero-fin
remainder (suc n) d@(suc d' , _) = (remainder-helper n d' 1 d (+'-right-suc >=> +'-right-zero))

private

  small-remainder-helper : (n x y : Nat) (d : Nat⁺) -> (p : (x +' y == ⟨ d ⟩)) ->
                           (lt1 : n < x) ->
                           Fin.i (remainder-helper n x y d p) == n +' y
  small-remainder-helper n       zero    y d p lt1 = bot-elim (zero-≮ lt1)
  small-remainder-helper zero    (suc x) y d p lt1 = refl
  small-remainder-helper (suc n) (suc x) y d p lt1 =
    small-remainder-helper n x (suc y) d (+'-right-suc >=> p) (pred-≤ lt1) >=> +'-right-suc

  small-remainder : (d : Nat⁺) (n : Fin ⟨ d ⟩) -> remainder (Fin.i n) d == n
  small-remainder d@(suc _  , _) (zero  , n<d) = fin-i-path refl
  small-remainder d@(suc d' , _) (suc n , n<d) =
    fin-i-path
      ((small-remainder-helper n d' 1 d (+'-right-suc >=> +'-right-zero) (pred-≤ n<d))
       >=> +'-right-suc >=> +'-right-zero)

  large-remainder-helper : (n x y : Nat) (d : Nat⁺) -> (p : x +' y == ⟨ d ⟩) ->
                           remainder-helper (x +' n) x y d p == remainder n d
  large-remainder-helper n zero    y d p = refl
  large-remainder-helper n (suc x) y d p = large-remainder-helper n x (suc y) d (+'-right-suc >=> p)

  remainder-+' : (n : Nat) (d : Nat⁺) -> remainder (⟨ d ⟩ +' n) d == remainder n d
  remainder-+' n d@(suc d' , _) = large-remainder-helper n d' 1 d (+'-right-suc >=> +'-right-zero)

  large-remainder : (d : Nat⁺) {n : Nat} (d≤n : ⟨ d ⟩ ≤ n) -> remainder n d == remainder ⟨ d≤n ⟩ d
  large-remainder d@(d' , _) {n} (k , p) = (cong (\x -> remainder x d) path) >=> (remainder-+' k d)
    where
    path : n == (d' +' k)
    path = sym p >=> (+'-commute {k} {d'})

quotient : (n : Nat) (d : Nat⁺) -> Nat
private
  quotient-helper : (n : Nat) (x : Nat) (d : Nat⁺) -> Nat
  quotient-helper n       zero    d = suc (quotient n d)
  quotient-helper zero    (suc x) d = zero
  quotient-helper (suc n) (suc x) d = quotient-helper n x d
quotient zero    d              = zero
quotient (suc n) d@(suc d' , _) = quotient-helper n d' d

private
  quotient-helper-+' : {n : Nat} (x : Nat) {d : Nat⁺} -> quotient-helper (x +' n) x d == suc (quotient n d)
  quotient-helper-+' zero    = refl
  quotient-helper-+' (suc x) = quotient-helper-+' x

  quotient-+' : (n : Nat) (d : Nat⁺) -> quotient (⟨ d ⟩ +' n) d == suc (quotient n d)
  quotient-+' n ((suc d') , _) = (quotient-helper-+' d')

  large-quotient : (d : Nat⁺) {n : Nat} (d≤n : ⟨ d ⟩ ≤ n ) -> quotient n d == suc (quotient ⟨ d≤n ⟩ d)
  large-quotient d@(d' , _) {n} (k , p) = (cong (\x -> quotient x d) path) >=> (quotient-+' k d)
    where
    path : n == (d' +' k)
    path = sym p >=> (+'-commute {k} {d'})

  small-quotient-helper : (a x : Nat) (b : Nat⁺)
                           -> (a < x) -> quotient-helper a x b == zero
  small-quotient-helper a       zero    b a<x = bot-elim (zero-≮ a<x)
  small-quotient-helper zero    (suc x) b a<x = refl
  small-quotient-helper (suc a) (suc x) b a<x = small-quotient-helper a x b (pred-≤ a<x)

  small-quotient : (d : Nat⁺) (n : Fin ⟨ d ⟩) -> quotient (Fin.i n) d == 0
  small-quotient _ (zero , _) = refl
  small-quotient d@(suc d' , _) (suc n , n<d) = small-quotient-helper n d' d (pred-≤ n<d)


remainder-path : (d : Nat⁺) (q : Nat) (r : Fin ⟨ d ⟩) -> remainder ((q *' ⟨ d ⟩) +' (Fin.i r)) d == r
remainder-path d zero    r = small-remainder d r
remainder-path d (suc q) r =
  large-remainder d ((q *' ⟨ d ⟩ +' (Fin.i r)) ,
                     +'-commute {_} {⟨ d ⟩} >=> sym (+'-assoc {⟨ d ⟩} {_} {_}))
  >=> remainder-path d q r

quotient-path : (d : Nat⁺) (q : Nat) (r : Fin ⟨ d ⟩) -> quotient ((q *' ⟨ d ⟩) +' (Fin.i r)) d == q
quotient-path d zero    r = small-quotient d r
quotient-path d (suc q) r =
  large-quotient d ((q *' ⟨ d ⟩ +' (Fin.i r)) , +'-commute {_} {⟨ d ⟩} >=> sym (+'-assoc {⟨ d ⟩} {_} {_}))
  >=> cong suc (quotient-path d q r)

private
  decompose-path' : (d : Nat⁺) (n : Nat) (b : Nat) -> (n < b) ->
                    n == (quotient n d) *' ⟨ d ⟩ +' Fin.i (remainder n d)
  decompose-path' d n zero n<b = bot-elim (zero-≮ n<b)
  decompose-path' d@(d'@(suc d'') , _) n (suc b) n<b = handle (split-nat< n d')
    where
    n≤b : n ≤ b
    n≤b = pred-≤ n<b
    handle : ((n < d') ⊎ (d' ≤ n)) -> n == (quotient n d) *' ⟨ d ⟩ +' Fin.i (remainder n d)
    handle (inj-l n<d) =
      sym (\i -> (small-quotient d (n , n<d) i) *' d' +' Fin.i (small-remainder d (n , n<d) i))
    handle (inj-r (k , p)) =
      begin
        n
      ==< sym p >
        k +' d'
      ==< cong (_+' d') (decompose-path' d k b k<b) >
        ((quotient k d) *' ⟨ d ⟩ +' Fin.i (remainder k d))  +' d'
      ==< +'-commute {_} {d'} >=> sym (+'-assoc {d'}) >
        ((suc (quotient k d)) *' ⟨ d ⟩) +' Fin.i (remainder k d)
      ==< cong2 _+'_ (cong (_*' d') (sym (large-quotient d (k , p))))
                     (cong Fin.i (sym (large-remainder d (k , p)))) >
        (quotient n d) *' ⟨ d ⟩ +' Fin.i (remainder n d)
      end
      where
      k<n : k < n
      k<n = d'' , +'-right-suc >=> (+'-commute {d'} {k}) >=> p
      k<b : k < b
      k<b = trans-≤ k<n n≤b

  decompose-path : (d : Nat⁺) (n : Nat) ->
                   n == (quotient n d) *' ⟨ d ⟩ +' Fin.i (remainder n d)
  decompose-path d n = decompose-path' d n (suc n) (same-≤ (suc n))


quotient-remainder : (d : Nat⁺) (n : Nat) -> QuotientRemainder d n
quotient-remainder d n = record
  { q = quotient n d
  ; r = remainder n d
  ; path = sym (decompose-path d n)
  }

isContr-QuotientRemainder : {d : Nat⁺} {n : Nat} -> isContr (QuotientRemainder d n)
isContr-QuotientRemainder {d} {n} .fst = quotient-remainder d n
isContr-QuotientRemainder {d} {n} .snd qr2 = (\i -> record
  { q = q-path i
  ; r = r-path i
  ; path = p-path i
  })
  where
  module qr = QuotientRemainder (quotient-remainder d n)
  module qr2 = QuotientRemainder qr2
  q-path : qr.q == qr2.q
  q-path = cong (\x -> quotient x d) (sym qr2.path) >=> quotient-path d qr2.q qr2.r
  r-path : qr.r == qr2.r
  r-path = cong (\x -> remainder x d) (sym qr2.path) >=> remainder-path d qr2.q qr2.r
  p-path : PathP (\i -> (q-path i) *' ⟨ d ⟩ +' Fin.i (r-path i) == n) qr.path qr2.path
  p-path = isProp->PathP (\i -> isSetNat _ _)
