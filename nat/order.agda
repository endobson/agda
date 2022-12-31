{-# OPTIONS --cubical --safe --exact-split #-}

module nat.order where

open import base
open import equality
open import univalence
open import functions
open import hlevel
open import isomorphism
open import nat.arithmetic
open import nat.properties
open import relation
open import sigma.base
open import sum
open import truncation

private
  _≤_ : Nat -> Nat -> Type₀
  m ≤ n = Σ[ x ∈ Nat ] x +' m == n

  _≥_ : Nat -> Nat -> Set
  m ≥ n = n ≤ m

  _<_ : Nat -> Nat -> Set
  m < n = (suc m) ≤ n

  _>_ : Nat -> Nat -> Set
  m > n = n < m

  _≮_ : Nat -> Nat -> Set
  m ≮ n = ¬ (m < n)

  _≯_ : Nat -> Nat -> Set
  m ≯ n = ¬ (m > n)


_ℕ≤_ : Nat -> Nat -> Type₀
_ℕ≤_ = _≤_

_ℕ<_ : Nat -> Nat -> Set
_ℕ<_ = _<_

_<⁺_ : Nat⁺ -> Nat⁺ -> Set
m <⁺ n = ⟨ m ⟩ < ⟨ n ⟩

_≤⁺_ : Nat⁺ -> Nat⁺ -> Set
m ≤⁺ n = ⟨ m ⟩ ≤ ⟨ n ⟩

module _ {m n : Nat} (lt1@(x1 , p1) lt2@(x2 , p2) : m ≤ n) where
  private
    p-x : x1 == x2
    p-x = (transport (sym (+'-right-path m)) (p1 >=> (sym p2)))

    p-p : PathP (\i -> p-x i +' m == n) p1 p2
    p-p = isSet->Square isSetNat

  isProp-ℕ≤ : lt1 == lt2
  isProp-ℕ≤ i .fst = p-x i
  isProp-ℕ≤ i .snd = p-p i

isProp≮ : {m n : Nat} -> isProp (m ≮ n)
isProp≮ = isProp¬ _

zero-≤ : {n : Nat} -> zero ≤ n
zero-≤ {n} = (n , +'-right-zero)

suc-≤ : {m n : Nat} -> m ≤ n -> suc m ≤ suc n
suc-≤ (x , p) = (x , +'-right-suc >=> cong suc p)

zero-< : {n : Nat} -> zero < (suc n)
zero-< = suc-≤ zero-≤

suc-< : {m n : Nat} -> m < n -> suc m < suc n
suc-< = suc-≤

zero-≮ : {n : Nat} -> n ≮ zero
zero-≮ (zero  , p) = zero-suc-absurd (sym p)
zero-≮ (suc _ , p) = zero-suc-absurd (sym p)

pred-≤ : {m n : Nat} -> m ≤ n -> pred m ≤ pred n
pred-≤ {m = zero}              _       = zero-≤
pred-≤ {m = suc _} {n = zero}  lt      = bot-elim (zero-≮ lt)
pred-≤ {m = suc _} {n = suc _} (x , p) = (x , cong pred (sym +'-right-suc >=> p))

-- Decidability of <

decide-nat< : (x : Nat) -> (y : Nat) -> Dec (x < y)
decide-nat< _       zero    = no zero-≮
decide-nat< zero    (suc n) = yes zero-<
decide-nat< (suc m) (suc n) with (decide-nat< m n)
... | yes pr = yes (suc-≤ pr)
... | no f = no (f ∘ pred-≤)

split-nat< : (x : Nat) -> (y : Nat) -> (x < y) ⊎ (x ≥ y)
split-nat< _       zero    = inj-r zero-≤
split-nat< zero    (suc n) = inj-l zero-<
split-nat< (suc m) (suc n) with (split-nat< m n)
... | inj-l lt = inj-l (suc-≤ lt)
... | inj-r lt = inj-r (suc-≤ lt)

-- Helper constructors and paths

zero-≤->zero : {n : Nat} -> n ≤ zero -> n == zero
zero-≤->zero (0     , path) = path
zero-≤->zero (suc _ , path) = bot-elim (zero-suc-absurd (sym path))

same-≤ : (n : Nat) -> n ≤ n
same-≤ zero = zero-≤
same-≤ (suc n) = suc-≤ (same-≤ n)

same-pred-≤ : (n : Nat) -> pred n ≤ n
same-pred-≤ zero    = same-≤ zero
same-pred-≤ (suc n) = 1 , refl

same-pred-< : (n : Nat⁺) -> pred ⟨ n ⟩ < ⟨ n ⟩
same-pred-< (suc n , _) = 0 , refl

pos-pred-≤ : {m n : Nat} -> Pos' n -> m ≤ (pred n) -> m < n
pos-pred-≤ {m} {zero} ()
pos-pred-≤ {m} {suc n} _ lt = suc-≤ lt

pred-==-≤ : {m n : Nat} -> m == pred n -> m ≤ n
pred-==-≤ {n = zero}    p = (0 , p)
pred-==-≤ {n = (suc n)} p = (1 , cong suc p)

add1-< : (n : Nat) -> n < (suc n)
add1-< zero = zero-<
add1-< (suc n) = suc-< (add1-< n)

right-suc-≤ : {m n : Nat} -> m ≤ n -> m ≤ (suc n)
right-suc-≤ (x , p) = suc x , cong suc p

right-suc-< : {m n : Nat} -> m < n -> m < (suc n)
right-suc-< = right-suc-≤

weaken-ℕ< : {m n : Nat} -> m < n -> m ≤ n
weaken-ℕ< lt = pred-≤ (right-suc-≤ lt)

private
  weaken-< = weaken-ℕ<

strengthen-≤ : {m n : Nat} -> m ≤ n -> m != n -> m < n
strengthen-≤ (0     , path) ¬path = bot-elim (¬path path)
strengthen-≤ (suc x , path) ¬path = (x , +'-right-suc >=> path)

trans-ℕ≤ : {m n o : Nat} -> m ≤ n -> n ≤ o -> m ≤ o
trans-ℕ≤ (x1 , p1) (x2 , p2) =
  x1 +' x2 , +'-left (+'-commute {x1} {x2}) >=> +'-assoc {x2} {x1} >=> cong (x2 +'_) p1 >=> p2

private
  trans-≤ = trans-ℕ≤

trans-ℕ<-ℕ≤ : {m n o : Nat} -> (m < n) -> (n ≤ o) -> (m < o)
trans-ℕ<-ℕ≤ = trans-≤

private
  trans-<-≤ = trans-ℕ<-ℕ≤

trans-ℕ≤-ℕ< : {m n o : Nat} -> m ≤ n -> n < o -> m < o
trans-ℕ≤-ℕ< {m} {n} {o} (x1 , p1) (x2 , p2) = x2 +' x1 , path
  where
  path : (x2 +' x1) +' suc m == o
  path = +'-assoc {x2}
         >=> cong (x2 +'_) (+'-right-suc >=> cong suc p1)
         >=> p2
private
  trans-≤-< = trans-ℕ≤-ℕ<

trans-ℕ< : {m n o : Nat} -> (m < n) -> (n < o) -> (m < o)
trans-ℕ< lt1 lt2 = trans-≤-< (pred-≤ (right-suc-≤ lt1)) lt2

private
  trans-< = trans-ℕ<

comparison-nat< : Comparison _<_
comparison-nat< x y z x<z = handle (split-nat< x y)
  where
  handle : (x < y) ⊎ (y ≤ x) -> ∥ (x < y) ⊎ (y < z) ∥
  handle (inj-l x<y) = ∣ inj-l x<y ∣
  handle (inj-r y≤x) = ∣ inj-r (trans-≤-< y≤x x<z) ∣

private
  <->!= : {m n : Nat} -> m < n -> m != n
  <->!= {m} {n} (x , p) m==n =
    zero-suc-absurd (transport (sym (+'-right-path m)) (m==n >=> sym p >=> +'-right-suc))

same-≮ : {n : Nat} -> (n ≮ n)
same-≮ {n} lt = <->!= lt refl

<->Pos' : {x y : Nat} -> x < y -> Pos' y
<->Pos' (zero  , p) = transport (\i -> Pos' (p i)) tt
<->Pos' (suc _ , p) = transport (\i -> Pos' (p i)) tt

Pos'->< : {y : Nat} -> Pos' y -> 0 < y
Pos'->< {zero} ()
Pos'->< {suc _} _ = zero-<

-- suc-≤ introduces a path

suc-≤-iso : {m n : Nat} -> Iso (m ≤ n) (suc m ≤ suc n)
Iso.fun suc-≤-iso = suc-≤
Iso.inv suc-≤-iso = pred-≤
Iso.rightInv suc-≤-iso _ = isProp-ℕ≤ _ _
Iso.leftInv  suc-≤-iso _ = isProp-ℕ≤ _ _

suc-≤-== : {m n : Nat} -> (m ≤ n) == (suc m ≤ suc n)
suc-≤-== = ua (isoToEquiv suc-≤-iso)

-- Helpers for addition and ≤

+-left-≤ : {m n : Nat} -> (x : Nat) -> m ≤ n == (x +' m) ≤ (x +' n)
+-left-≤ {m} {n} x =
  induction {P = (\x -> m ≤ n == (x +' m) ≤ (x +' n))}
            refl (_>=> suc-≤-==) x

+-left-≤⁻ : {m n : Nat} -> (x : Nat) -> (x +' m) ≤ (x +' n) -> m ≤ n
+-left-≤⁻ zero    lt = lt
+-left-≤⁻ (suc x) lt = +-left-≤⁻ x (pred-≤ lt)

+-left-≤⁺ : {m n : Nat} -> (x : Nat) -> m ≤ n -> (x +' m) ≤ (x +' n)
+-left-≤⁺ zero    lt = lt
+-left-≤⁺ (suc x) lt = suc-≤ (+-left-≤⁺ x lt)

+-left-< : {m n : Nat} -> (x : Nat) -> m < n == (x +' m) < (x +' n)
+-left-< {m} {n} x =
  induction {P = (\x -> m < n == (x +' m) < (x +' n))}
              refl (_>=> suc-≤-==) x

+-left-<⁻ : {m n : Nat} -> (x : Nat) -> (x +' m) < (x +' n) -> m < n
+-left-<⁻ zero    lt = lt
+-left-<⁻ (suc x) lt = +-left-<⁻ x (pred-≤ lt)

+-left-<⁺ : {m n : Nat} -> (x : Nat) -> m < n -> (x +' m) < (x +' n)
+-left-<⁺ zero    lt = lt
+-left-<⁺ (suc x) lt = suc-≤ (+-left-<⁺ x lt)

+-right-≤ : {m n : Nat} -> (x : Nat) -> m ≤ n == (m +' x) ≤ (n +' x)
+-right-≤ {m} {n} x =
  transport (\i -> m ≤ n == (+'-commute {x} {m} i) ≤ (+'-commute {x} {n} i)) (+-left-≤ x)

+-right-≤⁺ : {m n : Nat} -> (x : Nat) -> m ≤ n -> (m +' x) ≤ (n +' x)
+-right-≤⁺ {m} {n} x lt =
  transport (\k -> (+'-commute {x} {m} k) ≤ (+'-commute {x} {n} k)) (+-left-≤⁺ x lt)

+-right-≤⁻ : {m n : Nat} -> (x : Nat) -> (m +' x) ≤ (n +' x) -> m ≤ n
+-right-≤⁻ {m} {n} x lt =
  +-left-≤⁻ x (transport (\k -> (+'-commute {m} {x} k) ≤ (+'-commute {n} {x} k)) lt)

+-right-< : {m n : Nat} -> (x : Nat) -> m < n == (m +' x) < (n +' x)
+-right-< = +-right-≤

+-right-<⁺ : {m n : Nat} -> (x : Nat) -> m < n -> (m +' x) < (n +' x)
+-right-<⁺ = +-right-≤⁺

+-right-<⁻ : {m n : Nat} -> (x : Nat) -> (m +' x) < (n +' x) -> m < n
+-right-<⁻ = +-right-≤⁻

+-both-≤⁺ : {a b c d : Nat} -> a ≤ b -> c ≤ d -> (a +' c) ≤ (b +' d)
+-both-≤⁺ {a} {b} {c} {d} (e , e+a=b) (f , f+c=d) = (e +' f , path)
  where
  path : (e +' f) +' (a +' c) == (b +' d)
  path =
    begin
      (e +' f) +' (a +' c)
    ==< +'-assoc {e} {f} {a +' c} >
      e +' (f +' (a +' c))
    ==< +'-right {e} (sym (+'-assoc {f} {a} {c})) >
      e +' ((f +' a) +' c)
    ==< +'-right {e} (+'-left (+'-commute {f} {a})) >
      e +' ((a +' f) +' c)
    ==< +'-right {e} (+'-assoc {a} {f} {c}) >
      e +' (a +' (f +' c))
    ==< sym (+'-assoc {e} {a} {f +' c}) >
      (e +' a) +' (f +' c)
    ==< (\i -> (e+a=b i) +' (f+c=d i)) >
      b +' d
    end

+-both-<⁺ : {a b c d : Nat} -> a < b -> c < d -> (a +' c) < (b +' d)
+-both-<⁺ {a} {b} {c} {d} a<b c<d = trans-<-≤ desuc (+-both-≤⁺ a<b c<d)
  where
  desuc : (a +' c) < (suc a +' suc c)
  desuc = 1 , cong suc (sym +'-right-suc)

-- Helpers for multiplication and ≤

*-left-≤⁺ : {m n : Nat} -> (x : Nat) -> m ≤ n -> (x *' m) ≤ (x *' n)
*-left-≤⁺ zero    lt = zero-≤
*-left-≤⁺ (suc x) lt = +-both-≤⁺ lt (*-left-≤⁺ x lt)

*-left-<⁺ : {x m n : Nat} -> x > 0 -> m < n -> (x *' m) < (x *' n)
*-left-<⁺ {zero}             x-gt lt = bot-elim (zero-≮ x-gt)
*-left-<⁺ {suc zero} {m} {n} x-gt lt =
  transport (\i -> *'-left-one {m} (~ i) < *'-left-one {n} (~ i)) lt
*-left-<⁺ {suc (suc x)} x-gt lt = +-both-<⁺ lt (*-left-<⁺ (zero-< {x}) lt)



*-right-≤⁺ : {m n : Nat} -> (x : Nat) -> m ≤ n -> (m *' x) ≤ (n *' x)
*-right-≤⁺ {m} {n} x lt =
  transport (\i -> (*'-commute {x} {m} i) ≤ (*'-commute {x} {n} i))
            (*-left-≤⁺ x lt)

*-right-<⁺ : {x m n : Nat} -> x > 0 -> m < n -> (m *' x) < (n *' x)
*-right-<⁺ {x} {m} {n} x>0 lt =
  transport (\i -> (*'-commute {x} {m} i) < (*'-commute {x} {n} i))
            (*-left-<⁺ x>0 lt)

*-left-<⁻ : {m n : Nat} -> (x : Nat) -> (x *' m) < (x *' n) -> m < n
*-left-<⁻ {m} {n} x prod-lt = handle (split-nat< m n)
  where
  handle : (m < n) ⊎ (n ≤ m) -> m < n
  handle (inj-l lt) = lt
  handle (inj-r lt) = bot-elim (same-≮ (trans-<-≤ prod-lt (*-left-≤⁺ x lt)))

*-left-≤⁻ : {m n : Nat} -> (x : Nat⁺) -> (⟨ x ⟩ *' m) ≤ (⟨ x ⟩ *' n) -> m ≤ n
*-left-≤⁻ {m} {n} x⁺@((suc x) , _) prod-lt = handle (split-nat< n m)
  where
  handle : (m > n) ⊎ (m ≤ n) -> m ≤ n
  handle (inj-r lt) = lt
  handle (inj-l gt) = bot-elim (same-≮ (trans-≤-< prod-lt (*-left-<⁺ (zero-< {x}) gt)))

*-right-<⁻ : {m n : Nat} -> (x : Nat) -> (m *' x) < (n *' x) -> m < n
*-right-<⁻ {m} {n} x lt =
  *-left-<⁻ x (transport (\i -> (*'-commute {m} {x} i) < (*'-commute {n} {x} i)) lt)

*-right-≤⁻ : {m n : Nat} -> (x : Nat⁺) -> (m *' ⟨ x ⟩) ≤ (n *' ⟨ x ⟩) -> m ≤ n
*-right-≤⁻ {m} {n} x⁺@(x , _) lt =
  *-left-≤⁻ x⁺ (transport (\i -> (*'-commute {m} {x} i) ≤ (*'-commute {n} {x} i)) lt)

*-prod-right-< : {m n : Nat} -> (m > 1) -> (p : Nat⁺) -> m *' n == ⟨ p ⟩ -> n < ⟨ p ⟩
*-prod-right-< {zero} {n} m>1 _ path = bot-elim (zero-≮ m>1)
*-prod-right-< {suc zero} {n} m>1 _ path = bot-elim (same-≮ m>1)
*-prod-right-< {m@(suc (suc m'))} {zero} m>1 (p , p-pos) path =
  bot-elim (transport (cong Pos' (sym path >=> *'-right-zero {m})) p-pos)
*-prod-right-< {m@(suc (suc m'))} {n@(suc n')} m>1 (p , _) path =
  (n' +' (m' *' n)) , path'
  where
  path' : (n' +' (m' *' n)) +' (suc n) == p
  path' = +'-right-suc >=> +'-commute {_} {n} >=> path

*-prod-left-< : {m n : Nat} -> (n > 1) -> (p : Nat⁺) -> m *' n == ⟨ p ⟩ -> m < ⟨ p ⟩
*-prod-left-< {m} {n} n>1 p path = *-prod-right-< n>1 p (*'-commute {n} {m} >=> path)


-- Helpers for exponentiation and ≤

^-suc-≤ : {m : Nat} -> m ≥ 1 -> (n : Nat) ->  (m ^' n) ≤ (m ^' (suc n))
^-suc-≤     (x , path) zero    = (x , path >=> (sym ^'-right-one))
^-suc-≤ {m} m≥1        (suc n) = *-left-≤⁺ m (^-suc-≤ m≥1 n)

^-suc-< : {m : Nat} -> m > 1 -> (n : Nat) ->  (m ^' n) < (m ^' (suc n))
^-suc-<     (x , path) zero    = (x , path >=> (sym ^'-right-one))
^-suc-< {m} m>1        (suc n) = *-left-<⁺ (weaken-< m>1) (^-suc-< m>1 n)

private
  2^n-large' : (n m : Nat) -> n == m -> n < (2 ^' n)
  2^n-large' zero _ _ = zero-<
  2^n-large' (suc zero) _ _ = suc-< zero-<
  2^n-large' (suc n@(suc n')) zero p = zero-suc-absurd (sym p)
  2^n-large' (suc n@(suc n')) (suc m) p = trans-≤-< lt1 lt2
    where
    lt1 : (suc n) ≤ (2 *' n)
    lt1 = n' , +'-right-suc >=> +'-right {suc n'} (sym *'-left-one)
    lt2 : (2 *' n) < (2 ^' (suc n))
    lt2 = *-left-<⁺ (zero-< {1}) (2^n-large' n m (cong pred p))


2^n-large : (n : Nat) -> n < (2 ^' n)
2^n-large n = 2^n-large' n n refl

ℕ≤-antisym : {m n : Nat} -> m ≤ n -> n ≤ m -> m == n
ℕ≤-antisym (zero  , p1) _ = p1
ℕ≤-antisym {m} {n} (suc i , p1) (j , p2) = bot-elim (zero-suc-absurd (sym path))
  where
  path : (suc i +' j) == 0
  path = transport (sym (+'-right-path n))
                   (+'-assoc {suc i} >=> cong (suc i +'_) p2 >=> p1)

ℕ<-asym : Asymmetric _<_
ℕ<-asym {x} {y} x<y y<x = same-≮ (trans-< x<y y<x)



private
  ≮->≥ : {m n : Nat} -> m ≮ n -> m ≥ n
  ≮->≥             {n = zero}  m≮n = zero-≤
  ≮->≥ {m = zero}  {n = suc n} m≮n = bot-elim (m≮n zero-<)
  ≮->≥ {m = suc m} {n = suc n} m≮n = suc-≤ (≮->≥ (m≮n ∘ suc-≤))

  ≮-≥-iso : {m n : Nat} -> Iso (m ≮ n) (m ≥ n)
  Iso.fun ≮-≥-iso = ≮->≥
  Iso.inv ≮-≥-iso n≤m m<n = same-≮ (trans-≤-< n≤m m<n)
  Iso.rightInv ≮-≥-iso _ = isProp-ℕ≤ _ _
  Iso.leftInv  ≮-≥-iso _ = isProp≮ _ _

connected-nat< : Connected _<_
connected-nat< x≮y y≮x = ℕ≤-antisym (≮->≥ y≮x) (≮->≥ x≮y)


≮==≥ : {m n : Nat} -> m ≮ n == m ≥ n
≮==≥ = ua (isoToEquiv ≮-≥-iso)

-- Properties of ≤/< and -'

≤-minus : {m n p : Nat} -> (m +' n) ≤ p -> m ≤ (p -' n)
≤-minus {m} {n} {p} (i , path) = (i , path')
  where
  path' : i +' m == p -' n
  path' =
    sym (+'-minus-right n)
    >=> (cong (_-' n) (+'-assoc {i} >=> path))

<-minus : {m n p : Nat} -> (m +' n) < p -> m < (p -' n)
<-minus {m} {n} {p} (i , path) = (i , path')
  where
  path' : i +' (suc m) == p -' n
  path' =
    sym (+'-minus-right n)
    >=> (cong (_-' n) (+'-assoc {i} >=> path))

<-minus-rev : {m n p : Nat} -> m < (p -' n) -> (m +' n) < p
<-minus-rev {m} {n} {p} m<p-n@(i , path) = (i , path')
  where
  check-path : i +' suc m == p -' n
  check-path = path
  path' : i +' (suc (m +' n)) == p
  path' =
    sym (+'-assoc {i} {suc m} {n})
    >=> (cong (_+' n) path)
    >=> (+'-minus-rev n (<->Pos' m<p-n))

≤-minus->zero : {m n : Nat} -> m ≤ n -> m -' n == 0
≤-minus->zero {zero} {zero}  lt = refl
≤-minus->zero {zero} {suc n} lt = refl
≤-minus->zero {suc m} {zero} lt = bot-elim (zero-≮ lt)
≤-minus->zero {suc m} {suc n} lt = ≤-minus->zero {m} {n} (pred-≤ lt)

<-minus-iso : {m n p : Nat} -> Iso ((m +' n) < p) (m < (p -' n))
Iso.fun <-minus-iso = <-minus
Iso.inv <-minus-iso = <-minus-rev
Iso.rightInv <-minus-iso _ = ΣProp-path (isSetNat _ _) refl
Iso.leftInv  <-minus-iso _ = ΣProp-path (isSetNat _ _) refl

<-minus-path : {m n p : Nat} -> ((m +' n) < p) == (m < (p -' n))
<-minus-path = ua (isoToEquiv <-minus-iso)

-- ≤ and max/min

≤-min-left : {m n : Nat} -> (min m n) ≤ m
≤-min-left {zero}  {n}     = zero-≤
≤-min-left {suc _} {zero}  = zero-≤
≤-min-left {suc m} {suc n} = suc-≤ ≤-min-left

≤-min-right : {m n : Nat} -> (min m n) ≤ n
≤-min-right {zero}  {n}     = zero-≤
≤-min-right {suc _} {zero}  = zero-≤
≤-min-right {suc m} {suc n} = suc-≤ ≤-min-right

≤-max-left : {m n : Nat} -> m ≤ (max m n)
≤-max-left {zero}  {n}     = zero-≤
≤-max-left {suc m} {zero}  = same-≤ (suc m)
≤-max-left {suc m} {suc n} = suc-≤ ≤-max-left

≤-max-right : {m n : Nat} -> n ≤ (max m n)
≤-max-right {zero}  {n}     = same-≤ n
≤-max-right {suc _} {zero}  = zero-≤
≤-max-right {suc m} {suc n} = suc-≤ ≤-max-right

≤-min-greatest : {m n x : Nat} -> x ≤ m -> x ≤ n -> x ≤ (min m n)
≤-min-greatest {m}     {n}     {zero} x≤m x≤n = zero-≤
≤-min-greatest {zero}  {n}     {suc x} x≤m x≤n = x≤m
≤-min-greatest {suc _} {zero}  {suc x} x≤m x≤n = x≤n
≤-min-greatest {suc m} {suc n} {suc x} x≤m x≤n =
  suc-≤ (≤-min-greatest {m} {n} {x} (pred-≤ x≤m) (pred-≤ x≤n))

≤-max-least : {m n x : Nat} -> m ≤ x -> n ≤ x -> (max m n) ≤ x
≤-max-least {zero}  {n}     {x} m≤x n≤x = n≤x
≤-max-least {suc _} {zero}  {x} m≤x n≤x = m≤x
≤-max-least {suc m} {suc n} {zero}  m≤x n≤x = bot-elim (zero-≮ m≤x)
≤-max-least {suc m} {suc n} {suc x} m≤x n≤x =
  suc-≤ (≤-max-least {m} {n} {x} (pred-≤ m≤x) (pred-≤ n≤x))


max-monotonic-≤ : {a b c d : Nat} -> a ≤ b -> c ≤ d -> max a c ≤ max b d
max-monotonic-≤ a≤b c≤d = ≤-max-least a≤bd c≤bd
  where
  a≤bd = trans-≤ a≤b ≤-max-left
  c≤bd = trans-≤ c≤d ≤-max-right

-- max-monotonic-≤ a1 a2 a1≤a2=

-- Flipped ≤


_≤'_ : Nat -> Nat -> Type₀
m ≤' n = Σ[ x ∈ Nat ] m +' x == n

≤==≤' : {m n : Nat} -> m ≤ n == m ≤' n
≤==≤' {m} {n} i = Σ[ x ∈ Nat ] ((+'-commute {x} {m} i) == n)

≤'->≤ : {m n : Nat} -> m ≤' n -> m ≤ n
≤'->≤ = transport (sym ≤==≤')

-- Step based ≤
data _≤s_ : Nat -> Nat -> Set where
 refl-≤s : {m : Nat} -> m ≤s m
 step-≤s : {m n : Nat} -> m ≤s n -> m ≤s suc n

_<s_ : Nat -> Nat -> Set
m <s n = (suc m) ≤s n

suc-≤s : {m n : Nat} -> m ≤s n -> (suc m) ≤s (suc n)
suc-≤s refl-≤s = refl-≤s
suc-≤s (step-≤s rec) = step-≤s (suc-≤s rec)

zero-≤s : (m : Nat) -> 0 ≤s m
zero-≤s zero = refl-≤s
zero-≤s (suc n) = step-≤s (zero-≤s n)

≤s->≤ : {m n : Nat} -> m ≤s n -> m ≤ n
≤s->≤ {m} refl-≤s = same-≤ m
≤s->≤ (step-≤s rec) = right-suc-≤ (≤s->≤ rec)

≤->≤s : {m n : Nat} -> m ≤ n -> m ≤s n
≤->≤s {m} {n}     (zero , p) = transport (\i -> m ≤s (p i)) refl-≤s
≤->≤s {n = zero}  (suc i , p) = zero-suc-absurd (sym p)
≤->≤s {n = suc _} (suc i , p) = step-≤s (≤->≤s (i , cong pred p))

-- Decidable <


trichotomous-nat< : Trichotomous _<_
trichotomous-nat< x y = handle (decide-nat x y) (decide-nat< x y) (decide-nat< y x)
  where
  handle : Dec (x == y) -> Dec (x < y) -> Dec (y < x) -> Tri (x < y) (x == y) (y < x)
  handle (yes x==y) _         _         = tri= (\ lt -> <->!= lt x==y) x==y (\ lt -> <->!= lt (sym x==y))
  handle (no  x!=y) (yes x<y) (no y≮x)  = tri< x<y x!=y y≮x
  handle (no  x!=y) (no x≮y)  (yes y<x) = tri> x≮y x!=y y<x
  handle (no  x!=y) (yes x<y) (yes y<x) = bot-elim (ℕ<-asym x<y y<x)
  handle (no  x!=y) (no x<y)  (no y<x)  = bot-elim (x!=y (ℕ≤-antisym (≮->≥ y<x) (≮->≥ x<y)))



decide-nat≤ : (x : Nat) -> (y : Nat) -> Dec (x ≤ y)
decide-nat≤ zero    _       = yes zero-≤
decide-nat≤ (suc m) zero    = no zero-≮
decide-nat≤ (suc m) (suc n) with (decide-nat≤ m n)
... | yes pr = yes (suc-≤ pr)
... | no f = no (f ∘ pred-≤)

connex'-≤ : Connex' _≤_
connex'-≤ zero    _    = inj-l zero-≤
connex'-≤ (suc m) zero = inj-r zero-≤
connex'-≤ (suc m) (suc n) = (⊎-map suc-≤ suc-≤) (connex'-≤ m n)

connex-ℕ≤ : Connex _≤_
connex-ℕ≤ m n = ∣ connex'-≤ m n ∣

total-order-≤ : TotalOrder _≤_
total-order-≤ = (trans-≤ , connex-ℕ≤ , ℕ≤-antisym)
total-order-≥ : TotalOrder _≥_
total-order-≥ = flip-total-order total-order-≤

module _ where
  private
    module _ {P : Nat -> Set}
             (p0 : P zero)
             (psuc : {m : Nat} -> ({n : Nat} -> (n ≤s m) -> P n) -> P (suc m))
             where
      InnerP : Nat -> Type₀
      InnerP m = ({n : Nat} -> (n ≤s m) -> P n)

      inner-zero : InnerP 0
      inner-zero refl-≤s = p0

      inner-suc : {n : Nat} -> InnerP n -> InnerP (suc n)
      inner-suc f refl-≤s      = psuc f
      inner-suc f (step-≤s lt) = f lt

      inner : (m : Nat) -> InnerP m
      inner zero    = inner-zero
      inner (suc m) = inner-suc (inner m)

      strong-induction-≤s : (m : Nat) -> P m
      strong-induction-≤s m = inner m refl-≤s

  strong-induction : {P : Nat -> Set}
                     (p0 : P zero)
                     (psuc : {m : Nat} -> ({n : Nat} -> (n ≤ m) -> P n) -> P (suc m))
                     -> (m : Nat) -> P m
  strong-induction p0 psuc m = strong-induction-≤s p0 (\f -> psuc (f ∘ ≤->≤s)) m

  strong-induction' : {P : Nat -> Set}
                      (p : {m : Nat} -> ({n : Nat} -> (n < m) -> P n) -> P m)
                      -> (m : Nat) -> P m
  strong-induction' {P} p m = strong-induction-≤s p0 (\f -> p (f ∘ ≤->≤s ∘ pred-≤)) m
    where
    p0 : P 0
    p0 = p (bot-elim ∘ zero-≮)


-- Induction based ≤
data _≤i_ : Nat -> Nat -> Set where
 zero-≤i : {n : Nat} -> zero ≤i n
 suc-≤i : {m n : Nat} -> m ≤i n -> suc m ≤i suc n

_<i_ : Nat -> Nat -> Set
m <i n = (suc m) ≤i n

isProp≤i : {m n : Nat} -> isProp (m ≤i n)
isProp≤i zero-≤i      zero-≤i      = refl
isProp≤i (suc-≤i lt1) (suc-≤i lt2) = cong suc-≤i (isProp≤i lt1 lt2)

zero-<i : {n : Nat} -> zero <i (suc n)
zero-<i = suc-≤i zero-≤i

zero-≮i : {n : Nat} -> ¬ (n <i zero)
zero-≮i ()

same-≤i : (n : Nat) -> n ≤i n
same-≤i zero    = zero-≤i
same-≤i (suc n) = suc-≤i (same-≤i n)

right-suc-≤i : {m n : Nat} -> m ≤i n -> m ≤i (suc n)
right-suc-≤i zero-≤i = zero-≤i
right-suc-≤i (suc-≤i lt) = suc-≤i (right-suc-≤i lt)

pred-≤i : {m n : Nat} -> m ≤i n -> pred m ≤i pred n
pred-≤i zero-≤i     = zero-≤i
pred-≤i (suc-≤i lt) = lt

≤->≤i : {m n : Nat} -> m ≤ n -> m ≤i n
≤->≤i {m = m}     (0     , p) = transport (\i -> m ≤i p i) (same-≤i m)
≤->≤i {n = zero}  (suc i , p) = bot-elim (zero-suc-absurd (sym p))
≤->≤i {n = suc n} (suc i , p) = right-suc-≤i (≤->≤i (i , cong pred p))

≤i->≤ : {m n : Nat} -> m ≤i n -> m ≤ n
≤i->≤ zero-≤i = zero-≤
≤i->≤ (suc-≤i lt) = suc-≤ (≤i->≤ lt)


≤-≤i-iso : {m n : Nat} -> Iso (m ≤ n) (m ≤i n)
Iso.fun ≤-≤i-iso = ≤->≤i
Iso.inv ≤-≤i-iso = ≤i->≤
Iso.rightInv ≤-≤i-iso _ = isProp≤i _ _
Iso.leftInv  ≤-≤i-iso _ = isProp-ℕ≤ _ _

≤==≤i : {m n : Nat} -> (m ≤ n) == (m ≤i n)
≤==≤i = ua (isoToEquiv ≤-≤i-iso)

-- Decision procedures
decide-nat<i : (x : Nat) -> (y : Nat) -> Dec (x <i y)
decide-nat<i _       zero    = no zero-≮i
decide-nat<i zero    (suc n) = yes zero-<i
decide-nat<i (suc m) (suc n) with (decide-nat<i m n)
... | yes pr = yes (suc-≤i pr)
... | no f = no (f ∘ pred-≤i)

split-nat<i : (x : Nat) -> (y : Nat) -> (x <i y) ⊎ (y ≤i x)
split-nat<i _       zero    = inj-r zero-≤i
split-nat<i zero    (suc n) = inj-l zero-<i
split-nat<i (suc m) (suc n) with (split-nat<i m n)
... | inj-l lt = inj-l (suc-≤i lt)
... | inj-r lt = inj-r (suc-≤i lt)

-- + helpers
+-left-≤i⁻ : {m n : Nat} -> (x : Nat) -> (x +' m) ≤i (x +' n) -> m ≤i n
+-left-≤i⁻ zero    lt = lt
+-left-≤i⁻ (suc x) lt = +-left-≤i⁻ x (pred-≤i lt)

+-left-≤i⁺ : {m n : Nat} -> (x : Nat) -> m ≤i n -> (x +' m) ≤i (x +' n)
+-left-≤i⁺ zero    lt = lt
+-left-≤i⁺ (suc x) lt = suc-≤i (+-left-≤i⁺ x lt)

+-left-<i⁻ : {m n : Nat} -> (x : Nat) -> (x +' m) <i (x +' n) -> m <i n
+-left-<i⁻ zero    lt = lt
+-left-<i⁻ (suc x) lt = +-left-<i⁻ x (pred-≤i lt)

+-left-<i⁺ : {m n : Nat} -> (x : Nat) -> m <i n -> (x +' m) <i (x +' n)
+-left-<i⁺ zero    lt = lt
+-left-<i⁺ (suc x) lt = suc-≤i (+-left-<i⁺ x lt)

+-right-≤i⁺ : {m n : Nat} -> (x : Nat) -> m ≤i n -> (m +' x) ≤i (n +' x)
+-right-≤i⁺ {m} {n} x lt =
  transport (\k -> (+'-commute {x} {m} k) ≤i (+'-commute {x} {n} k)) (+-left-≤i⁺ x lt)

+-right-≤i⁻ : {m n : Nat} -> (x : Nat) -> (m +' x) ≤i (n +' x) -> m ≤i n
+-right-≤i⁻ {m} {n} x lt =
  +-left-≤i⁻ x (transport (\k -> (+'-commute {m} {x} k) ≤i (+'-commute {n} {x} k)) lt)

+-right-<i⁺ : {m n : Nat} -> (x : Nat) -> m <i n -> (m +' x) <i (n +' x)
+-right-<i⁺ = +-right-≤i⁺

+-right-<i⁻ : {m n : Nat} -> (x : Nat) -> (m +' x) <i (n +' x) -> m <i n
+-right-<i⁻ = +-right-≤i⁻

-- Transitive helpers
trans-≤i : {m n o : Nat} -> m ≤i n -> n ≤i o -> m ≤i o
trans-≤i zero-≤i      _           = zero-≤i
trans-≤i (suc-≤i lt1) (suc-≤i lt2) = suc-≤i (trans-≤i lt1 lt2)

trans-<i-≤i : {m n o : Nat} -> (m <i n) -> (n ≤i o) -> (m <i o)
trans-<i-≤i = trans-≤i

trans-≤i-<i : {m n o : Nat} -> m ≤i n -> n <i o -> m <i o
trans-≤i-<i zero-≤i      (suc-≤i _  ) = suc-≤i zero-≤i
trans-≤i-<i (suc-≤i lt1) (suc-≤i lt2) = suc-≤i (trans-≤i-<i lt1 lt2)

trans-<i : {m n o : Nat} -> (m <i n) -> (n <i o) -> (m <i o)
trans-<i lt1 lt2 = trans-≤i-<i (pred-≤i (right-suc-≤i lt1)) lt2

suc-monotonic-≤ : Monotonic _≤_ _≤_ suc
suc-monotonic-≤ a1 a2 a1≤a2 = suc-≤ a1≤a2
suc-monotonic-≥ : Monotonic _≥_ _≥_ suc
suc-monotonic-≥ a1 a2 a1≥a2 = suc-≤ a1≥a2
suc-monotonic-< : Monotonic _<_ _<_ suc
suc-monotonic-< a1 a2 a1<a2 = suc-≤ a1<a2
suc-monotonic-> : Monotonic _>_ _>_ suc
suc-monotonic-> a1 a2 a1>a2 = suc-≤ a1>a2


-- WellFounded
Acc-Nat< : (n : Nat) -> (x : Nat) -> (x < n) -> Acc _<_ x
Acc-Nat< zero x x<n = acc (\y y<x -> bot-elim (zero-≮ (trans-< y<x x<n)))
Acc-Nat< (suc n) x sx≤sn = acc (\y y<x -> Acc-Nat< n y (trans-<-≤ y<x (pred-≤ sx≤sn)))

WellFounded-Nat< : WellFounded _<_
WellFounded-Nat< n = Acc-Nat< (suc n) n (same-≤ (suc n))
