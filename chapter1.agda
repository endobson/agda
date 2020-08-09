{-# OPTIONS --cubical --safe --exact-split #-}

module chapter1 where

open import equality
open import base
open import abs
open import nat
open import int
open import div
open import prime
open import gcd
open import prime-gcd
open import solver

ex1-1 : {a b c d : Int} -> GCD a b (int 1) -> c div a -> d div b -> GCD c d (int 1)
ex1-1 {a} {b} {c} {d} (gcd _ _ _ gcd-f) c-div-a d-div-b =
  gcd tt div-one div-one
  (\x x-div-c x-div-d ->
    (gcd-f x (div-trans x-div-c c-div-a) (div-trans x-div-d d-div-b)))

ex1-2' : {a b c : Nat} -> GCD' a b 1 -> GCD' a c 1 -> GCD' a (b *' c) 1
ex1-2' = relatively-prime-*'

ex1-2 : {a b c : Int} -> GCD a b (int 1) -> GCD a c (int 1)
                      -> GCD a (b * c) (int 1)
ex1-2 {a} {b} {c} g1 g2 = g7
  where
  g1' : GCD' (abs' a) (abs' b) 1
  g1' = (gcd->gcd' g1)
  g2' : GCD' (abs' a) (abs' c) 1
  g2' = (gcd->gcd' g2)
  g3 : GCD' (abs' a) (abs' b *' abs' c) 1
  g3 = (ex1-2' g1' g2')
  g4 : GCD (abs a) (int (abs' b *' abs' c)) (int 1)
  g4 = (gcd'->gcd/nat g3)
  g5 : GCD (abs a) (abs b * abs c) (int 1)
  g5 = transport (\i -> GCD (abs a) (int-inject-*' {abs' b} {abs' c} i) (int 1)) g4
  g6 : GCD (abs a) (abs (b * c)) (int 1)
  g6 = transport (\i -> GCD (abs a) (abs-inject-* {b} {c} (~ i)) (int 1)) g5
  g7 : GCD a (b * c) (int 1)
  g7 = (gcd-remove-abs (gcd-sym (gcd-remove-abs (gcd-sym g6))))

RPrime : Int -> Int -> Set
RPrime a b = GCD a b (int 1)

rp-* : {a b c : Int} -> RPrime b a -> RPrime c a -> RPrime (b * c) a
rp-* rp1 rp2 = gcd-sym (ex1-2 (gcd-sym rp1) (gcd-sym rp2))

rp-^ : {a b : Int} -> RPrime a b -> (n : Nat) -> {Pos' n} -> RPrime (a ^ n) b
rp-^ {a} {b} rp (suc (zero)) = transport (\i -> RPrime (^-right-one {a} (~ i)) b) rp
rp-^ rp (suc (suc n)) = rp-* rp (rp-^ rp (suc n))

rp-sym : {a b : Int} -> RPrime a b -> RPrime b a
rp-sym = gcd-sym


ex1-3 : {a b : Int} -> (RPrime a b)
         -> (n k : Nat) -> {Pos' n} -> {Pos' k} -> RPrime (a ^ n) (b ^ k)
ex1-3 rp n k {pos-n} {pos-k} = (rp-sym (rp-^ (rp-sym (rp-^ rp n {pos-n})) k {pos-k}))


ex1-4' : {a b n : Int} -> RPrime a b -> (GCD (a + b) (a + - b)) n -> n div (int 2)
ex1-4' {a} {b} {n} rp (gcd _ n%a+b n%a-b f) with (gcd->linear-combo rp)
... | (linear-combo a b _ x y {proof}) = res
  where
  lin-proof : (x + y) * (a + b) + (x + - y) * (a + - b) == (int 2)
  lin-proof =
    begin
      (x + y) * (a + b) + (x + - y) * (a + - b)
    ==< IntSolver.solve 4
        (\ x y a b  ->
          (x ⊕ y) ⊗ (a ⊕ b) ⊕ (x ⊕ (⊖ y)) ⊗ (a ⊕ (⊖ b)) ,
          (© (int 2)) ⊗ (x ⊗ a ⊕ y ⊗ b))
        refl x y a b >
      (int 2) * (x * a + y * b)
    ==< *-right {int 2} proof >
      (int 2) * (int 1)
    ==<>
      (int 2)
    end
  res : n div (int 2)
  res =
   transport
     (\ i -> n div (lin-proof i))
     (div-linear n%a+b n%a-b {x + y} {x + - y})

ex1-4 : {a b : Int} -> RPrime a b -> (GCD (a + b) (a + - b) (int 1)) ⊎ (GCD (a + b) (a + - b) (int 2))
ex1-4 {a} {b} rp with (gcd-exists (a + b) (a + - b))
... | (d@(nonneg _) , g@(gcd _ _ _ _)) = res
  where
  d-div : d div (int 2)
  d-div = (ex1-4' rp g)
  res : (GCD (a + b) (a + - b) (int 1)) ⊎ (GCD (a + b) (a + - b) (int 2))
  res with (≤->≤i (div->≤ d-div))
  ... | (suc-≤i zero-≤i) = inj-l g
  ... | (suc-≤i (suc-≤i zero-≤i)) = inj-r g
  ... | zero-≤i = bot-elim (zero-suc-absurd (sym (nonneg-injective (div-zero->zero d-div))))


ex1-6 : {a b d : Int} -> RPrime a b -> d div (a + b) -> RPrime a d × RPrime b d
ex1-6 {a} {b} {d} (gcd _ _ _ f) d%a+b =
    (gcd tt div-one div-one f-a) , (gcd tt div-one div-one f-b)
  where
  f-a : (x : Int) -> x div a -> x div d -> x div (int 1)
  f-a x x%a x%d = (f x x%a x%b)
    where
    p : - a + ( a + b) == b
    p = (sym (+-assoc { - a})) >=> (+-left (+-commute { - a} {a})) >=> (+-left (add-minus-zero {a}))
    x%b : x div b
    x%b = transport (\i -> x div (p i)) (div-sum (div-negate x%a) (div-trans x%d d%a+b))

  f-b : (x : Int) -> x div b -> x div d -> x div (int 1)
  f-b x x%b x%d = (f x x%a x%b)
    where
    p : - b + ( a + b) == a
    p = (+-right { - b} (+-commute {a} {b})) >=>
        (sym (+-assoc { - b})) >=> (+-left (+-commute { - b} {b})) >=> (+-left (add-minus-zero {b}))
    x%a : x div a
    x%a = transport (\i -> x div (p i)) (div-sum (div-negate x%b) (div-trans x%d d%a+b))

ex1-5-arith-type : Set
ex1-5-arith-type = ∀ a b -> ((a + b) * (a + b) +  - (a * a + - (a * b) + b * b))
                            == ((a * b) * (int 3))

ex1-5-arith : ex1-5-arith-type
ex1-5-arith a b =
  IntSolver.solve 2
    (\ a b ->
      ((a ⊕ b) ⊗ (a ⊕ b) ⊕  ⊖ (a ⊗ a ⊕ ⊖ (a ⊗ b) ⊕ b ⊗ b)) ,
      ((a ⊗ b) ⊗ (© (int 3))))
    refl a b

ex1-5' : {a b : Int} -> ex1-5-arith-type -> RPrime a b ->
   (GCD (a + b) (a * a + - (a * b) + b * b) (int 1)) ⊎
   (GCD (a + b) (a * a + - (a * b) + b * b) (int 3))
ex1-5' {a} {b} arith-proof rp with (gcd-exists (a + b) (a * a + - (a * b) + b * b))
... | (d@(nonneg d-nat) , g@(gcd _ d%a+b d%term _)) = res
  where
  ¬2%3 : ¬ (2 div' 3)
  ¬2%3 (zero          , pr) = zero-suc-absurd pr
  ¬2%3 ((suc zero)    , pr) = zero-suc-absurd (suc-injective (suc-injective pr))
  ¬2%3 ((suc (suc _)) , pr) =
    (zero-suc-absurd (sym (suc-injective (suc-injective (suc-injective pr)))))

  reordered-gcd : (GCD (a + b) ((a * b) * (int 3)) d)
  reordered-gcd = transport (\i -> GCD (a + b) (arith-proof a b i) d)
                            (gcd-add-linear (gcd-negate g) (a + b))

  d-div : d div (int 3)
  d-div = (euclids-lemma {a = d} {b = (a * b)} {c = (int 3)} d%ab3 rp-d-ab)
    where
    d%ab3 : d div ((a * b) * (int 3))
    d%ab3 = (GCD.%b reordered-gcd)

    rp-ad-bd : (RPrime a d) × (RPrime b d)
    rp-ad-bd = (ex1-6 rp d%a+b)

    rp-d-ab : (RPrime d (a * b))
    rp-d-ab = (ex1-2 (gcd-sym (proj₁ rp-ad-bd)) (gcd-sym (proj₂ rp-ad-bd)))

  res : (GCD (a + b) (a * a + - (a * b) + b * b) (int 1)) ⊎
        (GCD (a + b) (a * a + - (a * b) + b * b) (int 3))
  res = handle (abs' d) d-div refl
    where
    handle : (x : Nat) -> (int x) div (int 3) -> (int x) == d
             -> (GCD (a + b) (a * a + - (a * b) + b * b) (int 1)) ⊎
                (GCD (a + b) (a * a + - (a * b) + b * b) (int 3))
    handle 0 x%3 _ =
      bot-elim (zero-suc-absurd (sym (nonneg-injective (div-zero->zero x%3))))
    handle 1 _ path_ =
      inj-l (transport (\i -> GCD (a + b) (a * a + - (a * b) + b * b) (path (~ i))) g)
    handle 2 _ path =
      bot-elim (¬2%3 (div->div' (transport (\i -> (path (~ i)) div (int 3)) d-div)))
    handle 3 _ path =
      inj-r (transport (\i -> GCD (a + b) (a * a + - (a * b) + b * b) (path (~ i))) g)
    handle (suc (suc (suc (suc x)))) x%3 _ =
      bot-elim (zero-≮ (pred-≤ (pred-≤ (pred-≤ (div->≤ x%3)))))

--ex1-5 : {a b : Int} -> RPrime a b ->
--   (GCD (a + b) (a * a + - (a * b) + b * b) (int 1)) ⊎
--   (GCD (a + b) (a * a + - (a * b) + b * b) (int 3))
--ex1-5 = ex1-5' ex1-5-arith
