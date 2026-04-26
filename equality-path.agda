{-# OPTIONS --cubical --safe --exact-split #-}

module equality-path where

open import base
open import cubical

open cubical public using (PathP; ~_)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A A1 A2 : Type ℓ
    B : A -> Type ℓ
    C : (a : A) -> (B a) -> Type ℓ


-- SquareP A l r b t : i j -> (A i j)
-- Organized like cartesian plane
--
--         t
--  (0,1) -- (1,1)
--  l |        | r
--  (0,0) -- (1,0)
--         b

SquareP : {ℓ : Level} (A : I -> I -> Type ℓ)
          {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (\i -> A i0 i) a₀₀ a₀₁)
          {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (\i -> A i1 i) a₁₀ a₁₁)
          (a₋₀ : PathP (\i -> A i i0) a₀₀ a₁₀)
          (a₋₁ : PathP (\i -> A i i1) a₀₁ a₁₁) -> Type ℓ
SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = PathP (\i -> PathP (\j -> A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋


Square : {a₀₀ : A} {a₀₁ : A} (a₀₋ : Path A a₀₀ a₀₁)
         {a₁₀ : A} {a₁₁ : A} (a₁₋ : Path A a₁₀ a₁₁)
         (a₋₀ : Path A a₀₀ a₁₀)
         (a₋₁ : Path A a₀₁ a₁₁) -> Type _
Square {A = A} a₀₋ a₁₋ a₋₀ a₋₁ = SquareP (\ _ _ -> A) a₀₋ a₁₋ a₋₀ a₋₁

ConstantSquare : (a : A) -> Type _
ConstantSquare a = Square {a₀₀ = a} refl refl refl refl

--

cong : (f : (a : A) -> (B a)) -> {x y : A} -> (p : x == y) -> PathP (\i -> (B (p i))) (f x) (f y)
cong f p i = f (p i)

cong2 : {A : Type ℓ₁} -> {B : Type ℓ₂} -> {C : Type ℓ₃} ->
        (f : A -> B -> C) -> {a c : A} -> {b d : B} -> a == c -> b == d -> f a b == f c d
cong2 f p1 p2 i = f (p1 i) (p2 i)

cong2-dep : (f : (a : A) -> (b : B a) -> C a b)
            {x y : A} (p : x == y)
            {u : B x} {v : B y} (q : PathP (\i -> B (p i)) u v)
            -> PathP (\i -> C (p i) (q i)) (f x u) (f y v)
cong2-dep f p q i = f (p i) (q i)

sym : {x y : A} -> x == y -> y == x
sym p i = p (~ i)

transport : {A B : Type ℓ} -> A == B -> A -> B
transport p a = transp (\i -> p i) i0 a

transportRefl : (x : A) -> transport refl x == x
transportRefl {A = A} x i = transp (λ _ -> A) i x

transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A == B) (x : A)
                   -> PathP (\ i -> p i) x (transport p x)
transport-filler p x i = transp (\j -> p (i ∧ j)) (~ i) x

module _ {x : A} (P : ∀ y -> x == y -> Type ℓ) (d : P x refl) where

  J : {y : A} -> (p : x == y) -> P y p
  J p = transport (\i -> P (p i) (\j -> p (i ∧ j))) d

  JRefl : J refl == d
  JRefl = transportRefl d

_∙∙_∙∙_ : {w x y z : A} -> w == x -> x == y -> y == z -> w == z
(p ∙∙ q ∙∙ r) i =
  hcomp (\ j -> \ { (i = i0) -> p (~ j)
                  ; (i = i1) -> r j})
        (q i)

doubleCompPath-filler :
  {ℓ : Level} {A : Type ℓ} {w x y z : A}
  (p : w == x) (q : x == y) (r : y == z)
  -> PathP (\i -> p (~ i) == r i) q (p ∙∙ q ∙∙ r)
doubleCompPath-filler p q r j i =
  hfill (\ j -> (\ { (i = i0) -> (p (~ j))
                   ; (i = i1) -> r j }))
        (inS (q i)) j

module _ {ℓ : Level} {A : Type ℓ} {x y : A} (p : x == y) where
  ∙∙-refl-sides : Path (x == y) (refl ∙∙ p ∙∙ refl) p
  ∙∙-refl-sides = sym (doubleCompPath-filler refl p refl)

module _ {ℓ : Level} {A : Type ℓ} {x : A} where
  ∙∙-refl : Path (x == x) (refl ∙∙ refl ∙∙ refl) refl
  ∙∙-refl = ∙∙-refl-sides refl


trans : {x y z : A} -> x == y -> y == z -> x == z
trans p1 p2 = p1 ∙∙ refl ∙∙ p2

infixl 20 _>=>_
_>=>_ : {x y z : A} -> x == y -> y == z -> x == z
p1 >=> p2 = trans p1 p2


private
  _∙_ = trans

compPath-filler : {x y z : A} (p : x == y) (q : y == z) -> PathP (\i -> x == (q i)) p (p ∙ q)
compPath-filler p q i j =
  hcomp (\ k -> \ { (i = i0) -> p (j ∨ ~ k)
                  ; (i = i1) -> doubleCompPath-filler p refl q k j
                  ; (j = i0) -> p (~ k)
                  ; (j = i1) -> q (i ∧ k)
                  })
        (p i1)


compPath-filler' : {ℓ : Level} {A : Type ℓ} {x y z : A}
  (p : x == y) (q : y == z) -> PathP (\i -> (p i) == z) (p ∙ q) q
compPath-filler' p q i j =
 hcomp (\ k -> \{ (j = i0) -> p (i ∨ ~ k)
                ; (j = i1) -> q k
                ; (i = i0) -> doubleCompPath-filler p refl q k j
                ; (i = i1) -> q (j ∧ k)
                })
       (q i0)


-- Path identies with refl
compPath-refl-right : {x y : A} (p : x == y) -> (p >=> refl) == p
compPath-refl-right p = sym (compPath-filler p refl)

compPath-refl-left : {x y : A} (p : x == y) -> (refl >=> p) == p
compPath-refl-left p = compPath-filler' refl p

compPath-sym : {x y : A} (p : x == y) -> (p >=> sym p) == refl
compPath-sym p = contract >=> ∙∙-refl
  where
  contract : (p >=> sym p) == (refl >=> refl)
  contract j = (\i -> p (i ∧ (~ j))) >=> (\i -> p (~ i ∧ (~ j)))


module _ {ℓ : Level} {A : Type ℓ} where
  private
    compPath-filler² : {x y z : A} (p : x == y) (q : y == z) (k i j : I) -> A
    compPath-filler² p q k i j =
      hfill
        (\k -> \{ (i = i0) -> p (j ∨ ~ k)
                ; (i = i1) -> doubleCompPath-filler p refl q k j
                ; (j = i0) -> p (~ k)
                ; (j = i1) -> q (i ∧ k)
                })
        (inS (p i1)) k

  opaque
    compPath/doubleCompPath-filler-refl :
      (x : A) -> compPath-filler (reflᵉ x) (reflᵉ x) ==
                 doubleCompPath-filler (reflᵉ x) (reflᵉ x) (reflᵉ x)
    compPath/doubleCompPath-filler-refl x =
      compPath-filler²-square₂
      where
      junk : Path (x == x) refl refl
      junk j k =
        hcomp (\l -> (\{ (j = i0) -> x
                       ; (j = i1) -> x
                       ; (k = i0) -> x
                       ; (k = i1) -> x
                       }))
          x

      junk=refl : junk == refl
      junk=refl l j k =
        hfill (\l -> (\{ (j = i0) -> x
                       ; (j = i1) -> x
                       ; (k = i0) -> x
                       ; (k = i1) -> x
                       }))
          (inS x) (~ l)

      compPath-filler²-square₁ :
       PathP (\k -> Square (\j -> junk j k) ((reflᵉ x) >=> (reflᵉ x)) (reflᵉ x) (reflᵉ x))
             (compPath-filler (reflᵉ x) (reflᵉ x))
             (doubleCompPath-filler (reflᵉ x) (reflᵉ x) (reflᵉ x))
      compPath-filler²-square₁ l i j =
        compPath-filler² (reflᵉ x) (reflᵉ x)
          (~ l ∨ i) (i ∨ l) j

      compPath-filler²-square₂ :
        Path (Square refl ((reflᵉ x) >=> (reflᵉ x)) (reflᵉ x) (reflᵉ x))
             (compPath-filler (reflᵉ x) (reflᵉ x))
             (doubleCompPath-filler (reflᵉ x) (reflᵉ x) (reflᵉ x))
      compPath-filler²-square₂ =
        transport
          (\l ->
            PathP (\k -> Square (\j -> (junk=refl l) j k) ((reflᵉ x) >=> (reflᵉ x)) (reflᵉ x) (reflᵉ x))
                  (compPath-filler (reflᵉ x) (reflᵉ x))
                  (doubleCompPath-filler (reflᵉ x) (reflᵉ x) (reflᵉ x)))
          compPath-filler²-square₁

module _ {ℓ : Level} {A : Type ℓ} where
  private
    compPath-filler'² : {x y z : A} (p : x == y) (q : y == z) (k i j : I) -> A
    compPath-filler'² p q k i j =
      hfill
        (\ k -> \{ (j = i0) -> p (i ∨ ~ k)
                 ; (j = i1) -> q k
                 ; (i = i0) -> doubleCompPath-filler p refl q k j
                 ; (i = i1) -> q (j ∧ k)
                 })
        (inS (q i0)) k

  compPath/doubleCompPath-filler'-refl :
    (x : A) -> compPath-filler' (reflᵉ x) (reflᵉ x) ==
               sym (doubleCompPath-filler (reflᵉ x) (reflᵉ x) (reflᵉ x))
  compPath/doubleCompPath-filler'-refl x =
    compPath-filler'²-square₂
    where
    junk : Path (x == x) refl refl
    junk j l =
      hcomp (\m -> \{ (l = i0) -> x
                    ; (l = i1) -> x
                    ; (j = i0) -> x
                    ; (j = i1) -> x
                    })
        x

    junk=refl : junk == refl
    junk=refl l j k =
      hfill (\l -> (\{ (j = i0) -> x
                     ; (j = i1) -> x
                     ; (k = i0) -> x
                     ; (k = i1) -> x
                     }))
        (inS x) (~ l)

    compPath-filler'²-square₁ :
      PathP (\l -> Square (reflᵉ x >=> reflᵉ x) (\j -> junk j l) (reflᵉ x) (reflᵉ x))
        (compPath-filler' (reflᵉ x) (reflᵉ x))
        (sym (doubleCompPath-filler (reflᵉ x) (reflᵉ x) (reflᵉ x)))
    compPath-filler'²-square₁ l j k = compPath-filler'² (reflᵉ x) (reflᵉ x) (~ j ∨ ~ l) (j ∧ ~ l) k

    compPath-filler'²-square₂ :
      Path (Square (reflᵉ x >=> reflᵉ x) (reflᵉ x) (reflᵉ x) (reflᵉ x))
        (compPath-filler' (reflᵉ x) (reflᵉ x))
        (sym (doubleCompPath-filler (reflᵉ x) (reflᵉ x) (reflᵉ x)))
    compPath-filler'²-square₂ =
      transport
        (\l ->
          PathP (\k -> Square ((reflᵉ x) >=> (reflᵉ x)) (\j -> (junk=refl l) j k) (reflᵉ x) (reflᵉ x))
                (compPath-filler' (reflᵉ x) (reflᵉ x))
                (sym (doubleCompPath-filler (reflᵉ x) (reflᵉ x) (reflᵉ x))))
        compPath-filler'²-square₁



-- Path composition with transport
transport-twice : ∀ {A B C : Type ℓ} (p : B == C) (q : A == B) (x : A)
                  -> transport p (transport q x) == (transport (q >=> p) x)
transport-twice p q x =
  (\i -> transport p (transport (compPath-refl-right q (~ i)) x))
  >=> (\i -> transport (\j -> p (i ∨ j)) (transport (q >=> (\j -> p (i ∧ j))) x))
  >=> transportRefl (transport (q >=> p) x)

transport-sym : (p : A1 == A2) (x : A1) ->
                transport (sym p) (transport p x) == x
transport-sym p x i =
  transp (\j -> p (~ j ∧ ~ i)) i (transp (\j -> p (j ∧ ~ i)) i x)

-- Path composition on PathP

transP : {A : I -> Type ℓ} {a0 : A i0} {a1 : A i1} {B_i1 : Type ℓ} {B : A i1 == B_i1}
         {b1 : B_i1} (p : PathP A a0 a1) (q : PathP (\i -> B i) a1 b1)
         -> PathP (\j -> ((\k -> A k) ∙ B) j) a0 b1
transP {A = A} {a0 = a0} {B = B} p q i =
  comp (\j -> compPath-filler (\k -> A k) B j i)
       (\j -> (\ { (i = i0) -> a0
                 ; (i = i1) -> q j}))
       (p i)

transP-mid : {A : I -> Type ℓ} {a0 : A i0} {b0 : A i0} {b1 : A i1} {a1 : A i1}
             (p : Path (A i0) a0 b0) (q : PathP A b0 b1) (r : Path (A i1) b1 a1) ->
             PathP A a0 a1
transP-mid p q r i =
  hcomp (\k -> \{ (i = i0) -> p (~ k)
                ; (i = i1) -> r k
                })
        (q i)

transP-left : {A : I -> Type ℓ} {a0 : A i0} {a1 : A i1}
              (p : PathP A a0 a1) {b1 : A i1} (q : Path (A i1) a1 b1)
              -> PathP A a0 b1
transP-left p q = transP-mid refl p q

transP-right : {A : I -> Type ℓ} {a0 : A i0} {b0 : A i0}
               (p : Path (A i0) a0 b0) {b1 : A i1} (q : PathP A b0 b1)
               -> PathP A a0 b1
transP-right p q = transP-mid p q refl

module _ {ℓA : Level} {A : I -> Type ℓA}
         {a : A i0} {b : A i1} {c : A i1} {d : A i0}
         (p : PathP (\j -> A j) a b)
         (q : Path (A i1) b c)
         (r : PathP (\j -> A (~ j)) c d)
  where

  -- Diagram for transP-sides
  --
  --      i0    p>  i1
  --  j0  +----------+
  --      | a      b |
  --  ans |          | q
  --   V  |          | V
  --      | d      c |
  --  j1  +----------+
  --           <r

  private
    module _ (i j : I) where
      raw-transP-sides : A j
      raw-transP-sides =
        comp
         (\k -> A (~ k ∨ j))
         (\k -> \{ (i = i0) -> p (~ k ∨ j)
                 ; (i = i1) -> r (k ∧ ~ j)
                 ; (j = i1) -> q i
                 })
         (q i)

  transP-sides : Path (A i0) a d
  transP-sides i = raw-transP-sides i i0

  transP-sides-filler : PathP (\j -> PathP (\i -> A j) (p j) (r (~ j))) transP-sides q
  transP-sides-filler j i = raw-transP-sides i j


transP-sym : {A : I -> Type ℓ} {a : A i0} {b : A i1} {c : A i0}
             (p : PathP (\i -> A i)     a b)
             (q : PathP (\i -> A (~ i)) b c) ->
             Path (A i0) a c
transP-sym p q = transP-sides p refl q


-- Path reversal on PathP
symP : {A : I -> Type ℓ} -> {a0 : A i0} {a1 : A i1} -> PathP A a0 a1 -> PathP (\k -> A (~ k)) a1 a0
symP p k = p (~ k)

-- Path composition is associative.

module _ {x y z w : A} (p : x == y) (q : y == z) (r : z == w)
  where
  doubleCompPath-assoc-left :
    p ∙∙ q ∙∙ r == (p >=> q) >=> r
  doubleCompPath-assoc-left = step₁ >=> step₂
    where
    step₁ : (p ∙∙ q ∙∙ r) == ((refl ∙∙ p ∙∙ refl) ∙∙ q ∙∙ r)
    step₁ j = (doubleCompPath-filler refl p refl j) ∙∙ q ∙∙ r
    step₂ : ((refl ∙∙ p ∙∙ refl) ∙∙ q ∙∙ r) ==
            ((p ∙∙ refl ∙∙ q) ∙∙ refl ∙∙ r)
    step₂ i = ((\j -> p (j ∧ i)) ∙∙ (\j -> p (j ∨ i)) ∙∙ (\j -> q (j ∧ i))) ∙∙ (\j -> q (j ∨ i)) ∙∙ r

  doubleCompPath-assoc-right :
    p ∙∙ q ∙∙ r == p >=> (q >=> r)
  doubleCompPath-assoc-right = step₁ >=> step₂
    where
    step₁ : (p ∙∙ q ∙∙ r) == ( p ∙∙ q ∙∙ (refl ∙∙ r ∙∙ refl))
    step₁ j = p ∙∙ q ∙∙ (doubleCompPath-filler refl r refl j)
    step₂ : (p ∙∙ q ∙∙ (refl ∙∙ r ∙∙ refl)) ==
            (p ∙∙ refl ∙∙ (q ∙∙ refl ∙∙ r))
    step₂ i = p ∙∙ (\j -> q (j ∧ ~ i)) ∙∙ ((\j -> q (j ∨ ~ i)) ∙∙ (\j -> r (j ∧ ~ i)) ∙∙ (\j -> r (j ∨ ~ i)))

  compPath-assoc : (p >=> q) >=> r == p >=> (q >=> r)
  compPath-assoc = sym doubleCompPath-assoc-left >=> doubleCompPath-assoc-right


-- congruence rules

module _ {ℓA1 ℓA2 : Level} {A1 : Type ℓA1} {A2 : Type ℓA2} (f : A1 -> A2) where
  private
    module _ {x y z : A1} (p₁ : x == y) (p₂ : y == z) where
      step₁ : Square (cong f (p₁ >=> p₂)) (reflᵉ (f y)) (cong f p₁) (cong f (sym p₂))
      step₁ i j = f (doubleCompPath-filler p₁ refl p₂ (~ i) j)

      step₂ : Square (reflᵉ (f y)) (cong f p₁ >=> cong f p₂) (cong f (sym p₁)) (cong f p₂)
      step₂ i j = doubleCompPath-filler (cong f p₁) refl (cong f p₂) i j

  cong-trans : {x y z : A1} (p1 : x == y) (p2 : y == z) ->
       cong f (p1 >=> p2) == cong f p1 >=> cong f p2
  cong-trans p₁ p₂ = transP-sym (step₁ p₁ p₂) (step₂ p₁ p₂)

  cong-trans-refl-both : (x : A1) ->
    PathP (\i -> Square (cong f (∙∙-refl i)) (∙∙-refl i) refl refl)
          (cong-trans refl refl)
          (reflᵉ (reflᵉ (f x)))
  cong-trans-refl-both x =
      transP-left (\i -> transP-sym (step₁-refl i) (step₂-refl i))
        (transP-sides-filler _ _ _)
    where
    center : ConstantSquare (f x)
    center _ _ = f x

    step₁-refl :
      PathP (\i -> Square (cong f (∙∙-refl {x = x} i)) refl refl refl)
            (step₁ (reflᵉ x) (reflᵉ x))
            center
    step₁-refl k i j = f (doubleCompPath-filler refl (reflᵉ x) refl (~ i ∧ ~ k) j)

    step₂-refl :
      PathP (\i -> Square refl (∙∙-refl {x = f x} i) refl refl)
            (step₂ (reflᵉ x) (reflᵉ x))
            center
    step₂-refl k i j = (doubleCompPath-filler refl (reflᵉ (f x)) refl (i ∧ ~ k) j)


private
  module _ {ℓA1 ℓA2 : Level} {A1 : Type ℓA1} {A2 : Type ℓA2} (f : A1 -> A2) where
    cong-compPath-filler : {x y z : A1} (p : x == y) (q : y == z) ->
      PathP
        (\k -> PathP (\i -> f x == f (q i)) (cong f p) (cong-trans f p q k))
        (\i j -> f (compPath-filler p q i j))
        (compPath-filler (cong f p) (cong f q))
    cong-compPath-filler {x} {y} {z} = \p q -> J (P2 x y p) (P2-refl x y p) q
      where
      module _ (x : A1) where
        P1 : (y : A1) -> x == y -> Type _
        P1 y p =
          PathP (\k -> PathP (\i -> f x == f (q i)) (cong f p) (cong-trans f p q k))
            (\i j -> f (compPath-filler p q i j))
            (compPath-filler (cong f p) (cong f q))
          where
          q = reflᵉ y

        P1-refl : P1 x refl
        P1-refl = ans
          where

          ans' : PathP (\i -> reflᵉ (f x) == (cong-trans f (reflᵉ x) (reflᵉ x) i))
                       (cong (cong f) (sym (∙∙-refl {x = x})))
                       (sym (∙∙-refl {x = f x}))
          ans' j i = cong-trans-refl-both f x (~ i) j

          ans :
            PathP (\k -> PathP (\i -> f x == f x) refl (cong-trans f refl refl k))
              (\i j -> f (compPath-filler (reflᵉ x) (reflᵉ x) i j))
              (compPath-filler refl refl)
          ans = transP-mid
            (cong (cong (cong f)) (compPath/doubleCompPath-filler-refl x))
            ans'
            (sym (compPath/doubleCompPath-filler-refl (f x)))


      module _ (x y : A1) (p : x == y) where
        P2 : (z : A1) -> y == z -> Type _
        P2 z q =
          PathP (\k -> PathP (\i -> f x == f (q i)) (cong f p) (cong-trans f p q k))
            (\i j -> f (compPath-filler p q i j))
            (compPath-filler (cong f p) (cong f q))

        P2-refl : P2 y refl
        P2-refl = J (P1 x) (P1-refl x) p

    cong-compPath-filler' : {x y z : A1} (p : x == y) (q : y == z) ->
      PathP
        (\k -> PathP (\i -> f (p i) == f z) (cong-trans f p q k) (cong f q))
        (\i j -> f (compPath-filler' p q i j))
        (compPath-filler' (cong f p) (cong f q))
    cong-compPath-filler' {x} {y} {z} = \p q -> J (P2 x y p) (P2-refl x y p) q
      where
      module _ (x : A1) where
        P1 : (y : A1) -> x == y -> Type _
        P1 y p =
          PathP
            (\k -> PathP (\i -> f (p i) == f y) (cong-trans f p q k) (cong f q))
            (\i j -> f (compPath-filler' p q i j))
            (compPath-filler' (cong f p) (cong f q))
          where
          q = reflᵉ y

        P1-refl : P1 x refl
        P1-refl = ans
          where

          ans' : PathP (\i -> (cong-trans f (reflᵉ x) (reflᵉ x) i) == reflᵉ (f x))
                       (cong (cong f) (∙∙-refl {x = x}))
                       (∙∙-refl {x = f x})
          ans' j i = cong-trans-refl-both f x i j

          ans :
            PathP (\k -> PathP (\i -> f x == f x) (cong-trans f refl refl k) (cong f refl))
              (\i j -> f (compPath-filler' (reflᵉ x) (reflᵉ x) i j))
              (compPath-filler' (cong f refl) (cong f refl))
          ans =
            transP-mid
            (cong (cong (\p -> cong f (sym p))) (compPath/doubleCompPath-filler'-refl x))
            ans'
            (cong (cong sym) (sym (compPath/doubleCompPath-filler'-refl (f x))))


      module _ (x y : A1) (p : x == y) where
        P2 : (z : A1) -> y == z -> Type _
        P2 z q =
         PathP (\k -> PathP (\i -> f (p i) == f z) (cong-trans f p q k) (cong f q))
           (\i j -> f (compPath-filler' p q i j))
           (compPath-filler' (cong f p) (cong f q))

        P2-refl : P2 y refl
        P2-refl = J (P1 x) (P1-refl x) p



  module _ {ℓ1 ℓ2 : Level} {A1 : Type ℓ1} {A2 : Type ℓ2}
           (f : A1 -> A2) {x y : A1} (p : x == y) where
    cong-trans-refl-left :
      PathP (\j -> Path (f x == f y)
                    (cong f (compPath-refl-left p j))
                    (compPath-refl-left (cong f p) j))
        (cong-trans f refl p)
        (reflᵉ (cong f p))
    cong-trans-refl-left i j = cong-compPath-filler' f refl p j i


-- Substitution
substᵉ : {x y : A} -> (P : A → Type ℓ) -> x == y -> P x -> P y
substᵉ P path = transport (\i -> (P (path i)))

abstract
  subst : {x y : A} -> (P : A → Type ℓ) -> x == y -> P x -> P y
  subst = substᵉ

subst2 : {a11 a12 : A1} {a21 a22 : A2} -> (P : A1 -> A2 -> Type ℓ) ->
         a11 == a12 -> a21 == a22 -> P a11 a21 -> P a12 a22
subst2 P path1 path2 = transport (\ i -> (P (path1 i) (path2 i)))

subst-filler : {x y : A} -> (Q : A -> Type ℓ) -> (p : x == y) -> (qx : (Q x))
             -> PathP (\i -> Q (p i)) qx (substᵉ Q p qx)
subst-filler Q p qx = transport-filler (cong Q p) qx

abstract
  subst-filler2 :  {x y : A} -> (Q : A -> Type ℓ) (p1 p2 : x == y) (pp : p1 == p2)
                   (qx : Q x) -> PathP (\k -> Q (p1 k)) qx (substᵉ Q p2 qx)
  subst-filler2 Q p1 p2 pp qx = transP-left (subst-filler Q p1 qx) (\k -> subst Q (pp k) qx)

  subst-refl : {x : A} -> {P : A → Type ℓ} -> {px : P x} -> subst P refl px == px
  subst-refl {px = px} = transportRefl px


-- True identity

path->id : {x y : A} -> x == y -> x === y
path->id {x = x} {y = y} path = (subst (x ===_) path refl-===)

id->path : {x y : A} -> x === y -> x == y
id->path refl-=== = refl


module EqReasoning where
  -- Equational reasoning
  infix  1 begin_
  infixr 2 _==<>_ _==<_>_
  infix  3 _end

  begin_ : {x y : A} -> x == y -> x == y
  begin x==y  =  x==y

  _==<>_ : (x : A) {y : A} -> x == y -> x == y
  x ==<> x==y  =  x==y

  _==<_>_ : (x : A) {y z : A} -> x == y -> y == z -> x == z
  x ==< x==y > y==z  =  trans x==y y==z

  _end : (x : A) -> x == x
  x end  =  refl

_!=_ : A -> A -> Type _
x != y = ¬ (x == y)

_!==_ : A -> A -> Type _
x !== y = ¬ (x === y)
