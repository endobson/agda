{-# OPTIONS --cubical --safe --exact-split #-}

module truncation.generic where

open import base
open import cubical
open import functions
open import hlevel.base
open import hlevel
open import pointed.spheres
open import pointed.base
open import pointed.suspension
open import pointed.suspension-loop-eq
open import truncation
open import equality-path
open import pointed.loop-space
open import equality.square
open import equality.square2
open import equivalence
open import isomorphism
open import funext

-- Cribbed from Cubical.HITs.Truncation.Base in cubical library.

data HubAndSpokeₙ {ℓ : Level} (n : Nat) (A : Type ℓ) : Type ℓ where
  ∣_∣ : A -> HubAndSpokeₙ n A
  hub : (Sⁿ n -> HubAndSpokeₙ n A) -> HubAndSpokeₙ n A
  spoke : (f : (Sⁿ n -> HubAndSpokeₙ n A)) (x : Sⁿ n) -> hub f == f x

Squashₙ : {ℓ : Level} -> Nat -> Type ℓ -> Type ℓ
Squashₙ zero _ = Lift _ Top
Squashₙ (suc n) A = HubAndSpokeₙ n A

squashₙ : {ℓ : Level} {A : Type ℓ} -> (n : Nat) -> A -> Squashₙ n A
squashₙ zero _ = lift tt
squashₙ (suc _) a = ∣ a ∣

Squashₙ∙ : {ℓ : Level} (n : Nat) (A∙ : Type∙ ℓ) -> Type∙ ℓ
Squashₙ∙ n (A , ★A) = Squashₙ n A , squashₙ n ★A

{-
module _ {ℓ : Level} {A : Type ℓ} where
  Squash≃Squashₙ : Squash A ≃ Squashₙ 1 A
  Squash≃Squashₙ = isoToEquiv (iso⁻¹ (iso₁ >iso> iso₂))
    where

    data Squash1 : Type ℓ where
      center : A -> Squash1
      branch : Squash1 -> Squash1 -> Squash1
      left : ∀ l r -> branch l r == l
      right : ∀ l r -> branch l r == r

    iso₁ : Iso (Squashₙ 1 A) Squash1
    iso₁ = iso f b fb bf
      where
      f : Squashₙ 1 A -> Squash1
      f ∣ x ∣ = center x
      f (hub w) = branch (f (w north)) (f (w south))
      f (spoke w north i) = left (f (w north)) (f (w south)) i
      f (spoke w south i) = right (f (w north)) (f (w south)) i

      fixed-wheel :
        HubAndSpokeₙ 0 A -> HubAndSpokeₙ 0 A ->
        Sⁿ 0 -> HubAndSpokeₙ 0 A
      fixed-wheel a b north = a
      fixed-wheel a b south = b

      b : Squash1 -> Squashₙ 1 A
      b (center x) = ∣ x ∣
      b (branch l r) = hub (fixed-wheel (b l) (b r))
      b (left l r i) = spoke (fixed-wheel (b l) (b r)) north i
      b (right l r i) = spoke (fixed-wheel (b l) (b r)) south i

      fb : ∀ x -> f (b x) == x
      fb (center x) = refl
      fb (branch l r) j = branch (fb l j) (fb r j)
      fb (left l r i) j = left (fb l j) (fb r j) i
      fb (right l r i) j = right (fb l j) (fb r j) i

      fixed-wheel-path :
        (w  : Sⁿ 0 -> HubAndSpokeₙ 0 A) ->
        fixed-wheel (w north) (w south) == w
      fixed-wheel-path w i north = w north
      fixed-wheel-path w i south = w south


      bf : ∀ x -> b (f x) == x
      bf ∣ x ∣ = refl
      bf (hub w) = cong hub ((cong2 fixed-wheel (bf (w north)) (bf (w south))) >=>
                             fixed-wheel-path w)
      bf (spoke w north i) = ans i
        where
        p : (fixed-wheel (b (f (w north))) (b (f (w south)))) ==
            w
        p = (cong2 fixed-wheel (bf (w north)) (bf (w south))) >=>
            fixed-wheel-path w

        p₂ : (\j -> (p j north)) == bf (w north)
        p₂ = compPath-refl-right (bf (w north))

        ans : PathP (\i -> (b (f (spoke w north i))) == (spoke w north i))
                    (bf (hub w)) (bf (w north))
        ans = transP-left (\i j -> spoke (p j) north i) p₂
      bf (spoke w south i) = ans i
        where
        p : (fixed-wheel (b (f (w north))) (b (f (w south)))) ==
            w
        p = (cong2 fixed-wheel (bf (w north)) (bf (w south))) >=>
            fixed-wheel-path w

        p₂ : (\j -> (p j south)) == bf (w south)
        p₂ = compPath-refl-right (bf (w south))

        ans : PathP (\i -> (b (f (spoke w south i))) == (spoke w south i))
                    (bf (hub w)) (bf (w south))
        ans = transP-left (\i j -> spoke (p j) south i) p₂


    iso₂ : Iso Squash1 (Squash A)
    iso₂ = iso f b fb bf
      where
      f : Squash1 -> Squash A
      f (center x) = ∣ x ∣
      f (branch l r) = f l
      f (left l r i) = f l
      f (right l r i) = squash (f l) (f r) i

      b : Squash A -> Squash1
      b ∣ x ∣ = center x
      b (squash x y i) =
        (sym (left (b x) (b y)) >=> right (b x) (b y)) i

      fb : ∀ x -> f (b x) == x
      fb ∣ x ∣ = refl
      fb (squash x y i) = s i
        where
        p : ∀ i -> f (b (squash x y i)) ==
                   (squash (f (b x)) (f (b y)) i)
        p i = (\j -> f (compPath-refl-left (right (b x) (b y)) j i))

        p₂ : PathP (\i -> (squash (f (b x)) (f (b y)) i) == squash x y i) (fb x) (fb y)
        p₂ i j = squash (fb x j) (fb y j) i

        s : PathP (\i -> f (b (squash x y i)) == squash x y i) (fb x) (fb y)
        s = transport (\k -> PathP (\i -> (p i (~ k)) == squash x y i) (fb x) (fb y))
                      p₂

      bf : ∀ x -> b (f x) == x
      bf (center x) = refl
      bf (branch l r) = bf l >=> (sym (left l r))
      bf (left l r i) = s i
        where
        p : PathP (\i -> (b (f l)) == (left l r i))
                  (bf l >=> (sym (left l r)))
                  (bf l >=> refl)
        p i = bf l >=> (\j -> left l r (~ j ∨ i))

        s : PathP (\i -> (b (f l)) == (left l r i)) (bf (branch l r)) (bf l)
        s = transP-left p (compPath-refl-right (bf l))
      bf (right l r i) = ans i
        where
        p1 : PathP (\i -> (bf l i) == (bf r i))
               (sym (left (b (f l)) (b (f r))) >=> right (b (f l)) (b (f r)))
               (sym (left l r) >=> right l r)
        p1 i = (sym (left (bf l i) (bf r i)) >=> right (bf l i) (bf r i))

        p2 : PathP (\i -> (bf l (~ i)) == (bf r (~ i)))
                   (sym (left l r) >=> right l r)
                   ((bf l) ∙∙ (sym (left l r) >=> right l r) ∙∙ sym (bf r))
        p2 = doubleCompPath-filler (bf l) (sym (left l r) >=> right l r) (sym (bf r))

        p3 : (sym (left (b (f l)) (b (f r))) >=> right (b (f l)) (b (f r))) ==
             (((bf l) >=> (sym (left l r) >=> right l r)) >=> sym (bf r))
        p3 = transP-sym p1 p2 >=> doubleCompPath-assoc-left _ _ _


        ans'2 : ((bf l >=> (sym (left l r))) >=> (right l r)) ==
                ((((bf l) >=> (sym (left l r) >=> right l r)) >=> sym (bf r)) >=>
                  (bf r))

        ans'2 =
          sym (compPath-refl-right _) >=>
          cong2 _>=>_ (compPath-assoc _ _ _) (sym (compPath-sym _)) >=>
          sym (compPath-assoc _ _ _)


        ans' : Square (bf l >=> (sym (left l r))) (bf r)
                      (((bf l) >=> (sym (left l r) >=> right l r)) >=> sym (bf r))
                      (right l r)

        ans' = compPaths->Square _ _ _ _ ans'2




        ans : PathP (\i -> (sym (left (b (f l)) (b (f r))) >=> right (b (f l)) (b (f r))) i ==
                           (right l r i))
                    (bf (branch l r)) (bf r)
        ans = transport (\j -> PathP (\i -> p3 (~ j) i == (right l r i)) (bf (branch l r)) (bf r))
                ans'
-}


private
  hlevel->contr-loops : {ℓ : Level} {A : Type ℓ}
    (i : Nat) -> isOfHLevel (suc i) A -> (a : A) -> isContr ⟨ Ωⁿ i (A , a) ⟩
  hlevel->contr-loops zero h a = a , h a
  hlevel->contr-loops {A = A} (suc n) h a =
    transport (\i -> isContr (fst (Ω-Ωⁿ-path {A∙ = (A , a)} n (~ i)))) rec
    where
    rec : isContr ⟨ Ωⁿ n (Ω (A , a)) ⟩
    rec = hlevel->contr-loops n (h a a) refl


  contr-loops->hlevel : {ℓ : Level} {A : Type ℓ}
    (i : Nat) -> ((a : A) -> isContr ⟨ Ωⁿ i (A , a) ⟩) ->
    isOfHLevel (suc i) A
  contr-loops->hlevel zero f a b = sym (snd (f a) a) >=> (snd (f a) b)
  contr-loops->hlevel {ℓ} {A} (suc i) f a b = contr-loops->hlevel i loop-contr
    where
    loop-contr : (p : a == b) -> isContr ⟨ Ωⁿ i ((a == b) , p) ⟩
    loop-contr p =
      transport (\j -> isContr ⟨ Ωⁿ i (tp j) ⟩)
        (transport (\j -> isContr (fst (Ω-Ωⁿ-path {A∙ = (A , a)} i j)))
          (f a))
      where
      tp : Path (Type∙ ℓ) ((a == a) , refl) ((a == b) , p)
      tp i = (a == (p i)) , (\j -> p (i ∧ j))

module _ {ℓ : Level} {A : Type ℓ} where
  -- TODO Make simpler
  looped-hlevel :
    (i : Nat) -> isOfHLevel (suc (suc i)) A -> (a : A) -> isOfHLevel (suc i) ⟨ Ω (A , a) ⟩
  looped-hlevel zero h a = h a a
  looped-hlevel (suc i) h a = h a a

  looped-hlevel' :
    (i : Nat) -> ((a : A) -> isOfHLevel (suc i) ⟨ Ω (A , a) ⟩) -> isOfHLevel (suc (suc i)) A
  looped-hlevel' zero h a b p = rec p
    where
    rec : isOfHLevel (suc zero) (a == b)
    rec = transport (\j -> isOfHLevel (suc zero) (a == (p j))) (h a)
  looped-hlevel' (suc i) h a b p = rec p
    where
    rec : isOfHLevel (suc (suc i)) (a == b)
    rec = transport (\j -> isOfHLevel (suc (suc i)) (a == (p j))) (h a)


n-loops==spheres : {ℓ : Level} (n : Nat) (A∙ : Type∙ ℓ) -> Ωⁿ n A∙ == Sⁿ∙ n ->∙∙ A∙
n-loops==spheres zero A∙ = sym (S⁰-maps-path A∙)
n-loops==spheres (suc i) A∙ =
  Ω-Ωⁿ-path i >=> n-loops==spheres i (Ω A∙) >=> sym (Susp∙-Ω-map-path _ _)



module _ {ℓ : Level} {A : Type ℓ} where
  private
    contr-squash-loops :
      ∀ (n : Nat) -> (v : Squashₙ (suc n) A) -> isContr ⟨ Ωⁿ n (Squashₙ (suc n) A , v) ⟩
    contr-squash-loops n v = subst isContr (cong fst (sym pT)) isContr-T₂
      where
      T₁ : Type∙ ℓ
      T₁ = Ωⁿ n (Squashₙ (suc n) A , v)
      T₂ : Type∙ ℓ
      T₂ = Sⁿ∙ n ->∙∙ (Squashₙ (suc n) A , v)
      pT : T₁ == T₂
      pT = n-loops==spheres n _

      isContr-T₂ : isContr ⟨ T₂ ⟩
      isContr-T₂ = (->∙-cons (\_ -> v) refl) , paths
        where
        paths : (f : (Sⁿ∙ n ->∙ (Squashₙ (suc n) A , v))) -> (->∙-cons (\_ -> v) refl) == f
        paths (->∙-cons f p) = \i -> ->∙-cons (f' (~ i)) (p' (~ i))
          where
          f' : Path (Sⁿ n -> Squashₙ (suc n) A) f (\_ -> v)
          f' = funExt (\s -> (sym (spoke f s) >=> spoke f north) >=> p)

          p' : PathP (\i -> f' i north == v) p refl
          p' = compPaths->Square _ _ _ _
            (compPath-refl-right p >=>
             sym (compPath-refl-left p) >=>
             cong (_>=> p) (sym (compPath-sym _)) >=>
             sym (compPath-refl-right _))


  isOfHLevel-Squashₙ : (n : Nat) -> isOfHLevel n (Squashₙ n A)
  isOfHLevel-Squashₙ zero = isContr-Lift isContrTop
  isOfHLevel-Squashₙ (suc n) = contr-loops->hlevel n step1
    where
    step1 : (v : Squashₙ (suc n) A) -> isContr ⟨ Ωⁿ n (Squashₙ (suc n) A , v) ⟩
    step1 = contr-squash-loops n

module _ {ℓ : Level} {A : Type ℓ} where
  contr-spheres : {n : Nat} -> isOfHLevel (suc n) A ->
                  (a : A) -> isContr (Sⁿ∙ n ->∙ (A , a))
  contr-spheres {n} h a =
    subst isContr (cong fst (n-loops==spheres n (A , a))) contr-loops
    where
    contr-loops : isContr ⟨ Ωⁿ n (A , a) ⟩
    contr-loops = hlevel->contr-loops _ h a


module _ {ℓA : Level} {A : Type ℓA} {n : Nat} where
  fill-sphere :
    (h : isOfHLevel (suc n) A)
    (s : (Sⁿ n -> A)) -> Σ[ a ∈ A ] (∀ i -> s i == a)
  fill-sphere h s =
    _ , (\i j -> app∙ (isContr->isProp contr-sphere s₂ s₃ j) i)
    where
    contr-sphere : isContr (Sⁿ∙ n ->∙ (A , s north))
    contr-sphere = contr-spheres h (s north)

    s₂ : (Sⁿ∙ n ->∙ (A , s north))
    s₂ = ->∙-cons s refl
    s₃ : (Sⁿ∙ n ->∙ (A , s north))
    s₃ = ->∙-cons (\_ -> app∙ (fst contr-sphere) north) (->∙-path (fst contr-sphere))


module _
  {ℓA ℓP : Level} {A : Type ℓA}
  {n : Nat} {P : Squashₙ (suc n) A -> Type ℓP}
  (h : ∀ a -> isOfHLevel (suc n) (P a)) (f : ∀ a -> P ∣ a ∣)
  where

  ∥ₙ-elim : ∀ a -> P a
  private
    module shared (w : Sⁿ n -> Squashₙ (suc n) A) where
      w' : (i : Sⁿ n) -> P (w i)
      w' i = ∥ₙ-elim (w i)

      t : (i : Sⁿ n) -> P (hub w)
      t i = transport (\j -> P (spoke w i (~ j))) (∥ₙ-elim (w i))

      filled-sphere : Σ[ p ∈ P (hub w) ] (∀ i -> t i == p)
      filled-sphere = fill-sphere (h (hub w)) t

  ∥ₙ-elim ∣ a ∣ = f a
  ∥ₙ-elim (hub w) = fst filled-sphere
    where
    open shared w
  ∥ₙ-elim (spoke w s i) = transP-right hub' spoke' i
    where
    open shared w
    u : P (hub w)
    u = fst filled-sphere

    spoke' : PathP (\i -> P (spoke w s i)) (t s) (w' s)
    spoke' = symP (transport-filler _ _)

    hub' : Path (P (hub w)) u (t s)
    hub' = sym (snd filled-sphere s)

  private
    ∥ₙ-elim-path : ∀ a -> ∥ₙ-elim ∣ a ∣ == f a
    ∥ₙ-elim-path a = refl


module _
  {ℓA ℓB ℓP : Level} {A : Type ℓA} {B : Type ℓB}
  {n : Nat} {P : Squashₙ (suc n) A -> Squashₙ (suc n) B -> Type ℓP}
  (h : ∀ a b -> isOfHLevel (suc n) (P a b)) (f : ∀ a b -> P ∣ a ∣ ∣ b ∣)
  where

  ∥ₙ-elim2 : ∀ a b -> P a b
  ∥ₙ-elim2 = ∥ₙ-elim (\a -> isOfHLevelΠ (suc n) (\b -> h a b)) f'
    where
    f' : ∀ a b -> P ∣ a ∣ b
    f' a = ∥ₙ-elim (h ∣ a ∣) (f a)
