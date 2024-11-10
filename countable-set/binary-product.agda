{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module countable-set.binary-product where

open import additive-group
open import additive-group.instances.nat
open import base
open import countable-set
open import equality
open import equivalence.base
open import equivalence
open import isomorphism
open import fin
open import functions
open import hlevel
open import nat
open import nat.order
open import order
open import order.instances.nat
open import ordered-semiring
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import ordered-semiring.instances.nat
open import ordered-semiring.squares
open import semiring
open import sequence
open import semiring.instances.nat
open import sigma.base
open import sigma
open import relation
open import truncation

private
  -- data UpperTri : Nat -> Nat -> Type₀ where
  --   upper-tri-base : UpperTri zero zero
  --   upper-tri-shift : {x y : ℕ} -> UpperTri (suc x) y -> UpperTri x (suc y)
  --   upper-tri-reset : {x : ℕ} -> UpperTri zero x -> UpperTri (suc x) zero

  -- ΣUpperTri : Type₀
  -- ΣUpperTri = Σ[ x ∈ ℕ ] Σ[ y ∈ ℕ ] (UpperTri x y)

  -- isProp-UpperTri : (x y : ℕ) -> isProp (UpperTri x y)
  -- isProp-UpperTri x    (suc y) (upper-tri-shift t1) (upper-tri-shift t2) =
  --   cong upper-tri-shift (isProp-UpperTri (suc x) y t1 t2)
  -- isProp-UpperTri zero    zero    upper-tri-base upper-tri-base = refl
  -- isProp-UpperTri (suc x) zero (upper-tri-reset t1) (upper-tri-reset t2) =
  --   cong upper-tri-reset (isProp-UpperTri zero x t1 t2)

  -- isContr-UpperTri : (x y : ℕ) -> isContr (UpperTri x y)
  -- isContr-UpperTri x y = val , isProp-UpperTri x y val
  --   where
  --   rec : (x y b : ℕ) -> (x + y) ≤ b -> UpperTri x y
  --   rec x       (suc y) b       lt =
  --     upper-tri-shift (rec (suc x) y b (trans-=-≤ (sym +'-right-suc) lt))
  --   rec zero    zero    b       _  =
  --     upper-tri-base
  --   rec (suc x) zero    (suc b) lt  =
  --     upper-tri-reset (rec zero x b (trans-=-≤ (sym +-right-zero) (pred-≤ lt)))
  --   rec (suc x) zero    zero lt  = bot-elim (zero-≮ lt)

  --   val = rec x y (x + y) refl-≤

  -- UpperTri->ℕ : {x y : ℕ} -> (UpperTri x y) -> ℕ
  -- UpperTri->ℕ upper-tri-base = 0
  -- UpperTri->ℕ (upper-tri-shift t) = suc (UpperTri->ℕ t)
  -- UpperTri->ℕ (upper-tri-reset t) = suc (UpperTri->ℕ t)

  -- ℕ->ΣUpperTri : {x y : ℕ} -> (UpperTri x y) -> ℕ
  -- ℕ->ΣUpperTri zero = upper-tri-base = 0
  -- ℕ->ΣUpperTri (upper-tri-shift t) = suc (UpperTri->ℕ t)
  -- ℕ->ΣUpperTri (upper-tri-reset t) = suc (UpperTri->ℕ t)

  data UpperSquare : Type₀ where
    full-square : (n : ℕ) -> UpperSquare
    square-bottom : (n : ℕ) -> Fin n -> UpperSquare
    square-side : (n : ℕ) -> Fin n -> UpperSquare

  data UpperSquare' (n : Nat) : Type₀ where
    full-square : UpperSquare' n
    square-bottom : Fin n -> UpperSquare' n
    square-side : Fin n -> UpperSquare' n

  UpperSquare2 : Type₀
  UpperSquare2 = Σ ℕ UpperSquare'

  UpperSquare->ℕ : UpperSquare -> ℕ
  UpperSquare->ℕ (full-square n) = n * n
  UpperSquare->ℕ (square-bottom n (i , _)) = (suc i) + n * n
  UpperSquare->ℕ (square-side n (i , _)) = (suc i + n) + n * n

  UpperSquare2->ℕ : UpperSquare2 -> ℕ
  UpperSquare2->ℕ (n , full-square) = n * n
  UpperSquare2->ℕ (n , square-bottom (i , _)) = (suc i) + n * n
  UpperSquare2->ℕ (n , square-side (i , _)) = (suc i + n) + n * n


  UpperSquare-n : UpperSquare -> ℕ
  UpperSquare-n (full-square n) = n
  UpperSquare-n (square-bottom n _) = n
  UpperSquare-n (square-side n _) = n

  isInjective-square : isInjective (\(n : ℕ) -> n * n)
  isInjective-square {n} {m} p =
    antisym-≤ (squares-ordered-≤ zero-≤ (path-≤ p))
              (squares-ordered-≤ zero-≤ (path-≤ (sym p)))


  UpperSquare2->ℕ-sqrt≤ : (u : UpperSquare2) -> (fst u * fst u) ≤ (UpperSquare2->ℕ u)
  UpperSquare2->ℕ-sqrt≤ (n , full-square) = refl-≤
  UpperSquare2->ℕ-sqrt≤ (n , square-bottom i) = +₂-preserves-≤ zero-≤
  UpperSquare2->ℕ-sqrt≤ (n , square-side i) = +₂-preserves-≤ zero-≤

  UpperSquare2->ℕ-sqrt< : (u : UpperSquare2) -> (UpperSquare2->ℕ u) < (suc (fst u) * suc (fst u))
  UpperSquare2->ℕ-sqrt< (n , full-square) =
    squares-ordered⁺ (zero-≮ {n}) refl-≤
  UpperSquare2->ℕ-sqrt< (n , square-bottom (i , si≤n)) =
    trans-≤-< (+₂-preserves-≤ si≤n) (*₁-preserves-< (zero-< {n}) refl-≤)
  UpperSquare2->ℕ-sqrt< (n , square-side (i , si≤n)) =
    trans-≤-< (trans-≤-= (trans-=-≤ (+-assocᵉ (suc i) n (n * n)) (+₂-preserves-≤ si≤n))
                         (cong (n +_) (*-commuteᵉ (suc n) n)))
              refl-≤



  ∃!floor-sqrt : (n : Nat) -> ∃![ m ∈ ℕ ] ((m * m) ≤ n × n < (suc m * suc m))
  ∃!floor-sqrt n = val , isProp-Σm val
    where
    count-down : (m : ℕ) -> n < (suc m * suc m) -> Σ[ m ∈ ℕ ] ((m * m) ≤ n × n < (suc m * suc m))
    count-down zero n<sm² = zero , (zero-≤ , n<sm²)
    count-down m@(suc m') n<sm² = handle (split-< n (m * m))
      where
      handle : n < (m * m) ⊎ (m * m) ≤ n -> Σ[ m ∈ ℕ ] ((m * m) ≤ n × n < (suc m * suc m))
      handle (inj-l n<m²) = count-down m' n<m²
      handle (inj-r m²≤n) = m , (m²≤n , n<sm²)

    initial-bound : n < (suc n * suc n)
    initial-bound =
      trans-=-≤
       (sym *-left-one)
       (trans-≤-< (*₂-preserves-≤ (suc-≤ (zero-≤ {n})) zero-≤)
                  (*₁-preserves-< (zero-< {n}) refl-≤))

    val : Σ[ m ∈ ℕ ] ((m * m) ≤ n × n < (suc m * suc m))
    val = count-down n initial-bound

    isProp-Σm : isProp (Σ[ m ∈ ℕ ] ((m * m) ≤ n × n < (suc m * suc m)))
    isProp-Σm (m1 , m1²≤n , n<sm1²) (m2 , m2²≤n , n<sm2²) =
      ΣProp-path (isProp× isProp-≤ isProp-<) (antisym-≤ m1≤m2 m2≤m1)
      where
      m1≤m2 : m1 ≤ m2
      m1≤m2 = pred-≤ (squares-ordered-< zero-≮ (trans-≤-< m1²≤n n<sm2²))
      m2≤m1 : m2 ≤ m1
      m2≤m1 = pred-≤ (squares-ordered-< zero-≮ (trans-≤-< m2²≤n n<sm1²))

  UpperSquare2->ℕ-same-n : (u1 u2 : UpperSquare2) -> UpperSquare2->ℕ u1 == UpperSquare2->ℕ u2 ->
                           fst u1 == fst u2
  UpperSquare2->ℕ-same-n u1 u2 p = sym check2 >=> check >=> check3
    where
    check : (∃!-val (∃!floor-sqrt (UpperSquare2->ℕ u1))) ==
            (∃!-val (∃!floor-sqrt (UpperSquare2->ℕ u2)))
    check i = ∃!-val (∃!floor-sqrt (p i))

    check2 : ∃!-val (∃!floor-sqrt (UpperSquare2->ℕ u1)) == fst u1
    check2 = ∃!-unique (∃!floor-sqrt (UpperSquare2->ℕ u1)) (fst u1)
               (UpperSquare2->ℕ-sqrt≤ u1 , UpperSquare2->ℕ-sqrt< u1)
    check3 : ∃!-val (∃!floor-sqrt (UpperSquare2->ℕ u2)) == fst u2
    check3 = ∃!-unique (∃!floor-sqrt (UpperSquare2->ℕ u2)) (fst u2)
               (UpperSquare2->ℕ-sqrt≤ u2 , UpperSquare2->ℕ-sqrt< u2)



  ℕ->UpperSquare : (n : ℕ) -> fiber UpperSquare->ℕ n
  ℕ->UpperSquare n = handle (split-< i 1)
    where
    ∃!m = ∃!floor-sqrt n
    m = ∃!-val ∃!m
    i : ℕ
    i = (fst (proj₁ (snd (fst ∃!m))))
    i<1mm : i < (1 + m + m)
    i<1mm = +₂-reflects-< (trans-=-< (snd (proj₁ (∃!-prop ∃!m))) (trans-<-= (proj₂ (∃!-prop ∃!m)) path))
      where
      path : (suc m) * (suc m) == (1 + m + m) + (m * m)
      path =
        +-right (*-commuteᵉ m (suc m)) >=>
        sym (+-assocᵉ (1 + m) m (m * m))

    handle : (i < 1) ⊎ (1 ≤ i) -> fiber UpperSquare->ℕ n
    handle (inj-l i<1) = full-square m , (cong (_+ (m * m)) (sym i=0)) >=> (snd (proj₁ (∃!-prop ∃!m)))
      where
      i=0 : i == 0
      i=0 = antisym-≤ (pred-≤ i<1) zero-≤
    handle (inj-r (j , j+1=i)) = handle2 (split-< j m)
      where
      handle2 : (j < m) ⊎ (m ≤ j) -> fiber UpperSquare->ℕ n
      handle2 (inj-l j<m) =
        square-bottom m (j , j<m) ,
        (cong (_+ (m * m)) (+-commuteᵉ 1 j >=> j+1=i)) >=>
        (snd (proj₁ (∃!-prop ∃!m)))
      handle2 (inj-r (k , k+m=j)) =
        square-side m (k , k<m) ,
        (cong (_+ (m * m)) (cong suc k+m=j >=> +-commuteᵉ 1 j >=> j+1=i)) >=>
        (snd (proj₁ (∃!-prop ∃!m)))
        where
        k<m : k < m
        k<m = +₂-reflects-< (trans-=-< k+m=j (+₂-reflects-< (trans-=-< j+1=i (trans-<-= i<1mm 1mm=mm1))))
          where
          1mm=mm1 : (1 + m + m) == (m + m + 1)
          1mm=mm1 = +-commuteᵉ (1 + m) m >=> +-right (+-commuteᵉ 1 m) >=> sym (+-assocᵉ m m 1)

  isInjective-UpperSquare'->ℕ : {n : Nat} -> isInjective (\s -> UpperSquare2->ℕ (n , s))
  isInjective-UpperSquare'->ℕ {n} {full-square} {full-square} _ = refl
  isInjective-UpperSquare'->ℕ {n} {square-bottom i} {square-bottom j} p =
    cong square-bottom (fin-i-path (cong pred (+'-right-injective {n * n} p)))
  isInjective-UpperSquare'->ℕ {n} {square-side _} {square-side _} p =
    cong square-side (fin-i-path (cong pred (+'-right-injective {n} (+'-right-injective {n * n} p))))
  isInjective-UpperSquare'->ℕ {n} {square-bottom i} {full-square} p =
    zero-suc-absurd (sym (+'-right-injective {n * n} p))
  isInjective-UpperSquare'->ℕ {n} {full-square} {square-bottom j} p =
    sym (isInjective-UpperSquare'->ℕ (sym p))
  isInjective-UpperSquare'->ℕ {n} {square-side i} {full-square} p =
    zero-suc-absurd (sym (+'-right-injective {n * n} p))
  isInjective-UpperSquare'->ℕ {n} {full-square} {square-side j} p =
    sym (isInjective-UpperSquare'->ℕ (sym p))
  isInjective-UpperSquare'->ℕ {n} {square-bottom i} {square-side j} p =
    bot-elim (convert-≤ n≤i (Fin.i<n i))
    where
    n≤i : n ≤ Fin.i i
    n≤i = Fin.i j , sym (cong pred (+'-right-injective {n * n} p))
  isInjective-UpperSquare'->ℕ {n} {square-side i} {square-bottom j} p =
    sym (isInjective-UpperSquare'->ℕ (sym p))


  isInjective-UpperSquare2->ℕ : isInjective UpperSquare2->ℕ
  isInjective-UpperSquare2->ℕ {n1 , s1} {n2 , s2} p = ns1=nt1 >=> (\i -> n2 , t1=s2 i)
    where
    n1=n2 : n1 == n2
    n1=n2 = UpperSquare2->ℕ-same-n (n1 , s1) (n2 , s2) p

    t1 : UpperSquare' n2
    t1 = substᵉ UpperSquare' n1=n2 s1

    ns1=nt1 : Path UpperSquare2 (n1 , s1) (n2 , t1)
    ns1=nt1 i = n1=n2 i , subst-filler UpperSquare' n1=n2 s1 i

    t1=s2 : t1 == s2
    t1=s2 = isInjective-UpperSquare'->ℕ (cong UpperSquare2->ℕ (sym ns1=nt1) >=> p)


  isProp-fiber-ℕ->UpperSquare2 : (n : ℕ) -> isProp (fiber UpperSquare2->ℕ n)
  isProp-fiber-ℕ->UpperSquare2 n (s1 , p1) (s2 , p2) =
    ΣProp-path (isSetNat _ _) (isInjective-UpperSquare2->ℕ (p1 >=> sym p2))

  ℕ->UpperSquare2 : (n : ℕ) -> fiber UpperSquare2->ℕ n
  ℕ->UpperSquare2 n = case (handle (split-< i 1)) of (\ (s , p) -> (m , s) , p)
    where
    ∃!m = ∃!floor-sqrt n
    m = ∃!-val ∃!m
    i : ℕ
    i = (fst (proj₁ (snd (fst ∃!m))))
    i<1mm : i < (1 + m + m)
    i<1mm = +₂-reflects-< (trans-=-< (snd (proj₁ (∃!-prop ∃!m))) (trans-<-= (proj₂ (∃!-prop ∃!m)) path))
      where
      path : (suc m) * (suc m) == (1 + m + m) + (m * m)
      path =
        +-right (*-commuteᵉ m (suc m)) >=>
        sym (+-assocᵉ (1 + m) m (m * m))

    handle : (i < 1) ⊎ (1 ≤ i) -> (Σ[ s ∈ UpperSquare' m ] (UpperSquare2->ℕ (m , s) == n))
    handle (inj-l i<1) = full-square , (cong (_+ (m * m)) (sym i=0)) >=> (snd (proj₁ (∃!-prop ∃!m)))
      where
      i=0 : i == 0
      i=0 = antisym-≤ (pred-≤ i<1) zero-≤
    handle (inj-r (j , j+1=i)) = handle2 (split-< j m)
      where
      handle2 : (j < m) ⊎ (m ≤ j) -> (Σ[ s ∈ UpperSquare' m ] (UpperSquare2->ℕ (m , s) == n))
      handle2 (inj-l j<m) =
        square-bottom (j , j<m) ,
        (cong (_+ (m * m)) (+-commuteᵉ 1 j >=> j+1=i)) >=>
        (snd (proj₁ (∃!-prop ∃!m)))
      handle2 (inj-r (k , k+m=j)) =
        square-side (k , k<m) ,
        (cong (_+ (m * m)) (cong suc k+m=j >=> +-commuteᵉ 1 j >=> j+1=i)) >=>
        (snd (proj₁ (∃!-prop ∃!m)))
        where
        k<m : k < m
        k<m = +₂-reflects-< (trans-=-< k+m=j (+₂-reflects-< (trans-=-< j+1=i (trans-<-= i<1mm 1mm=mm1))))
          where
          1mm=mm1 : (1 + m + m) == (m + m + 1)
          1mm=mm1 = +-commuteᵉ (1 + m) m >=> +-right (+-commuteᵉ 1 m) >=> sym (+-assocᵉ m m 1)

  US≃ℕ : UpperSquare2 ≃ ℕ
  US≃ℕ = UpperSquare2->ℕ ,
         record { equiv-proof = \ n -> ℕ->UpperSquare2 n , isProp-fiber-ℕ->UpperSquare2 n _ }

  ∀LargeUS' : {ℓ : Level} (P : ℕ -> Type ℓ) -> Type ℓ
  ∀LargeUS' P = ∀Largeℕ' (\n -> ∀ (us : UpperSquare' n) -> P (UpperSquare2->ℕ (n , us)))

  ∀LargeUS : {ℓ : Level} (P : ℕ -> Type ℓ) -> Type ℓ
  ∀LargeUS P = ∥ ∀LargeUS' P ∥

  ∀LargeUS≃∀Largeℕ : {ℓ : Level} (P : ℕ -> Type ℓ) -> ∀LargeUS P ≃ ∀Largeℕ P
  ∀LargeUS≃∀Largeℕ P = isoToEquiv (isProp->iso (∥-map forward) (∥-map backward) squash squash)
    where
    forward : ∀LargeUS' P -> ∀Largeℕ' P
    forward (n , f) = n * n , g
      where
      g : (m : ℕ) -> (n * n) ≤ m -> P m
      g m n*n≤m = subst P (eqSec US≃ℕ m) (f (fst us) ans (snd us))
        where
        us : UpperSquare2
        us = eqInv US≃ℕ m
        check : fst us == ∃!-val (∃!floor-sqrt m)
        check = refl
        check2 : (fst us * fst us) ≤ m
        check2 = proj₁ (∃!-prop (∃!floor-sqrt m))
        check3 : m < (suc (fst us) * suc (fst us))
        check3 = proj₂ (∃!-prop (∃!floor-sqrt m))
        check4 : (n * n) < (suc (fst us) * suc (fst us))
        check4 = trans-≤-< n*n≤m check3
        check5 : n < suc (fst us)
        check5 = squares-ordered-< zero-≮ check4
        ans : n ≤ fst us
        ans = pred-≤ check5

    backward : ∀Largeℕ' P -> ∀LargeUS' P
    backward (n , f) = (n , g)
      where
      m≤m² : (m : ℕ) -> m ≤ (m * m)
      m≤m² zero = refl-≤
      m≤m² (suc m) = (trans-=-≤ (sym *-left-one) (*₂-preserves-≤ (suc-≤ (zero-≤ {m})) zero-≤))

      g : (m : ℕ) -> (n ≤ m) -> (s : UpperSquare' m) -> P (UpperSquare2->ℕ (m , s))
      g m n≤m (full-square) = f _ (trans-≤ n≤m (m≤m² m))
      g m n≤m (square-side _) =
        f _ (trans-≤ n≤m (trans-≤ (m≤m² m) (trans-=-≤ (sym +-left-zero) (+₂-preserves-≤ zero-≤))))
      g m n≤m (square-bottom _) =
        f _ (trans-≤ n≤m (trans-≤ (m≤m² m) (trans-=-≤ (sym +-left-zero) (+₂-preserves-≤ zero-≤))))

  UpperSquare2->ℕ×ℕ : UpperSquare2 -> ℕ × ℕ
  UpperSquare2->ℕ×ℕ (n , full-square) = n , n
  UpperSquare2->ℕ×ℕ (n , square-bottom (i , _)) = n , i
  UpperSquare2->ℕ×ℕ (n , square-side (i , _)) = i , n


  isInjective-UpperSquare'->ℕ×ℕ : {n : ℕ} -> isInjective (\s -> UpperSquare2->ℕ×ℕ (n , s))
  isInjective-UpperSquare'->ℕ×ℕ {n} {full-square} {full-square} p = refl
  isInjective-UpperSquare'->ℕ×ℕ {n} {square-bottom i1} {square-bottom i2} p =
    cong square-bottom (fin-i-path (cong proj₂ p))
  isInjective-UpperSquare'->ℕ×ℕ {n} {square-side i1} {square-side i2} p =
    cong square-side (fin-i-path (cong proj₁ p))
  isInjective-UpperSquare'->ℕ×ℕ {n} {full-square} {square-side (i , i<n)} p =
    bot-elim (irrefl-path-< (sym (cong proj₁ p)) i<n)
  isInjective-UpperSquare'->ℕ×ℕ {n} {square-bottom _} {square-side (i , i<n)} p =
    bot-elim (irrefl-path-< (sym (cong proj₁ p)) i<n)
  isInjective-UpperSquare'->ℕ×ℕ {n} {square-side (i , i<n)} {full-square} p =
    bot-elim (irrefl-path-< (cong proj₁ p) i<n)
  isInjective-UpperSquare'->ℕ×ℕ {n} {square-side (i , i<n)} {square-bottom _} p =
    bot-elim (irrefl-path-< (cong proj₁ p) i<n)
  isInjective-UpperSquare'->ℕ×ℕ {n} {square-bottom (i , i<n)} {full-square} p =
    bot-elim (irrefl-path-< (cong proj₂ p) i<n)
  isInjective-UpperSquare'->ℕ×ℕ {n} {full-square} {square-bottom (i , i<n)} p =
    bot-elim (irrefl-path-< (sym (cong proj₂ p)) i<n)


  isInjective-UpperSquare2->ℕ×ℕ-n-path : {n1 n2 : ℕ} ->
    {s1 : UpperSquare' n1} {s2 : UpperSquare' n2} ->
    UpperSquare2->ℕ×ℕ (n1 , s1) == UpperSquare2->ℕ×ℕ (n2 , s2) ->
    n1 == n2
  isInjective-UpperSquare2->ℕ×ℕ-n-path {n1} {n2} {full-square} {full-square} p =
    cong proj₁ p
  isInjective-UpperSquare2->ℕ×ℕ-n-path {n1} {n2} {square-side _} {square-side _} p =
    cong proj₂ p
  isInjective-UpperSquare2->ℕ×ℕ-n-path {n1} {n2} {square-bottom _} {square-bottom _} p =
    cong proj₁ p
  isInjective-UpperSquare2->ℕ×ℕ-n-path {n1} {n2} {full-square} {square-side _} p =
    cong proj₂ p
  isInjective-UpperSquare2->ℕ×ℕ-n-path {n1} {n2} {full-square} {square-bottom _} p =
    cong proj₁ p
  isInjective-UpperSquare2->ℕ×ℕ-n-path {n1} {n2} {square-side _} {full-square} p =
    cong proj₂ p
  isInjective-UpperSquare2->ℕ×ℕ-n-path {n1} {n2} {square-bottom _} {full-square} p =
    cong proj₁ p
  isInjective-UpperSquare2->ℕ×ℕ-n-path {n1} {n2}
    {square-bottom (i1 , i1<n1)} {square-side (i2 , i2<n2)} p =
    bot-elim (asym-< (trans-=-< (sym (cong proj₂ p)) i1<n1) (trans-=-< (cong proj₁ p) i2<n2))
  isInjective-UpperSquare2->ℕ×ℕ-n-path {n1} {n2}
    {square-side (i1 , i1<n1)} {square-bottom (i2 , i2<n2)} p =
    bot-elim (asym-< (trans-=-< (sym (cong proj₁ p)) i1<n1) (trans-=-< (cong proj₂ p) i2<n2))


  isInjective-UpperSquare2->ℕ×ℕ : isInjective (\s -> UpperSquare2->ℕ×ℕ s)
  isInjective-UpperSquare2->ℕ×ℕ {n1 , s1} {n2 , s2} p =
    ns1=nt1 >=> (\i -> n2 , t1=s2 i)
    where
    n1=n2 : n1 == n2
    n1=n2 = isInjective-UpperSquare2->ℕ×ℕ-n-path p

    t1 : UpperSquare' n2
    t1 = substᵉ UpperSquare' n1=n2 s1

    ns1=nt1 : Path UpperSquare2 (n1 , s1) (n2 , t1)
    ns1=nt1 i = n1=n2 i , subst-filler UpperSquare' n1=n2 s1 i

    t1=s2 : t1 == s2
    t1=s2 = isInjective-UpperSquare'->ℕ×ℕ (cong UpperSquare2->ℕ×ℕ (sym ns1=nt1) >=> p)

  isProp-fiber-ℕ×ℕ->UpperSquare2 : (p : ℕ × ℕ) -> isProp (fiber UpperSquare2->ℕ×ℕ p)
  isProp-fiber-ℕ×ℕ->UpperSquare2 p (s1 , p1) (s2 , p2) =
    ΣProp-path (isSet× isSetNat isSetNat _ _) (isInjective-UpperSquare2->ℕ×ℕ (p1 >=> sym p2))


  ℕ×ℕ->UpperSquare2 : (p : ℕ × ℕ) -> fiber UpperSquare2->ℕ×ℕ p
  ℕ×ℕ->UpperSquare2 (n1 , n2) = handle (trichotomous-< n1 n2)
    where
    handle : Tri< n1 n2 -> fiber UpperSquare2->ℕ×ℕ (n1 , n2)
    handle (tri< n1<n2 _ _) = (n2 , square-side (n1 , n1<n2)) , refl
    handle (tri> _ _ n2<n1) = (n1 , square-bottom (n2 , n2<n1)) , refl
    handle (tri= _ n1=n2 _) = (n1 , full-square) , (\i -> n1 , n1=n2 i)


  US≃ℕ×ℕ : UpperSquare2 ≃ (ℕ × ℕ)
  US≃ℕ×ℕ = UpperSquare2->ℕ×ℕ ,
           record { equiv-proof = \ p -> ℕ×ℕ->UpperSquare2 p , isProp-fiber-ℕ×ℕ->UpperSquare2 p _ }

  ℕ≃ℕ×ℕ : ℕ ≃ (ℕ × ℕ)
  ℕ≃ℕ×ℕ = equiv⁻¹ US≃ℕ >eq> US≃ℕ×ℕ



  -- Injective-UpperSquare2->ℕ×ℕ : Injective (\s -> UpperSquare2->ℕ×ℕ s)
  -- Injective-UpperSquare2->ℕ×ℕ {n1 , full-square} {n2 , full-square} p i =
  --   proj₁ (p i) , full-square
  -- Injective-UpperSquare2->ℕ×ℕ {n1 , square-bottom i1} {n2 , square-bottom i2} p =
  --   \i -> p1 i , square-bottom (p2 i , p3 i)
  --   where
  --   p1 : n1 == n2
  --   p1 i = (proj₁ (p i))
  --   p2 : (Fin.i i1) == (Fin.i i2)
  --   p2 i = (proj₂ (p i))
  --   p3 : PathP (\i -> p2 i < p1 i) (Fin.i<n i1) (Fin.i<n i2)
  --   p3 = isProp->PathP (\_ -> isProp-<)
  -- Injective-UpperSquare2->ℕ×ℕ {n1 , square-side i1} {n2 , square-side i2} p =
  --   \i -> p1 i , square-side (p2 i , p3 i)
  --   where
  --   p1 : n1 == n2
  --   p1 i = (proj₂ (p i))
  --   p2 : (Fin.i i1) == (Fin.i i2)
  --   p2 i = (proj₁ (p i))
  --   p3 : PathP (\i -> p2 i < p1 i) (Fin.i<n i1) (Fin.i<n i2)
  --   p3 = isProp->PathP (\_ -> isProp-<)



  -- Injective-UpperSquare'->ℕ×ℕ {n} {square-side _} {square-side _} p =
  --   cong square-side (fin-i-path (cong pred (+'-right-injective {n} (+'-right-injective {n * n} p))))
  -- Injective-UpperSquare'->ℕ×ℕ {n} {square-bottom i} {full-square} p =
  --   zero-suc-absurd (sym (+'-right-injective {n * n} p))
  -- Injective-UpperSquare'->ℕ×ℕ {n} {full-square} {square-bottom j} p =
  --   sym (Injective-UpperSquare'->ℕ (sym p))
  -- Injective-UpperSquare'->ℕ×ℕ {n} {square-side i} {full-square} p =
  --   zero-suc-absurd (sym (+'-right-injective {n * n} p))
  -- Injective-UpperSquare'->ℕ×ℕ {n} {full-square} {square-side j} p =
  --   sym (Injective-UpperSquare'->ℕ (sym p))
  -- Injective-UpperSquare'->ℕ×ℕ {n} {square-bottom i} {square-side j} p =
  --   bot-elim (convert-≤ n≤i (Fin.i<n i))
  --   where
  --   n≤i : n ≤ Fin.i i
  --   n≤i = Fin.i j , sym (cong pred (+'-right-injective {n * n} p))
  -- Injective-UpperSquare'->ℕ×ℕ {n} {square-side i} {square-bottom j} p =
  --   sym (Injective-UpperSquare'->ℕ (sym p))



-- private
--   isCountableSet'-ℕ×ℕ : isCountableSet' (ℕ × ℕ)
--   isCountableSet'-ℕ×ℕ = ?


  --isCountableSet'-Σ : {ℓA ℓB : Level} {a
