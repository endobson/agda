{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module programming-languages.july2023.lambda-calc where

open import base
open import relation
open import equality
open import additive-group
open import additive-group.instances.nat
open import nat
open import nat.order
open import order
open import truncation
open import order.instances.nat

BoundVar : Type₀
BoundVar = Nat

data Term : Type₀ where
  bound-var : BoundVar -> Term
  lam : Term -> Term
  app : Term -> Term -> Term

data WellBoundTerm (n : Nat) : Pred Term ℓ-zero where
  bound-var : {v : BoundVar} -> v < n -> WellBoundTerm n (bound-var v)
  app : {t1 t2 : Term} -> WellBoundTerm n t1 -> WellBoundTerm n t2 ->
        WellBoundTerm n (app t1 t2)
  lam : {t : Term} -> WellBoundTerm (suc n) t -> WellBoundTerm n (lam t)

data LCIncBound (i : Nat) : Rel Term ℓ-zero where
  bound-var-< : {j : Nat} -> j < i -> LCIncBound i (bound-var j) (bound-var j)
  bound-var-≥ : {j : Nat} -> j ≥ i -> LCIncBound i (bound-var j) (bound-var (suc j))
  app : {l r l2 r2 : Term} -> LCIncBound i l l2 -> LCIncBound i r r2 ->
        LCIncBound i (app l r) (app l2 r2)
  lam : {b b2 : Term} -> LCIncBound (suc i) b b2 -> LCIncBound i (lam b) (lam b2)

∃!lc-inc-bound : (i : Nat) -> TotalFunctional (LCIncBound i)
∃!lc-inc-bound i (bound-var j) = handle (split-< j i)
  where
  handle : (j < i ⊎ i ≤ j) -> ∃! Term (LCIncBound i (bound-var j))
  handle (inj-l j<i) = (bound-var j , bound-var-< j<i) , unique
    where
    unique : (x : Σ Term (LCIncBound i (bound-var j))) -> (_ == x)
    unique (_ , bound-var-< j<i2) = cong wrap (isProp-< j<i j<i2)
      where
      wrap : j < i -> Σ Term (LCIncBound i (bound-var j))
      wrap lt = bound-var j , bound-var-< lt
    unique (_ , bound-var-≥ i≤j) = bot-elim (convert-≤ i≤j j<i)
  handle (inj-r i≤j) = (bound-var (suc j) , bound-var-≥ i≤j) , unique
    where
    unique : (x : Σ Term (LCIncBound i (bound-var j))) -> (_ == x)
    unique (_ , bound-var-< j<i) = bot-elim (convert-≤ i≤j j<i)
    unique (_ , bound-var-≥ i≤j2) = cong wrap (isProp-≤ i≤j i≤j2)
      where
      wrap : i ≤ j -> Σ Term (LCIncBound i (bound-var j))
      wrap le = bound-var (suc j) , bound-var-≥ le
∃!lc-inc-bound i (lam b) = ans , unique
  where
  rec : ∃! Term (LCIncBound (suc i) b)
  rec = ∃!lc-inc-bound (suc i) b
  wrap : Σ Term (LCIncBound (suc i) b) -> Σ Term (LCIncBound i (lam b))
  wrap (v , p) = lam v , lam p
  ans : Σ Term (LCIncBound i (lam b))
  ans = wrap (fst rec)
  unique : (x : Σ Term (LCIncBound i (lam b))) -> ans == x
  unique (lam b2 , lam s) = cong wrap (snd rec (b2 , s))
∃!lc-inc-bound i (app f a) = ans , unique
  where
  rec-f : ∃! Term (LCIncBound i f)
  rec-f = ∃!lc-inc-bound i f
  rec-a : ∃! Term (LCIncBound i a)
  rec-a = ∃!lc-inc-bound i a

  wrap : Σ Term (LCIncBound i f) -> Σ Term (LCIncBound i a) ->
         Σ Term (LCIncBound i (app f a))
  wrap (f , fp) (a , ap) = app f a , app fp ap
  ans : Σ Term (LCIncBound i (app f a))
  ans = wrap (fst rec-f) (fst rec-a)
  unique : (x : Σ Term (LCIncBound i (app f a))) -> ans == x
  unique (app f2 a2 , app fp2 ap2) =
    cong2 wrap (snd rec-f (f2 , fp2)) (snd rec-a (a2 , ap2))

lc-inc-bound : (i : Nat) -> Term -> Term
lc-inc-bound i t = ∃!-val (∃!lc-inc-bound i t)


data LCSubst (t : Term) (i : Nat) : Rel Term ℓ-zero where
  bound-var-< : {j : Nat} -> j < i -> LCSubst t i (bound-var j) (bound-var j)
  bound-var-= : {j : Nat} -> j == i -> LCSubst t i (bound-var j) t
  bound-var-> : {j : Nat} -> j > i -> LCSubst t i (bound-var j) (bound-var (pred j))
  app : {l r l2 r2 : Term} -> LCSubst t i l l2 -> LCSubst t i r r2 ->
        LCSubst t i (app l r) (app l2 r2)
  lam : {b b2 : Term} ->
        LCSubst (lc-inc-bound 0 t) (suc i) b b2 ->
        LCSubst t i (lam b) (lam b2)



lc-subst2 : (e : Term) -> (i : Nat) -> (t : Term) -> ∃! Term (LCSubst e i t)
lc-subst2 e i (bound-var j) = handle (trichotomous-< j i)
  where
  handle : Tri< j i -> ∃! Term (LCSubst e i (bound-var j))
  handle (tri< j<i ¬j=i ¬i<j) = (bound-var j , bound-var-< j<i) , unique
    where
    unique : (x : Σ Term (LCSubst e i (bound-var j))) -> _ == x
    unique (_ , bound-var-= j=i) = bot-elim (¬j=i j=i)
    unique (_ , bound-var-< lt) = cong wrap (isProp-< j<i lt)
      where
      wrap : j < i -> Σ Term (LCSubst e i (bound-var j))
      wrap lt = bound-var j , bound-var-< lt
    unique (_ , bound-var-> i<j) = bot-elim (¬i<j i<j)
  handle (tri= ¬j<i j=i ¬i<j) = (e , bound-var-= j=i) , unique
    where
    unique : (x : Σ Term (LCSubst e i (bound-var j))) -> _ == x
    unique (_ , bound-var-= j=i2) =
      cong (\p -> e , bound-var-= p) (isSetNat j i j=i j=i2)
    unique (_ , bound-var-< j<i) = bot-elim (¬j<i j<i)
    unique (_ , bound-var-> i<j) = bot-elim (¬i<j i<j)
  handle (tri> ¬j<i ¬j=i i<j) = (bound-var (pred j) , bound-var-> i<j) , unique
    where
    unique : (x : Σ Term (LCSubst e i (bound-var j))) -> _ == x
    unique (_ , bound-var-= j=i) = bot-elim (¬j=i j=i)
    unique (_ , bound-var-< j<i) = bot-elim (¬j<i j<i)
    unique (_ , bound-var-> gt) = cong wrap (isProp-< i<j gt)
      where
      wrap : i < j -> Σ Term (LCSubst e i (bound-var j))
      wrap gt = bound-var (pred j) , bound-var-> gt
lc-subst2 e i (lam b) = ans , unique
  where
  inc-e = lc-inc-bound 0 e
  rec : ∃! Term (LCSubst inc-e (suc i) b)
  rec = lc-subst2 inc-e (suc i) b
  wrap : Σ Term (LCSubst inc-e (suc i) b) -> Σ Term (LCSubst e i (lam b))
  wrap (v , p) = lam v , lam p
  ans : Σ Term (LCSubst e i (lam b))
  ans = wrap (fst rec)
  unique : (x : Σ Term (LCSubst e i (lam b))) -> ans == x
  unique (lam b2 , lam s) = cong wrap (snd rec (b2 , s))
lc-subst2 e i (app f a) = ans , unique
  where
  rec-f : ∃! Term (LCSubst e i f)
  rec-f = lc-subst2 e i f
  rec-a : ∃! Term (LCSubst e i a)
  rec-a = lc-subst2 e i a

  wrap : Σ Term (LCSubst e i f) -> Σ Term (LCSubst e i a) ->
         Σ Term (LCSubst e i (app f a))
  wrap (f , fp) (a , ap) = app f a , app fp ap
  ans : Σ Term (LCSubst e i (app f a))
  ans = wrap (fst rec-f) (fst rec-a)
  unique : (x : Σ Term (LCSubst e i (app f a))) -> ans == x
  unique (app f2 a2 , app fp2 ap2) =
    cong2 wrap (snd rec-f (f2 , fp2)) (snd rec-a (a2 , ap2))


-- ;; Replaces the specified variabe with the argument lc-subst e i t => t[e/i]
lc-subst : Term -> Nat -> Term -> Term
lc-subst e i t = ∃!-val (lc-subst2 e i t)


lc-subst-inc-bound : (a b c : Term) (i : Nat) ->
                     (LCIncBound i b c) -> (LCSubst a i c b)
lc-subst-inc-bound a (bound-var j) (bound-var j) i (bound-var-< j<i) =
  bound-var-< j<i
lc-subst-inc-bound a (bound-var j) (bound-var (suc j)) i (bound-var-≥ j≥i) =
  bound-var-> (suc-≤ j≥i)
lc-subst-inc-bound a (app lb rb) (app lc rc) i (app li ri) =
  let rec-l = lc-subst-inc-bound a lb lc i li in
  let rec-r = lc-subst-inc-bound a rb rc i ri in
  app rec-l rec-r
lc-subst-inc-bound a (lam b) (lam c) i (lam inc) =
  let rec = lc-subst-inc-bound (lc-inc-bound 0 a) b c (suc i) inc in
  lam rec

lc-subst-inc-bound* : (a b : Term) (i : Nat) -> (lc-subst a i (lc-inc-bound i b)) == b
lc-subst-inc-bound* a b i =
  ∃!-unique (lc-subst2 a i (lc-inc-bound i b)) _
            (lc-subst-inc-bound a b (lc-inc-bound i b) i (∃!-prop (∃!lc-inc-bound i b)))

_Rel∘_ : {ℓA ℓB ℓC ℓ1 ℓ2 : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} ->
       REL B C ℓ1 -> REL A B ℓ2 -> REL A C (ℓ-max* 3 ℓB ℓ1 ℓ2)
_Rel∘_ {B = B} R1 R2 a c = Σ[ b ∈ B ] (R1 b c × R2 a b)

_Rel⇒_ : {ℓA ℓB ℓR : Level} {A : Type ℓA} {B : Type ℓB} ->
       Rel (REL A B ℓR) _
_Rel⇒_ R1 R2 = ∀ a b -> R1 a b -> R2 a b


lc-inc-bound-twice : (j k : Nat) -> (k ≤ j) ->
  (LCIncBound (suc j) Rel∘ LCIncBound k) Rel⇒ (LCIncBound k Rel∘ LCIncBound j)
lc-inc-bound-twice j k k≤j a b (bound-var i , bound-var-< i<sj , bound-var-< i<k) =
  (bound-var i , bound-var-< i<k , bound-var-< (trans-<-≤ i<k k≤j))
lc-inc-bound-twice j k k≤j a b (bound-var (suc i) , bound-var-< si<sj , bound-var-≥ k≤i) =
  (bound-var i , bound-var-≥ k≤i , bound-var-< (pred-≤ si<sj))
lc-inc-bound-twice j k k≤j a b (bound-var i , bound-var-≥ sj≤i , bound-var-< i<k) =
  bot-elim (irrefl-< (trans-< sj≤i (trans-≤ i<k k≤j)))
lc-inc-bound-twice j k k≤j a b (bound-var (suc i) , bound-var-≥ sj≤si , bound-var-≥ k≤i) =
  bound-var (suc i) , bound-var-≥ (trans-≤ k≤i (weaken-< (add1-< i))) ,
                      bound-var-≥ (pred-≤ sj≤si)
lc-inc-bound-twice j k k≤j a b (_ , lam body1 , lam body2) =
  let (_ , rec-body1 , rec-body2) =
       lc-inc-bound-twice (suc j) (suc k) (suc-≤ k≤j) _ _ (_ , body1 , body2) in
  (_ , lam rec-body1 , lam rec-body2)
lc-inc-bound-twice j k k≤j a b (_ , app l1 r1 , app l2 r2) =
  let (_ , rec-l1 , rec-l2) = lc-inc-bound-twice j k k≤j _ _ (_ , l1 , l2) in
  let (_ , rec-r1 , rec-r2) = lc-inc-bound-twice j k k≤j _ _ (_ , r1 , r2) in
  (_ , app rec-l1 rec-r1 , app rec-l2 rec-r2)


lc-inc-bound-twice* : (a : Term) (j k : Nat) -> (k ≤ j) ->
  (lc-inc-bound (suc j) (lc-inc-bound k a)) ==
  (lc-inc-bound k (lc-inc-bound j a))
lc-inc-bound-twice* a j k k≤j = sym p2 >=> cong (lc-inc-bound k) (sym p1)
  where
  ka : ∃! Term (LCIncBound k a)
  ka = ∃!lc-inc-bound k a
  sjka : ∃! Term (LCIncBound (suc j) (∃!-val ka))
  sjka = ∃!lc-inc-bound (suc j) (∃!-val ka)

  res : (LCIncBound k Rel∘ LCIncBound j) a (∃!-val sjka)
  res = lc-inc-bound-twice j k k≤j _ _ (_ , ∃!-prop sjka , ∃!-prop ka)

  res-v = fst res
  p1 : (lc-inc-bound j a) == res-v
  p1 = ∃!-unique (∃!lc-inc-bound j a) _ (snd (snd res))
  p2 : (lc-inc-bound k res-v) == ∃!-val sjka
  p2 = ∃!-unique (∃!lc-inc-bound k res-v) _ (fst (snd res))


lc-inc-bound-subst-bv :
  (a : Term) (k i j : Nat) -> (j ≤ i) ->
  (t1 res : Term) ->
  LCSubst a i (bound-var k) t1 ->
  LCIncBound j t1 res ->
  Σ[ t2 ∈ Term ] Σ[ t3 ∈ Term ]
    (LCIncBound j (bound-var k) t2 ×
     LCIncBound j a t3 ×
     LCSubst t3 (suc i) t2 res)
lc-inc-bound-subst-bv a k i j j≤i t1 res
  (bound-var-= k=i) inc-t1 =
  (_ , _ , (bound-var-≥ (trans-≤-= j≤i (sym k=i))) , inc-t1 ,
           (bound-var-= (cong suc k=i)))
lc-inc-bound-subst-bv a k i j j≤i t1 res
  (bound-var-< k<i) (bound-var-< k<j) =
  (_ , _ , (bound-var-< k<j) , ∃!-prop (∃!lc-inc-bound j a) ,
           bound-var-< (trans-< k<i (add1-< i)))
lc-inc-bound-subst-bv a k i j j≤i t1 res
  (bound-var-< k<i) (bound-var-≥ k≥j) =
  (_ , _ , bound-var-≥ k≥j , ∃!-prop (∃!lc-inc-bound j a) ,
           bound-var-< (suc-< k<i))
lc-inc-bound-subst-bv a k i j j≤i t1 res
  (bound-var-> i<k) (bound-var-< pk<j) =
  bot-elim (convert-≤ j≤i i<j)
  where
  i<j : i < j
  i<j = trans-≤-< (pred-≤ i<k) pk<j
lc-inc-bound-subst-bv a zero i j j≤i t1 res
  (bound-var-> i<k) (bound-var-≥ j≤pk) = bot-elim (zero-≮ i<k)
lc-inc-bound-subst-bv a (suc _) i j j≤i t1 res
  (bound-var-> i<k) (bound-var-≥ j≤pk) =
  (_ , _ , bound-var-≥ (weaken-< (trans-≤-< j≤i i<k)) , ∃!-prop (∃!lc-inc-bound j a) ,
           (bound-var-> (suc-≤ i<k)))

lc-inc-bound-subst-bv-≤ : (a : Term) (k i j : Nat) -> (i ≤ j) ->
  (t1 res : Term) ->
  LCSubst a i (bound-var k) t1 ->
  LCIncBound j t1 res ->
  Σ[ t2 ∈ Term ] Σ[ t3 ∈ Term ]
    (LCIncBound (suc j) (bound-var k) t2 ×
     LCIncBound j a t3 ×
     LCSubst t3 i t2 res)
lc-inc-bound-subst-bv-≤ a k i j i≤j t1 res
  (bound-var-= k=i) inc-t1 =
  (_ , _ , (bound-var-< (suc-≤ (trans-=-≤ k=i i≤j))) , inc-t1 ,
           (bound-var-= k=i))
lc-inc-bound-subst-bv-≤ a k i j i≤j t1 res
  (bound-var-< k<i) (bound-var-< k<j) =
  (_ , _ , (bound-var-< (right-suc-≤ k<j)) , ∃!-prop (∃!lc-inc-bound j a),
           (bound-var-< k<i))
lc-inc-bound-subst-bv-≤ a k i j i≤j t1 res
  (bound-var-< k<i) (bound-var-≥ j≤k) =
  bot-elim (convert-≤ (trans-≤ i≤j j≤k) k<i)
lc-inc-bound-subst-bv-≤ a zero i j i≤j t1 res
  (bound-var-> i<k) _ =
  bot-elim (zero-≮ i<k)
lc-inc-bound-subst-bv-≤ a k@(suc _) i j i≤j t1 res
  (bound-var-> i<k) (bound-var-< pk<j) =
  (_ , _ , (bound-var-< (suc-< pk<j)) , ∃!-prop (∃!lc-inc-bound j a),
           (bound-var-> i<k))
lc-inc-bound-subst-bv-≤ a k@(suc _) i j i≤j t1 res
  (bound-var-> i<k) (bound-var-≥ j≤pk) =
  (_ , _ , (bound-var-≥ (suc-≤ j≤pk)) , ∃!-prop (∃!lc-inc-bound j a),
           (bound-var-> (right-suc-≤ i<k)))





lc-inc-bound-subst* : (a b : Term) (i j : Nat) -> (j ≤ i) ->
                      (lc-inc-bound j (lc-subst a i b)) ==
                      (lc-subst (lc-inc-bound j a) (suc i) (lc-inc-bound j b))
lc-inc-bound-subst* a b@(bound-var k) i j j≤i =
  sym p3 >=> \ii -> lc-subst (p2 (~ ii)) (suc i) (p1 (~ ii))
  where
  t1 = lc-subst2 a i b
  res = ∃!lc-inc-bound j (∃!-val t1)
  rec = lc-inc-bound-subst-bv a k i j j≤i _ _ (∃!-prop t1) (∃!-prop res)
  t2 = fst rec
  t3 = fst (snd rec)
  inc-jb-t2 = fst (snd (snd rec))
  inc-ja-t3 = fst (snd (snd (snd rec)))
  subst-t3-si-t2-res = snd (snd (snd (snd rec)))

  p1 : lc-inc-bound j b == t2
  p1 = ∃!-unique (∃!lc-inc-bound j b) _ inc-jb-t2
  p2 : lc-inc-bound j a == t3
  p2 = ∃!-unique (∃!lc-inc-bound j a) _ inc-ja-t3
  p3 : lc-subst t3 (suc i) t2 == ∃!-val res
  p3 = ∃!-unique (lc-subst2 t3 (suc i) t2) _ subst-t3-si-t2-res
lc-inc-bound-subst* a (lam b) i j j≤i = cong lam (rec >=> p2)
  where
  rec : (lc-inc-bound (suc j) (lc-subst (lc-inc-bound 0 a) (suc i) b)) ==
        (lc-subst (lc-inc-bound (suc j) (lc-inc-bound 0 a)) (suc (suc i)) (lc-inc-bound (suc j) b))
  rec = lc-inc-bound-subst* (lc-inc-bound 0 a) b (suc i) (suc j) (suc-≤ j≤i)

  p1 : (lc-inc-bound (suc j) (lc-inc-bound 0 a)) ==  (lc-inc-bound 0 (lc-inc-bound j a))
  p1 = lc-inc-bound-twice* a j 0 zero-≤

  p2 : (lc-subst (lc-inc-bound (suc j) (lc-inc-bound 0 a)) (suc (suc i)) (lc-inc-bound (suc j) b)) ==
       (lc-subst (lc-inc-bound 0 (lc-inc-bound j a)) (suc (suc i)) (lc-inc-bound (suc j) b))
  p2 ii = (lc-subst (p1 ii) (suc (suc i)) (lc-inc-bound (suc j) b))
lc-inc-bound-subst* a (app bl br) i j j≤i =
  cong2 app (lc-inc-bound-subst* a bl i j j≤i)
            (lc-inc-bound-subst* a br i j j≤i)


lc-inc-bound-subst-≤* : (a b : Term) (i j : Nat) -> (i ≤ j) ->
                        (lc-inc-bound j (lc-subst a i b)) ==
                        (lc-subst (lc-inc-bound j a) i (lc-inc-bound (suc j) b))
lc-inc-bound-subst-≤* a b@(bound-var k) i j i≤j =
  sym p3 >=> \ii -> lc-subst (p2 (~ ii)) i (p1 (~ ii))
  where
  t1 = lc-subst2 a i b
  res = ∃!lc-inc-bound j (∃!-val t1)
  rec = lc-inc-bound-subst-bv-≤ a k i j i≤j _ _ (∃!-prop t1) (∃!-prop res)
  t2 = fst rec
  t3 = fst (snd rec)
  inc-jb-t2 = fst (snd (snd rec))
  inc-ja-t3 = fst (snd (snd (snd rec)))
  subst-t3-si-t2-res = snd (snd (snd (snd rec)))

  p1 : lc-inc-bound (suc j) b == t2
  p1 = ∃!-unique (∃!lc-inc-bound (suc j) b) _ inc-jb-t2
  p2 : lc-inc-bound j a == t3
  p2 = ∃!-unique (∃!lc-inc-bound j a) _ inc-ja-t3
  p3 : lc-subst t3 i t2 == ∃!-val res
  p3 = ∃!-unique (lc-subst2 t3 i t2) _ subst-t3-si-t2-res
lc-inc-bound-subst-≤* a (lam b) i j j≤i = cong lam (rec >=> p2)
  where
  rec : (lc-inc-bound (suc j) (lc-subst (lc-inc-bound 0 a) (suc i) b)) ==
        (lc-subst (lc-inc-bound (suc j) (lc-inc-bound 0 a)) (suc i) (lc-inc-bound (suc (suc j)) b))
  rec = lc-inc-bound-subst-≤* (lc-inc-bound 0 a) b (suc i) (suc j) (suc-≤ j≤i)

  p1 : (lc-inc-bound (suc j) (lc-inc-bound 0 a)) ==  (lc-inc-bound 0 (lc-inc-bound j a))
  p1 = lc-inc-bound-twice* a j 0 zero-≤

  p2 : (lc-subst (lc-inc-bound (suc j) (lc-inc-bound 0 a)) (suc i) (lc-inc-bound (suc (suc j)) b)) ==
       (lc-subst (lc-inc-bound 0 (lc-inc-bound j a)) (suc i) (lc-inc-bound (suc (suc j)) b))
  p2 ii = (lc-subst (p1 ii) (suc i) (lc-inc-bound (suc (suc j)) b))

lc-inc-bound-subst-≤* a (app bl br) i j j≤i =
  cong2 app (lc-inc-bound-subst-≤* a bl i j j≤i)
            (lc-inc-bound-subst-≤* a br i j j≤i)






lc-subst-twice-bv : (a b : Term) (j i k : Nat) -> (k ≤ i) ->
                    (lc-subst a i (lc-subst b k (bound-var j))) ==
                    (lc-subst (lc-subst a i b) k (lc-subst (lc-inc-bound k a) (suc i) (bound-var j)))
lc-subst-twice-bv a b j i k k≤i = handle (trichotomous-< (suc i) j) (trichotomous-< j k)
  where
  c = bound-var j

  module _ (si<j : suc i < j) where
    private
      k<j : k < j
      k<j = trans-< (suc-≤ k≤i) si<j
      i<pj : i < pred j
      i<pj = pred-≤ si<j
      k<pj : k < pred j
      k<pj = trans-≤-< k≤i i<pj

      p1 : lc-subst b k c == bound-var (pred j)
      p1 = ∃!-unique (lc-subst2 b k c) (bound-var (pred j)) (bound-var-> k<j)
      p2 : lc-subst a i (bound-var (pred j)) == bound-var (pred (pred j))
      p2 = ∃!-unique (lc-subst2 a i (bound-var (pred j)))
                     (bound-var (pred (pred j))) (bound-var-> i<pj)
      simplify-left : lc-subst a i (lc-subst b k c) == bound-var (pred (pred j))
      simplify-left = cong (lc-subst a i) p1 >=> p2


      p3 : lc-subst (lc-inc-bound k a) (suc i) c == bound-var (pred j)
      p3 = ∃!-unique (lc-subst2 (lc-inc-bound k a) (suc i) c) (bound-var (pred j)) (bound-var-> si<j)
      p4 : lc-subst (lc-subst a i b) k (bound-var (pred j)) == bound-var (pred (pred j))
      p4 = ∃!-unique (lc-subst2 (lc-subst a i b) k (bound-var (pred j)))
                     (bound-var (pred (pred j))) (bound-var-> k<pj)
      simplify-right : lc-subst (lc-subst a i b) k (lc-subst (lc-inc-bound k a) (suc i) c) ==
                       bound-var (pred (pred j))
      simplify-right = cong (lc-subst (lc-subst a i b) k) p3 >=> p4

    si<j-case : lc-subst a i (lc-subst b k c) ==
                lc-subst (lc-subst a i b) k (lc-subst (lc-inc-bound k a) (suc i) c)
    si<j-case = simplify-left >=> sym simplify-right


  module _ (si=j : suc i == j) where
    private
      k<j : k < j
      k<j = trans-≤-< k≤i (path-≤ si=j)

      p1 : lc-subst b k c == bound-var (pred j)
      p1 = ∃!-unique (lc-subst2 b k c) (bound-var (pred j)) (bound-var-> k<j)
      pj=i : pred j == i
      pj=i = cong pred (sym si=j)
      p2 : lc-subst b k c == bound-var i
      p2 = p1 >=> cong bound-var pj=i
      p3 : lc-subst a i (bound-var i) == a
      p3 = ∃!-unique (lc-subst2 a i (bound-var i)) a (bound-var-= refl)
      p4 : lc-subst a i (lc-subst b k c) == a
      p4 = cong (lc-subst a i) p2 >=> p3


      p5 : lc-subst (lc-inc-bound k a) (suc i) c == (lc-inc-bound k a)
      p5 = ∃!-unique (lc-subst2 (lc-inc-bound k a) (suc i) c) (lc-inc-bound k a) (bound-var-= (sym si=j))
      p6 : lc-subst (lc-subst a i b) k (lc-inc-bound k a) == a
      p6 = lc-subst-inc-bound* _ a k
      p7 : lc-subst (lc-subst a i b) k (lc-subst (lc-inc-bound k a) (suc i) c) == a
      p7 = cong (lc-subst (lc-subst a i b) k) p5 >=> p6

    si=j-case : lc-subst a i (lc-subst b k c) ==
                lc-subst (lc-subst a i b) k (lc-subst (lc-inc-bound k a) (suc i) c)
    si=j-case = p4 >=> sym p7

  module _ (j<si : j < suc i) (k<j : k < j) where
    private
      pj<i : pred j < i
      pj<i = trans-<-≤ (same-pred-< (j , <->Pos' k<j)) (pred-≤ j<si)

      p1 : lc-subst b k c == bound-var (pred j)
      p1 = ∃!-unique (lc-subst2 b k c) (bound-var (pred j)) (bound-var-> k<j)
      p2 : lc-subst a i (bound-var (pred j)) == bound-var (pred j)
      p2 = ∃!-unique (lc-subst2 a i (bound-var (pred j)))
                     (bound-var (pred j)) (bound-var-< pj<i)
      simplify-left : lc-subst a i (lc-subst b k c) == bound-var (pred j)
      simplify-left = cong (lc-subst a i) p1 >=> p2


      p3 : lc-subst (lc-inc-bound k a) (suc i) c == bound-var j
      p3 = ∃!-unique (lc-subst2 (lc-inc-bound k a) (suc i) c) (bound-var j) (bound-var-< j<si)
      p4 : lc-subst (lc-subst a i b) k (bound-var j) == bound-var (pred j)
      p4 = ∃!-unique (lc-subst2 (lc-subst a i b) k (bound-var j))
                     (bound-var (pred j)) (bound-var-> k<j)
      simplify-right : lc-subst (lc-subst a i b) k (lc-subst (lc-inc-bound k a) (suc i) c) ==
                       bound-var (pred j)
      simplify-right = cong (lc-subst (lc-subst a i b) k) p3 >=> p4

    k<j<si-case : lc-subst a i (lc-subst b k c) ==
                  lc-subst (lc-subst a i b) k (lc-subst (lc-inc-bound k a) (suc i) c)
    k<j<si-case = simplify-left >=> sym simplify-right

  module _ (j=k : j == k) where
    private
      p1 : lc-subst b k c == b
      p1 = ∃!-unique (lc-subst2 b k c) b (bound-var-= j=k)
      simplify-left : lc-subst a i (lc-subst b k c) == lc-subst a i b
      simplify-left = cong (lc-subst a i) p1

      p2 : lc-subst (lc-inc-bound k a) (suc i) c == (bound-var j)
      p2 = ∃!-unique (lc-subst2 (lc-inc-bound k a) (suc i) c) (bound-var j)
                     (bound-var-< (trans-=-< j=k (suc-≤ k≤i)))
      p3 : lc-subst (lc-subst a i b) k (bound-var j) == (lc-subst a i b)
      p3 = ∃!-unique (lc-subst2 (lc-subst a i b) k (bound-var j)) (lc-subst a i b) (bound-var-= j=k)

      simplify-right : lc-subst (lc-subst a i b) k (lc-subst (lc-inc-bound k a) (suc i) c) ==
                       (lc-subst a i b)
      simplify-right = cong (lc-subst (lc-subst a i b) k) p2 >=> p3

    j=k-case : lc-subst a i (lc-subst b k c) ==
               lc-subst (lc-subst a i b) k (lc-subst (lc-inc-bound k a) (suc i) c)
    j=k-case = simplify-left >=> sym simplify-right

  module _ (j<k : j < k) where
    private
      j<i : j < i
      j<i = trans-<-≤ j<k k≤i

      p1 : lc-subst b k c == bound-var j
      p1 = ∃!-unique (lc-subst2 b k c) _ (bound-var-< j<k)
      p2 : lc-subst a i (bound-var j) == bound-var j
      p2 = ∃!-unique (lc-subst2 a i (bound-var j)) _ (bound-var-< j<i)
      simplify-left : lc-subst a i (lc-subst b k c) == bound-var j
      simplify-left = cong (lc-subst a i) p1 >=> p2

      p3 : lc-subst (lc-inc-bound k a) (suc i) c == (bound-var j)
      p3 = ∃!-unique (lc-subst2 (lc-inc-bound k a) (suc i) c) _
                     (bound-var-< (trans-< j<i (add1-< i)))
      p4 : lc-subst (lc-subst a i b) k (bound-var j) == (bound-var j)
      p4 = ∃!-unique (lc-subst2 (lc-subst a i b) k (bound-var j)) _
                     (bound-var-< j<k)
      simplify-right : lc-subst (lc-subst a i b) k (lc-subst (lc-inc-bound k a) (suc i) c) ==
                       (bound-var j)
      simplify-right = cong (lc-subst (lc-subst a i b) k) p3 >=> p4

    j<k-case : lc-subst a i (lc-subst b k c) ==
               lc-subst (lc-subst a i b) k (lc-subst (lc-inc-bound k a) (suc i) c)
    j<k-case = simplify-left >=> sym simplify-right


  handle : Tri< (suc i) j -> Tri< j k ->
           (lc-subst a i (lc-subst b k c)) ==
           (lc-subst (lc-subst a i b) k (lc-subst (lc-inc-bound k a) (suc i) c))
  handle (tri< si<j _ _) _ = si<j-case si<j
  handle (tri= _ si=j _) _ = si=j-case si=j
  handle (tri> _ _ si>j) (tri> _ _ j>k) = k<j<si-case si>j j>k
  handle (tri> _ _ _)    (tri= _ j=k _) = j=k-case j=k
  handle (tri> _ _ si>j) (tri< j<k _ _) = j<k-case j<k


module _ where
  lc-subst-twice : (a b c : Term) (i j : Nat) -> (j ≤ i) ->
                   (lc-subst a i (lc-subst b j c)) ==
                   (lc-subst (lc-subst a i b) j (lc-subst (lc-inc-bound j a) (suc i) c))
  lc-subst-twice a b c@(bound-var k) i j j≤i =
    lc-subst-twice-bv a b k i j j≤i
  lc-subst-twice a b (lam c) i j j≤i = ans
    where
    p1 : lc-subst b j (lam c) == (lam (lc-subst (lc-inc-bound 0 b) (suc j) c))
    p1 = ∃!-unique (lc-subst2 b j (lam c)) _ (lam (∃!-prop (lc-subst2 (lc-inc-bound 0 b) (suc j) c)))

    p2 : lc-subst a i (lam (lc-subst (lc-inc-bound 0 b) (suc j) c)) ==
         lam (lc-subst (lc-inc-bound 0 a) (suc i) (lc-subst (lc-inc-bound 0 b) (suc j) c))
    p2 = ∃!-unique (lc-subst2 a i (lam (lc-subst (lc-inc-bound 0 b) (suc j) c))) _
                   (lam (∃!-prop (lc-subst2 (lc-inc-bound 0 a) (suc i) _)))

    simplify-left : lc-subst a i (lc-subst b j (lam c)) ==
                    lam (lc-subst (lc-inc-bound 0 a) (suc i) (lc-subst (lc-inc-bound 0 b) (suc j) c))
    simplify-left = cong (lc-subst a i) p1 >=> p2

    rec : (lc-subst (lc-inc-bound 0 a) (suc i) (lc-subst (lc-inc-bound 0 b) (suc j) c)) ==
          (lc-subst (lc-subst (lc-inc-bound 0 a) (suc i) (lc-inc-bound 0 b))
                    (suc j) (lc-subst (lc-inc-bound (suc j) (lc-inc-bound 0 a)) (suc (suc i)) c))
    rec = lc-subst-twice (lc-inc-bound 0 a) (lc-inc-bound 0 b) c (suc i) (suc j) (suc-≤ j≤i)

    p3 : lc-subst (lc-inc-bound j a) (suc i) (lam c) ==
         lam (lc-subst (lc-inc-bound 0 (lc-inc-bound j a)) (suc (suc i)) c)
    p3 = ∃!-unique (lc-subst2 (lc-inc-bound j a) (suc i) (lam c)) _
                   (lam (∃!-prop (lc-subst2 (lc-inc-bound 0 (lc-inc-bound j a)) (suc (suc i)) c)))

    p5 : lc-subst (lc-subst a i b) j
           (lam (lc-subst (lc-inc-bound 0 (lc-inc-bound j a)) (suc (suc i)) c)) ==
         lam (lc-subst (lc-inc-bound 0 (lc-subst a i b)) (suc j)
               (lc-subst (lc-inc-bound 0 (lc-inc-bound j a)) (suc (suc i)) c))
    p5 = ∃!-unique (lc-subst2 (lc-subst a i b) j
                              (lam (lc-subst (lc-inc-bound 0 (lc-inc-bound j a)) (suc (suc i)) c))) _
                   (lam (∃!-prop (lc-subst2 (lc-inc-bound 0 (lc-subst a i b)) (suc j) _)))

    simplify-right :
      lc-subst (lc-subst a i b) j (lc-subst (lc-inc-bound j a) (suc i) (lam c)) ==
      lam (lc-subst (lc-inc-bound 0 (lc-subst a i b)) (suc j)
                    (lc-subst (lc-inc-bound 0 (lc-inc-bound j a)) (suc (suc i)) c))
    simplify-right = cong (lc-subst (lc-subst a i b) j) p3 >=> p5

    ans = simplify-left >=> cong lam (rec >=> inner) >=> sym simplify-right
      where
      fix1 : (lc-subst (lc-inc-bound 0 a) (suc i) (lc-inc-bound 0 b)) ==
             (lc-inc-bound 0 (lc-subst a i b))
      fix1 = sym (lc-inc-bound-subst* a b i 0 zero-≤)
      fix2 : (lc-inc-bound (suc j) (lc-inc-bound 0 a)) ==
             (lc-inc-bound 0 (lc-inc-bound j a))
      fix2 = lc-inc-bound-twice* a j 0 zero-≤


      inner : (lc-subst (lc-subst (lc-inc-bound 0 a) (suc i) (lc-inc-bound 0 b))
                    (suc j) (lc-subst (lc-inc-bound (suc j) (lc-inc-bound 0 a)) (suc (suc i)) c)) ==
              (lc-subst (lc-inc-bound 0 (lc-subst a i b)) (suc j)
               (lc-subst (lc-inc-bound 0 (lc-inc-bound j a)) (suc (suc i)) c))
      inner k = (lc-subst (fix1 k) (suc j) (lc-subst (fix2 k) (suc (suc i)) c))
  lc-subst-twice a b (app cl cr) i j j≤i =
    cong2 app (lc-subst-twice a b cl i j j≤i) (lc-subst-twice a b cr i j j≤i)








data BetaReduction : Rel Term ℓ-zero where
  beta-step : (b a : Term) -> BetaReduction (app (lam b) a) (lc-subst a 0 b)

data EtaReduction : Rel Term ℓ-zero where
  eta-step : (t : Term) -> EtaReduction (lam (app t (bound-var 0))) t


data TermContext : Type₀ where
  hole : TermContext
  lam : TermContext -> TermContext
  app-left : TermContext -> Term -> TermContext
  app-right : Term -> TermContext -> TermContext

-- C[t1] == t2
data FilledContext (t : Term) : TermContext -> Term -> Type₀ where
  hole : FilledContext t hole t
  lam : {c : TermContext} {t2 : Term} -> FilledContext t c t2 -> FilledContext t (lam c) (lam t2)
  app-left  : {c : TermContext} {t2 : Term} ->
              FilledContext t c t2 -> (t3 : Term) -> FilledContext t (app-left c t3) (app t2 t3)
  app-right : {c : TermContext} {t3 : Term} ->
              (t2 : Term) -> FilledContext t c t3 -> FilledContext t (app-right t2 c) (app t2 t3)


fill-context : (c : TermContext) -> (t : Term) -> Σ Term (FilledContext t c)
fill-context hole    t = t , hole
fill-context (lam c) t =
  let (rec-t , rec-fc) = (fill-context c t) in
  lam rec-t , lam rec-fc
fill-context (app-left c tr) t =
  let (rec-t , rec-fc) = (fill-context c t) in
  app rec-t tr , app-left rec-fc tr
fill-context (app-right tl c) t =
  let (rec-t , rec-fc) = (fill-context c t) in
  app tl rec-t , app-right tl rec-fc


data ContextualClosure (R : Rel Term ℓ-zero) : Rel Term ℓ-zero where
  hole : {t1 t2 : Term} (r : R t1 t2) -> ContextualClosure R t1 t2
  lam : {t1 t2 : Term} (c : ContextualClosure R t1 t2) -> ContextualClosure R (lam t1) (lam t2)
  app-left : {t1 t2 tr : Term} (c : ContextualClosure R t1 t2) ->
             ContextualClosure R (app t1 tr) (app t2 tr)
  app-right : {t1 t2 tl : Term} (c : ContextualClosure R t1 t2) ->
              ContextualClosure R (app tl t1) (app tl t2)


β : Rel Term ℓ-zero
β = BetaReduction

η : Rel Term ℓ-zero
η = EtaReduction

βη : Rel Term ℓ-zero
βη x y = (β x y) ⊎ (η x y)

β→ : Rel Term ℓ-zero
β→ = ContextualClosure β

η→ : Rel Term ℓ-zero
η→ = ContextualClosure η

βη→ : Rel Term ℓ-zero
βη→ = ContextualClosure βη

β→* : Rel Term ℓ-zero
β→* = TransitiveReflexiveClosure β→

η→* : Rel Term ℓ-zero
η→* = TransitiveReflexiveClosure η→

βη→* : Rel Term ℓ-zero
βη→* = TransitiveReflexiveClosure βη→

βη= : Rel Term ℓ-zero
βη= = SymmetricClosure βη→*

isNormalForm : Pred Term ℓ-zero
isNormalForm t = ¬ (Σ[ s ∈ Term ] (βη→ s t))

data DiamondLikeRes {ℓ : Level} {A : Type ℓ} (R : Rel A ℓ) (a2 a3 : A) : Type ℓ where
  dl-same : a2 == a3 -> DiamondLikeRes R a2 a3
  dl-left : R a2 a3 -> DiamondLikeRes R a2 a3
  dl-right : R a3 a2 -> DiamondLikeRes R a2 a3
  dl-both : (a4 : A) -> R a2 a4 -> R a3 a4 -> DiamondLikeRes R a2 a3

isDiamondLike : {ℓ : Level} -> {A : Type ℓ} -> Pred (Rel A ℓ) ℓ
isDiamondLike R = ∀ a1 a2 a3 -> R a1 a2 -> R a1 a3 -> DiamondLikeRes R a2 a3

isDiamondLike-η→ : isDiamondLike η→
isDiamondLike-η→ t1 t2 t3 (hole (eta-step _)) (hole (eta-step _)) = dl-same refl
isDiamondLike-η→ _ _ _ (lam c2) (lam c3) = handle dl
  where
  dl = isDiamondLike-η→ _ _ _ c2 c3
  handle : {t2 t3 : Term} -> DiamondLikeRes η→ t2 t3 -> DiamondLikeRes η→ (lam t2) (lam t3)
  handle (dl-same p) = dl-same (cong lam p)
  handle (dl-left r) = dl-left (lam r)
  handle (dl-right r) = dl-right (lam r)
  handle (dl-both t4 r2 r3) = dl-both (lam t4) (lam r2) (lam r3)
isDiamondLike-η→ _ _ _ (app-left c2) (app-left c3) = handle dl
  where
  dl = isDiamondLike-η→ _ _ _ c2 c3
  handle : {t2 t3 tr : Term} -> DiamondLikeRes η→ t2 t3 -> DiamondLikeRes η→ (app t2 tr) (app t3 tr)
  handle (dl-same p) = dl-same (cong (\x -> app x _) p)
  handle (dl-left r) = dl-left (app-left r)
  handle (dl-right r) = dl-right (app-left r)
  handle (dl-both t4 r2 r3) = dl-both (app t4 _) (app-left r2) (app-left r3)
isDiamondLike-η→ _ _ _ (app-right c2) (app-right c3) = handle dl
  where
  dl = isDiamondLike-η→ _ _ _ c2 c3
  handle : {t2 t3 tl : Term} -> DiamondLikeRes η→ t2 t3 -> DiamondLikeRes η→ (app tl t2) (app tl t3)
  handle (dl-same p) = dl-same (cong (\x -> app _ x) p)
  handle (dl-left r) = dl-left (app-right r)
  handle (dl-right r) = dl-right (app-right r)
  handle (dl-both t4 r2 r3) = dl-both (app _ t4) (app-right r2) (app-right r3)
isDiamondLike-η→ _ _ _ (app-left c2) (app-right c3) =
  dl-both _ (app-right c3) (app-left c2)
isDiamondLike-η→ _ _ _ (app-right c2) (app-left c3) =
  dl-both _ (app-left c3) (app-right c2)
isDiamondLike-η→ _ _ _ (lam (app-left c2)) (hole (eta-step _)) =
  dl-both _ (hole (eta-step _)) c2
isDiamondLike-η→ _ _ _ (hole (eta-step _)) (lam (app-left c3)) =
  dl-both _ c3 (hole (eta-step _))
isDiamondLike-η→ _ _ _ (hole (eta-step _)) (lam (hole ()))
isDiamondLike-η→ _ _ _ (hole (eta-step _)) (lam (app-right (hole ())))
isDiamondLike-η→ _ _ _ (lam (hole ())) (hole (eta-step _))
isDiamondLike-η→ _ _ _ (lam (app-right (hole ()))) (hole (eta-step _))

isDiamondLike' : {ℓ : Level} -> {A : Type ℓ} -> Pred (Rel A ℓ) ℓ
isDiamondLike' {A = A} R =
  ∀ a1 a2 a3 -> R a1 a2 -> R a1 a3 -> Σ[ a4 ∈ A ] (R? a2 a4 × R? a3 a4)
  where
  R? = ReflexiveClosure R

module _ {ℓ : Level} {A : Type ℓ} {R : Rel A ℓ} where
  private
    R? : Rel A ℓ
    R? = ReflexiveClosure R

  isDiamondLike->isDiamondLike' : isDiamondLike R -> isDiamondLike' R
  isDiamondLike->isDiamondLike' dl a1 a2 a3 r12 r13 = handle (dl a1 a2 a3 r12 r13)
    where
    handle : DiamondLikeRes R a2 a3 -> _
    handle (dl-same a2=a3) = a3 , (subst (R? a2) a2=a3 rc-refl , rc-refl)
    handle (dl-left r23) = a3 , (rc-rel r23 , rc-refl)
    handle (dl-right r32) = a2 , (rc-refl , rc-rel r32)
    handle (dl-both a4 r24 r34) = a4 , (rc-rel r24 , rc-rel r34)


hasDiamondProperty : {ℓ : Level} -> {A : Type ℓ} -> Pred (Rel A ℓ) ℓ
hasDiamondProperty {A = A} R = (a1 a2 a3 : A) -> R a1 a2 -> R a1 a3 -> Σ[ a4 ∈ A ] (R a2 a4 × R a3 a4)

isChurchRosser : {ℓ : Level} -> {A : Type ℓ} -> Pred (Rel A ℓ) ℓ
isChurchRosser = hasDiamondProperty


trc-depth : {ℓ : Level} {A : Type ℓ} {R : Rel A ℓ} ->
            {x y : A} -> (TransitiveReflexiveClosure R x y) -> Nat
trc-depth trc-refl    = 0
trc-depth (trc-rel _) = 0
trc-depth (trc-trans l r) = suc (trc-depth l + trc-depth r)

module _ {ℓ : Level} {A : Type ℓ} {R : Rel A ℓ} (dl : isDiamondLike' R) where
  private
    R? : Rel A ℓ
    R? = ReflexiveClosure R

    R* : Rel A ℓ
    R* = TransitiveReflexiveClosure R

    R?->R* : {x y : A} -> R? x y -> R* x y
    R?->R* (rc-refl)  = trc-refl
    R?->R* (rc-rel r) = trc-rel r

    isDiamondLike->isChurchRosser-single :
      (a1 a2 a3 : A) -> (R? a1 a2) -> (R* a1 a3) -> Σ[ a4 ∈ A ] (R* a2 a4 × R? a3 a4)
    isDiamondLike->isChurchRosser-single a1 a2 a3 rc-refl r13 =
      a3 , (r13 , rc-refl)
    isDiamondLike->isChurchRosser-single a1 a2 a3 (rc-rel r12) trc-refl =
      a2 , (trc-refl , rc-rel r12)
    isDiamondLike->isChurchRosser-single a1 a2 a3 (rc-rel r12) (trc-rel r13) =
      handle (dl a1 a2 a3 r12 r13)
      where
      handle : Σ[ a4 ∈ A ] (R? a2 a4 × R? a3 a4) -> Σ[ a4 ∈ A ] (R* a2 a4 × R? a3 a4)
      handle (a4 , (r24 , r34)) = a4 , (R?->R* r24 , r34)
    isDiamondLike->isChurchRosser-single a1 a2 a3 r?12@(rc-rel _) (trc-trans {b = a4} r*14 r*43) =
      -- first merge 1->2 and 1->4 at 5
      let (a5 , (r*25 , r?45)) = isDiamondLike->isChurchRosser-single a1 a2 a4 r?12 r*14 in
      let (a6 , (r*56 , r?36)) = isDiamondLike->isChurchRosser-single a4 a5 a3 r?45 r*43 in
      (a6 , ((trc-trans r*25 r*56) , r?36))

  isDiamondLike->isChurchRosser :
    (a1 a2 a3 : A) -> (R* a1 a2) -> (R* a1 a3) -> Σ[ a4 ∈ A ] (R* a2 a4 × R* a3 a4)
  isDiamondLike->isChurchRosser a1 a2 a3 (trc-rel r12) r*13 =
    let (a4 , (r*24 , r?34)) = isDiamondLike->isChurchRosser-single _ _ _ (rc-rel r12) r*13 in
    a4 , (r*24 , R?->R* r?34)
  isDiamondLike->isChurchRosser a1 a2 a3 (trc-refl) r*13 =
    let (a4 , (r*24 , r?34)) = isDiamondLike->isChurchRosser-single _ _ _ (rc-refl) r*13 in
    a4 , (r*24 , R?->R* r?34)
  isDiamondLike->isChurchRosser a1 a2 a3 (trc-trans r*14 r*42) r*13 =
    let (a5 , (r*45 , r*35)) = isDiamondLike->isChurchRosser _ _ _ r*14 r*13 in
    let (a6 , (r*26 , r*56)) = isDiamondLike->isChurchRosser _ _ _ r*42 r*45 in
    a6 , (r*26 , trc-trans r*35 r*56)

hasDiamondProperty-η→* : hasDiamondProperty η→*
hasDiamondProperty-η→* =
  isDiamondLike->isChurchRosser (isDiamondLike->isDiamondLike' isDiamondLike-η→)


data ParBetaReduction : Rel Term ℓ-zero where
  refl-step : {t : Term} -> ParBetaReduction t t
  beta-step : (bs bt as at : Term) ->
              (br : ParBetaReduction bs bt) -> (ar : ParBetaReduction as at) ->
              ParBetaReduction (app (lam bs) as) (lc-subst at 0 bt)
  app : {fs ft as at : Term} ->
        (fr : ParBetaReduction fs ft) -> (ar : ParBetaReduction as at) ->
        ParBetaReduction (app fs as) (app ft at)
  lam : {bs bt : Term} ->
        (br : ParBetaReduction bs bt) ->
        ParBetaReduction (lam bs) (lam bt)

parβ : Rel Term ℓ-zero
parβ = ParBetaReduction

lc-inc-bound-parβ : {a1 a2 : Term} (i : Nat) -> parβ a1 a2 ->
                    parβ (lc-inc-bound i a1) (lc-inc-bound i a2)
lc-inc-bound-parβ i refl-step = refl-step
lc-inc-bound-parβ i (app rl rr) =
  app (lc-inc-bound-parβ i rl) (lc-inc-bound-parβ i rr)
lc-inc-bound-parβ i (lam b) =
  lam (lc-inc-bound-parβ (suc i) b)
lc-inc-bound-parβ i (beta-step bs bt as at br ar) = ans
  where
  rec-bs : parβ (lc-inc-bound (suc i) bs) (lc-inc-bound (suc i) bt)
  rec-bs = lc-inc-bound-parβ (suc i) br

  rec-as : parβ (lc-inc-bound i as) (lc-inc-bound i at)
  rec-as = lc-inc-bound-parβ i ar

  rec : parβ (lc-inc-bound i (app (lam bs) as))
             (lc-subst (lc-inc-bound i at) 0 (lc-inc-bound (suc i) bt))
  rec = beta-step _ _ _ _ rec-bs rec-as

  ans : parβ (lc-inc-bound i (app (lam bs) as)) (lc-inc-bound i (lc-subst at 0 bt))
  ans = subst (parβ (lc-inc-bound i (app (lam bs) as)))
              (sym (lc-inc-bound-subst-≤* at bt 0 i zero-≤)) rec

subst-parβ1 : {a1 a2 : Term} (i : Nat) -> parβ a1 a2 -> (b : Term) ->
             parβ (lc-subst a1 i b) (lc-subst a2 i b)
subst-parβ1 i r12 (bound-var j) with (trichotomous-< j i)
... | (tri< _ _ _) = refl-step
... | (tri= _ _ _) = r12
... | (tri> _ _ _) = refl-step
subst-parβ1 {a1} {a2} i r12 (lam b) =
  lam (subst-parβ1 (suc i) (lc-inc-bound-parβ 0 r12) b)
subst-parβ1 i r12 (app f x) = app (subst-parβ1 i r12 f) (subst-parβ1 i r12 x)


abstract
  subst-parβ : {a1 a2 b1 b2 : Term} (i : Nat) -> parβ a1 a2 -> parβ b1 b2 ->
               parβ (lc-subst a1 i b1) (lc-subst a2 i b2)
  subst-parβ i ra12 (refl-step {t}) = subst-parβ1 i ra12 t
  subst-parβ i ra12 (lam rb12) =
    lam (subst-parβ (suc i) (lc-inc-bound-parβ 0 ra12) rb12)
  subst-parβ i ra12 (app rbf12 rbx12) =
    app (subst-parβ i ra12 rbf12) (subst-parβ i ra12 rbx12)
  subst-parβ {a1} {a2} i ra12 (beta-step b1 b2 ia1 ia2 rb12 ria12) = ans
    where
    rec-b : parβ (lc-subst (lc-inc-bound 0 a1) (suc i) b1) (lc-subst (lc-inc-bound 0 a2) (suc i) b2)
    rec-b = subst-parβ (suc i) (lc-inc-bound-parβ 0 ra12) rb12
    rec-ia : parβ (lc-subst a1 i ia1) (lc-subst a2 i ia2)
    rec-ia = subst-parβ i ra12 ria12

    subst-twice' : (lc-subst (lc-subst a2 i ia2) 0 (lc-subst (lc-inc-bound 0 a2) (suc i) b2)) ==
                   (lc-subst a2 i (lc-subst ia2 0 b2))
    subst-twice' = sym (lc-subst-twice a2 ia2 b2 i 0 zero-≤)

    ans1 : parβ (app (lam (lc-subst (lc-inc-bound 0 a1) (suc i) b1)) (lc-subst a1 i ia1))
                (lc-subst (lc-subst a2 i ia2) 0 (lc-subst (lc-inc-bound 0 a2) (suc i) b2))
    ans1 = beta-step _ _ _ _ rec-b rec-ia

    ans : parβ (app (lam (lc-subst (lc-inc-bound 0 a1) (suc i) b1)) (lc-subst a1 i ia1))
               (lc-subst a2 i (lc-subst ia2 0 b2))
    ans = subst (parβ (app (lam (lc-subst (lc-inc-bound 0 a1) (suc i) b1)) (lc-subst a1 i ia1)))
                subst-twice' ans1


hasDiamondProperty-parβ : hasDiamondProperty parβ
hasDiamondProperty-parβ _ _ t3 refl-step r13 =
  t3 , (r13 , refl-step)
hasDiamondProperty-parβ _ t2 _ r12@(beta-step _ _ _ _ _ _) refl-step =
  t2 , (refl-step , r12)
hasDiamondProperty-parβ _ t2 _ r12@(app _ _) refl-step =
  t2 , (refl-step , r12)
hasDiamondProperty-parβ _ t2 _ r12@(lam _) refl-step =
  t2 , (refl-step , r12)
hasDiamondProperty-parβ _ _ _ (app rl12 rr12) (app rl13 rr13) =
  let (l4 , (rl24 , rl34)) = hasDiamondProperty-parβ _ _ _ rl12 rl13 in
  let (r4 , (rr24 , rr34)) = hasDiamondProperty-parβ _ _ _ rr12 rr13 in
  (app l4 r4) , (app rl24 rr24 , app rl34 rr34)
hasDiamondProperty-parβ _ _ _ (lam b12) (lam b13) =
  let (b4 , (r24 , r34)) = hasDiamondProperty-parβ _ _ _ b12 b13 in
  (lam b4) , (lam r24 , lam r34)
hasDiamondProperty-parβ (app (lam b1) a1) t2 t3
                        (beta-step b1 b2 a1 a2 rb12 ra12)
                        (beta-step b1 b3 a1 a3 rb13 ra13) =
  let (b4 , (rb24 , rb34)) = hasDiamondProperty-parβ _ _ _ rb12 rb13 in
  let (a4 , (ra24 , ra34)) = hasDiamondProperty-parβ _ _ _ ra12 ra13 in
  (lc-subst a4 0 b4) , (subst-parβ 0 ra24 rb24 , subst-parβ 0 ra34 rb34)
hasDiamondProperty-parβ (app (lam b1) a1) t2 (app (lam b3) a3)
                        (beta-step b1 b2 a1 a2 rb12 ra12)
                        (app (lam rb13) ra13) =
  let (b4 , (rb24 , rb34)) = hasDiamondProperty-parβ _ _ _ rb12 rb13 in
  let (a4 , (ra24 , ra34)) = hasDiamondProperty-parβ _ _ _ ra12 ra13 in
  (lc-subst a4 0 b4) , (subst-parβ 0 ra24 rb24 , beta-step _ _ _ _ rb34 ra34)
hasDiamondProperty-parβ (app (lam b1) a1) t2 (app (lam b3) a3)
                        (beta-step b1 b2 a1 a2 rb12 ra12)
                        (app (refl-step) ra13) =
  let (b4 , (rb24 , rb34)) = hasDiamondProperty-parβ _ _ _ rb12 refl-step in
  let (a4 , (ra24 , ra34)) = hasDiamondProperty-parβ _ _ _ ra12 ra13 in
  (lc-subst a4 0 b4) , (subst-parβ 0 ra24 rb24 , beta-step _ _ _ _ rb34 ra34)
hasDiamondProperty-parβ (app (lam b1) a1) (app (lam b2) a2) t3
                        (app (lam rb12) ra12)
                        (beta-step b1 b3 a1 a3 rb13 ra13) =
  let (b4 , (rb24 , rb34)) = hasDiamondProperty-parβ _ _ _ rb12 rb13 in
  let (a4 , (ra24 , ra34)) = hasDiamondProperty-parβ _ _ _ ra12 ra13 in
  (lc-subst a4 0 b4) , (beta-step _ _ _ _ rb24 ra24 , subst-parβ 0 ra34 rb34)
hasDiamondProperty-parβ (app (lam b1) a1) (app (lam b2) a2) t3
                        (app refl-step ra12)
                        (beta-step b1 b3 a1 a3 rb13 ra13) =
  let (b4 , (rb24 , rb34)) = hasDiamondProperty-parβ _ _ _ refl-step rb13 in
  let (a4 , (ra24 , ra34)) = hasDiamondProperty-parβ _ _ _ ra12 ra13 in
  (lc-subst a4 0 b4) , (beta-step _ _ _ _ rb24 ra24 , subst-parβ 0 ra34 rb34)
