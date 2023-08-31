{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal2 where

open import additive-group
open import additive-group.instances.nat
open import base
open import cubical
open import category.base
open import category.constructions.product
open import category.constructions.triple-product
open import category.monoidal.base
open import equality-path
open import hlevel
open import nat
open import nat.order
open import boolean
open import truncation
open import relation
open import sigma.base
open import sum
open import order
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import order.instances.nat

open import category.monoidal.formal-base hiding
  ( canon
  ; dirpath-to-canon'
  ; isDirectedMor
  ; DirectedMor
  ; DirectedPath
  ; dirpath-to-canon
  ; dirmor->branches=
  ; dirmor->rank<
  ; dirpath->rank≤
  )

isDirectedMor : {a b : WObj} -> Pred (BasicMor a b) ℓ-zero
isDirectedMor (α⇒' a b c) = Top
isDirectedMor (m ⊗ˡ' w) = isDirectedMor m
isDirectedMor (w ⊗ʳ' m) = isDirectedMor m
isDirectedMor (α⇐' _ _ _) = Bot
isDirectedMor (λ⇒' _) = Bot
isDirectedMor (λ⇐' _) = Bot
isDirectedMor (ρ⇒' _) = Bot
isDirectedMor (ρ⇐' _) = Bot

DirectedMor : WObj -> WObj -> Type₀
DirectedMor a b = Σ (BasicMor a b) isDirectedMor

isDirectedPath : {a b : WObj} -> Pred (BasicPath a b) ℓ-zero
isDirectedPath (empty p) = Top
isDirectedPath (m :: p) = isDirectedMor m × isDirectedPath p

DirectedPath : WObj -> WObj -> Type₀
DirectedPath a b = Σ (BasicPath a b) isDirectedPath

isεFree : Pred WObj ℓ-zero
isεFree ε = Bot
isεFree var = Top
isεFree (a ⊗ b) = isεFree a × isεFree b

isVar : Pred WObj ℓ-zero
isVar ε = Bot
isVar var = Top
isVar (_ ⊗ _) = Bot

is⊗ : Pred WObj ℓ-zero
is⊗ ε = Bot
is⊗ var = Bot
is⊗ (_ ⊗ _) = Top

isRTree : Pred WObj ℓ-zero
isRTree ε = Bot
isRTree var = Top
isRTree (a ⊗ b) = isVar a × isRTree b

isCanon : Pred WObj ℓ-zero
isCanon ε = Top
isCanon m@var = isRTree m
isCanon m@(_ ⊗ _) = isRTree m

isProp-isVar : (o : WObj) -> isProp (isVar o)
isProp-isVar ε = isPropBot
isProp-isVar var = isPropTop
isProp-isVar (_ ⊗ _) = isPropBot

isProp-isRTree : (o : WObj) -> isProp (isRTree o)
isProp-isRTree ε = isPropBot
isProp-isRTree var = isPropTop
isProp-isRTree (a ⊗ b) = isProp× (isProp-isVar a) (isProp-isRTree b)

isProp-isCanon : (o : WObj) -> isProp (isCanon o)
isProp-isCanon ε = isPropTop
isProp-isCanon m@var = isProp-isRTree m
isProp-isCanon m@(_ ⊗ _) = isProp-isRTree m

rank-induction : {ℓ : Level}
  {P : Pred WObj ℓ} ->
  (rec : (o1 : WObj) -> ((o2 : WObj) -> WObj-rank o2 < WObj-rank o1 -> P o2) -> P o1)
  (o : WObj) -> P o
rank-induction {ℓ} {P} rec = \o -> strong-induction' rec' _ o refl-≤
  where
  P' : Pred Nat ℓ
  P' n = (o : WObj) -> (WObj-rank o < n) -> P o
  rec' : {m : Nat} -> ({n : Nat} -> n < m -> P' n) -> P' m
  rec' hyp o1 r1<m = rec o1 (hyp r1<m)

length-induction : {ℓ : Level}
  {P : Pred WObj ℓ} ->
  (rec : (o1 : WObj) -> ((o2 : WObj) -> WObj-length o2 < WObj-length o1 -> P o2) -> P o1)
  (o : WObj) -> P o
length-induction {ℓ} {P} rec = \o -> strong-induction' rec' _ o refl-≤
  where
  P' : Pred Nat ℓ
  P' n = (o : WObj) -> (WObj-length o < n) -> P o
  rec' : {m : Nat} -> ({n : Nat} -> n < m -> P' n) -> P' m
  rec' hyp o1 r1<m = rec o1 (hyp r1<m)

rank-length-induction : {ℓ : Level}
  {P : Pred WObj ℓ} ->
  (rec : (o1 : WObj) -> ((o2 : WObj) -> ((WObj-length o2 < WObj-length o1) ⊎
                                         ((WObj-rank o2 < WObj-rank o1) ×
                                          (WObj-length o1 == WObj-length o2))) -> P o2) ->
         P o1)
  (o : WObj) -> P o
rank-length-induction {ℓ} {P} rec = rec3
  where
  P2' : Pred WObj _
  P2' o1 = (o2 : WObj) ->
           (WObj-length o2 < WObj-length o1) ->
           P o2

  Q2' : Rel WObj _
  Q2' o1 o2 = (WObj-length o2 < WObj-length o1) -> P o2

  rec2 : (o : WObj) -> P2' o
  rec2 = length-induction rec1-inner
    where
    rec1-inner : (o1 : WObj) -> ((ot : WObj) -> WObj-length ot < WObj-length o1 -> P2' ot) -> P2' o1
    rec1-inner o1 lhyp =
      rank-induction rec2-inner
      where
      rec2-inner : (o2 : WObj) -> ((ot : WObj) -> WObj-rank ot < WObj-rank o2 -> Q2' o1 ot) -> Q2' o1 o2
      rec2-inner o2 rhyp l2<l1 =
        rec o2 (\{ o3 (inj-l l3<l2) -> lhyp o2 l2<l1 o3 l3<l2
                 ; o3 (inj-r (r3<r2 , l2=l3)) ->
                   rhyp o3 r3<r2 (trans-=-< (sym l2=l3) l2<l1)
                 })

  rec3 : (o : WObj) -> P o
  rec3 = rank-induction rec3-inner
    where
    rec3-inner : (o1 : WObj) -> ((ot : WObj) -> WObj-rank ot < WObj-rank o1 -> P ot) -> P o1
    rec3-inner o1 rhyp =
      rec o1 (\{ o2 (inj-l l2<l1) -> rec2 o1 o2 l2<l1
               ; o2 (inj-r (r2<r1 , l1=l2)) -> rhyp o2 r2<r1
               })


isRTree->isεFree : (o : WObj) -> isRTree o -> isεFree o
isRTree->isεFree var tt = tt
isRTree->isεFree (var ⊗ o) (tt , rt) = tt , (isRTree->isεFree o rt)


εF-0<length : (o : WObj) -> (εF : isεFree o) -> 0 < WObj-length o
εF-0<length var _ = zero-<
εF-0<length (a ⊗ b) (εFa , εFb) =
  +-preserves-0< (εF-0<length a εFa) (εF-0<length b εFb)

isRTree-0<length : (o : WObj) -> (rt : isRTree o) -> 0 < WObj-length o
isRTree-0<length o rt = εF-0<length o (isRTree->isεFree o rt)


∃!canon : (n : Nat) -> ∃![ o ∈ WObj ] (WObj-length o == n × isCanon o)
∃!canon = \n -> val n , isProp' _
  where
  val' : (n : Nat) -> Σ[ o ∈ WObj ] (WObj-length o == (suc n) × isRTree o × isCanon o)
  val' zero = var , refl , tt , tt
  val' (suc n) =
    let (o , p , rt , _) = val' n in
    (var ⊗ o) , (cong suc p) , (tt , rt) , (tt , rt)

  val : (n : Nat) -> Σ[ o ∈ WObj ] (WObj-length o == n × isCanon o)
  val zero = ε , refl , tt
  val (suc n) = let (o , p , _ , c) = val' n in (o , p , c)

  val-path' : {n : Nat} ->
               (o1 : WObj) -> WObj-length o1 == n -> isRTree o1 ->
               (o2 : WObj) -> WObj-length o2 == n -> isRTree o2 ->
               o1 == o2
  val-path' var p1 rt1 var p2 rt2 = refl
  val-path' (var ⊗ o1) p1 (_ , rt1) var p2 rt2 = bot-elim (irrefl-< 1<1)
    where
    1<1 : 1 < 1
    1<1 = trans-<-= (suc-< (isRTree-0<length o1 rt1)) (p1 >=> sym p2)
  val-path' var p1 c1 (var ⊗ o2) p2 (_ , rt2) = bot-elim (irrefl-< 1<1)
    where
    1<1 : 1 < 1
    1<1 = trans-<-= (suc-< (isRTree-0<length o2 rt2)) (p2 >=> sym p1)
  val-path' (var ⊗ o1) p1 (_ , rt1) (var ⊗ o2) p2 (_ , rt2) =
    cong (var ⊗_) (val-path' o1 (cong pred p1) rt1 o2 (cong pred p2) rt2)

  val-path : {n : Nat} -> (s1 s2 : Σ[ o ∈ WObj ] (WObj-length o == n × isCanon o)) ->
             (fst s1) == (fst s2)
  val-path (ε , p1 , c1) (ε , p2 , c2) = refl
  val-path (ε , p1 , c1) (var , p2 , c2) =
    zero-suc-absurd (p1 >=> sym p2)
  val-path (var , p1 , c1) (ε , p2 , c2) =
    zero-suc-absurd (p2 >=> sym p1)
  val-path ((var ⊗ o1) , p1 , c1) (ε , p2 , c2) =
    zero-suc-absurd (p2 >=> sym p1)
  val-path (ε , p1 , c1) ((var ⊗ o2) , p2 , c2) =
    zero-suc-absurd (p1 >=> sym p2)
  val-path s1@((var ⊗ o1) , p1 , c1) s2@(var , p2 , c2) =
    val-path' (var ⊗ o1) p1 c1 var p2 c2
  val-path (var , p1 , c1) (var , p2 , c2) =
    val-path' var p1 c1 var p2 c2
  val-path (var , p1 , c1) ((var ⊗ o2) , p2 , c2) =
    val-path' var p1 c1 (var ⊗ o2) p2 c2
  val-path ((var ⊗ o1) , p1 , c1) ((var ⊗ o2) , p2 , c2) =
    val-path' (var ⊗ o1) p1 c1 (var ⊗ o2) p2 c2

  isProp' : {n : Nat} -> isProp (Σ[ o ∈ WObj ] (WObj-length o == n × isCanon o))
  isProp' s1 s2 = ΣProp-path (\{o} -> isProp× (isSetNat _ _) (isProp-isCanon o))
                  (val-path s1 s2)


canon : (n : Nat) -> WObj
canon n = ∃!-val (∃!canon n)

canon' : WObj -> WObj
canon' o = (canon (WObj-length o))

canon-εF-full : (o1 : WObj) -> isεFree o1 ->
                Σ[ o2 ∈ WObj ] (WObj-length o2 == (WObj-length o1) × isCanon o2)
canon-εF-full = \o1 εF ->
  let (oR , pR , rR , cR) = rank-induction rec o1 εF in
  (oR , pR , cR)
  where
  rec : (o1 : WObj) ->
        ((o2 : WObj) -> WObj-rank o2 < WObj-rank o1 ->
          isεFree o2 ->
          Σ[ o3 ∈ WObj ] (WObj-length o3 == (WObj-length o2) × isRTree o3 × isCanon o3)
          ) ->
        isεFree o1 ->
        Σ[ o2 ∈ WObj ] (WObj-length o2 == (WObj-length o1) × isRTree o2 × isCanon o2)
  rec var hyp _ = var , refl , tt , tt
  rec (var ⊗ o) hyp (_ , εF) =
    let (o2 , p2 , r2 , c2) = rec o hyp εF in
    (var ⊗ o2 , cong suc p2 , (tt , r2) , (tt , r2))
  rec ((o1 ⊗ o2) ⊗ o3) hyp ((εF1 , εF2) , εF3) =
    let (oR , pR , rR , cR) = hyp (o1 ⊗ (o2 ⊗ o3)) (assoc-rank< o1 o2 o3) (εF1 , (εF2 , εF3)) in
    (oR , pR >=> (sym (+-assocᵉ (WObj-length o1) (WObj-length o2) (WObj-length o3))) , rR , cR)


  -- rec ((o1 ⊗ o2) ⊗ o3) hyp ((εF1 , εF2) , εF3) =
  --   hyp (o1 ⊗ (o2 ⊗ o3)) (assoc-rank< o1 o2 o3) (εF1 , (εF2 , εF3))

canon-εF : (o : WObj) -> isεFree o -> WObj
canon-εF o εF = fst (canon-εF-full o εF)

canon-εF-path : (o : WObj) -> (εF : isεFree o) -> canon-εF o εF == canon' o
canon-εF-path o εF =
  cong fst (sym (snd (∃!canon (WObj-length o)) (canon-εF-full o εF)))



canon-branches : (n : Nat) -> WObj-branches (canon n) == pred n
canon-branches zero = refl
canon-branches (suc zero) = refl
canon-branches (suc (suc n)) = cong suc (canon-branches (suc n))

canon-rank : (n : Nat) -> WObj-rank (canon n) == 0
canon-rank zero = refl
canon-rank (suc zero) = refl
canon-rank (suc (suc n)) = canon-rank (suc n)

assoc-canon-path : (o1 o2 o3 : WObj) ->
                   canon' ((o1 ⊗ o2) ⊗ o3) == canon' (o1 ⊗ (o2 ⊗ o3))
assoc-canon-path o1 o2 o3 =
  cong canon (+-assocᵉ (WObj-length o1) (WObj-length o2) (WObj-length o3))

assoc-canon-εF-path :
  (o1 o2 o3 : WObj) (εF1 : isεFree o1) (εF2 : isεFree o2) (εF3 : isεFree o3) ->
  canon-εF ((o1 ⊗ o2) ⊗ o3) ((εF1 , εF2) , εF3) ==
  canon-εF (o1 ⊗ (o2 ⊗ o3)) (εF1 , (εF2 , εF3))
assoc-canon-εF-path o1 o2 o3 εF1 εF2 εF3 =
  canon-εF-path ((o1 ⊗ o2) ⊗ o3) ((εF1 , εF2) , εF3) >=>
  assoc-canon-path o1 o2 o3 >=>
  sym (canon-εF-path (o1 ⊗ (o2 ⊗ o3)) (εF1 , (εF2 , εF3)))

dirpath-to-canon-εF : (o : WObj) -> (εF : isεFree o) -> DirectedPath o (canon-εF o εF)
dirpath-to-canon-εF = rank-induction rec
  where
  rec : (o1 : WObj) ->
        ((o2 : WObj) -> WObj-rank o2 < WObj-rank o1 ->
         (εF2 : isεFree o2) -> DirectedPath o2 (canon-εF o2 εF2)) ->
        (εF1 : isεFree o1) -> DirectedPath o1 (canon-εF o1 εF1)
  rec var hyp _ = (empty refl) , tt
  rec (var ⊗ o1) hyp (_ , εF) = lift-path (rec o1 hyp εF)
    where
    lift-path : {o1 o2 : WObj} -> DirectedPath o1 o2 -> DirectedPath (var ⊗ o1) (var ⊗ o2)
    lift-path (empty p , _) = (empty (cong (var ⊗_) p) , tt)
    lift-path (m :: p , (dm , dp)) =
      let (p2 , dp2) = lift-path (p , dp) in
      ((var ⊗ʳ' m) :: p2) , dm , dp2
  rec ((o1 ⊗ o2) ⊗ o3) hyp ((εF1 , εF2) , εF3) =
    let (p , dp) = res in (α⇒' o1 o2 o3 :: p , tt , dp)
    where
    res : DirectedPath (o1 ⊗ (o2 ⊗ o3)) (canon-εF ((o1 ⊗ o2) ⊗ o3) ((εF1 , εF2) , εF3))
    res =
      transport (\i -> DirectedPath (o1 ⊗ (o2 ⊗ o3)) (assoc-canon-εF-path o1 o2 o3 εF1 εF2 εF3 (~ i)))
                (hyp (o1 ⊗ (o2 ⊗ o3)) (assoc-rank< o1 o2 o3) (εF1 , (εF2 , εF3)))

dirpath-to-isCanon : (o1 o2 : WObj) -> (isεFree o1) -> (isCanon o2) ->
                     (WObj-length o1 == WObj-length o2) ->
                     DirectedPath o1 o2
dirpath-to-isCanon o1 o2 εF c2 lp =
  transport (\i -> DirectedPath o1 ((canon-εF-path o1 εF >=> c=o2) i))
            (dirpath-to-canon-εF o1 εF)
  where
  c=o2 : canon' o1 == o2
  c=o2 = cong fst (snd (∃!canon (WObj-length o1)) (o2 , sym lp , c2))



{-
dirpath-to-canon : (o : WObj) -> (isRTree o) -> DirectedPath o (canon (WObj-length o))
dirpath-to-canon = \ o rtree -> strong-induction' rec _ o refl-≤ rtree
  where
  P : Pred Nat _
  P n = (o : WObj) -> WObj-rank o ≤ n -> (isRTree o) -> DirectedPath o (canon (WObj-length o))

  rec : {bound : Nat} -> ({n : Nat} -> n < bound -> P n) -> P bound
  rec hyp ε lt _ = (empty refl) , tt
  rec hyp (var ⊗ o) lt (_ , rtree) = lift-path rec-res
    where
    rec-res : DirectedPath o (canon (WObj-length o))
    rec-res = rec hyp o lt rtree

    lift-path : {o1 o2 : WObj} -> DirectedPath o1 o2 -> DirectedPath (var ⊗ o1) (var ⊗ o2)
    lift-path (empty p , _) = (empty (cong (var ⊗_) p) , tt)
    lift-path (m :: p , (dm , dp)) =
      let (p2 , dp2) = lift-path (p , dp) in
      ((var ⊗ʳ' m) :: p2) , dm , dp2
  rec hyp ((o1 ⊗ o2) ⊗ o3) lt ((εfree1 , εfree2) , rtree) =
    let (p , dp) = rec-res' in
    (α⇒' o1 o2 o3) :: p , tt , dp
    where
    rec-res : DirectedPath (o1 ⊗ (o2 ⊗ o3)) (canon (WObj-length (o1 ⊗ (o2 ⊗ o3))))
    rec-res = hyp (trans-<-≤ (assoc-rank< o1 o2 o3) lt) _ refl-≤ (εfree1 , (εfree2 , rtree))

    rec-res' : DirectedPath (o1 ⊗ (o2 ⊗ o3)) (canon (WObj-length ((o1 ⊗ o2) ⊗ o3)))
    rec-res' =
      transport (\i -> DirectedPath (o1 ⊗ (o2 ⊗ o3))
                                    (canon (+-assocᵉ (WObj-length o1) (WObj-length o2) (WObj-length o3)
                                                     (~ i))))
                rec-res
-}

data DirectedMor' : WObj -> WObj -> Type₀ where
  α⇒' : (a b c : WObj) -> DirectedMor' ((a ⊗ b) ⊗ c) (a ⊗ (b ⊗ c))
  _⊗ˡ'_ : {a b : WObj} -> DirectedMor' a b -> (c : WObj) -> DirectedMor' (a ⊗ c) (b ⊗ c)
  _⊗ʳ'_ : (a : WObj) -> {b c : WObj} -> DirectedMor' b c -> DirectedMor' (a ⊗ b) (a ⊗ c)

dm'->dm : {a b : WObj} -> DirectedMor' a b -> DirectedMor a b
dm'->dm (α⇒' a b c) = (α⇒' a b c) , tt
dm'->dm (m ⊗ˡ' w) = let (m2 , dm2) = dm'->dm m in (m2 ⊗ˡ' w , dm2)
dm'->dm (w ⊗ʳ' m) = let (m2 , dm2) = dm'->dm m in (w ⊗ʳ' m2 , dm2)

dm'->bm : {a b : WObj} -> DirectedMor' a b -> BasicMor a b
dm'->bm m = fst (dm'->dm m)

dm->dm' : {a b : WObj} -> DirectedMor a b -> DirectedMor' a b
dm->dm' (α⇒' a b c , _) = α⇒' a b c
dm->dm' (m ⊗ˡ' w , dm) = dm->dm' (m , dm) ⊗ˡ' w
dm->dm' (w ⊗ʳ' m , dm) = w ⊗ʳ' dm->dm' (m , dm)

dm'->branches= : {o1 o2 : WObj} -> DirectedMor' o1 o2 -> WObj-branches o1 == WObj-branches o2
dm'->branches= (α⇒' a b c) =
  cong suc (cong suc (+-assocᵉ (WObj-branches a) (WObj-branches b) (WObj-branches c)) >=>
            sym +'-right-suc)
dm'->branches= (m ⊗ˡ' c) =
  cong suc (+-left (dm'->branches= m))
dm'->branches= (a ⊗ʳ' m) =
  cong suc (+-right (dm'->branches= m))

dm'->rank< : {o1 o2 : WObj} -> DirectedMor' o1 o2 -> WObj-rank o2 < WObj-rank o1
dm'->rank< (α⇒' a b c) = assoc-rank< a b c
dm'->rank< {o1 ⊗ c} {o2 ⊗ c} (m ⊗ˡ' c) =
  trans-<-=
    (+₁-preserves-< {a = WObj-branches o2} (+₂-preserves-< rec))
    (\i -> (dm'->branches= m (~ i)) + (WObj-rank o1 + WObj-rank c))
  where
  rec : WObj-rank o2 < WObj-rank o1
  rec = dm'->rank< m
dm'->rank< {a ⊗ o1} {a ⊗ o2} (a ⊗ʳ' m) =
  (+₁-preserves-< {a = WObj-branches a} (+₁-preserves-< rec))
  where
  rec : WObj-rank o2 < WObj-rank o1
  rec = dm'->rank< m

dm'-preserves-isεFree : {a b : WObj} -> DirectedMor' a b -> isεFree a -> isεFree b
dm'-preserves-isεFree (α⇒' a b c) ((εF1 , εF2) , εF3) = εF1 , (εF2 , εF3)
dm'-preserves-isεFree (m ⊗ˡ' w) (εF1 , εF2) = dm'-preserves-isεFree m εF1 , εF2
dm'-preserves-isεFree (w ⊗ʳ' m) (εF1 , εF2) = εF1 , dm'-preserves-isεFree m εF2

dm'->length= : {o1 o2 : WObj} -> DirectedMor' o1 o2 -> WObj-length o1 == WObj-length o2
dm'->length= (α⇒' a b c) =
  +-assocᵉ (WObj-length a) (WObj-length b) (WObj-length c)
dm'->length= (m ⊗ˡ' c) = +-left (dm'->length= m)
dm'->length= (a ⊗ʳ' m) = +-right (dm'->length= m)


dirmor->branches= : {o1 o2 : WObj} -> DirectedMor o1 o2 -> WObj-branches o1 == WObj-branches o2
dirmor->branches= (α⇒' a b c , _) =
  cong suc (cong suc (+-assocᵉ (WObj-branches a) (WObj-branches b) (WObj-branches c)) >=>
            sym +'-right-suc)
dirmor->branches= (m ⊗ˡ' c , dm) =
  cong suc (+-left (dirmor->branches= (m , dm)))
dirmor->branches= (a ⊗ʳ' m , dm) =
  cong suc (+-right (dirmor->branches= (m , dm)))

dirmor->length= : {o1 o2 : WObj} -> DirectedMor o1 o2 -> WObj-length o1 == WObj-length o2
dirmor->length= (α⇒' a b c , _) =
  +-assocᵉ (WObj-length a) (WObj-length b) (WObj-length c)
dirmor->length= (m ⊗ˡ' c , dm) =
  +-left (dirmor->length= (m , dm))
dirmor->length= (a ⊗ʳ' m , dm) =
  +-right (dirmor->length= (m , dm))


dirmor->rank< : {o1 o2 : WObj} -> DirectedMor o1 o2 -> WObj-rank o2 < WObj-rank o1
dirmor->rank< (α⇒' a b c , _) = assoc-rank< a b c
dirmor->rank< {o1 ⊗ c} {o2 ⊗ c} (m ⊗ˡ' c , dm) =
  trans-<-=
    (+₁-preserves-< {a = WObj-branches o2} (+₂-preserves-< rec))
    (\i -> (dirmor->branches= (m , dm) (~ i)) + (WObj-rank o1 + WObj-rank c))
  where
  rec : WObj-rank o2 < WObj-rank o1
  rec = dirmor->rank< (m , dm)
dirmor->rank< {a ⊗ o1} {a ⊗ o2} (a ⊗ʳ' m , dm) =
  (+₁-preserves-< {a = WObj-branches a} (+₁-preserves-< rec))
  where
  rec : WObj-rank o2 < WObj-rank o1
  rec = dirmor->rank< (m , dm)


dirmor-preserves-isεFree : {a b : WObj} -> DirectedMor a b -> isεFree a -> isεFree b
dirmor-preserves-isεFree m = dm'-preserves-isεFree (dm->dm' m)

dirpath-preserves-isεFree : {a b : WObj} -> DirectedPath a b -> isεFree a -> isεFree b
dirpath-preserves-isεFree (empty p , _) = transport (\i -> isεFree (p i))
dirpath-preserves-isεFree (m :: p , dm , dp) εF =
  dirpath-preserves-isεFree (p , dp) (dirmor-preserves-isεFree (m , dm) εF)


dirpath->rank≤ : {o1 o2 : WObj} -> DirectedPath o1 o2 -> WObj-rank o2 ≤ WObj-rank o1
dirpath->rank≤ (empty p , _) = path-≤ (cong WObj-rank (sym p))
dirpath->rank≤ ((m :: p) , dm , dp) =
  trans-≤ (dirpath->rank≤ (p , dp)) (weaken-< (dirmor->rank< (m , dm)))

dirpath->length= : {o1 o2 : WObj} -> DirectedPath o1 o2 -> WObj-length o1 == WObj-length o2
dirpath->length= (empty p , _) = cong WObj-length p
dirpath->length= ((m :: p) , dm , dp) =
  dirmor->length= (m , dm) >=> dirpath->length= (p , dp)

_dp++_ : {o1 o2 o3 : WObj} -> DirectedPath o1 o2 -> DirectedPath o2 o3 -> DirectedPath o1 o3
_dp++_ {o3 = o3} (empty p , _) =
  transp (\i -> DirectedPath (p (~ i)) o3) i0
_dp++_ (m :: p , dm , dp) p2 =
  let (rp , rdp) = (p , dp) dp++ p2 in
  (m :: rp , dm , rdp)

WObj-left : (o : WObj) -> is⊗ o -> WObj
WObj-left (l ⊗ r) _ = l

WObj-right : (o : WObj) -> is⊗ o -> WObj
WObj-right (l ⊗ r) _ = r

cons-dirmor : {a b c : WObj} -> DirectedMor a b -> DirectedPath b c -> DirectedPath a c
cons-dirmor (m , dm) (p , dp) = m :: p , dm , dp

module _ where
  private
    encode : WObj -> Nat
    encode ε = 0
    encode var = 1
    encode (_ ⊗ _) = 2

    WObj-left' : WObj -> WObj
    WObj-left' ε = ε
    WObj-left' var = var
    WObj-left' (l ⊗ r) = l

    WObj-right' : WObj -> WObj
    WObj-right' ε = ε
    WObj-right' var = var
    WObj-right' (l ⊗ r) = r

  Discrete-WObj : Discrete WObj
  Discrete-WObj ε ε       = yes refl
  Discrete-WObj ε var     = no (\p -> zero-suc-absurd (cong encode p))
  Discrete-WObj ε (_ ⊗ _) = no (\p -> zero-suc-absurd (cong encode p))
  Discrete-WObj var ε       = no (\p -> zero-suc-absurd (cong encode (sym p)))
  Discrete-WObj var var     = yes refl
  Discrete-WObj var (_ ⊗ _) = no (\p -> zero-suc-absurd (cong pred (cong encode p)))
  Discrete-WObj (_ ⊗ _) ε = no (\p -> zero-suc-absurd (cong encode (sym p)))
  Discrete-WObj (_ ⊗ _) var = no (\p -> zero-suc-absurd (cong pred (cong encode (sym p))))
  Discrete-WObj (l1 ⊗ r1) (l2 ⊗ r2) with (Discrete-WObj l1 l2) | (Discrete-WObj r1 r2)
  ... | (no ¬pl) | _        = no (\p -> ¬pl (cong WObj-left' p))
  ... | (yes pl) | (no ¬pr) = no (\p -> ¬pr (cong WObj-right' p))
  ... | (yes pl) | (yes pr) = yes (cong2 _⊗_ pl pr)

isSet-WObj : isSet WObj
isSet-WObj = Discrete->isSet Discrete-WObj



module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C)
         (obj : Obj C) (magic : Magic) where
  open CategoryHelpers C
  open MonoidalStrHelpers MC renaming (⊗ to ⊗F)

  inj₀ : WObj -> Obj C
  inj₀ var = obj
  inj₀ ε = unit
  inj₀ (l ⊗ r) = (inj₀ l) ⊗₀ (inj₀ r)

  basic-mor->mor : {a b : WObj} -> BasicMor a b -> C [ inj₀ a , inj₀ b ]
  basic-mor->mor (α⇒' _ _ _) = α⇒
  basic-mor->mor (α⇐' _ _ _) = α⇐
  basic-mor->mor (λ⇒' _) = λ⇒
  basic-mor->mor (λ⇐' _) = λ⇐
  basic-mor->mor (ρ⇒' _) = ρ⇒
  basic-mor->mor (ρ⇐' _) = ρ⇐
  basic-mor->mor (m ⊗ˡ' w) = basic-mor->mor m ⊗₁ id C
  basic-mor->mor (w ⊗ʳ' m) = id C ⊗₁ basic-mor->mor m

  basic-path->mor : {a b : WObj} -> BasicPath a b -> C [ inj₀ a , inj₀ b ]
  basic-path->mor {a} {b} (empty p) =
    transp (\i -> C [ inj₀ a , inj₀ (p i) ]) i0 (id C)
  basic-path->mor (m :: p) = basic-mor->mor m ⋆ basic-path->mor p

  directed-path->mor : {a b : WObj} -> DirectedPath a b -> C [ inj₀ a , inj₀ b ]
  directed-path->mor (p , _) = basic-path->mor p

  dm'->mor : {a b : WObj} -> DirectedMor' a b -> C [ inj₀ a , inj₀ b ]
  dm'->mor m = basic-mor->mor (dm'->bm m)

  directed-path->mor-dp++ : {a b c : WObj} -> (p1 : DirectedPath a b) (p2 : DirectedPath b c) ->
    directed-path->mor (p1 dp++ p2) == directed-path->mor p1 ⋆ directed-path->mor p2
  directed-path->mor-dp++ {a} {b} {c} (empty p , _) p2 =
    sym ⋆-left-id >=>
    (\j ->
      (transp (\i -> C [ inj₀ a , inj₀ (p (i ∧ j)) ]) (~ j) (id C)) ⋆
      (directed-path->mor (transp (\i -> DirectedPath (p ((~ i) ∨ j)) c) j p2)))
  directed-path->mor-dp++ {a} {b} {c} (m :: p , dm , dp) p2 =
    ⋆-right (directed-path->mor-dp++ (p , dp) p2) >=>
    (sym ⋆-assoc)

  private
    P : Pred WObj _
    P o1 = (o2 : WObj) -> (isεFree o1) -> (isCanon o2) ->
           (m1 m2 : DirectedPath o1 o2) ->
           (directed-path->mor m1 == directed-path->mor m2)

    rec : (o1 : WObj) -> ((o3 : WObj) -> (WObj-length o3 < WObj-length o1 ⊎
                                          (WObj-rank o3 < WObj-rank o1 ×
                                           WObj-length o1 == WObj-length o3) -> P o3)) -> P o1
    rec o1 hyp o2 _ _ (m1@(empty p1) , _) (m2@(empty p2) , _) =
      cong basic-path->mor m1=m2
      where
      m1=m2 : m1 == m2
      m1=m2 i = empty (isSet-WObj _ _ p1 p2 i)
    rec o1 hyp o2 _ _ ((m1 :: p1) , (dm1 , dp1)) ((empty q2) , _) =
      bot-elim (irrefl-path-< (sym (cong WObj-rank q2)) r2<r1)
      where
      r2<r1 : WObj-rank o2 < WObj-rank o1
      r2<r1 = trans-≤-< (dirpath->rank≤ (p1 , dp1)) (dirmor->rank< (m1 , dm1))
    rec o1 hyp o2 _ _ ((empty q1) , _) ((m2 :: p2) , (dm2 , dp2)) =
      bot-elim (irrefl-path-< (sym (cong WObj-rank q1)) r2<r1)
      where
      r2<r1 : WObj-rank o2 < WObj-rank o1
      r2<r1 = trans-≤-< (dirpath->rank≤ (p2 , dp2)) (dirmor->rank< (m2 , dm2))

    rec os hyp ot εF-os c-ot ((_::_ {ol} m1 p1) , (dm1 , dp1))
                             ((_::_ {or} m2 p2) , (dm2 , dp2)) =
      cases (m1 , dm1) (m2 , dm2)
      where

      SubSolution1 : {os ol or : WObj} ->
                     DirectedMor' os ol -> DirectedMor' os or ->
                     Type _
      SubSolution1 {os} {ol} {or} m1 m2 =
        Σ[ os' ∈ WObj ]
        Σ[ m1' ∈ DirectedMor' ol os' ]
        Σ[ m2' ∈ DirectedMor' or os' ]
        ((dm'->mor m1 ⋆ dm'->mor m1') == (dm'->mor m2 ⋆ dm'->mor m2'))

      SubSolution : {os ol or : WObj} ->
                    DirectedMor' os ol -> DirectedMor' os or ->
                    Type _
      SubSolution {os} {ol} {or} m1 m2 =
        Σ[ os' ∈ WObj ]
        Σ[ p1 ∈ DirectedPath ol os' ]
        Σ[ p2 ∈ DirectedPath or os' ]
        ((dm'->mor m1 ⋆ directed-path->mor p1) == (dm'->mor m2 ⋆ directed-path->mor p2))

      ss1->ss : {os ol or : WObj} (m1 : DirectedMor' os ol) (m2 : DirectedMor' os or) ->
                SubSolution1 m1 m2 -> SubSolution m1 m2
      ss1->ss {os} {ol} {or} _ _ (os' , m1 , m2 , p) =
        os' ,
        (cons-dirmor (dm'->dm m1) (empty refl , _)) ,
        (cons-dirmor (dm'->dm m2) (empty refl , _)) ,
        (sym ⋆-assoc >=> (⋆-left p) >=> ⋆-assoc)

      sym-ss1 : {os ol or : WObj} (m1 : DirectedMor' os ol) (m2 : DirectedMor' os or) ->
                SubSolution1 m1 m2 -> SubSolution1 m2 m1
      sym-ss1 _ _ (os' , m1' , m2' , p) = os' , m2' , m1' , sym p

      sym-ss : {os ol or : WObj} (m1 : DirectedMor' os ol) (m2 : DirectedMor' os or) ->
               SubSolution m1 m2 -> SubSolution m2 m1
      sym-ss _ _ (os' , p1 , p2 , p) = os' , p2 , p1 , sym p

      use-subsolution :
        {ol or : WObj}
        (m1 : DirectedMor' os ol) -> (m2 : DirectedMor' os or) ->
        (p1 : DirectedPath ol ot) -> (p2 : DirectedPath or ot) ->
        SubSolution m1 m2 ->
        basic-path->mor (dm'->bm m1 :: (fst p1)) ==
        basic-path->mor (dm'->bm m2 :: (fst p2))
      use-subsolution {ol} {or} m1 m2 (p1 , dp1) (p2 , dp2)
                       (os' , q1 , q2 , m-path) =
        (\i -> basic-mor->mor (dm'->bm m1) ⋆ rec-l i) >=>
        sym ⋆-assoc >=>
        ⋆-left m-path >=>
        ⋆-assoc >=>
        (\i -> basic-mor->mor (dm'->bm m2) ⋆ rec-r (~ i))
        where

        εF-os' : isεFree os'
        εF-os' =
          dirpath-preserves-isεFree q1 (dm'-preserves-isεFree m1 εF-os)

        os'->ot : DirectedPath os' ot
        os'->ot = dirpath-to-isCanon os' ot εF-os' c-ot lp
          where
          lp : WObj-length os' == WObj-length ot
          lp = sym (dirpath->length= q1) >=> dirpath->length= (p1 , dp1)

        rec-l : basic-path->mor p1 ==
                directed-path->mor q1 ⋆ directed-path->mor os'->ot
        rec-l = hyp ol (inj-r (dm'->rank< m1 , dm'->length= m1)) ot (dm'-preserves-isεFree m1 εF-os) c-ot
                       (p1 , dp1) (q1 dp++ os'->ot) >=>
                directed-path->mor-dp++ q1 os'->ot

        rec-r : basic-path->mor p2 ==
                directed-path->mor q2 ⋆ directed-path->mor os'->ot
        rec-r = hyp or (inj-r (dm'->rank< m2 , dm'->length= m2)) ot (dm'-preserves-isεFree m2 εF-os) c-ot
                       (p2 , dp2) (q2 dp++ os'->ot) >=>
                directed-path->mor-dp++ q2 os'->ot

      use-ss :
        (m1 : DirectedMor' os ol) -> (m2 : DirectedMor' os or) ->
        SubSolution m1 m2 ->
        basic-path->mor (dm'->bm m1 :: p1) ==
        basic-path->mor (dm'->bm m2 :: p2)
      use-ss m1 m2 = use-subsolution m1 m2 (p1 , dp1) (p2 , dp2)

      use-ss1 :
        (m1 : DirectedMor' os ol) -> (m2 : DirectedMor' os or) ->
        SubSolution1 m1 m2 ->
        basic-path->mor (dm'->bm m1 :: p1) ==
        basic-path->mor (dm'->bm m2 :: p2)
      use-ss1 m1 m2 ss1 = use-ss m1 m2 (ss1->ss m1 m2 ss1)



      lr-case : {w1 w2 ol' or' : WObj} ->
                (m1 : DirectedMor' w2 ol') (m2 : DirectedMor' w1 or') ->
                SubSolution1 (m1 ⊗ˡ' w1) (w2 ⊗ʳ' m2)
      lr-case {w1} {w2} {ol'} {or'} m1 m2 = ss1
        where
        m1F = (m1 ⊗ˡ' w1)
        m2F = (w2 ⊗ʳ' m2)

        os' : WObj
        os' = (ol' ⊗ or')

        m1' : DirectedMor (w2 ⊗ or') os'
        m1' = dm'->dm (m1 ⊗ˡ' or')
        m2' : DirectedMor (ol' ⊗ w1) os'
        m2' = dm'->dm (ol' ⊗ʳ' m2)

        ss1 : SubSolution1 m1F m2F
        ss1 = os' , (ol' ⊗ʳ' m2) , (m1 ⊗ˡ' or') , (sym serialize₁₂ >=> serialize₂₁)

      ar-case : {w1 w2 w3 or' : WObj} ->
                (m : DirectedMor' w3 or') ->
                SubSolution1 (α⇒' w1 w2 w3) ((w1 ⊗ w2) ⊗ʳ' m)
      ar-case {w1} {w2} {w3} {or'} m =
        (w1 ⊗ (w2 ⊗ or')) , (w1 ⊗ʳ' (w2 ⊗ʳ' m)) , α⇒' w1 w2 or' ,
        α⇒-swap >=> ⋆-left (⊗₁-left (F-id ⊗F _))


      all-case : {w1 w2 w3 or' : WObj} ->
                 (m : DirectedMor' w1 or') ->
                 SubSolution1 (α⇒' w1 w2 w3) ((m ⊗ˡ' w2) ⊗ˡ' w3)
      all-case {w1} {w2} {w3} {or'} m =
        (or' ⊗ (w2 ⊗ w3)) , (m ⊗ˡ' (w2 ⊗ w3)) , α⇒' or' w2 w3 ,
        ⋆-right (⊗₁-right (sym (F-id ⊗F _))) >=> α⇒-swap

      alr-case : {w1 w2 w3 or' : WObj} ->
                 (m : DirectedMor' w2 or') ->
                 SubSolution1 (α⇒' w1 w2 w3) ((w1 ⊗ʳ' m) ⊗ˡ' w3)
      alr-case {w1} {w2} {w3} {or'} m =
        (w1 ⊗ (or' ⊗ w3)) , (w1 ⊗ʳ' (m ⊗ˡ' w3)) , α⇒' w1 or' w3 ,
        α⇒-swap

      aa-case : {w1 w2 w3 w4 : WObj} ->
                SubSolution (α⇒' (w1 ⊗ w2) w3  w4) ((α⇒' w1 w2 w3) ⊗ˡ' w4)
      aa-case {w1} {w2} {w3} {w4} =
        (w1 ⊗ (w2 ⊗ (w3 ⊗ w4))) ,
        cons-dirmor (dm'->dm (α⇒' w1 w2 (w3 ⊗ w4))) (empty refl , _) ,
        cons-dirmor (dm'->dm (α⇒' w1 (w2 ⊗ w3) w4))
          (cons-dirmor (dm'->dm (w1 ⊗ʳ' (α⇒' w2 w3 w4))) (empty refl , _)) ,
        sym ⋆-assoc >=>
        ⋆-left pentagon >=>
        ⋆-assoc >=>
        ⋆-assoc

      ll-case : {w1 w2 ol' or' : WObj} ->
                (m1 : DirectedMor' w1 ol') ->
                (m2 : DirectedMor' w1 or') ->
                isεFree w1 ->
                isεFree w2 ->
                w1 ⊗ w2 == os ->
                SubSolution (m1 ⊗ˡ' w2) (m2 ⊗ˡ' w2)
      ll-case {w1} {w2} {ol'} {or'} m1 m2 εF-w1 εF-w2 w1⊗w2=os =
        (canon' w1) ⊗ w2 ,
        lift-path p1' ,
        lift-path p2' ,
        same-path
        where
        ot' = (canon' w1)
        c-ot' = proj₂ (∃!-prop (∃!canon (WObj-length w1)))
        lp-ot' = proj₁ (∃!-prop (∃!canon (WObj-length w1)))
        p1' : DirectedPath ol' ot'
        p1' = dirpath-to-isCanon ol' ot' (dm'-preserves-isεFree m1 εF-w1)
                c-ot' (sym (lp-ot' >=> dm'->length= m1))
        p2' : DirectedPath or' ot'
        p2' = dirpath-to-isCanon or' ot' (dm'-preserves-isεFree m2 εF-w1)
                c-ot' (sym (lp-ot' >=> dm'->length= m2))

        l1<l12 : WObj-length w1 < WObj-length os
        l1<l12 =
          trans-<-= (trans-=-< (sym +'-right-zero) (+₁-preserves-< (εF-0<length w2 εF-w2)))
                    (cong WObj-length w1⊗w2=os)

        sub-ans : directed-path->mor (cons-dirmor (dm'->dm m1) p1') ==
                  directed-path->mor (cons-dirmor (dm'->dm m2) p2')
        sub-ans =
          hyp w1 (inj-l l1<l12) ot' εF-w1 c-ot'
            (cons-dirmor (dm'->dm m1) p1') (cons-dirmor (dm'->dm m2) p2')

        lift-path : {o1 o2 : WObj} -> DirectedPath o1 o2 -> DirectedPath (o1 ⊗ w2) (o2 ⊗ w2)
        lift-path (empty p , _) = (empty (cong (_⊗ w2) p) , tt)
        lift-path (m :: p , (dm , dp)) =
          let (p2 , dp2) = lift-path (p , dp) in
          ((m ⊗ˡ' w2) :: p2) , dm , dp2

        directed-path->mor-lift-path : {o1 o2 : WObj} -> (p : DirectedPath o1 o2) ->
          directed-path->mor (lift-path p) == (directed-path->mor p) ⊗₁ id C
        directed-path->mor-lift-path {o1} {o2} ep@(empty p , _) = ans2
          where
          ans2 : transport (\i -> C [ inj₀ (o1 ⊗ w2) , inj₀ (p i ⊗ w2) ]) (id C) ==
                 F-mor ⊗F (directed-path->mor ep , id C)
          ans2 =
            transP-sym
              (symP (transport-filler (\i -> C [ inj₀ (o1 ⊗ w2) , inj₀ (p i ⊗ w2) ]) (id C)))
              (transP-right
                (sym (F-id ⊗F (inj₀ o1 , inj₀ w2)))
                (\i -> F-mor ⊗F (transport-filler (\j -> C [ inj₀ o1 , inj₀ (p j) ]) (id C) i ,
                                 id C)))
        directed-path->mor-lift-path (m :: p , dm , dp) =
          ⋆-right (directed-path->mor-lift-path (p , dp)) >=>
          sym split₁ˡ

        same-path : directed-path->mor (lift-path (cons-dirmor (dm'->dm m1) p1')) ==
                    directed-path->mor (lift-path (cons-dirmor (dm'->dm m2) p2'))
        same-path =
          ⋆-right (directed-path->mor-lift-path p1') >=>
          sym split₁ˡ >=>
          ⊗₁-left sub-ans >=>
          split₁ˡ >=>
          sym (⋆-right (directed-path->mor-lift-path p2'))

      rr-case : {w1 w2 ol' or' : WObj} ->
                (m1 : DirectedMor' w2 ol') ->
                (m2 : DirectedMor' w2 or') ->
                isεFree w1 ->
                isεFree w2 ->
                w1 ⊗ w2 == os ->
                SubSolution (w1 ⊗ʳ' m1) (w1 ⊗ʳ' m2)
      rr-case {w1} {w2} {ol'} {or'} m1 m2 εF-w1 εF-w2 w1⊗w2=os =
        w1 ⊗ (canon' w2) ,
        lift-path p1' ,
        lift-path p2' ,
        same-path
        where
        ot' = (canon' w2)
        c-ot' = proj₂ (∃!-prop (∃!canon (WObj-length w2)))
        lp-ot' = proj₁ (∃!-prop (∃!canon (WObj-length w2)))
        p1' : DirectedPath ol' ot'
        p1' = dirpath-to-isCanon ol' ot' (dm'-preserves-isεFree m1 εF-w2)
                c-ot' (sym (lp-ot' >=> dm'->length= m1))
        p2' : DirectedPath or' ot'
        p2' = dirpath-to-isCanon or' ot' (dm'-preserves-isεFree m2 εF-w2)
                c-ot' (sym (lp-ot' >=> dm'->length= m2))

        l1<l12 : WObj-length w2 < WObj-length os
        l1<l12 =
          trans-<-= (trans-=-< (sym +'-left-zero) (+₂-preserves-< (εF-0<length w1 εF-w1)))
                    (cong WObj-length w1⊗w2=os)

        sub-ans : directed-path->mor (cons-dirmor (dm'->dm m1) p1') ==
                  directed-path->mor (cons-dirmor (dm'->dm m2) p2')
        sub-ans =
          hyp w2 (inj-l l1<l12) ot' εF-w2 c-ot'
            (cons-dirmor (dm'->dm m1) p1') (cons-dirmor (dm'->dm m2) p2')

        lift-path : {o1 o2 : WObj} -> DirectedPath o1 o2 -> DirectedPath (w1 ⊗ o1) (w1 ⊗ o2)
        lift-path (empty p , _) = (empty (cong (w1 ⊗_) p) , tt)
        lift-path (m :: p , (dm , dp)) =
          let (p2 , dp2) = lift-path (p , dp) in
          ((w1 ⊗ʳ' m) :: p2) , dm , dp2

        directed-path->mor-lift-path : {o1 o2 : WObj} -> (p : DirectedPath o1 o2) ->
          directed-path->mor (lift-path p) == id C ⊗₁ (directed-path->mor p)
        directed-path->mor-lift-path {o1} {o2} ep@(empty p , _) = ans2
          where
          ans2 : transport (\i -> C [ inj₀ (w1 ⊗ o1) , inj₀ (w1 ⊗ p i) ]) (id C) ==
                 F-mor ⊗F (id C , directed-path->mor ep)
          ans2 =
            transP-sym
              (symP (transport-filler (\i -> C [ inj₀ (w1 ⊗ o1) , inj₀ (w1 ⊗ p i) ]) (id C)))
              (transP-right
                (sym (F-id ⊗F (inj₀ w1 , inj₀ o1)))
                (\i -> F-mor ⊗F (id C ,
                                 transport-filler (\j -> C [ inj₀ o1 , inj₀ (p j) ]) (id C) i)))
        directed-path->mor-lift-path (m :: p , dm , dp) =
          ⋆-right (directed-path->mor-lift-path (p , dp)) >=>
          sym split₂ˡ

        same-path : directed-path->mor (lift-path (cons-dirmor (dm'->dm m1) p1')) ==
                    directed-path->mor (lift-path (cons-dirmor (dm'->dm m2) p2'))
        same-path =
          ⋆-right (directed-path->mor-lift-path p1') >=>
          sym split₂ˡ >=>
          ⊗₁-right sub-ans >=>
          split₂ˡ >=>
          sym (⋆-right (directed-path->mor-lift-path p2'))




      cases' : (m1 : DirectedMor' os ol) (m2 : DirectedMor' os or) ->
               basic-path->mor (dm'->bm m1 :: p1) == basic-path->mor (dm'->bm m2 :: p2)
      cases' m1@(α⇒' o1 o2 o3) m2@(α⇒' o1 o2 o3) =
        cong (α⇒ ⋆_) p1=p2
        where
        p1=p2 : basic-path->mor p1 == basic-path->mor p2
        p1=p2 =
          let ((εF1 , εF2) , εF3) = εF-os in
          hyp ol (inj-r (dm'->rank< m1 , dm'->length= m1)) ot
              (εF1 , (εF2 , εF3)) c-ot (p1 , dp1) (p2 , dp2)

      cases' m1F@(m1 ⊗ˡ' w1) m2F@(w2 ⊗ʳ' m2) =
        use-ss1 m1F m2F (lr-case m1 m2)
      cases' m1F@(w1 ⊗ʳ' m1) m2F@(m2 ⊗ˡ' w2) =
        use-ss1 m1F m2F (sym-ss1 m2F m1F (lr-case m2 m1))
      cases' m1F@(α⇒' o1 o2 o3) m2F@(_ ⊗ʳ' m)      =
        use-ss1 m1F m2F (ar-case m)
      cases' m1F@(_ ⊗ʳ' m)      m2F@(α⇒' o1 o2 o3) =
        use-ss1 m1F m2F (sym-ss1 m2F m1F (ar-case m))
      cases' m1F@(α⇒' o1 o2 o3)     m2F@((m ⊗ˡ' _) ⊗ˡ' _) =
        use-ss1 m1F m2F (all-case m)
      cases' m1F@((m ⊗ˡ' _) ⊗ˡ' _)  m2F@(α⇒' o1 o2 o3)    =
        use-ss1 m1F m2F (sym-ss1 m2F m1F (all-case m))
      cases' m1F@(α⇒' o1 o2 o3) m2F@((_ ⊗ʳ' m) ⊗ˡ' _)      =
        use-ss1 m1F m2F (alr-case m)
      cases' m1F@((_ ⊗ʳ' m) ⊗ˡ' _)      m2F@(α⇒' o1 o2 o3) =
        use-ss1 m1F m2F (sym-ss1 m2F m1F (alr-case m))

      cases' m1F@(α⇒' o1 o2 o3) m2F@((α⇒' _ _ _) ⊗ˡ' _)    =
        use-ss m1F m2F aa-case
      cases' m1F@((α⇒' _ _ _) ⊗ˡ' _)    m2F@(α⇒' o1 o2 o3) =
        use-ss m1F m2F (sym-ss m2F m1F aa-case)

      cases' m1F@(m1 ⊗ˡ' w) m2F@(m2 ⊗ˡ' w) =
        use-ss m1F m2F (ll-case m1 m2 (proj₁ εF-os) (proj₂ εF-os) refl)
      cases' m1F@(w ⊗ʳ' m1) m2F@(w ⊗ʳ' m2) =
        use-ss m1F m2F (rr-case m1 m2 (proj₁ εF-os) (proj₂ εF-os) refl)

      cases : {o : WObj} (m1 : DirectedMor o ol) (m2 : DirectedMor o or) ->
              basic-path->mor (fst m1 :: p1) == basic-path->mor (fst m2 :: p2)
      cases {o} (α⇒' a b c , _) = magic
        -- where
        -- sub : (m2 : DirectedMor o or) -> basic-path->mor ((α⇒' a b c) :: p1) ==
        --                                  basic-path->mor (fst m2 :: p2)
        -- sub = magic
      cases {o} (m ⊗ˡ' w2 , _) = magic
      cases {o} (w1 ⊗ʳ' m , _) = magic

    parallel-dirpaths-to-canon : ∀ o -> P o
    parallel-dirpaths-to-canon = rank-length-induction rec
