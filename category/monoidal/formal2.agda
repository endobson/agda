{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal2 where

open import additive-group
open import additive-group.instances.nat
open import base
open import category.base
open import category.constructions.product
open import category.constructions.triple-product
open import category.monoidal.base
open import equality
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


-- canon-suc-reduce : {n : Nat} -> 0 < n -> canon (suc n) == var ⊗ (canon n)
-- canon-suc-reduce {zero} 0<0 = bot-elim (zero-≮ 0<0)
-- canon-suc-reduce {suc n} _ = refl
--
-- canon-εF-assoc : (o1 o2 o3 : Obj) (εF1 : isεFree o1) (εF2 : isεFree o2) (εF1 : isεFree or2)

-- canon-εF-path : (o : WObj) -> (εF : isεFree o) -> canon-εF o εF == canon (WObj-length o)
-- canon-εF-path = rank-induction rec
--   where
--   rec : (o1 : WObj) ->
--         ((o2 : WObj) -> WObj-rank o2 < WObj-rank o1 ->
--               (εF : isεFree o2) -> canon-εF o2 εF == canon (WObj-length o2)) ->
--         (εF : isεFree o1) -> canon-εF o1 εF == canon (WObj-length o1)
--   rec var hyp _ = refl
--   rec (var ⊗ o) hyp (_ , εF) =
--     cong (var ⊗_) (rec o hyp εF) >=>
--     (sym (canon-suc-reduce (εF-0<length o εF)))
--   rec ((o1 ⊗ o2) ⊗ o3) hyp ((εF1 , εF2) , εF3) =
--     ? >=>
--     hyp (o1 ⊗ (o2 ⊗ o3)) (assoc-rank< o1 o2 o3) (εF1 , (εF2 , εF3)) >=>
--     ?

-- canon-εF' : (o : WObj) -> isεFree o -> WObj
-- canon-εF' = \o -> strong-induction'
--
-- canon-εF' (var ⊗ o) (_ , εF) = var ⊗ (canon-εF o εF)
-- canon-εF' ((o1 ⊗ o2) ⊗ o3) ((εF1 , εF2) , εF3) =
--   canon-εF (o1 ⊗ (o2 ⊗ o3)) (εF1 , (εF2 , εF3))



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



dirpath->rank≤ : {o1 o2 : WObj} -> DirectedPath o1 o2 -> WObj-rank o2 ≤ WObj-rank o1
dirpath->rank≤ (empty p , _) = path-≤ (cong WObj-rank (sym p))
dirpath->rank≤ ((m :: p) , dm , dp) =
  trans-≤ (dirpath->rank≤ (p , dp)) (weaken-< (dirmor->rank< (m , dm)))

dirpath->length= : {o1 o2 : WObj} -> DirectedPath o1 o2 -> WObj-length o1 == WObj-length o2
dirpath->length= (empty p , _) = cong WObj-length p
dirpath->length= ((m :: p) , dm , dp) =
  dirmor->length= (m , dm) >=> dirpath->length= (p , dp)


WObj-left : (o : WObj) -> is⊗ o -> WObj
WObj-left (l ⊗ r) _ = l

WObj-right : (o : WObj) -> is⊗ o -> WObj
WObj-right (l ⊗ r) _ = r

cons-dirmor : {a b c : WObj} -> DirectedMor a b -> DirectedPath b c -> DirectedPath a c
cons-dirmor (m , dm) (p , dp) = m :: p , dm , dp

module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C)
         (obj : Obj C) (magic : Magic) where
  open CategoryHelpers C
  open MonoidalStrHelpers MC renaming (⊗ to ⊗F)

  isSet-WObj : isSet WObj
  isSet-WObj = magic

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
    transport (\i -> C [ inj₀ a , inj₀ (p i) ]) (id C)
  basic-path->mor (m :: p) = basic-mor->mor m ⋆ basic-path->mor p

  directed-path->mor : {a b : WObj} -> DirectedPath a b -> C [ inj₀ a , inj₀ b ]
  directed-path->mor (p , _) = basic-path->mor p

  dm'->mor : {a b : WObj} -> DirectedMor' a b -> C [ inj₀ a , inj₀ b ]
  dm'->mor m = basic-mor->mor (dm'->bm m)

  private
    P : Pred WObj _
    P o1 = (o2 : WObj) -> (isεFree o1) -> (isCanon o2) ->
           (m1 m2 : DirectedPath o1 o2) ->
           (directed-path->mor m1 == directed-path->mor m2)

    rec : (o1 : WObj) -> ((o3 : WObj) -> WObj-rank o3 < WObj-rank o1 -> P o3) -> P o1
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
      cases m1 m2 {dm1} {dm2}
      where
      cases : {o : WObj} (m1 : BasicMor o ol) (m2 : BasicMor o or) ->
              {isDirectedMor m1} -> {isDirectedMor m2} ->
              basic-path->mor (m1 :: p1) == basic-path->mor (m2 :: p2)
      cases = magic

      SubSolution1 : {os ol or : WObj} ->
                     DirectedMor' os ol -> DirectedMor' os or ->
                     Type _
      SubSolution1 {os} {ol} {or} m1 m2 =
        Σ[ os' ∈ WObj ]
        Σ[ m1' ∈ DirectedMor' ol os' ]
        Σ[ m2' ∈ DirectedMor' or os' ]
        ((dm'->mor m1 ⋆ dm'->mor m1') == (dm'->mor m2 ⋆ dm'->mor m2'))

      sym-ss : {os ol or : WObj} (m1 : DirectedMor' os ol) (m2 : DirectedMor' os or) ->
               SubSolution1 m1 m2 -> SubSolution1 m2 m1
      sym-ss _ _ (os' , m1' , m2' , p) = os' , m2' , m1' , sym p


      use-subsolution :
        {ol or : WObj}
        (m1 : DirectedMor' os ol) -> (m2 : DirectedMor' os or) ->
        (p1 : DirectedPath ol ot) -> (p2 : DirectedPath or ot) ->
        SubSolution1 m1 m2 ->
        basic-path->mor (dm'->bm m1 :: (fst p1)) ==
        basic-path->mor (dm'->bm m2 :: (fst p2))
      use-subsolution {ol} {or} m1 m2 (p1 , dp1) (p2 , dp2)
                      (os' , m1' , m2' , m-path) =
        (\i -> basic-mor->mor (dm'->bm m1) ⋆ rec-l i) >=>
        sym ⋆-assoc >=>
        ⋆-left m-path >=>
        ⋆-assoc >=>
        (\i -> basic-mor->mor (dm'->bm m2) ⋆ rec-r (~ i))
        where

        εF-os' : isεFree os'
        εF-os' =
          dm'-preserves-isεFree m1' (dm'-preserves-isεFree m1 εF-os)

        os'->ot : DirectedPath os' ot
        os'->ot = dirpath-to-isCanon os' ot εF-os' c-ot lp
          where
          lp : WObj-length os' == WObj-length ot
          lp = sym (dm'->length= m1') >=> dirpath->length= (p1 , dp1)

        rec-l : basic-path->mor p1 ==
                directed-path->mor (cons-dirmor (dm'->dm m1') os'->ot)
        rec-l = hyp ol (dm'->rank< m1) ot (dm'-preserves-isεFree m1 εF-os) c-ot
                       (p1 , dp1) (cons-dirmor (dm'->dm m1') os'->ot)

        rec-r : basic-path->mor p2 ==
                directed-path->mor (cons-dirmor (dm'->dm m2') os'->ot)
        rec-r = hyp or (dm'->rank< m2) ot (dm'-preserves-isεFree m2 εF-os) c-ot
                       (p2 , dp2) (cons-dirmor (dm'->dm m2') os'->ot)


      use-ss :
        (m1 : DirectedMor' os ol) -> (m2 : DirectedMor' os or) ->
        SubSolution1 m1 m2 ->
        basic-path->mor (dm'->bm m1 :: p1) ==
        basic-path->mor (dm'->bm m2 :: p2)
      use-ss m1 m2 = use-subsolution m1 m2 (p1 , dp1) (p2 , dp2)


      lr-case : {w1 w2 ol' or' : WObj} ->
                (m1 : DirectedMor' w2 ol') (m2 : DirectedMor' w1 or') ->
                SubSolution1 (m1 ⊗ˡ' w1) (w2 ⊗ʳ' m2)
      lr-case {w1} {w2} {ol'} {or'} m1 m2 = ss
        where
        m1F = (m1 ⊗ˡ' w1)
        m2F = (w2 ⊗ʳ' m2)

        os' : WObj
        os' = (ol' ⊗ or')

        m1' : DirectedMor (w2 ⊗ or') os'
        m1' = dm'->dm (m1 ⊗ˡ' or')
        m2' : DirectedMor (ol' ⊗ w1) os'
        m2' = dm'->dm (ol' ⊗ʳ' m2)

        ss : SubSolution1 m1F m2F
        ss = os' , (ol' ⊗ʳ' m2) , (m1 ⊗ˡ' or') , (sym serialize₁₂ >=> serialize₂₁)

      ar-case : {w1 w2 w3 or' : WObj} ->
                (m : DirectedMor' w3 or') ->
                SubSolution1 (α⇒' w1 w2 w3) ((w1 ⊗ w2) ⊗ʳ' m)
      ar-case {w1} {w2} {w3} {or'} m =
        (w1 ⊗ (w2 ⊗ or')) , (w1 ⊗ʳ' (w2 ⊗ʳ' m)) , α⇒' w1 w2 or' ,
        α⇒-swap >=> ⋆-left (⊗₁-left (F-id ⊗F _))


      cases' : (m1 : DirectedMor' os ol) (m2 : DirectedMor' os or) ->
               basic-path->mor (dm'->bm m1 :: p1) == basic-path->mor (dm'->bm m2 :: p2)
      cases' m1@(α⇒' o1 o2 o3) m2@(α⇒' o1 o2 o3) =
        cong (α⇒ ⋆_) p1=p2
        where
        p1=p2 : basic-path->mor p1 == basic-path->mor p2
        p1=p2 =
          let ((εF1 , εF2) , εF3) = εF-os in
          hyp ol (dm'->rank< m1) ot (εF1 , (εF2 , εF3)) c-ot (p1 , dp1) (p2 , dp2)

      cases' m1F@(m1 ⊗ˡ' w1) m2F@(w2 ⊗ʳ' m2) =
        use-ss m1F m2F (lr-case m1 m2)
      cases' m1F@(w1 ⊗ʳ' m1) m2F@(m2 ⊗ˡ' w2) =
        use-ss m1F m2F (sym-ss m2F m1F (lr-case m2 m1))
      cases' m1F@(α⇒' o1 o2 o3) m2F@(_ ⊗ʳ' m)      =
        use-ss m1F m2F (ar-case m)
      cases' m1F@(_ ⊗ʳ' m)      m2F@(α⇒' o1 o2 o3) =
        use-ss m1F m2F (sym-ss m2F m1F (ar-case m))


      cases' (α⇒' o1 o2 o3) (_ ⊗ˡ' _)      = magic
      cases' (_ ⊗ˡ' _)      (α⇒' o1 o2 o3) = magic
      cases' (_ ⊗ˡ' _)      (_ ⊗ˡ' _)      = magic
      cases' (_ ⊗ʳ' _)      (_ ⊗ʳ' _)      = magic

    parallel-dirpaths-to-canon : ∀ o -> P o
    parallel-dirpaths-to-canon = rank-induction rec
