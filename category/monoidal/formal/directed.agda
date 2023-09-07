{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal.directed where

open import additive-group
open import additive-group.instances.nat
open import base
open import boolean
open import category.base
open import category.constructions.product
open import category.constructions.triple-product
open import category.monoidal.base
open import category.monoidal.formal.base
open import cubical
open import equality-path
open import hlevel
open import nat
open import nat.order
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import relation
open import sigma.base
open import sum
open import truncation

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

isRTree : Pred WObj ℓ-zero
isRTree ε = Bot
isRTree var = Top
isRTree (a ⊗ b) = isVar a × isRTree b

isCanon : Pred WObj ℓ-zero
isCanon ε = Top
isCanon m@var = isRTree m
isCanon m@(_ ⊗ _) = isRTree m

isProp-isRTree : (o : WObj) -> isProp (isRTree o)
isProp-isRTree ε = isPropBot
isProp-isRTree var = isPropTop
isProp-isRTree (a ⊗ b) = isProp× (isProp-isVar a) (isProp-isRTree b)

isProp-isCanon : (o : WObj) -> isProp (isCanon o)
isProp-isCanon ε = isPropTop
isProp-isCanon m@var = isProp-isRTree m
isProp-isCanon m@(_ ⊗ _) = isProp-isRTree m

isRTree->isεFree : (o : WObj) -> isRTree o -> isεFree o
isRTree->isεFree var tt = tt
isRTree->isεFree (var ⊗ o) (tt , rt) = tt , (isRTree->isεFree o rt)

split-isCanon : (o : WObj) -> isCanon o -> isε o ⊎ isRTree o
split-isCanon ε x = inj-l x
split-isCanon var x = inj-r x
split-isCanon (_ ⊗ _) x = inj-r x

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

dirmor->is⊗₂ : {a b : WObj} -> DirectedMor a b -> is⊗ b
dirmor->is⊗₂ (α⇒' a b c , tt) = tt
dirmor->is⊗₂ (m ⊗ˡ' w , _) = tt
dirmor->is⊗₂ (w ⊗ʳ' m , _) = tt


dirmor-preserves-isεFree : {a b : WObj} -> DirectedMor a b -> isεFree a -> isεFree b
dirmor-preserves-isεFree (α⇒' a b c , tt) ((εF1 , εF2) , εF3) = εF1 , (εF2 , εF3)
dirmor-preserves-isεFree (m ⊗ˡ' w , dm) (εF1 , εF2) = dirmor-preserves-isεFree (m , dm) εF1 , εF2
dirmor-preserves-isεFree (w ⊗ʳ' m , dm) (εF1 , εF2) = εF1 , dirmor-preserves-isεFree (m , dm) εF2

dirmor-reflects-isεFree : {a b : WObj} -> DirectedMor a b -> isεFree b -> isεFree a
dirmor-reflects-isεFree (α⇒' a b c , tt) (εF1 , (εF2 , εF3)) = ((εF1 , εF2) , εF3)
dirmor-reflects-isεFree (m ⊗ˡ' w , dm) (εF1 , εF2) = dirmor-reflects-isεFree (m , dm) εF1 , εF2
dirmor-reflects-isεFree (w ⊗ʳ' m , dm) (εF1 , εF2) = εF1 , dirmor-reflects-isεFree (m , dm) εF2

dirpath-preserves-isεFree : {a b : WObj} -> DirectedPath a b -> isεFree a -> isεFree b
dirpath-preserves-isεFree (empty p , _) = transport (\i -> isεFree (p i))
dirpath-preserves-isεFree (m :: p , dm , dp) εF =
  dirpath-preserves-isεFree (p , dp) (dirmor-preserves-isεFree (m , dm) εF)

dirpath-reflects-isεFree : {a b : WObj} -> DirectedPath a b -> isεFree b -> isεFree a
dirpath-reflects-isεFree (empty p , _) = transport (\i -> isεFree (p (~ i)))
dirpath-reflects-isεFree (m :: p , dm , dp) εF =
  dirmor-reflects-isεFree (m , dm) (dirpath-reflects-isεFree (p , dp) εF)

dirpath-preserves-isε : {a b : WObj} -> DirectedPath a b -> isε a -> isε b
dirpath-preserves-isε (empty p , _) = transport (\i -> isε (p i))
dirpath-preserves-isε ((α⇒' _ _ _) :: p , dm , dp) iε = bot-elim iε
dirpath-preserves-isε ((_ ⊗ˡ' _) :: p , dm , dp) iε = bot-elim iε
dirpath-preserves-isε ((_ ⊗ʳ' _) :: p , dm , dp) iε = bot-elim iε

dirpath-reflects-isε : {a b : WObj} -> DirectedPath a b -> isε b -> isε a
dirpath-reflects-isε (empty p , _) = transport (\i -> isε (p (~ i)))
dirpath-reflects-isε ((α⇒' _ _ _) :: p , dm , dp) iε =
  dirpath-reflects-isε (p , dp) iε
dirpath-reflects-isε ((_ ⊗ˡ' _) :: p , dm , dp) iε =
  dirpath-reflects-isε (p , dp) iε
dirpath-reflects-isε ((_ ⊗ʳ' _) :: p , dm , dp) iε =
  dirpath-reflects-isε (p , dp) iε


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

cons-dirmor : {a b c : WObj} -> DirectedMor a b -> DirectedPath b c -> DirectedPath a c
cons-dirmor (m , dm) (p , dp) = m :: p , dm , dp

dirmor-lift-⊗ˡ : {o1 o2 : WObj} -> DirectedMor o1 o2 -> (o3 : WObj) -> DirectedMor (o1 ⊗ o3) (o2 ⊗ o3)
dirmor-lift-⊗ˡ (m , dm) o = (m ⊗ˡ' o , dm)

dirmor-lift-⊗ʳ : (o1 : WObj) {o2 o3 : WObj} -> DirectedMor o2 o3  -> DirectedMor (o1 ⊗ o2) (o1 ⊗ o3)
dirmor-lift-⊗ʳ o (m , dm) = (o ⊗ʳ' m , dm)

dm-cases : {ℓ : Level} {P : {o1 o2 : WObj} -> (DirectedMor o1 o2) -> Type ℓ} ->
           (∀ a b c -> (P (α⇒' a b c , tt))) ->
           (∀ {o1 o2} (m : DirectedMor o1 o2) -> (w : WObj) -> (P (fst m ⊗ˡ' w , snd m))) ->
           (∀ {o1 o2} (m : DirectedMor o1 o2) -> (w : WObj) -> (P (w ⊗ʳ' fst m , snd m))) ->
           {o1 o2 : WObj} (m : DirectedMor o1 o2) -> P m
dm-cases f1 f2 f3 (α⇒' a b c , _) = f1 a b c
dm-cases f1 f2 f3 (m ⊗ˡ' w , dm) = f2 (m , dm) w
dm-cases f1 f2 f3 (w ⊗ʳ' m , dm) = f3 (m , dm) w


module InMonoidalDir {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C)
         (obj : Obj C) where
  open CategoryHelpers C
  open MonoidalStrHelpers MC renaming (⊗ to ⊗F)
  open InMonoidal MC obj

  directed-path->mor : {a b : WObj} -> DirectedPath a b -> C [ inj₀ a , inj₀ b ]
  directed-path->mor (p , _) = basic-path->mor p

  dm->mor : {a b : WObj} -> DirectedMor a b -> C [ inj₀ a , inj₀ b ]
  dm->mor (m , _)= basic-mor->mor m

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
    Hyp : Pred WObj _
    Hyp o = (o2 : WObj) -> (WObj-length o2 < WObj-length o ⊎
                            (WObj-rank o2 < WObj-rank o ×
                             WObj-length o == WObj-length o2)) -> P o2

  record SubSolution {os ol or : WObj} (m1 : DirectedMor os ol) (m2 : DirectedMor os or) : Type ℓM where
    constructor sub-solution
    field
      {os'} : WObj
      p1 : DirectedPath ol os'
      p2 : DirectedPath or os'
      path : (dm->mor m1 ⋆ directed-path->mor p1) == (dm->mor m2 ⋆ directed-path->mor p2)

  sub-solution1 : {os ol or os' : WObj} {m1 : DirectedMor os ol} {m2 : DirectedMor os or} ->
    (p1 : DirectedMor ol os')
    (p2 : DirectedMor or os')
    (path : (dm->mor m1 ⋆ dm->mor p1) == (dm->mor m2 ⋆ dm->mor p2)) ->
    SubSolution m1 m2
  sub-solution1 m1 m2 p = sub-solution
    (cons-dirmor m1 (empty refl , _))
    (cons-dirmor m2 (empty refl , _))
    (sym ⋆-assoc >=> (⋆-left p) >=> ⋆-assoc)

  sym-ss : {os ol or : WObj} {m1 : DirectedMor os ol} {m2 : DirectedMor os or} ->
           SubSolution m1 m2 -> SubSolution m2 m1
  sym-ss (sub-solution p1 p2 p) = sub-solution p2 p1 (sym p)

  opaque
    lr-case : {w1 w2 ol' or' : WObj} ->
              (m1 : DirectedMor w2 ol') (m2 : DirectedMor w1 or') ->
              SubSolution (fst m1 ⊗ˡ' w1 , snd m1) (w2 ⊗ʳ' fst m2 , snd m2)
    lr-case {w1} {w2} {ol'} {or'} m1 m2 =
      sub-solution1 m2' m1' (sym serialize₁₂ >=> serialize₂₁)
      where
      m1F : DirectedMor (w2 ⊗ w1) (ol' ⊗ w1)
      m1F = (fst m1 ⊗ˡ' w1 , snd m1)
      m2F : DirectedMor (w2 ⊗ w1) (w2 ⊗ or')
      m2F = (w2 ⊗ʳ' fst m2 , snd m2)

      os' : WObj
      os' = (ol' ⊗ or')

      m1' : DirectedMor (w2 ⊗ or') os'
      m1' = fst m1 ⊗ˡ' or' , snd m1
      m2' : DirectedMor (ol' ⊗ w1) os'
      m2' = ol' ⊗ʳ' fst m2 , snd m2

    ar-case : {w1 w2 w3 or' : WObj} ->
              (m : DirectedMor w3 or') ->
              SubSolution (α⇒' w1 w2 w3 , tt) ((w1 ⊗ w2) ⊗ʳ' fst m , snd m)
    ar-case {w1} {w2} {w3} {or'} (m , dm) =
      sub-solution1 (w1 ⊗ʳ' (w2 ⊗ʳ' m) , dm) (α⇒' w1 w2 or' , tt)
       (α⇒-swap >=> ⋆-left (⊗₁-left (F-id ⊗F _)))

    all-case : {w1 w2 w3 or' : WObj} ->
               (m : DirectedMor w1 or') ->
               SubSolution (α⇒' w1 w2 w3 , tt) ((fst m ⊗ˡ' w2) ⊗ˡ' w3 , snd m)
    all-case {w1} {w2} {w3} {or'} (m , dm) =
      sub-solution1 (m ⊗ˡ' (w2 ⊗ w3) , dm) (α⇒' or' w2 w3 , tt)
        (⋆-right (⊗₁-right (sym (F-id ⊗F _))) >=> α⇒-swap)

    alr-case : {w1 w2 w3 or' : WObj} ->
               (m : DirectedMor w2 or') ->
               SubSolution (α⇒' w1 w2 w3 , tt) ((w1 ⊗ʳ' fst m) ⊗ˡ' w3 , snd m)
    alr-case {w1} {w2} {w3} {or'} (m , dm) =
      sub-solution1 (w1 ⊗ʳ' (m ⊗ˡ' w3) , dm) (α⇒' w1 or' w3 , tt) α⇒-swap

    aa-case : {w1 w2 w3 w4 : WObj} ->
              SubSolution (α⇒' (w1 ⊗ w2) w3  w4 , tt) ((α⇒' w1 w2 w3) ⊗ˡ' w4 , tt)
    aa-case {w1} {w2} {w3} {w4} = sub-solution
      (cons-dirmor (α⇒' w1 w2 (w3 ⊗ w4) , tt) (empty refl , _))
      (cons-dirmor (α⇒' w1 (w2 ⊗ w3) w4 , tt)
        (cons-dirmor (w1 ⊗ʳ' (α⇒' w2 w3 w4) , tt) (empty refl , _)))
      (sym ⋆-assoc >=>
       ⋆-left pentagon >=>
       ⋆-assoc >=>
       ⋆-assoc)

    a-case : (o1 o2 o3 : WObj) -> SubSolution (α⇒' o1 o2 o3 , tt) (α⇒' o1 o2 o3 , tt)
    a-case o1 o2 o3 = sub-solution (empty refl , tt) (empty refl , tt) refl

    rr-case : {w1 w2 ol' or' : WObj} ->
              Hyp (w1 ⊗ w2) ->
              (m1 : DirectedMor w2 ol') ->
              (m2 : DirectedMor w2 or') ->
              isεFree w1 ->
              isεFree w2 ->
              SubSolution (w1 ⊗ʳ' fst m1 , snd m1) (w1 ⊗ʳ' fst m2 , snd m2)
    rr-case {w1} {w2} {ol'} {or'} hyp m1 m2 εF-w1 εF-w2 =
      sub-solution (lift-path p1') (lift-path p2') same-path
      where
      ot' : WObj
      ot' = (canon' w2)
      c-ot' : isCanon ot'
      c-ot' = proj₂ (∃!-prop (∃!canon (WObj-length w2)))
      lp-ot' : WObj-length ot' == WObj-length w2
      lp-ot' = proj₁ (∃!-prop (∃!canon (WObj-length w2)))
      p1' : DirectedPath ol' ot'
      p1' = dirpath-to-isCanon ol' ot' (dirmor-preserves-isεFree m1 εF-w2)
              c-ot' (sym (lp-ot' >=> dirmor->length= m1))
      p2' : DirectedPath or' ot'
      p2' = dirpath-to-isCanon or' ot' (dirmor-preserves-isεFree m2 εF-w2)
              c-ot' (sym (lp-ot' >=> dirmor->length= m2))

      l1<l12 : WObj-length w2 < WObj-length (w1 ⊗ w2)
      l1<l12 = (trans-=-< (sym +'-left-zero) (+₂-preserves-< (εF-0<length w1 εF-w1)))

      sub-ans : directed-path->mor (cons-dirmor m1 p1') ==
                directed-path->mor (cons-dirmor m2 p2')
      sub-ans =
        hyp w2 (inj-l l1<l12) ot' εF-w2 c-ot'
          (cons-dirmor m1 p1') (cons-dirmor m2 p2')

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

      same-path : directed-path->mor (lift-path (cons-dirmor m1 p1')) ==
                  directed-path->mor (lift-path (cons-dirmor m2 p2'))
      same-path =
        ⋆-right (directed-path->mor-lift-path p1') >=>
        sym split₂ˡ >=>
        ⊗₁-right sub-ans >=>
        split₂ˡ >=>
        sym (⋆-right (directed-path->mor-lift-path p2'))


    ll-case : {w1 w2 ol' or' : WObj} ->
              (Hyp (w1 ⊗ w2)) ->
              (m1 : DirectedMor w1 ol') ->
              (m2 : DirectedMor w1 or') ->
              isεFree w1 ->
              isεFree w2 ->
              SubSolution (fst m1 ⊗ˡ' w2 , snd m1) (fst m2 ⊗ˡ' w2 , snd m2)
    ll-case {w1} {w2} {ol'} {or'} hyp m1 m2 εF-w1 εF-w2 =
      sub-solution (lift-path p1') (lift-path p2') same-path
      where
      ot' : WObj
      ot' = (canon' w1)
      c-ot' : isCanon ot'
      c-ot' = proj₂ (∃!-prop (∃!canon (WObj-length w1)))
      lp-ot' : WObj-length ot' == WObj-length w1
      lp-ot' = proj₁ (∃!-prop (∃!canon (WObj-length w1)))
      p1' : DirectedPath ol' ot'
      p1' = dirpath-to-isCanon ol' ot' (dirmor-preserves-isεFree m1 εF-w1)
              c-ot' (sym (lp-ot' >=> dirmor->length= m1))
      p2' : DirectedPath or' ot'
      p2' = dirpath-to-isCanon or' ot' (dirmor-preserves-isεFree m2 εF-w1)
              c-ot' (sym (lp-ot' >=> dirmor->length= m2))

      l1<l12 : WObj-length w1 < WObj-length (w1 ⊗ w2)
      l1<l12 = trans-=-< (sym +'-right-zero) (+₁-preserves-< (εF-0<length w2 εF-w2))

      sub-ans : directed-path->mor (cons-dirmor m1 p1') ==
                directed-path->mor (cons-dirmor m2 p2')
      sub-ans =
        hyp w1 (inj-l l1<l12) ot' εF-w1 c-ot'
          (cons-dirmor m1 p1') (cons-dirmor m2 p2')

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

      same-path : directed-path->mor (lift-path (cons-dirmor m1 p1')) ==
                  directed-path->mor (lift-path (cons-dirmor m2 p2'))
      same-path =
        ⋆-right (directed-path->mor-lift-path p1') >=>
        sym split₁ˡ >=>
        ⊗₁-left sub-ans >=>
        split₁ˡ >=>
        sym (⋆-right (directed-path->mor-lift-path p2'))


  use-subsolution :
    {os ot ol or : WObj} ->
    (Hyp os) ->
    (m1 : DirectedMor os ol) -> (m2 : DirectedMor os or) ->
    (p1 : DirectedPath ol ot) -> (p2 : DirectedPath or ot) ->
    isεFree os ->
    isCanon ot ->
    SubSolution m1 m2 ->
    directed-path->mor (cons-dirmor m1 p1) ==
    directed-path->mor (cons-dirmor m2 p2)
  use-subsolution {os} {ot} {ol} {or} hyp m1 m2 (p1 , dp1) (p2 , dp2)
                  εF-os c-ot
                  (sub-solution {os'} q1 q2 m-path) =
    (\i -> (dm->mor m1) ⋆ rec-l i) >=>
    sym ⋆-assoc >=>
    ⋆-left m-path >=>
    ⋆-assoc >=>
    (\i -> (dm->mor m2) ⋆ rec-r (~ i))
    where

    εF-os' : isεFree os'
    εF-os' =
      dirpath-preserves-isεFree q1 (dirmor-preserves-isεFree m1 εF-os)

    os'->ot : DirectedPath os' ot
    os'->ot = dirpath-to-isCanon os' ot εF-os' c-ot lp
      where
      lp : WObj-length os' == WObj-length ot
      lp = sym (dirpath->length= q1) >=> dirpath->length= (p1 , dp1)

    rec-l : basic-path->mor p1 ==
            directed-path->mor q1 ⋆ directed-path->mor os'->ot
    rec-l = hyp ol (inj-r (dirmor->rank< m1 , dirmor->length= m1)) ot
                   (dirmor-preserves-isεFree m1 εF-os) c-ot
                   (p1 , dp1) (q1 dp++ os'->ot) >=>
            directed-path->mor-dp++ q1 os'->ot

    rec-r : basic-path->mor p2 ==
            directed-path->mor q2 ⋆ directed-path->mor os'->ot
    rec-r = hyp or (inj-r (dirmor->rank< m2 , dirmor->length= m2)) ot
                   (dirmor-preserves-isεFree m2 εF-os) c-ot
                   (p2 , dp2) (q2 dp++ os'->ot) >=>
            directed-path->mor-dp++ q2 os'->ot

  a-cases : {or : WObj} (o1 o2 o3 : WObj) ->
            (m2 : DirectedMor ((o1 ⊗ o2) ⊗ o3) or) ->
            SubSolution (α⇒' o1 o2 o3 , tt) m2
  a-cases o1 o2 o3 =
    \{ (α⇒' o1 o2 o3 , _)      -> (a-case o1 o2 o3)
     ; (_ ⊗ʳ' m , dm)          -> (ar-case (m , dm))
     ; ((m ⊗ˡ' _) ⊗ˡ' _ , dm)  -> (all-case (m , dm))
     ; ((_ ⊗ʳ' m) ⊗ˡ' _ , dm)  -> (alr-case (m , dm))
     ; ((α⇒' _ _ _) ⊗ˡ' _ , _) -> aa-case
     }

  l-cases : {os' ol' or : WObj}
            (m1 : DirectedMor os' ol') (w1 : WObj) ->
            (Hyp (os' ⊗ w1)) ->
            isεFree os' -> isεFree w1 ->
            (m2 : DirectedMor (os' ⊗ w1) or) ->
            SubSolution (fst m1 ⊗ˡ' w1 , snd m1) m2
  l-cases {os'} {ol'} {or} m1 w1 hyp εF-os' εF-w1 =
    \{ (w2 ⊗ʳ' m2 , dm2) -> (lr-case m1 (m2 , dm2))
     ; (m2 ⊗ˡ' w , dm2)  -> (ll-case hyp m1 (m2 , dm2) εF-os' εF-w1)
     ; m2F@(α⇒' o1 o2 o3 , _) ->
       case m1
       return (\ (x : DirectedMor _ _) -> SubSolution (fst x ⊗ˡ' w1 , snd x) m2F)
       of
       \{ (m ⊗ˡ' w2 , dm)         -> (sym-ss (all-case (m , dm)))
        ; (w2 ⊗ʳ' m , dm)         -> (sym-ss (alr-case (m , dm)))
        ; (m@(α⇒' o1 o2 o3) , dm) -> (sym-ss aa-case)
        }
     }

  r-cases : {os' ol or' : WObj}
            (w1 : WObj) (m1 : DirectedMor os' or') ->
            (Hyp (w1 ⊗ os')) ->
            isεFree os' -> isεFree w1 ->
            (m2 : DirectedMor (w1 ⊗ os') ol) ->
            SubSolution (w1 ⊗ʳ' fst m1 , snd m1) m2
  r-cases {os'} {ol} {or'} w1 m1 hyp εF-os' εF-w1 =
    \{ (α⇒' o1 o2 o3 , _) -> (sym-ss (ar-case m1))
     ; (m2 ⊗ˡ' w2 , dm2) -> (sym-ss (lr-case (m2 , dm2) m1))
     ; (w ⊗ʳ' m2 , dm2) -> (rr-case hyp m1 (m2 , dm2) εF-w1 εF-os')
     }

  private
    opaque
      rec : (o1 : WObj) -> (Hyp o1) -> P o1
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
        use-ss (cases (m1 , dm1) (m2 , dm2))
        where
        use-ss :
          {m1 : DirectedMor os ol} -> {m2 : DirectedMor os or} ->
          SubSolution m1 m2 ->
          basic-path->mor (fst m1 :: p1) ==
          basic-path->mor (fst m2 :: p2)
        use-ss = use-subsolution hyp _ _ (p1 , dp1) (p2 , dp2) εF-os c-ot

        cases : (m1 : DirectedMor os ol) (m2 : DirectedMor os or) -> SubSolution m1 m2
        cases m =
          dm-cases {P = \{os} {ol} m -> (Hyp os) -> isεFree os ->
                                        (m2 : DirectedMor _ _) ->
                                        SubSolution m m2}
          (\o1 o2 o3 _ _ -> a-cases o1 o2 o3)
          (\ m w1 hyp εF-os -> l-cases m w1 hyp (proj₁ εF-os) (proj₂ εF-os))
          (\ m w1 hyp εF-os -> r-cases w1 m hyp (proj₂ εF-os) (proj₁ εF-os))
          m hyp εF-os

  parallel-dirpaths-to-canon : ∀ o -> P o
  parallel-dirpaths-to-canon = rank-length-induction rec
