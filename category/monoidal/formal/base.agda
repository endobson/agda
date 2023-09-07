{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal.base where

open import additive-group
open import additive-group.instances.nat
open import base
open import category.base
open import category.constructions.triple-product
open import category.monoidal.base
open import cubical
open import equality hiding (transport) -- TODO fix
open import equality-path using (transport)
open import hlevel
open import nat
open import nat.order
open import order
open import order.instances.nat
open import relation


data WObj : Type₀ where
  var : WObj
  ε : WObj
  _⊗_ : WObj -> WObj -> WObj

WObj-length : WObj -> Nat
WObj-length var = 1
WObj-length ε = 0
WObj-length (a ⊗ b) = WObj-length a + WObj-length b

WObj-branches : WObj -> Nat
WObj-branches ε = 0
WObj-branches var = 0
WObj-branches (a ⊗ b) = suc (WObj-branches a + WObj-branches b)

WObj-rank : WObj -> Nat
WObj-rank ε = 0
WObj-rank var = 0
WObj-rank (a ⊗ b) = WObj-branches a + (WObj-rank a + WObj-rank b)

isεFree : Pred WObj ℓ-zero
isεFree ε = Bot
isεFree var = Top
isεFree (a ⊗ b) = isεFree a × isεFree b

isOnlyε : Pred WObj ℓ-zero
isOnlyε ε = Top
isOnlyε var = Bot
isOnlyε (a ⊗ b) = isOnlyε a × isOnlyε b

isProp-isOnlyε : (o : WObj) -> isProp (isOnlyε o)
isProp-isOnlyε ε = isPropTop
isProp-isOnlyε var = isPropBot
isProp-isOnlyε (a ⊗ b) = isProp× (isProp-isOnlyε a) (isProp-isOnlyε b)


isε : Pred WObj ℓ-zero
isε ε = Top
isε var = Bot
isε (_ ⊗ _) = Bot

isVar : Pred WObj ℓ-zero
isVar ε = Bot
isVar var = Top
isVar (_ ⊗ _) = Bot

isProp-isVar : (o : WObj) -> isProp (isVar o)
isProp-isVar ε = isPropBot
isProp-isVar var = isPropTop
isProp-isVar (_ ⊗ _) = isPropBot

is⊗ : Pred WObj ℓ-zero
is⊗ ε = Bot
is⊗ var = Bot
is⊗ (_ ⊗ _) = Top

WObj-left : (o : WObj) -> is⊗ o -> WObj
WObj-left (l ⊗ r) _ = l

WObj-right : (o : WObj) -> is⊗ o -> WObj
WObj-right (l ⊗ r) _ = r

isOnlyε->¬isεFree : (a : WObj) -> isOnlyε a -> isεFree a -> Bot
isOnlyε->¬isεFree var bot _ = bot
isOnlyε->¬isεFree ε _ bot = bot
isOnlyε->¬isεFree (l ⊗ _) (oε , _) (εF , _) = isOnlyε->¬isεFree l oε εF

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

branch-induction : {ℓ : Level}
  {P : Pred WObj ℓ} ->
  (rec : (o1 : WObj) -> ((o2 : WObj) -> WObj-branches o2 < WObj-branches o1 -> P o2) -> P o1)
  (o : WObj) -> P o
branch-induction {ℓ} {P} rec = \o -> strong-induction' rec' _ o refl-≤
  where
  P' : Pred Nat ℓ
  P' n = (o : WObj) -> (WObj-branches o < n) -> P o
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

data BasicMor : WObj -> WObj -> Type₀ where
  α⇒' : (a b c : WObj) -> BasicMor ((a ⊗ b) ⊗ c) (a ⊗ (b ⊗ c))
  α⇐' : (a b c : WObj) -> BasicMor (a ⊗ (b ⊗ c)) ((a ⊗ b) ⊗ c)
  λ⇒' : (a : WObj) -> BasicMor (ε ⊗ a) a
  λ⇐' : (a : WObj) -> BasicMor a (ε ⊗ a)
  ρ⇒' : (a : WObj) -> BasicMor (a ⊗ ε) a
  ρ⇐' : (a : WObj) -> BasicMor a (a ⊗ ε)
  _⊗ˡ'_ : {a b : WObj} -> BasicMor a b -> (c : WObj) -> BasicMor (a ⊗ c) (b ⊗ c)
  _⊗ʳ'_ : (a : WObj) -> {b c : WObj} -> BasicMor b c -> BasicMor (a ⊗ b) (a ⊗ c)

data BasicPath (s t : WObj) : Type₀ where
  empty : (s == t) -> BasicPath s t
  _::_ : {m : WObj} -> BasicMor s m -> BasicPath m t -> BasicPath s t

invert-bm : {o1 o2 : WObj} -> BasicMor o1 o2 -> BasicMor o2 o1
invert-bm (α⇒' a b c) = (α⇐' a b c)
invert-bm (α⇐' a b c) = (α⇒' a b c)
invert-bm (λ⇒' a) = (λ⇐' a)
invert-bm (λ⇐' a) = (λ⇒' a)
invert-bm (ρ⇒' a) = (ρ⇐' a)
invert-bm (ρ⇐' a) = (ρ⇒' a)
invert-bm (l ⊗ˡ' w) = (invert-bm l ⊗ˡ' w)
invert-bm (w ⊗ʳ' r) = (w ⊗ʳ' invert-bm r)

-- data PathInverseInd {s t : WObj} (p1 : BasicPath s t) :
--                     {u : WObj} (p2 : BasicPath u t) (p3 : BasicPath u s) -> Type₀ where
--   path-inv-ind-start : PathInverseInd p1 p1 (empty refl)
--   path-inv-ind-step :
--     {u1 u2 : WObj} -> (m : BasicMor u1 u2) ->
--     (p2 : BasicPath u2 t) -> (p3 : BasicPath u1 s) ->
--     PathInverseInd p1 (m :: p2) p3 ->
--     PathInverseInd p1 p2 (invert-bm m :: p3)

_bp++_ : {o1 o2 o3 : WObj} -> BasicPath o1 o2 -> BasicPath o2 o3 -> BasicPath o1 o3
_bp++_ {o3 = o3} (empty p) = transport (\i -> BasicPath (p (~ i)) o3)
_bp++_ (m :: p)  p2 = m :: (p bp++ p2)

bm-snoc : {o1 o2 o3 : WObj} -> BasicPath o1 o2 -> BasicMor o2 o3 -> BasicPath o1 o3
bm-snoc p m = p bp++ (m :: (empty refl))

invert-bp : {o1 o2 : WObj} -> BasicPath o1 o2 -> BasicPath o2 o1
invert-bp {o1} {o2} p = rec p (empty refl)
  where
  rec : {o3 : WObj} -> BasicPath o3 o2 -> BasicPath o3 o1 -> BasicPath o2 o1
  rec (empty p) = transport (\i -> BasicPath (p i) o1)
  rec (m :: p) p2 = rec p (invert-bm m :: p2)

invert-bp' : {o1 o2 : WObj} -> BasicPath o1 o2 -> BasicPath o2 o1
invert-bp' (empty p) = (empty (sym p))
invert-bp' (m :: p) = bm-snoc (invert-bp' p) (invert-bm m)



assoc-rank< : (o1 o2 o3 : WObj) -> WObj-rank (o1 ⊗ (o2 ⊗ o3)) < WObj-rank ((o1 ⊗ o2) ⊗ o3)
assoc-rank< o1 o2 o3 = (b o1) , +'-right-suc >=> (sym branch-path)
  where
  b = WObj-branches
  r = WObj-rank

  branch-path : WObj-rank ((o1 ⊗ o2) ⊗ o3) == (suc (b o1)) + (WObj-rank (o1 ⊗ (o2 ⊗ o3)))
  branch-path =
    begin
      suc (b o1 + b o2) + ((b o1 + (r o1 + r o2)) + r o3)
    ==< cong suc (+-assocᵉ (b o1) (b o2) _) >
      suc (b o1 + (b o2 + ((b o1 + (r o1 + r o2)) + r o3)))
    ==< (\i -> (suc (b o1)) + path1 i) >
      (suc (b o1)) + (b o1 + (r o1 + (b o2 + (r o2 + r o3))))
    end
    where
    open EqReasoning

    path1 : (b o2 + ((b o1 + (r o1 + r o2)) + r o3)) ==
            (b o1 + (r o1 + (b o2 + (r o2 + r o3))))
    path1 =
      begin
        b o2 + ((b o1 + (r o1 + r o2)) + r o3)
      ==< (\i -> b o2 + (+-assocᵉ (b o1) (r o1 + r o2) (r o3)) i) >
        b o2 + (b o1 + ((r o1 + r o2) + r o3))
      ==< (\i -> b o2 + (b o1 + (+-assocᵉ (r o1)  (r o2) (r o3) i))) >
        b o2 + (b o1 + (r o1 + (r o2 + r o3)))
      ==< (\i -> b o2 + (+-assocᵉ (b o1) (r o1) (r o2 + r o3) (~ i))) >
        b o2 + ((b o1 + r o1) + (r o2 + r o3))
      ==< (\i -> +-assocᵉ (b o2) ((b o1) + (r o1)) (r o2 + r o3) (~ i)) >
        (b o2 + (b o1 + r o1)) + (r o2 + r o3)
      ==< (\i -> ((+-assocᵉ (b o2) (b o1) (r o1) (~ i)) + (r o2 + r o3))) >
        ((b o2 + b o1) + r o1) + (r o2 + r o3)
      ==< (\i -> ((+-commuteᵉ (b o2) (b o1) i) + (r o1)) + (r o2 + r o3)) >
        ((b o1 + b o2) + r o1) + (r o2 + r o3)
      ==< (\i -> ((+-assocᵉ (b o1) (b o2) (r o1) i) + (r o2 + r o3))) >
        (b o1 + (b o2 + r o1)) + (r o2 + r o3)
      ==< (\i -> (b o1 + (+-commuteᵉ (b o2) (r o1) i)) + (r o2 + r o3)) >
        (b o1 + (r o1 + b o2)) + (r o2 + r o3)
      ==< (\i -> +-assocᵉ (b o1) ((r o1) + (b o2)) (r o2 + r o3) i) >
        b o1 + ((r o1 + b o2) + (r o2 + r o3))
      ==< (\i -> b o1 + (+-assocᵉ (r o1) (b o2) (r o2 + r o3) i)) >
        b o1 + (r o1 + (b o2 + (r o2 + r o3)))
      end

AreInverses : {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) -> {a b : Obj C} ->
              (m1 : C [ a , b ]) (m2 : C [ b , a ]) -> Type _
AreInverses C m1 m2 = (m1 ⋆⟨ C ⟩ m2 == id C) × (m2 ⋆⟨ C ⟩ m1 == id C)

isIso->AreInverses :
  {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} -> {a b : Obj C} -> {m : C [ a , b ]} ->
  (i : isIso C m) -> AreInverses C m (isIso.inv i)
isIso->AreInverses (is-iso inv sec ret) = ret , sec

sym-AreInverses :
  {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) {a b : Obj C} {m1 : C [ a , b ]} {m2 : C [ b , a ]} ->
  AreInverses C m1 m2 -> AreInverses C m2 m1
sym-AreInverses _ (p1 , p2) = (p2 , p1)


module InMonoidal
  {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C) (obj : Obj C) where
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

  AreInverses-invert-bm : {a b : WObj} -> (m : BasicMor a b) ->
                          AreInverses C (basic-mor->mor m) (basic-mor->mor (invert-bm m))
  AreInverses-invert-bm (α⇒' a b c) =
    isIso->AreInverses (snd associator (triple (inj₀ a) (inj₀ b) (inj₀ c)))
  AreInverses-invert-bm (α⇐' a b c) =
    sym-AreInverses C (isIso->AreInverses (snd associator (triple (inj₀ a) (inj₀ b) (inj₀ c))))
  AreInverses-invert-bm (λ⇒' a) =
    isIso->AreInverses (snd unitorˡ (inj₀ a))
  AreInverses-invert-bm (λ⇐' a) =
    sym-AreInverses C (isIso->AreInverses (snd unitorˡ (inj₀ a)))
  AreInverses-invert-bm (ρ⇒' a) =
    isIso->AreInverses (snd unitorʳ (inj₀ a))
  AreInverses-invert-bm (ρ⇐' a) =
    sym-AreInverses C (isIso->AreInverses (snd unitorʳ (inj₀ a)))
  AreInverses-invert-bm (m ⊗ˡ' w) =
    let (p1 , p2) = (AreInverses-invert-bm m) in
    (sym split₁ˡ >=> ⊗₁-left p1 >=> F-id ⊗F _ ,
     sym split₁ˡ >=> ⊗₁-left p2 >=> F-id ⊗F _)
  AreInverses-invert-bm (w ⊗ʳ' m) =
    let (p1 , p2) = (AreInverses-invert-bm m) in
    (sym split₂ˡ >=> ⊗₁-right p1 >=> F-id ⊗F _ ,
     sym split₂ˡ >=> ⊗₁-right p2 >=> F-id ⊗F _)

  basic-path->mor-bp++ : {a b c : WObj} -> (p1 : BasicPath a b) (p2 : BasicPath b c) ->
    basic-path->mor (p1 bp++ p2) == basic-path->mor p1 ⋆ basic-path->mor p2
  basic-path->mor-bp++ {a} {b} {c} (empty p) p2 =
    sym ⋆-left-id >=>
    (\j ->
      (transp (\i -> C [ inj₀ a , inj₀ (p (i ∧ j)) ]) (~ j) (id C)) ⋆
      (basic-path->mor (transp (\i -> BasicPath (p ((~ i) ∨ j)) c) j p2)))
  basic-path->mor-bp++ {a} {b} {c} (m :: p) p2 =
    ⋆-right (basic-path->mor-bp++ p p2) >=>
    (sym ⋆-assoc)
