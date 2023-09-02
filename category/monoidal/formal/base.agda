{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal.base where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality
open import cubical
open import hlevel
open import nat
open import nat.order
open import order
open import order.instances.nat
open import relation
open import category.base
open import category.monoidal.base

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
