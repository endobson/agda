{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal-base where

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


record WMor (s t : WObj) : Type₀ where
  constructor wmor
  field
    length : (WObj-length s) == (WObj-length t)

isProp-WMor : {s t : WObj} -> isProp (WMor s t)
isProp-WMor (wmor l1) (wmor l2) i = wmor (isSetNat _ _ l1 l2 i)

wmor-path : {s t : WObj} {a b : WMor s t} -> a == b
wmor-path = isProp-WMor _ _

WSorts : CategorySorts ℓ-zero ℓ-zero
WSorts .CategorySorts.Obj = WObj
WSorts .CategorySorts.Mor = WMor

WOps : CategoryOps WSorts
WOps .CategoryOps.id = (wmor refl)
WOps .CategoryOps._⋆_ (wmor l1) (wmor l2) = wmor (l1 >=> l2)

WLaws : CategoryLaws WOps
WLaws .CategoryLaws.⋆-left-id _ = wmor-path
WLaws .CategoryLaws.⋆-right-id _ = wmor-path
WLaws .CategoryLaws.⋆-assoc _ _ _ = wmor-path
WLaws .CategoryLaws.isSet-Mor = isProp->isSet isProp-WMor


WCat : PreCategory ℓ-zero ℓ-zero
WCat = Laws->Category WLaws

MonoidalW : MonoidalStr WCat
MonoidalW = record
  { ⊗ = Bi-⊗
  ; unit = ε
  ; unitorˡ = unitorˡ
  ; unitorʳ = unitorʳ
  ; associator = associator
  ; triangle = wmor-path
  ; pentagon = wmor-path
  }
  where

  Bi-⊗ : BiFunctor WCat WCat WCat
  Bi-⊗ .Functor.obj (s , t) = s ⊗ t
  Bi-⊗ .Functor.mor (wmor l1 , wmor l2) = wmor (\i -> l1 i + l2 i)
  Bi-⊗ .Functor.id _ = wmor-path
  Bi-⊗ .Functor.⋆ _ _ = wmor-path

  unitorˡ : NaturalIsomorphism (appˡ {C = WCat} Bi-⊗ ε) (idF WCat)
  unitorˡ = record
    { NT-obj = \_ -> wmor +-left-zero
    ; NT-mor = \_ -> wmor-path
    } ,
    \c -> record
      { inv = wmor (sym +-left-zero)
      ; sec = wmor-path
      ; ret = wmor-path
      }

  unitorʳ : NaturalIsomorphism (appʳ {D = WCat} Bi-⊗ ε) (idF WCat)
  unitorʳ = record
    { NT-obj = \_ -> wmor +-right-zero
    ; NT-mor = \_ -> wmor-path
    } ,
    \c -> record
      { inv = wmor (sym +-right-zero)
      ; sec = wmor-path
      ; ret = wmor-path
      }

  associator : NaturalIsomorphism (LeftBiasedDoubleApplicationFunctor Bi-⊗)
                                  (RightBiasedDoubleApplicationFunctor Bi-⊗)
  associator = record
    { NT-obj = \{ (triple a b c) -> wmor (+-assocᵉ (WObj-length a) (WObj-length b) (WObj-length c)) }
    ; NT-mor = \_ -> wmor-path
    } ,
    \{ (triple a b c) -> record
      { inv = wmor (sym (+-assocᵉ (WObj-length a) (WObj-length b) (WObj-length c)))
      ; sec = wmor-path
      ; ret = wmor-path
      } }

data BasicMor : WObj -> WObj -> Type₀ where
  α⇒' : (a b c : WObj) -> BasicMor ((a ⊗ b) ⊗ c) (a ⊗ (b ⊗ c))
  α⇐' : (a b c : WObj) -> BasicMor (a ⊗ (b ⊗ c)) ((a ⊗ b) ⊗ c)
  λ⇒' : (a : WObj) -> BasicMor (ε ⊗ a) a
  λ⇐' : (a : WObj) -> BasicMor a (ε ⊗ a)
  ρ⇒' : (a : WObj) -> BasicMor (a ⊗ ε) a
  ρ⇐' : (a : WObj) -> BasicMor a (a ⊗ ε)
  _⊗ˡ'_ : {a b : WObj} -> BasicMor a b -> (c : WObj) -> BasicMor (a ⊗ c) (b ⊗ c)
  _⊗ʳ'_ : (a : WObj) -> {b c : WObj} -> BasicMor b c -> BasicMor (a ⊗ b) (a ⊗ c)

data BasicPath' (a : WObj) : WObj -> Type₀ where
  [] : BasicPath' a a
  _::_ : {c b : WObj} -> BasicMor c b -> BasicPath' a b -> BasicPath' a c

BasicPath : WObj -> WObj -> Type₀
BasicPath s t = BasicPath' t s

data isDirectedMor : Boolean -> {a b : WObj} -> BasicMor a b -> Type₀ where
  α⇒' : (a b c : WObj) -> isDirectedMor true (α⇒' a b c)
  α⇐' : (a b c : WObj) -> isDirectedMor false (α⇐' a b c)
  _⊗ˡ'_ : {d : Boolean} {a b : WObj} {m : BasicMor a b} ->
          isDirectedMor d m -> (c : WObj) -> isDirectedMor d (m ⊗ˡ' c)
  _⊗ʳ'_ : (a : WObj) {d : Boolean} {b c : WObj} {m : BasicMor b c} ->
          isDirectedMor d m -> isDirectedMor d (a ⊗ʳ' m)

DirectedMor : (d : Boolean) -> WObj -> WObj -> Type₀
DirectedMor d a b = Σ (BasicMor a b) (isDirectedMor d)

data DirectedPath' (d : Boolean) (a : WObj) : WObj -> Type₀ where
  [] : DirectedPath' d a a
  _::_ : {c b : WObj} -> DirectedMor d c b -> DirectedPath' d a b -> DirectedPath' d a c

DirectedPath : Boolean -> WObj -> WObj -> Type₀
DirectedPath d s t = DirectedPath' d t s


isTrivial : WObj -> Type₀
isTrivial ε = Top
isTrivial var = Top
isTrivial (_ ⊗ _) = Bot

isProp-isTrivial : (o : WObj) -> isProp (isTrivial o)
isProp-isTrivial ε = isPropTop
isProp-isTrivial var = isPropTop
isProp-isTrivial (_ ⊗ _) = isPropBot

isRightAssoc : WObj -> Type₀
isRightAssoc (a ⊗ b) = isTrivial a × isRightAssoc b
isRightAssoc ε = Top
isRightAssoc var = Top

isProp-isRightAssoc : (o : WObj) -> isProp (isRightAssoc o)
isProp-isRightAssoc ε = isPropTop
isProp-isRightAssoc var = isPropTop
isProp-isRightAssoc (a ⊗ b) = isProp× (isProp-isTrivial a) (isProp-isRightAssoc b)

data LeafShape : Type₀ where
  [ε] : LeafShape
  [v] : LeafShape
  ε::_ : LeafShape -> LeafShape
  v::_ : LeafShape -> LeafShape

ls-tail : LeafShape -> LeafShape
ls-tail [ε]     = [ε]
ls-tail [v]     = [v]
ls-tail (ε:: t) = t
ls-tail (v:: t) = t


module _ where
  private
    encode : LeafShape -> Nat
    encode [ε]     = 0
    encode [v]     = 1
    encode (ε:: _) = 2
    encode (v:: _) = 3


  Discrete-LeafShape : Discrete LeafShape
  Discrete-LeafShape [ε] [ε]     = yes refl
  Discrete-LeafShape [ε] [v]     =
    no (\p -> zero-suc-absurd (cong encode p))
  Discrete-LeafShape [ε] (ε:: _) =
    no (\p -> zero-suc-absurd (cong encode p))
  Discrete-LeafShape [ε] (v:: _) =
    no (\p -> zero-suc-absurd (cong encode p))
  Discrete-LeafShape [v] [ε]     =
    no (\p -> zero-suc-absurd (cong encode (sym p)))
  Discrete-LeafShape [v] [v]     = yes refl
  Discrete-LeafShape [v] (ε:: _) =
    no (\p -> zero-suc-absurd (cong pred (cong encode p)))
  Discrete-LeafShape [v] (v:: _) =
    no (\p -> zero-suc-absurd (cong pred (cong encode p)))
  Discrete-LeafShape (ε:: _) [ε]     =
    no (\p -> zero-suc-absurd (cong encode (sym p)))
  Discrete-LeafShape (ε:: _) [v]     =
    no (\p -> zero-suc-absurd (cong pred (cong encode (sym p))))
  Discrete-LeafShape (ε:: a) (ε:: b) with (Discrete-LeafShape a b)
  ... | (yes p) = yes (cong ε::_ p)
  ... | (no ¬p) = no (\p -> ¬p (cong ls-tail p))
  Discrete-LeafShape (ε:: _) (v:: _) =
    no (\p -> zero-suc-absurd (cong pred (cong pred (cong encode p))))
  Discrete-LeafShape (v:: _) [ε]     =
    no (\p -> zero-suc-absurd (cong encode (sym p)))
  Discrete-LeafShape (v:: _) [v]     =
    no (\p -> zero-suc-absurd (cong pred (cong encode (sym p))))
  Discrete-LeafShape (v:: _) (ε:: _) =
    no (\p -> zero-suc-absurd (cong pred (cong pred (cong encode (sym p)))))
  Discrete-LeafShape (v:: a) (v:: b) with (Discrete-LeafShape a b)
  ... | (yes p) = (yes (cong v::_ p))
  ... | (no ¬p) = no (\p -> ¬p (cong ls-tail p))

isSet-LeafShape : isSet LeafShape
isSet-LeafShape = Discrete->isSet Discrete-LeafShape

_ls++_ : LeafShape -> LeafShape -> LeafShape
[ε] ls++ l = ε:: l
[v] ls++ l = v:: l
(ε:: l1) ls++ l2 = ε:: (l1 ls++ l2)
(v:: l1) ls++ l2 = v:: (l1 ls++ l2)

leaf-shape : WObj -> LeafShape
leaf-shape ε = [ε]
leaf-shape var = [v]
leaf-shape (a ⊗ b) = leaf-shape a ls++ leaf-shape b

leaf-shape-assoc : (ls1 ls2 ls3 : LeafShape) ->
  ((ls1 ls++ ls2) ls++ ls3) == (ls1 ls++ (ls2 ls++ ls3))
leaf-shape-assoc [ε] _ _ = refl
leaf-shape-assoc [v] _ _ = refl
leaf-shape-assoc (ε:: l1) l2 l3 =
  cong ε::_ (leaf-shape-assoc l1 l2 l3)
leaf-shape-assoc (v:: l1) l2 l3 =
  cong v::_ (leaf-shape-assoc l1 l2 l3)

canonical-right-assoc : (s : LeafShape) ->
  ∃![ o ∈ WObj ] (isRightAssoc o × leaf-shape o == s)
canonical-right-assoc s = val s , isProp-LS s _
  where
  val : (s : LeafShape) -> Σ[ o ∈ WObj ] (isRightAssoc o × leaf-shape o == s)
  val [ε] = ε , (tt , refl)
  val [v] = var , (tt , refl)
  val (ε:: s) =
    let (o , ra , p) = val s in
    (ε ⊗ o) , (tt , ra) , cong ε::_ p
  val (v:: s) =
    let (o , ra , p) = val s in
    (var ⊗ o) , (tt , ra) , cong v::_ p

  ls-path : {s : LeafShape} ->
            (o1 : WObj) ->
            (isRightAssoc o1 × leaf-shape o1 == s) ->
            (o2 : WObj) ->
            (isRightAssoc o2 × leaf-shape o2 == s) ->
            o1 == o2
  ls-path ε (_ , _) ε (_ , _) = refl
  ls-path o1@ε (_ , p1) o2@var (_ , p2) =
    bot-elim (proj-r (dec->⊎ (Discrete-LeafShape (leaf-shape o1) (leaf-shape o2))) tt (p1 >=> sym p2))
  ls-path o1@ε (_ , p1) o2@(var ⊗ _) (_ , p2) =
    bot-elim (proj-r (dec->⊎ (Discrete-LeafShape (leaf-shape o1) (leaf-shape o2))) tt (p1 >=> sym p2))
  ls-path o1@ε (_ , p1) o2@(ε ⊗ _) (_ , p2) =
    bot-elim (proj-r (dec->⊎ (Discrete-LeafShape (leaf-shape o1) (leaf-shape o2))) tt (p1 >=> sym p2))
  ls-path o1@var (_ , p1) o2@ε (_ , p2) =
    bot-elim (proj-r (dec->⊎ (Discrete-LeafShape (leaf-shape o1) (leaf-shape o2))) tt (p1 >=> sym p2))
  ls-path var (_ , _) var (_ , _) = refl
  ls-path o1@var (_ , p1) o2@(var ⊗ _) (_ , p2) =
    bot-elim (proj-r (dec->⊎ (Discrete-LeafShape (leaf-shape o1) (leaf-shape o2))) tt (p1 >=> sym p2))
  ls-path o1@var (_ , p1) o2@(ε ⊗ _) (_ , p2) =
    bot-elim (proj-r (dec->⊎ (Discrete-LeafShape (leaf-shape o1) (leaf-shape o2))) tt (p1 >=> sym p2))
  ls-path o1@(var ⊗ _) (_ , p1) o2@ε (_ , p2) =
    bot-elim (proj-r (dec->⊎ (Discrete-LeafShape (leaf-shape o1) (leaf-shape o2))) tt (p1 >=> sym p2))
  ls-path o1@(var ⊗ _) (_ , p1) o2@var (_ , p2) =
    bot-elim (proj-r (dec->⊎ (Discrete-LeafShape (leaf-shape o1) (leaf-shape o2))) tt (p1 >=> sym p2))
  ls-path o1@(ε ⊗ _) (_ , p1) o2@ε (_ , p2) =
    bot-elim (proj-r (dec->⊎ (Discrete-LeafShape (leaf-shape o1) (leaf-shape o2))) tt (p1 >=> sym p2))
  ls-path o1@(ε ⊗ _) (_ , p1) o2@var (_ , p2) =
    bot-elim (proj-r (dec->⊎ (Discrete-LeafShape (leaf-shape o1) (leaf-shape o2))) tt (p1 >=> sym p2))
  ls-path o1@(var ⊗ _) (_ , p1) o2@(ε ⊗ _) (_ , p2) =
    bot-elim (proj-r (dec->⊎ (Discrete-LeafShape (leaf-shape o1) (leaf-shape o2))) tt (p1 >=> sym p2))
  ls-path o1@(ε ⊗ _) (_ , p1) o2@(var ⊗ _) (_ , p2) =
    bot-elim (proj-r (dec->⊎ (Discrete-LeafShape (leaf-shape o1) (leaf-shape o2))) tt (p1 >=> sym p2))
  ls-path (var ⊗ o1) ((_ , ra1) , p1) (var ⊗ o2) ((_ , ra2) , p2) =
    cong (var ⊗_) (ls-path o1 (ra1 , cong ls-tail p1) o2 (ra2 , cong ls-tail p2))
  ls-path (ε ⊗ o1) ((_ , ra1) , p1) (ε ⊗ o2) ((_ , ra2) , p2) =
    cong (ε ⊗_) (ls-path o1 (ra1 , (\ i -> ls-tail (p1 i))) o2 (ra2 , (\i -> ls-tail (p2 i))))


  isProp-LS : (s : LeafShape) -> isProp (Σ[ o ∈ WObj ] (isRightAssoc o × leaf-shape o == s))
  isProp-LS s x y = ΣProp-path (\{a} -> isProp× (isProp-isRightAssoc a) (isSet-LeafShape _ _))
                               (ls-path (fst x) (snd x) (fst y) (snd y))

canon : WObj -> WObj
canon o = ∃!-val (canonical-right-assoc (leaf-shape o))


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

dirpath-to-canon' : {n : Nat} -> (o : WObj) -> WObj-rank o ≤ n -> DirectedPath true o (canon o)
dirpath-to-canon' ε _ = []
dirpath-to-canon' var _ = []
dirpath-to-canon' (var ⊗ o) lt = lift-path (dirpath-to-canon' o lt)
  where
  lift-path : ∀ {o1 o2} -> DirectedPath true o1 o2 -> DirectedPath true (var ⊗ o1) (var ⊗ o2)
  lift-path [] = []
  lift-path ((m , d) :: p) = (var ⊗ʳ' m , var ⊗ʳ' d) :: lift-path p

dirpath-to-canon' (ε ⊗ o) lt = lift-path (dirpath-to-canon' o lt)
  where
  lift-path : ∀ {o1 o2} -> DirectedPath true o1 o2 -> DirectedPath true (ε ⊗ o1) (ε ⊗ o2)
  lift-path [] = []
  lift-path ((m , d) :: p) = (ε ⊗ʳ' m , ε ⊗ʳ' d) :: lift-path p

dirpath-to-canon' {zero} o@((o1 ⊗ o2) ⊗ o3) lt = bot-elim (zero-≮ (trans-<-≤ (assoc-rank< o1 o2 o3) lt))
dirpath-to-canon' {suc n} o@((o1 ⊗ o2) ⊗ o3) lt =
  transport (\i -> DirectedPath true o (c1=c2 (~ i)))
    ((α⇒' o1 o2 o3 , α⇒' o1 o2 o3) :: (dirpath-to-canon' {n} (o1 ⊗ (o2 ⊗ o3)) lt2))
  where
  lt2 : WObj-rank (o1 ⊗ (o2 ⊗ o3)) ≤ n
  lt2 = pred-≤ (trans-<-≤ (assoc-rank< o1 o2 o3) lt)

  c1=c2 : canon ((o1 ⊗ o2) ⊗ o3) == canon (o1 ⊗ (o2 ⊗ o3))
  c1=c2 i =
    ∃!-val (canonical-right-assoc (leaf-shape-assoc (leaf-shape o1) (leaf-shape o2) (leaf-shape o3) i))

dirpath-to-canon : (o : WObj) -> DirectedPath true o (canon o)
dirpath-to-canon o = dirpath-to-canon' o refl-≤

dirmor->branches= : {o1 o2 : WObj} -> DirectedMor true o1 o2 -> WObj-branches o1 == WObj-branches o2
dirmor->branches= (α⇒' a b c , α⇒' a b c) =
  cong suc (cong suc (+-assocᵉ (WObj-branches a) (WObj-branches b) (WObj-branches c)) >=>
            sym +'-right-suc)
dirmor->branches= (m ⊗ˡ' c , dm ⊗ˡ' c) =
  cong suc (+-left (dirmor->branches= (m , dm)))
dirmor->branches= (a ⊗ʳ' m , a ⊗ʳ' dm) =
  cong suc (+-right (dirmor->branches= (m , dm)))

dirmor->rank< : {o1 o2 : WObj} -> DirectedMor true o1 o2 -> WObj-rank o2 < WObj-rank o1
dirmor->rank< (α⇒' a b c , α⇒' a b c) = assoc-rank< a b c
dirmor->rank< {o1 ⊗ c} {o2 ⊗ c} (m ⊗ˡ' c , dm ⊗ˡ' c) =
  trans-<-=
    (+₁-preserves-< {a = WObj-branches o2} (+₂-preserves-< rec))
    (\i -> (dirmor->branches= (m , dm) (~ i)) + (WObj-rank o1 + WObj-rank c))
  where
  rec : WObj-rank o2 < WObj-rank o1
  rec = dirmor->rank< (m , dm)
dirmor->rank< {a ⊗ o1} {a ⊗ o2} (a ⊗ʳ' m , a ⊗ʳ' dm) =
  (+₁-preserves-< {a = WObj-branches a} (+₁-preserves-< rec))
  where
  rec : WObj-rank o2 < WObj-rank o1
  rec = dirmor->rank< (m , dm)

dirpath->rank≤ : {o1 o2 : WObj} -> DirectedPath true o1 o2 -> WObj-rank o2 ≤ WObj-rank o1
dirpath->rank≤ [] = refl-≤
dirpath->rank≤ (dm :: dp) = trans-≤ (dirpath->rank≤ dp) (weaken-< (dirmor->rank< dm))
