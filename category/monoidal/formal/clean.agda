{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal.clean where

open import base
open import category.monoidal.formal.base
open import equality
open import hlevel
open import relation
open import sigma.base
open import truncation

hasVar : Pred WObj ℓ-zero
hasVar ε = Bot
hasVar var = Top
hasVar (l ⊗ r) = hasVar l ⊎ hasVar r

-- WObj-εCount : WObj -> Nat
-- WObj-εCount var = 0
-- WObj-εCount ε = 1
-- WObj-εCount (a ⊗ b) = WObj-εCount a + WObj-εCount b

dec-hasVar : ∀ o -> hasVar o ⊎ isOnlyε o
dec-hasVar ε = inj-r tt
dec-hasVar var = inj-l tt
dec-hasVar (l ⊗ r) with dec-hasVar l | dec-hasVar r
... | (inj-l hv-l) | _            = inj-l (inj-l hv-l)
... | (inj-r oε-l) | (inj-l hv-r) = inj-l (inj-r hv-r)
... | (inj-r oε-l) | (inj-r oε-r) = inj-r (oε-l , oε-r)


data VarLocations : WObj -> Type₀ where
  var : VarLocations var
  _ε⊗_ : {a b : WObj} -> isOnlyε a -> VarLocations b -> VarLocations (a ⊗ b)
  _⊗ε_ : {a b : WObj} -> VarLocations a -> isOnlyε b -> VarLocations (a ⊗ b)
  _⊗_  : {a b : WObj} -> VarLocations a -> VarLocations b -> VarLocations (a ⊗ b)

dec-VarLocations : ∀ o -> VarLocations o ⊎ isOnlyε o
dec-VarLocations ε = inj-r tt
dec-VarLocations var = inj-l var
dec-VarLocations (l ⊗ r) with dec-VarLocations l | dec-VarLocations r
... | (inj-l vl-l) | (inj-l vl-r) = inj-l (vl-l ⊗ vl-r)
... | (inj-l vl-l) | (inj-r oε-r) = inj-l (vl-l ⊗ε oε-r)
... | (inj-r oε-l) | (inj-l vl-r) = inj-l (oε-l ε⊗ vl-r)
... | (inj-r oε-l) | (inj-r oε-r) = inj-r (oε-l , oε-r)

VarLocations->¬isOnlyε : ∀ {o} -> VarLocations o -> isOnlyε o -> Bot
VarLocations->¬isOnlyε var ()
VarLocations->¬isOnlyε (_ ε⊗ v) (_ , oε) = VarLocations->¬isOnlyε v oε
VarLocations->¬isOnlyε (v ⊗ε _) (oε , _) = VarLocations->¬isOnlyε v oε
VarLocations->¬isOnlyε (v ⊗ _) (oε , _) = VarLocations->¬isOnlyε v oε

isProp-VarLocations : ∀ {o} -> isProp (VarLocations o)
isProp-VarLocations var var = refl
isProp-VarLocations (vl-l1 ⊗ε oε-r1) (vl-l2 ⊗ε oε-r2) =
  cong2 _⊗ε_ (isProp-VarLocations vl-l1 vl-l2) (isProp-isOnlyε _ oε-r1 oε-r2)
isProp-VarLocations (_ ⊗ε oε-r) (_ ε⊗ vl-r) =
  bot-elim (VarLocations->¬isOnlyε vl-r oε-r)
isProp-VarLocations (_ ⊗ε oε-r) (_ ⊗ vl-r) =
  bot-elim (VarLocations->¬isOnlyε vl-r oε-r)
isProp-VarLocations (oε-l ε⊗ _) (vl-l ⊗ε _) =
  bot-elim (VarLocations->¬isOnlyε vl-l oε-l)
isProp-VarLocations (oε-l1 ε⊗ vl-r1) (oε-l2 ε⊗ vl-r2) =
  cong2 _ε⊗_ (isProp-isOnlyε _ oε-l1 oε-l2) (isProp-VarLocations vl-r1 vl-r2)
isProp-VarLocations (oε-l ε⊗ _) (vl-l ⊗ _) =
  bot-elim (VarLocations->¬isOnlyε vl-l oε-l)
isProp-VarLocations (_ ⊗ vl-r) (_ ⊗ε oε-r) =
  bot-elim (VarLocations->¬isOnlyε vl-r oε-r)
isProp-VarLocations (vl-l ⊗ _) (oε-l ε⊗ _) =
  bot-elim (VarLocations->¬isOnlyε vl-l oε-l)
isProp-VarLocations (vl-l1 ⊗ vl-r1) (vl-l2 ⊗ vl-r2) =
  cong2 _⊗_ (isProp-VarLocations vl-l1 vl-l2) (isProp-VarLocations vl-r1 vl-r2)


VarLocations⁰ : Pred WObj ℓ-zero
VarLocations⁰ o = VarLocations o ⊎ isOnlyε o


data Clean⁺ : WObj -> WObj -> Type₀ where
  var : Clean⁺ var var
  _ε⊗_ : {a b c : WObj} -> isOnlyε a -> Clean⁺ b c -> Clean⁺ (a ⊗ b) c
  _⊗ε_ : {a b c : WObj} -> Clean⁺ a c -> isOnlyε b -> Clean⁺ (a ⊗ b) c
  _⊗_ : {a b c d : WObj} -> Clean⁺ a b -> Clean⁺ c d -> Clean⁺ (a ⊗ c) (b ⊗ d)

data Clean : WObj -> WObj -> Type₀ where
  clean-zero : {a : WObj} -> isOnlyε a -> Clean a ε
  clean-suc : {a b : WObj} -> Clean⁺ a b -> Clean a b


Clean⁺->VarLocations : ∀ {o1 o2} -> Clean⁺ o1 o2 -> VarLocations o1
Clean⁺->VarLocations var = var
Clean⁺->VarLocations (oε ε⊗ c) = oε ε⊗ Clean⁺->VarLocations c
Clean⁺->VarLocations (c ⊗ε oε) = Clean⁺->VarLocations c ⊗ε oε
Clean⁺->VarLocations (c1 ⊗ c2) =
  Clean⁺->VarLocations c1 ⊗ Clean⁺->VarLocations c2



Clean⁺->isεFree : ∀ {o1 o2} -> Clean⁺ o1 o2 -> isεFree o2
Clean⁺->isεFree var = tt
Clean⁺->isεFree (_ ε⊗ c) = Clean⁺->isεFree c
Clean⁺->isεFree (c ⊗ε _) = Clean⁺->isεFree c
Clean⁺->isεFree (c1 ⊗ c2) = Clean⁺->isεFree c1 , Clean⁺->isεFree c2


Clean⁺->¬isOnlyε : ∀ {o1 o2} -> Clean⁺ o1 o2 -> isOnlyε o1 -> Bot
Clean⁺->¬isOnlyε var ()
Clean⁺->¬isOnlyε (_ ε⊗ c) (_ , oε) = Clean⁺->¬isOnlyε c oε
Clean⁺->¬isOnlyε (c ⊗ε _) (oε , _) = Clean⁺->¬isOnlyε c oε
Clean⁺->¬isOnlyε (c ⊗ _) (oε , _) = Clean⁺->¬isOnlyε c oε


Clean⁺-isεFree->path : ∀ {o1 o2} -> Clean⁺ o1 o2 -> isεFree o1 -> o1 == o2
Clean⁺-isεFree->path var _ = refl
Clean⁺-isεFree->path (oε ε⊗ _) (εF , _) = bot-elim (isOnlyε->¬isεFree _ oε εF)
Clean⁺-isεFree->path (_ ⊗ε oε) (_ , εF) = bot-elim (isOnlyε->¬isεFree _ oε εF)
Clean⁺-isεFree->path (l ⊗ r) (l-εF , r-εF) =
  cong2 _⊗_ (Clean⁺-isεFree->path l l-εF) (Clean⁺-isεFree->path r r-εF)

Clean-isεFree->path : ∀ {o1 o2} -> Clean o1 o2 -> isεFree o1 -> o1 == o2
Clean-isεFree->path (clean-zero oε) εF = bot-elim (isOnlyε->¬isεFree _ oε εF)
Clean-isεFree->path (clean-suc c) = Clean⁺-isεFree->path c

Clean-preserves-isεFree : ∀ {o1 o2} -> Clean o1 o2 -> isεFree o1 -> isεFree o2
Clean-preserves-isεFree (clean-zero oε) εF = bot-elim (isOnlyε->¬isεFree _ oε εF)
Clean-preserves-isεFree (clean-suc c) _ = Clean⁺->isεFree c


isProp-Clean⁺ : ∀ {o1 o2} -> isProp (Clean⁺ o1 o2)
isProp-Clean⁺ var var = refl
isProp-Clean⁺ (c-l1 ⊗ε oε-r1) (c-l2 ⊗ε oε-r2) =
  cong2 _⊗ε_ (isProp-Clean⁺ c-l1 c-l2) (isProp-isOnlyε _ oε-r1 oε-r2)
isProp-Clean⁺ (_ ⊗ε oε-r) (_ ε⊗ c-r) =
  bot-elim (Clean⁺->¬isOnlyε c-r oε-r)
isProp-Clean⁺ (_ ⊗ε oε-r) (_ ⊗ c-r) =
  bot-elim (Clean⁺->¬isOnlyε c-r oε-r)
isProp-Clean⁺ (oε-l ε⊗ _) (c-l ⊗ε _) =
  bot-elim (Clean⁺->¬isOnlyε c-l oε-l)
isProp-Clean⁺ (oε-l1 ε⊗ c-r1) (oε-l2 ε⊗ c-r2) =
  cong2 _ε⊗_ (isProp-isOnlyε _ oε-l1 oε-l2) (isProp-Clean⁺ c-r1 c-r2)
isProp-Clean⁺ (oε-l ε⊗ _) (c-l ⊗ _) =
  bot-elim (Clean⁺->¬isOnlyε c-l oε-l)
isProp-Clean⁺ (_ ⊗ c-r) (_ ⊗ε oε-r) =
  bot-elim (Clean⁺->¬isOnlyε c-r oε-r)
isProp-Clean⁺ (c-l ⊗ _) (oε-l ε⊗ _) =
  bot-elim (Clean⁺->¬isOnlyε c-l oε-l)
isProp-Clean⁺ (c-l1 ⊗ c-r1) (c-l2 ⊗ c-r2) =
  \i -> (isProp-Clean⁺ c-l1 c-l2 i) ⊗ (isProp-Clean⁺ c-r1 c-r2 i)

isProp-ΣClean⁺ : ∀ o1 -> (a b : Σ WObj (Clean⁺ o1)) -> a == b
isProp-ΣClean⁺ o1 a b = ΣProp-path isProp-Clean⁺ (isProp-ΣClean⁺' o1 a b)
  where
  isProp-ΣClean⁺' : ∀ o1 -> (a b : Σ WObj (Clean⁺ o1)) -> fst a == fst b
  isProp-ΣClean⁺' var (var , var) (var , var) = refl
  isProp-ΣClean⁺' (a ⊗ b) (_ , (l1 ε⊗ r1)) (_ , (l2 ⊗ε r2)) =
    bot-elim (Clean⁺->¬isOnlyε l2 l1)
  isProp-ΣClean⁺' (a ⊗ b) (_ , (l1 ε⊗ r1)) (_ , (l2 ε⊗ r2)) =
    isProp-ΣClean⁺' _  (_ , r1) (_ , r2)
  isProp-ΣClean⁺' (a ⊗ b) (_ , (l1 ⊗ε r1)) (_ , (l2 ⊗ε r2)) =
    isProp-ΣClean⁺' _  (_ , l1) (_ , l2)
  isProp-ΣClean⁺' (a ⊗ b) (_ , (l1 ⊗ε r1)) (_ , (l2 ε⊗ r2)) =
    bot-elim (Clean⁺->¬isOnlyε l1 l2)
  isProp-ΣClean⁺' (a ⊗ b) (_ , (l1 ⊗ r1)) (_ , (l2 ⊗ε r2)) =
    bot-elim (Clean⁺->¬isOnlyε r1 r2)
  isProp-ΣClean⁺' (a ⊗ b) (_ , (l1 ⊗ r1)) (_ , (l2 ε⊗ r2)) =
    bot-elim (Clean⁺->¬isOnlyε l1 l2)
  isProp-ΣClean⁺' (a ⊗ b) (_ , (l1 ⊗ε r1)) (_ , (l2 ⊗ r2))  =
    bot-elim (Clean⁺->¬isOnlyε r2 r1)
  isProp-ΣClean⁺' (a ⊗ b) (_ , (l1 ε⊗ r1)) (_ , (l2 ⊗ r2))  =
    bot-elim (Clean⁺->¬isOnlyε l2 l1)
  isProp-ΣClean⁺' (a ⊗ b) (_ , (l1 ⊗ r1)) (_ , (l2 ⊗ r2))  =
    cong2 _⊗_ (isProp-ΣClean⁺' _ (_ , l1) (_ , l2)) (isProp-ΣClean⁺' _ (_ , r1) (_ , r2))

isProp-ΣClean : ∀ o1 -> (a b : Σ WObj (Clean o1)) -> a == b
isProp-ΣClean o1 (_ , clean-zero oε) (_ , clean-suc c) =
  bot-elim (Clean⁺->¬isOnlyε c oε)
isProp-ΣClean o1 (ε , clean-zero p1) (ε , clean-zero p2) =
  \i -> ε , clean-zero (isProp-isOnlyε o1 p1 p2 i)
isProp-ΣClean o1 (_ , clean-suc c) (_ , clean-zero oε) =
  bot-elim (Clean⁺->¬isOnlyε c oε)
isProp-ΣClean o (o1 , clean-suc c1) (o2 , clean-suc c2) =
  let p = isProp-ΣClean⁺ o (o1 , c1) (o2 , c2) in
  \i -> fst (p i) , clean-suc (snd (p i))


opaque
  clean⁺ : {o : WObj} -> VarLocations o -> (Σ WObj (Clean⁺ o))
  clean⁺ var = var , var
  clean⁺ (oε-l ε⊗ vl-r) =
    let (o , c) = clean⁺ vl-r in o , oε-l ε⊗ c
  clean⁺ (vl-l ⊗ε oε-r) =
    let (o , c) = clean⁺ vl-l in o , c ⊗ε oε-r
  clean⁺ (vl-l ⊗ vl-r) =
    let (ol , cl) = clean⁺ vl-l in
    let (or , cr) = clean⁺ vl-r in
    (ol ⊗ or) , (cl ⊗ cr)

  Σclean : ∀ o -> (Σ WObj (Clean o))
  Σclean v with dec-VarLocations v
  ... | (inj-l vl) = let (o , c) = clean⁺ vl in (o , clean-suc c)
  ... | (inj-r oε) = ε , clean-zero oε

∃!clean : ∀ o -> ∃! WObj (Clean o)
∃!clean o = Σclean o , isProp-ΣClean o _

clean : WObj -> WObj
clean o = fst (Σclean o)
