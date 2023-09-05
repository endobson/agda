{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal.clean-mor where

open import additive-group
open import additive-group.instances.nat
open import base
open import category.base
open import category.monoidal.base
open import category.monoidal.formal.base
open import category.monoidal.formal.clean
open import category.monoidal.semicartesian -- TODO remove this dep
open import equality-path
open import nat.order
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import relation

isCleanMor : {a b : WObj} -> Pred (BasicMor a b) ℓ-zero
isCleanMor (λ⇒' _) = Top
isCleanMor (ρ⇒' _) = Top
isCleanMor (m ⊗ˡ' w) = isCleanMor m
isCleanMor (w ⊗ʳ' m) = isCleanMor m
isCleanMor (α⇒' a b c) = Bot
isCleanMor (α⇐' _ _ _) = Bot
isCleanMor (λ⇐' _) = Bot
isCleanMor (ρ⇐' _) = Bot

CleanMor : WObj -> WObj -> Type₀
CleanMor a b = Σ (BasicMor a b) isCleanMor

isCleanPath : {a b : WObj} -> Pred (BasicPath a b) ℓ-zero
isCleanPath (empty p) = Top
isCleanPath (m :: p) = isCleanMor m × isCleanPath p

CleanPath : WObj -> WObj -> Type₀
CleanPath a b = Σ (BasicPath a b) isCleanPath

isDirtyMor : {a b : WObj} -> Pred (BasicMor a b) ℓ-zero
isDirtyMor (λ⇐' _) = Top
isDirtyMor (ρ⇐' _) = Top
isDirtyMor (m ⊗ˡ' w) = isDirtyMor m
isDirtyMor (w ⊗ʳ' m) = isDirtyMor m
isDirtyMor (α⇒' a b c) = Bot
isDirtyMor (α⇐' _ _ _) = Bot
isDirtyMor (λ⇒' _) = Bot
isDirtyMor (ρ⇒' _) = Bot

DirtyMor : WObj -> WObj -> Type₀
DirtyMor a b = Σ (BasicMor a b) isDirtyMor

isDirtyPath : {a b : WObj} -> Pred (BasicPath a b) ℓ-zero
isDirtyPath (empty p) = Top
isDirtyPath (m :: p) = isDirtyMor m × isDirtyPath p

DirtyPath : WObj -> WObj -> Type₀
DirtyPath a b = Σ (BasicPath a b) isDirtyPath

cm-lift-⊗ˡ : {o1 o2 : WObj} -> CleanMor o1 o2 -> (o3 : WObj) -> CleanMor (o1 ⊗ o3) (o2 ⊗ o3)
cm-lift-⊗ˡ (m , cm) o = (m ⊗ˡ' o , cm)

cm-lift-⊗ʳ : (o1 : WObj) {o2 o3 : WObj} -> CleanMor o2 o3  -> CleanMor (o1 ⊗ o2) (o1 ⊗ o3)
cm-lift-⊗ʳ o (m , cm) = (o ⊗ʳ' m , cm)

cm-cons : {o1 o2 o3 : WObj} -> CleanMor o1 o2 -> CleanPath o2 o3 -> CleanPath o1 o3
cm-cons (m , cm) (p , cp) = (m :: p , cm , cp)

dm-lift-⊗ˡ : {o1 o2 : WObj} -> DirtyMor o1 o2 -> (o3 : WObj) -> DirtyMor (o1 ⊗ o3) (o2 ⊗ o3)
dm-lift-⊗ˡ (m , dm) o = (m ⊗ˡ' o , dm)

dm-lift-⊗ʳ : (o1 : WObj) {o2 o3 : WObj} -> DirtyMor o2 o3  -> DirtyMor (o1 ⊗ o2) (o1 ⊗ o3)
dm-lift-⊗ʳ o (m , dm) = (o ⊗ʳ' m , dm)


dm-cons : {o1 o2 o3 : WObj} -> DirtyMor o1 o2 -> DirtyPath o2 o3 -> DirtyPath o1 o3
dm-cons (m , dm) (p , dp) = (m :: p , dm , dp)


icp-bp++ : {a b c : WObj} -> (p1 : BasicPath a b) -> (p2 : BasicPath b c) ->
           isCleanPath p1 -> isCleanPath p2 -> isCleanPath (p1 bp++ p2)
icp-bp++ {a} {b} {c} (empty p) p2 icp1 icp2 = ans
  where
  ans : isCleanPath (transport (\i -> BasicPath (p (~ i)) c) p2)
  ans = transport (\i -> isCleanPath (transport-filler (\j -> BasicPath (p (~ j)) c) p2 i)) icp2
icp-bp++ (m :: p1) p2 (icm , icp1) icp2 =
  icm , (icp-bp++ p1 p2 icp1 icp2)

idp-bp++ : {a b c : WObj} -> (p1 : BasicPath a b) -> (p2 : BasicPath b c) ->
           isDirtyPath p1 -> isDirtyPath p2 -> isDirtyPath (p1 bp++ p2)
idp-bp++ {a} {b} {c} (empty p) p2 idp1 idp2 = ans
  where
  ans : isDirtyPath (transport (\i -> BasicPath (p (~ i)) c) p2)
  ans = transport (\i -> isDirtyPath (transport-filler (\j -> BasicPath (p (~ j)) c) p2 i)) idp2
idp-bp++ (m :: p1) p2 (idm , idp1) idp2 =
  idm , (idp-bp++ p1 p2 idp1 idp2)


_cp++_ : {o1 o2 o3 : WObj} -> CleanPath o1 o2 -> CleanPath o2 o3 -> CleanPath o1 o3
(p1 , icp1) cp++ (p2 , icp2) = p1 bp++ p2 , icp-bp++ p1 p2 icp1 icp2

_dp++_ : {o1 o2 o3 : WObj} -> DirtyPath o1 o2 -> DirtyPath o2 o3 -> DirtyPath o1 o3
(p1 , idp1) dp++ (p2 , idp2) = p1 bp++ p2 , idp-bp++ p1 p2 idp1 idp2


cp-lift-⊗ʳ : (o1 : WObj) {o2 o3 : WObj} -> CleanPath o2 o3 -> CleanPath (o1 ⊗ o2) (o1 ⊗ o3)
cp-lift-⊗ʳ o1 (empty p , _) = empty (cong (o1 ⊗_) p) , tt
cp-lift-⊗ʳ o1 (m :: p , cm , cp) = cm-cons (cm-lift-⊗ʳ o1 (m , cm)) (cp-lift-⊗ʳ o1 (p , cp))
cp-lift-⊗ˡ : {o2 o3 : WObj} -> CleanPath o2 o3 -> (o1 : WObj) -> CleanPath (o2 ⊗ o1) (o3 ⊗ o1)
cp-lift-⊗ˡ (empty p , _) o1 = empty (cong (_⊗ o1) p) , tt
cp-lift-⊗ˡ (m :: p , cm , cp) o1 = cm-cons (cm-lift-⊗ˡ (m , cm) o1) (cp-lift-⊗ˡ (p , cp) o1)
cp-lift-⊗ : {o1 o2 o3 o4 : WObj} -> CleanPath o1 o2 -> CleanPath o3 o4 -> CleanPath (o1 ⊗ o3) (o2 ⊗ o4)
cp-lift-⊗ {o1} {o2} {o3} {o4} p12 p34 = (cp-lift-⊗ˡ p12 o3) cp++ (cp-lift-⊗ʳ o2 p34)

dp-lift-⊗ʳ : (o1 : WObj) {o2 o3 : WObj} -> DirtyPath o2 o3 -> DirtyPath (o1 ⊗ o2) (o1 ⊗ o3)
dp-lift-⊗ʳ o1 (empty p , _) = empty (cong (o1 ⊗_) p) , tt
dp-lift-⊗ʳ o1 (m :: p , dm , dp) = dm-cons (dm-lift-⊗ʳ o1 (m , dm)) (dp-lift-⊗ʳ o1 (p , dp))
dp-lift-⊗ˡ : {o2 o3 : WObj} -> DirtyPath o2 o3 -> (o1 : WObj) -> DirtyPath (o2 ⊗ o1) (o3 ⊗ o1)
dp-lift-⊗ˡ (empty p , _) o1 = empty (cong (_⊗ o1) p) , tt
dp-lift-⊗ˡ (m :: p , dm , dp) o1 = dm-cons (dm-lift-⊗ˡ (m , dm) o1) (dp-lift-⊗ˡ (p , dp) o1)
dp-lift-⊗ : {o1 o2 o3 o4 : WObj} -> DirtyPath o1 o2 -> DirtyPath o3 o4 -> DirtyPath (o1 ⊗ o3) (o2 ⊗ o4)
dp-lift-⊗ {o1} {o2} {o3} {o4} p12 p34 = (dp-lift-⊗ˡ p12 o3) dp++ (dp-lift-⊗ʳ o2 p34)


invert-icm : {a b : WObj} -> (m : BasicMor a b) -> isCleanMor m -> isDirtyMor (invert-bm m)
invert-icm (λ⇒' _) x = x
invert-icm (λ⇐' _) x = x
invert-icm (ρ⇒' _) x = x
invert-icm (ρ⇐' _) x = x
invert-icm (α⇒' _ _ _) x = x
invert-icm (α⇐' _ _ _) x = x
invert-icm (m ⊗ˡ' _) x = invert-icm m x
invert-icm (_ ⊗ʳ' m) x = invert-icm m x

invert-idm : {a b : WObj} -> (m : BasicMor a b) -> isDirtyMor m -> isCleanMor (invert-bm m)
invert-idm (λ⇒' _) x = x
invert-idm (λ⇐' _) x = x
invert-idm (ρ⇒' _) x = x
invert-idm (ρ⇐' _) x = x
invert-idm (α⇒' _ _ _) x = x
invert-idm (α⇐' _ _ _) x = x
invert-idm (m ⊗ˡ' _) x = invert-idm m x
invert-idm (_ ⊗ʳ' m) x = invert-idm m x


invert-icp : {a b : WObj} -> (p : BasicPath a b) -> isCleanPath p -> isDirtyPath (invert-bp' p)
invert-icp (empty p) tt = tt
invert-icp (m :: p) (icm , icp) =
  idp-bp++ (invert-bp' p) (invert-bm m :: (empty refl)) (invert-icp p icp) (invert-icm m icm , tt)

invert-idp : {a b : WObj} -> (p : BasicPath a b) -> isDirtyPath p -> isCleanPath (invert-bp' p)
invert-idp (empty p) tt = tt
invert-idp (m :: p) (idm , idp) =
  icp-bp++ (invert-bp' p) (invert-bm m :: (empty refl)) (invert-idp p idp) (invert-idm m idm , tt)


invert-cm : {a b : WObj} -> CleanMor a b -> DirtyMor b a
invert-cm (m , cm) = invert-bm m , invert-icm m cm

invert-dm : {a b : WObj} -> DirtyMor a b -> CleanMor b a
invert-dm (m , dm) = invert-bm m , invert-idm m dm

invert-cp : {a b : WObj} -> CleanPath a b -> DirtyPath b a
invert-cp (p , icp) = invert-bp' p , invert-icp p icp

invert-dp : {a b : WObj} -> DirtyPath a b -> CleanPath b a
invert-dp (p , idp) = invert-bp' p , invert-idp p idp


isOnlyε->dirty-path : (a : WObj) -> isOnlyε a -> DirtyPath ε a
isOnlyε->dirty-path ε _ = (empty refl , tt)
isOnlyε->dirty-path var ()
isOnlyε->dirty-path (l ⊗ r) (oε-l , oε-r) =
  dm-cons (λ⇐' ε , tt) (dp-lift-⊗ (isOnlyε->dirty-path l oε-l) (isOnlyε->dirty-path r oε-r))


clean⁺->dirty-path : {a b : WObj} -> Clean⁺ a b -> DirtyPath b a
clean⁺->dirty-path var = (empty refl , tt)
clean⁺->dirty-path (oε ε⊗ c) =
  dm-cons (λ⇐' _ , tt) (dp-lift-⊗ (isOnlyε->dirty-path _ oε) (clean⁺->dirty-path c))
clean⁺->dirty-path (c ⊗ε oε) =
  dm-cons (ρ⇐' _ , tt) (dp-lift-⊗ (clean⁺->dirty-path c) (isOnlyε->dirty-path _ oε))
clean⁺->dirty-path (c1 ⊗ c2) =
  dp-lift-⊗ (clean⁺->dirty-path c1) (clean⁺->dirty-path c2)

clean->dirty-path : {a b : WObj} -> Clean a b -> DirtyPath b a
clean->dirty-path (clean-zero oε) = isOnlyε->dirty-path _ oε
clean->dirty-path (clean-suc c) = clean⁺->dirty-path c

clean->clean-path : {a b : WObj} -> Clean a b -> CleanPath a b
clean->clean-path c = invert-dp (clean->dirty-path c)


clean-mor-preserves-isOnlyε : {a b : WObj} -> CleanMor a b -> isOnlyε a -> isOnlyε b
clean-mor-preserves-isOnlyε (λ⇒' o , tt) (_ , oε) = oε
clean-mor-preserves-isOnlyε (ρ⇒' o , tt) (oε , _) = oε
clean-mor-preserves-isOnlyε (l ⊗ˡ' r , cl) (oε-l , oε-r) =
  clean-mor-preserves-isOnlyε (l , cl) oε-l , oε-r
clean-mor-preserves-isOnlyε (l ⊗ʳ' r , cr) (oε-l , oε-r) =
  oε-l , clean-mor-preserves-isOnlyε (r , cr) oε-r

clean-mor-preserves-Clean⁺ : {a b c : WObj} -> CleanMor a b -> Clean⁺ a c -> Clean⁺ b c
clean-mor-preserves-Clean⁺ (λ⇒' o , tt) (_ ε⊗ c) = c
clean-mor-preserves-Clean⁺ (λ⇒' o , tt) (c ⊗ε _) =
  bot-elim (Clean⁺->¬isOnlyε c tt)
clean-mor-preserves-Clean⁺ (λ⇒' o , tt) (c ⊗ _) =
  bot-elim (Clean⁺->¬isOnlyε c tt)
clean-mor-preserves-Clean⁺ (ρ⇒' o , tt) (_ ε⊗ c) =
  bot-elim (Clean⁺->¬isOnlyε c tt)
clean-mor-preserves-Clean⁺ (ρ⇒' o , tt) (c ⊗ε _) = c
clean-mor-preserves-Clean⁺ (ρ⇒' o , tt) (_ ⊗ c) =
  bot-elim (Clean⁺->¬isOnlyε c tt)
clean-mor-preserves-Clean⁺ ((l ⊗ˡ' _) , isC-l) (cl ⊗ cr) =
 (clean-mor-preserves-Clean⁺ (l , isC-l) cl) ⊗ cr
clean-mor-preserves-Clean⁺ ((_ ⊗ʳ' r) , isC-r) (cl ⊗ cr) =
  cl ⊗ (clean-mor-preserves-Clean⁺ (r , isC-r) cr)
clean-mor-preserves-Clean⁺ ((l ⊗ˡ' r) , cl)    (c ⊗ε oε) =
  (clean-mor-preserves-Clean⁺ (l , cl) c) ⊗ε oε
clean-mor-preserves-Clean⁺ ((l ⊗ʳ' r) , cr)    (oε ε⊗ c) =
  oε ε⊗ (clean-mor-preserves-Clean⁺ (r , cr) c)
clean-mor-preserves-Clean⁺ ((l ⊗ˡ' r) , cl)    (oε ε⊗ c) =
  clean-mor-preserves-isOnlyε (l , cl) oε ε⊗ c
clean-mor-preserves-Clean⁺ ((l ⊗ʳ' r) , cr)    (c ⊗ε oε) =
  c ⊗ε (clean-mor-preserves-isOnlyε (r , cr) oε)


clean-mor-preserves-Clean : {a b c : WObj} -> CleanMor a b -> Clean a c -> Clean b c
clean-mor-preserves-Clean cm (clean-zero oε) = clean-zero (clean-mor-preserves-isOnlyε cm oε)
clean-mor-preserves-Clean cm (clean-suc c) = clean-suc (clean-mor-preserves-Clean⁺ cm c)

clean-path-preserves-Clean : {a b c : WObj} -> CleanPath a b -> Clean a c -> Clean b c
clean-path-preserves-Clean {c = c} (empty p , tt) =
  transport (\i -> Clean (p i) c)
clean-path-preserves-Clean {c = c} (m :: p , cm , cp) cl =
  clean-path-preserves-Clean (p , cp) (clean-mor-preserves-Clean (m , cm) cl)

clean-mor->branches< : {a b : WObj} -> CleanMor a b -> WObj-branches b < WObj-branches a
clean-mor->branches< (λ⇒' o , _)    = refl-≤
clean-mor->branches< (ρ⇒' o , _)    = trans-<-= refl-≤ (sym +-right-zero)
clean-mor->branches< (m ⊗ˡ' _ , cm) = suc-< (+₂-preserves-< (clean-mor->branches< (m , cm)))
clean-mor->branches< (o ⊗ʳ' m , cm) = suc-< (+₁-preserves-< (clean-mor->branches< (m , cm)))

clean-path->branches≤ : {a b : WObj} -> CleanPath a b -> WObj-branches b ≤ WObj-branches a
clean-path->branches≤ (empty p , tt) =
  path-≤ (cong WObj-branches (sym p))
clean-path->branches≤ (m :: p , cm , cp) =
  weaken-< (trans-≤-< (clean-path->branches≤ (p , cp)) (clean-mor->branches< (m , cm)))


module InMonoidalClean {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C)
         (obj : Obj C) where
  open CategoryHelpers C
  open MonoidalStrHelpers MC renaming (⊗ to ⊗F)
  open MonoidalStrHelpers2 MC
  open InMonoidal MC obj


  dirty-path->mor : {a b : WObj} -> DirtyPath a b -> C [ inj₀ a , inj₀ b ]
  dirty-path->mor (p , _) = basic-path->mor p

  dirty-mor->mor : {a b : WObj} -> DirtyMor a b -> C [ inj₀ a , inj₀ b ]
  dirty-mor->mor (m , _) = basic-mor->mor m

  clean-path->mor : {a b : WObj} -> CleanPath a b -> C [ inj₀ a , inj₀ b ]
  clean-path->mor (p , _) = basic-path->mor p

  clean-mor->mor : {a b : WObj} -> CleanMor a b -> C [ inj₀ a , inj₀ b ]
  clean-mor->mor (m , _) = basic-mor->mor m

  private
    clean-path->mor-cp-lift-⊗ˡ : {o2 o3 : WObj} -> (l : CleanPath o2 o3) -> (r : WObj) ->
       clean-path->mor (cp-lift-⊗ˡ l r) == clean-path->mor l ⊗₁ (id C)
    clean-path->mor-cp-lift-⊗ˡ {o2} {o3} (empty p , tt) r = ans
      where
      ans : transport (\i -> C [ inj₀ (o2 ⊗ r) , inj₀ (p i ⊗ r) ]) (id C) ==
            transport (\i -> C [ inj₀ o2 , inj₀ (p i) ]) (id C) ⊗₁ (id C)
      ans = transP-sides
             (symP (transport-filler (\i -> C [ inj₀ (o2 ⊗ r) , inj₀ (p i ⊗ r) ]) (id C)))
             (sym (F-id ⊗F _))
             (\i -> (transport-filler (\i -> C [ inj₀ o2 , inj₀ (p i) ]) (id C) i) ⊗₁ (id C))
    clean-path->mor-cp-lift-⊗ˡ {o2} {o3} (m :: p , cm , cp) r =
      ⋆-right (clean-path->mor-cp-lift-⊗ˡ (p , cp) r) >=>
      sym split₁ˡ

    clean-path->mor-cp-lift-⊗ʳ : {o2 o3 : WObj} -> (l : WObj) -> (r : CleanPath o2 o3) ->
       clean-path->mor (cp-lift-⊗ʳ l r) == (id C) ⊗₁ clean-path->mor r
    clean-path->mor-cp-lift-⊗ʳ {o2} {o3} l (empty p , tt) = ans
      where
      ans : transport (\i -> C [ inj₀ (l ⊗ o2) , inj₀ (l ⊗ p i) ]) (id C) ==
            (id C) ⊗₁ transport (\i -> C [ inj₀ o2 , inj₀ (p i) ]) (id C)
      ans = transP-sides
             (symP (transport-filler (\i -> C [ inj₀ (l ⊗ o2) , inj₀ (l ⊗ p i) ]) (id C)))
             (sym (F-id ⊗F _))
             (\i -> (id C) ⊗₁ (transport-filler (\i -> C [ inj₀ o2 , inj₀ (p i) ]) (id C) i))
    clean-path->mor-cp-lift-⊗ʳ {o2} {o3} l (m :: p , cm , cp) =
      ⋆-right (clean-path->mor-cp-lift-⊗ʳ l (p , cp)) >=>
      sym split₂ˡ


  private
    P : Pred WObj _
    P o1 = (o2 : WObj) -> (Clean o1 o2) ->
           (p1 p2 : CleanPath o1 o2) ->
           (clean-path->mor p1 == clean-path->mor p2)
    Hyp : Pred WObj _
    Hyp o = (o' : WObj) -> (WObj-branches o' < WObj-branches o) -> P o'




  record DirtySubSolution {os ol or : WObj} (m1 : DirtyMor os ol) (m2 : DirtyMor os or) : Type ℓM where
    constructor dirty-sub-solution
    field
      {os'} : WObj
      p1 : DirtyPath ol os'
      p2 : DirtyPath or os'
      path : (dirty-mor->mor m1 ⋆ dirty-path->mor p1) == (dirty-mor->mor m2 ⋆ dirty-path->mor p2)

  record CleanSubSolution {os ol or : WObj} (m1 : CleanMor os ol) (m2 : CleanMor os or) : Type ℓM where
    constructor clean-sub-solution
    field
      {os'} : WObj
      p1 : CleanPath ol os'
      p2 : CleanPath or os'
      path : (clean-mor->mor m1 ⋆ clean-path->mor p1) == (clean-mor->mor m2 ⋆ clean-path->mor p2)

  clean-sub-solution1 : {os ol or os' : WObj} {m1 : CleanMor os ol} {m2 : CleanMor os or} ->
    (p1 : CleanMor ol os')
    (p2 : CleanMor or os')
    (path : (clean-mor->mor m1 ⋆ clean-mor->mor p1) == (clean-mor->mor m2 ⋆ clean-mor->mor p2)) ->
    CleanSubSolution m1 m2
  clean-sub-solution1 m1 m2 p = clean-sub-solution
    (cm-cons m1 (empty refl , _))
    (cm-cons m2 (empty refl , _))
    (sym ⋆-assoc >=> (⋆-left p) >=> ⋆-assoc)

  sym-clean-sub-solution : {os ol or : WObj} {m1 : CleanMor os ol} {m2 : CleanMor os or} ->
    CleanSubSolution m1 m2 -> CleanSubSolution m2 m1
  sym-clean-sub-solution (clean-sub-solution p1 p2 path) = clean-sub-solution p2 p1 (sym path)

  clean-sub-solution-lift-⊗ˡ :
    {os o1 o2 : WObj} {cm1 : CleanMor os o1} {cm2 : CleanMor os o2} ->
    CleanSubSolution cm1 cm2 -> (or : WObj) ->
    CleanSubSolution (cm-lift-⊗ˡ cm1 or) (cm-lift-⊗ˡ cm2 or)
  clean-sub-solution-lift-⊗ˡ (clean-sub-solution p1 p2 q) or =
    clean-sub-solution (cp-lift-⊗ˡ p1 or) (cp-lift-⊗ˡ p2 or)
      (⋆-right (clean-path->mor-cp-lift-⊗ˡ p1 or) >=>
       sym split₁ˡ >=>
       (\i -> q i ⊗₁ id C) >=>
       split₁ˡ >=>
       sym (⋆-right (clean-path->mor-cp-lift-⊗ˡ p2 or)))

  clean-sub-solution-lift-⊗ʳ :
    {os o1 o2 : WObj} {cm1 : CleanMor os o1} {cm2 : CleanMor os o2} ->
    (ol : WObj) -> CleanSubSolution cm1 cm2 ->
    CleanSubSolution (cm-lift-⊗ʳ ol cm1) (cm-lift-⊗ʳ ol cm2)
  clean-sub-solution-lift-⊗ʳ ol (clean-sub-solution p1 p2 q) =
    clean-sub-solution (cp-lift-⊗ʳ ol p1) (cp-lift-⊗ʳ ol p2)
      (⋆-right (clean-path->mor-cp-lift-⊗ʳ ol p1) >=>
       sym split₂ˡ >=>
       (\i -> id C ⊗₁ q i) >=>
       split₂ˡ >=>
       sym (⋆-right (clean-path->mor-cp-lift-⊗ʳ ol p2)))


  use-sub-solution :
    {os ot ol or : WObj} ->
    (Hyp os) ->
    (m1 : CleanMor os ol) -> (m2 : CleanMor os or) ->
    (p1 : CleanPath ol ot) -> (p2 : CleanPath or ot) ->
    (Clean os ot) ->
    CleanSubSolution m1 m2 ->
    clean-path->mor (cm-cons m1 p1) ==
    clean-path->mor (cm-cons m2 p2)
  use-sub-solution {os} {ot} {ol} {or} hyp m1 m2 p1 p2 c-os-ot
                  (clean-sub-solution {ot'} q1 q2 m-path) =
    ⋆-right (d1 >=> (basic-path->mor-bp++ (fst q1) (fst p-ot'-ot))) >=>
    sym ⋆-assoc >=>
    ⋆-left m-path >=>
    ⋆-assoc >=>
    ⋆-right (sym (d2 >=> (basic-path->mor-bp++ (fst q2) (fst p-ot'-ot))))
    where

    c-ol-ot : Clean ol ot
    c-ol-ot = clean-mor-preserves-Clean m1 c-os-ot
    c-or-ot : Clean or ot
    c-or-ot = clean-mor-preserves-Clean m2 c-os-ot
    c-ot'-ot : Clean ot' ot
    c-ot'-ot = clean-path-preserves-Clean q1 c-ol-ot

    p-ot'-ot : CleanPath ot' ot
    p-ot'-ot = clean->clean-path c-ot'-ot

    d1 : clean-path->mor p1 == clean-path->mor (q1 cp++ p-ot'-ot)
    d1 = hyp ol (clean-mor->branches< m1)
           ot c-ol-ot p1 (q1 cp++ p-ot'-ot)

    d2 : clean-path->mor p2 == clean-path->mor (q2 cp++ p-ot'-ot)
    d2 = hyp or (clean-mor->branches< m2)
           ot c-or-ot p2 (q2 cp++ p-ot'-ot)



  λλ-case : {o : WObj} -> CleanSubSolution (λ⇒' o , tt) (λ⇒' o , tt)
  λλ-case = clean-sub-solution (empty refl , tt) (empty refl , tt) refl

  ρρ-case : {o : WObj} -> CleanSubSolution (ρ⇒' o , tt) (ρ⇒' o , tt)
  ρρ-case = clean-sub-solution (empty refl , tt) (empty refl , tt) refl

  λρ-case : CleanSubSolution (λ⇒' ε , tt) (ρ⇒' ε , tt)
  λρ-case = clean-sub-solution (empty refl , tt) (empty refl , tt) (⋆-left λ⇒=ρ⇒)

  λr-case : {o1 o2 : WObj} (m : CleanMor o1 o2) -> CleanSubSolution (λ⇒' o1 , tt) (cm-lift-⊗ʳ ε m)
  λr-case {o1} {o2} m = clean-sub-solution1 m (λ⇒' o2 , tt) λ⇒-swap

  λl-case : {o1 o2 : WObj} (m : CleanMor ε o2) -> CleanSubSolution (λ⇒' o1 , tt) (cm-lift-⊗ˡ m o1)
  λl-case (λ⇐' _ , ())
  λl-case (ρ⇐' _ , ())

  ρl-case : {o1 o2 : WObj} (m : CleanMor o1 o2) -> CleanSubSolution (ρ⇒' o1 , tt) (cm-lift-⊗ˡ m ε)
  ρl-case {o1} {o2} m = clean-sub-solution1 m (ρ⇒' o2 , tt) ρ⇒-swap

  ρr-case : {o1 o2 : WObj} (m : CleanMor ε o1) -> CleanSubSolution (ρ⇒' o2 , tt) (cm-lift-⊗ʳ o2 m)
  ρr-case (λ⇐' _ , ())
  ρr-case (ρ⇐' _ , ())


  ll-case : {os' o1 o2 or : WObj} -> Hyp (os' ⊗ or) ->
            (m1 : CleanMor os' o1) (m2 : CleanMor os' o2) ->
            CleanSubSolution (cm-lift-⊗ˡ m1 or) (cm-lift-⊗ˡ m2 or)
  ll-case {os'} {o1} {o2} {or} hyp cm1 cm2 = clean-sub-solution-lift-⊗ˡ rec or
    where
    ot' : WObj
    ot' = clean os'

    c-os'-ot' : Clean os' ot'
    c-os'-ot' = (snd (Σclean os'))

    p1 : CleanPath o1 ot'
    p1 = clean->clean-path (clean-mor-preserves-Clean cm1 c-os'-ot')
    p2 : CleanPath o2 ot'
    p2 = clean->clean-path (clean-mor-preserves-Clean cm2 c-os'-ot')

    rec : CleanSubSolution cm1 cm2
    rec = clean-sub-solution p1 p2
            (hyp os' (trans-≤-< (trans-=-≤ (sym +-right-zero) (+₁-preserves-≤ zero-≤)) (add1-< _))
                 ot' c-os'-ot' (cm-cons cm1 p1) (cm-cons cm2 p2))

  rr-case : {os' o1 o2 ol : WObj} -> Hyp (ol ⊗ os') ->
            (m1 : CleanMor os' o1) (m2 : CleanMor os' o2) ->
            CleanSubSolution (cm-lift-⊗ʳ ol m1) (cm-lift-⊗ʳ ol m2)
  rr-case {os'} {o1} {o2} {ol} hyp cm1 cm2 = clean-sub-solution-lift-⊗ʳ ol rec
    where
    ot' : WObj
    ot' = clean os'

    c-os'-ot' : Clean os' ot'
    c-os'-ot' = (snd (Σclean os'))

    p1 : CleanPath o1 ot'
    p1 = clean->clean-path (clean-mor-preserves-Clean cm1 c-os'-ot')
    p2 : CleanPath o2 ot'
    p2 = clean->clean-path (clean-mor-preserves-Clean cm2 c-os'-ot')

    rec : CleanSubSolution cm1 cm2
    rec = clean-sub-solution p1 p2
            (hyp os' (trans-≤-< (trans-=-≤ (sym +-left-zero) (+₂-preserves-≤ zero-≤)) (add1-< _))
                 ot' c-os'-ot' (cm-cons cm1 p1) (cm-cons cm2 p2))



  lr-case : {os1 os2 ol' or' : WObj} -> -- Hyp (os1 ⊗ os2) ->
            (m1 : CleanMor os1 ol') (m2 : CleanMor os2 or') ->
            CleanSubSolution (cm-lift-⊗ˡ m1 os2) (cm-lift-⊗ʳ os1 m2)
  lr-case {os1} {os2} {ol'} {or'} m1 m2 =
    clean-sub-solution1 (cm-lift-⊗ʳ ol' m2) (cm-lift-⊗ˡ m1 or')
      (sym serialize₁₂ >=> serialize₂₁)


  λ-cases : {o1 o2 : WObj} -> (m : CleanMor (ε ⊗ o1) o2) -> CleanSubSolution (λ⇒' o1 , tt) m
  λ-cases (λ⇒' _   , tt) = λλ-case
  λ-cases (ρ⇒' _   , tt) = λρ-case
  λ-cases (_ ⊗ʳ' m , cm) = λr-case (m , cm)
  λ-cases (m ⊗ˡ' _ , cm) = λl-case (m , cm)

  ρ-cases : {o1 o2 : WObj} -> (m : CleanMor (o1 ⊗ ε) o2) -> CleanSubSolution (ρ⇒' o1 , tt) m
  ρ-cases (λ⇒' _   , tt) = sym-clean-sub-solution λρ-case
  ρ-cases (ρ⇒' _   , tt) = ρρ-case
  ρ-cases (_ ⊗ʳ' m , cm) = ρr-case (m , cm)
  ρ-cases (m ⊗ˡ' _ , cm) = ρl-case (m , cm)


  l-cases : {os1 os2 ol' or : WObj} ->
            (m2 : CleanMor (os1 ⊗ os2) or) ->
            Hyp (os1 ⊗ os2) ->
            (m1 : CleanMor os1 ol') ->
            CleanSubSolution (cm-lift-⊗ˡ m1 os2) m2
  l-cases (λ⇒' _ , tt)     hyp m1 = sym-clean-sub-solution (λl-case m1)
  l-cases (ρ⇒' _ , tt)     hyp m1 = sym-clean-sub-solution (ρl-case m1)
  l-cases (m2 ⊗ˡ' _ , cm2) hyp m1 = ll-case hyp m1 (m2 , cm2)
  l-cases (_ ⊗ʳ' m2 , cm2) hyp m1 = lr-case m1 (m2 , cm2)

  r-cases : {os1 os2 ol' or : WObj} ->
            (m2 : CleanMor (os1 ⊗ os2) or) ->
            Hyp (os1 ⊗ os2) -> (m1 : CleanMor os2 ol') ->
            CleanSubSolution (cm-lift-⊗ʳ os1 m1) m2
  r-cases (λ⇒' _ , tt)     hyp m1 = sym-clean-sub-solution (λr-case m1)
  r-cases (ρ⇒' _ , tt)     hyp m1 = sym-clean-sub-solution (ρr-case m1)
  r-cases (m2 ⊗ˡ' _ , cm2) hyp m1 = sym-clean-sub-solution (lr-case (m2 , cm2) m1)
  r-cases (_ ⊗ʳ' m2 , cm2) hyp m1 = rr-case hyp m1 (m2 , cm2)

  all-cases : {os ol or : WObj} ->
              (m1 : CleanMor os ol) ->
              Hyp os -> (m2 : CleanMor os or) ->
              CleanSubSolution m1 m2
  all-cases (λ⇒' _ , tt)     hyp m2 = λ-cases m2
  all-cases (ρ⇒' _ , tt)     hyp m2 = ρ-cases m2
  all-cases (m1 ⊗ˡ' _ , cm1) hyp m2 = l-cases m2 hyp (m1 , cm1)
  all-cases (_ ⊗ʳ' m1 , cm1) hyp m2 = r-cases m2 hyp (m1 , cm1)


  parallel-clean-paths-to-clean : (o : WObj) -> P o
  parallel-clean-paths-to-clean = branch-induction {P = P} rec
    where
    rec : (o : WObj) -> Hyp o -> P o
    rec o1 hyp o2 c12 (empty p1 , _) (empty p2 , _) =
      cong basic-path->mor p1=p2
      where
      p1=p2 : empty p1 == empty p2
      p1=p2 i = empty (isSet-WObj _ _ p1 p2 i)
    rec o1 hyp o2 c12 (m1 :: p1 , cm1 , cp1) (empty p2 , _) =
      bot-elim (irrefl-path-< (sym b1=b2) b2<b1)
      where
      b1=b2 : WObj-branches o1 == WObj-branches o2
      b1=b2 = cong WObj-branches p2
      b2<b1 : WObj-branches o2 < WObj-branches o1
      b2<b1 = trans-≤-< (clean-path->branches≤ (p1 , cp1))
                        (clean-mor->branches< (m1 , cm1))
    rec o1 hyp o2 c12 (empty p1 , _) (m2 :: p2 , cm2 , cp2) =
      bot-elim (irrefl-path-< (sym b1=b2) b2<b1)
      where
      b1=b2 : WObj-branches o1 == WObj-branches o2
      b1=b2 = cong WObj-branches p1
      b2<b1 : WObj-branches o2 < WObj-branches o1
      b2<b1 = trans-≤-< (clean-path->branches≤ (p2 , cp2))
                        (clean-mor->branches< (m2 , cm2))
    rec o1 hyp o2 c12 (m1 :: p1 , icm1 , icp1) (m2 :: p2 , icm2 , icp2) =
      use-sub-solution hyp cm1 cm2 (p1 , icp1) (p2 , icp2) c12
        (all-cases cm1 hyp cm2)
      where
      cm1 : CleanMor o1 _
      cm1 = m1 , icm1
      cm2 : CleanMor o1 _
      cm2 = m2 , icm2
