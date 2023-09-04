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
open import equality
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



module _ (magic : Magic) where
  private
    _cp++_ : {o1 o2 o3 : WObj} -> CleanPath o1 o2 -> CleanPath o2 o3 -> CleanPath o1 o3
    _cp++_ = magic
    cp-lift-⊗ʳ : (o1 : WObj) {o2 o3 : WObj} -> CleanPath o2 o3 -> CleanPath (o1 ⊗ o2) (o1 ⊗ o3)
    cp-lift-⊗ʳ = magic
    cp-lift-⊗ˡ : {o2 o3 : WObj} -> CleanPath o2 o3 -> (o1 : WObj) -> CleanPath (o2 ⊗ o1) (o3 ⊗ o1)
    cp-lift-⊗ˡ = magic
    cp-lift-⊗ : {o1 o2 o3 o4 : WObj} -> CleanPath o1 o2 -> CleanPath o3 o4 -> CleanPath (o1 ⊗ o3) (o2 ⊗ o4)
    cp-lift-⊗ {o1} {o2} {o3} {o4} p12 p34 = (cp-lift-⊗ˡ p12 o3) cp++ (cp-lift-⊗ʳ o2 p34)

    dm-cons : {o1 o2 o3 : WObj} -> DirtyMor o1 o2 -> DirtyPath o2 o3 -> DirtyPath o1 o3
    dm-cons = magic
    _dp++_ : {o1 o2 o3 : WObj} -> DirtyPath o1 o2 -> DirtyPath o2 o3 -> DirtyPath o1 o3
    _dp++_ = magic
    dp-lift-⊗ʳ : (o1 : WObj) {o2 o3 : WObj} -> DirtyPath o2 o3 -> DirtyPath (o1 ⊗ o2) (o1 ⊗ o3)
    dp-lift-⊗ʳ = magic
    dp-lift-⊗ˡ : {o2 o3 : WObj} -> DirtyPath o2 o3 -> (o1 : WObj) -> DirtyPath (o2 ⊗ o1) (o3 ⊗ o1)
    dp-lift-⊗ˡ = magic
    dp-lift-⊗ : {o1 o2 o3 o4 : WObj} -> DirtyPath o1 o2 -> DirtyPath o3 o4 -> DirtyPath (o1 ⊗ o3) (o2 ⊗ o4)
    dp-lift-⊗ {o1} {o2} {o3} {o4} p12 p34 = (dp-lift-⊗ˡ p12 o3) dp++ (dp-lift-⊗ʳ o2 p34)

  -- isOnlyε->clean-path : (a : WObj) -> isOnlyε a -> CleanPath a ε
  -- isOnlyε->clean-path ε _ = (empty refl , tt)
  -- isOnlyε->clean-path var ()
  -- isOnlyε->clean-path (l ⊗ r) (oε-l , oε-r) =
  --   (cp-lift-⊗ (isOnlyε->clean-path l oε-l) (isOnlyε->clean-path r oε-r)) cp++
  --   ((λ⇒' ε) :: (empty refl) , tt , tt)

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
  clean⁺->dirty-path (clean-⊗ _ _ c1 c2) =
    dp-lift-⊗ (clean⁺->dirty-path c1) (clean⁺->dirty-path c2)

-- clean-mor-preserves-Clean⁺ : {a b c : WObj} -> CleanMor a b -> Clean⁺ a c -> Clean⁺ b c
-- clean-mor-preserves-Clean⁺ (λ⇒' o , tt) (_ ε⊗ c) = c
-- clean-mor-preserves-Clean⁺ (λ⇒' o , tt) (c ⊗ε _) =
--   bot-elim (Clean⁺->¬isOnlyε c tt)
-- clean-mor-preserves-Clean⁺ (λ⇒' o , tt) (clean-⊗ _ _ c _) =
--   bot-elim (Clean⁺->¬isOnlyε c tt)
-- clean-mor-preserves-Clean⁺ (ρ⇒' o , tt) (c ⊗ε _) = c
-- clean-mor-preserves-Clean⁺ (ρ⇒' o , tt) (_ ε⊗ c) =
--   bot-elim (Clean⁺->¬isOnlyε c tt)
-- clean-mor-preserves-Clean⁺ (ρ⇒' o , tt) (clean-⊗ _ _ _ c) =
--   bot-elim (Clean⁺->¬isOnlyε c tt)
-- clean-mor-preserves-Clean⁺ ((l ⊗ˡ' r) , _) (clean-⊗ _ _ _ _) = ?
-- clean-mor-preserves-Clean⁺ ((l ⊗ˡ' r) , _) (_ ⊗ε _) = ?
-- clean-mor-preserves-Clean⁺ ((l ⊗ˡ' r) , _) (_ ε⊗ _) = ?
--
-- clean-mor-preserves-Clean⁺ ((l ⊗ʳ' r) , _) (clean-⊗ _ _ _ _) = ?
-- clean-mor-preserves-Clean⁺ ((l ⊗ʳ' r) , _) (_ ⊗ε _) = ?
-- clean-mor-preserves-Clean⁺ ((l ⊗ʳ' r) , _) (_ ε⊗ _) = ?


cm-lift-⊗ˡ : {o1 o2 : WObj} -> CleanMor o1 o2 -> (o3 : WObj) -> CleanMor (o1 ⊗ o3) (o2 ⊗ o3)
cm-lift-⊗ˡ (m , cm) o = (m ⊗ˡ' o , cm)

cm-lift-⊗ʳ : (o1 : WObj) {o2 o3 : WObj} -> CleanMor o2 o3  -> CleanMor (o1 ⊗ o2) (o1 ⊗ o3)
cm-lift-⊗ʳ o (m , cm) = (o ⊗ʳ' m , cm)

cm-cons : {o1 o2 o3 : WObj} -> CleanMor o1 o2 -> CleanPath o2 o3 -> CleanPath o1 o3
cm-cons (m , cm) (p , cp) = (m :: p , cm , cp)

module InMonoidalClean {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C)
         (obj : Obj C) (magic : Magic) where
  open CategoryHelpers C
  open MonoidalStrHelpers MC renaming (⊗ to ⊗F)
  open MonoidalStrHelpers2 MC
  open InMonoidal MC obj


  -- TODO Fix these
  private
    _cp++_ : {o1 o2 o3 : WObj} -> CleanPath o1 o2 -> CleanPath o2 o3 -> CleanPath o1 o3
    _cp++_ = magic
    cp-lift-⊗ʳ : (o1 : WObj) {o2 o3 : WObj} -> CleanPath o2 o3 -> CleanPath (o1 ⊗ o2) (o1 ⊗ o3)
    cp-lift-⊗ʳ = magic
    cp-lift-⊗ˡ : {o2 o3 : WObj} -> CleanPath o2 o3 -> (o1 : WObj) -> CleanPath (o2 ⊗ o1) (o3 ⊗ o1)
    cp-lift-⊗ˡ = magic
    cp-lift-⊗ : {o1 o2 o3 o4 : WObj} -> CleanPath o1 o2 -> CleanPath o3 o4 -> CleanPath (o1 ⊗ o3) (o2 ⊗ o4)
    cp-lift-⊗ {o1} {o2} {o3} {o4} p12 p34 = (cp-lift-⊗ˡ p12 o3) cp++ (cp-lift-⊗ʳ o2 p34)

    clean->clean-path : {a b : WObj} -> Clean a b -> CleanPath a b
    clean->clean-path = magic




  dirty-path->mor : {a b : WObj} -> DirtyPath a b -> C [ inj₀ a , inj₀ b ]
  dirty-path->mor (p , _) = basic-path->mor p

  dirty-mor->mor : {a b : WObj} -> DirtyMor a b -> C [ inj₀ a , inj₀ b ]
  dirty-mor->mor (m , _) = basic-mor->mor m

  clean-path->mor : {a b : WObj} -> CleanPath a b -> C [ inj₀ a , inj₀ b ]
  clean-path->mor (p , _) = basic-path->mor p

  clean-mor->mor : {a b : WObj} -> CleanMor a b -> C [ inj₀ a , inj₀ b ]
  clean-mor->mor (m , _) = basic-mor->mor m

  private
    clean-mor->mor-cm-lift-⊗ˡ : {o2 o3 : WObj} -> (l : CleanMor o2 o3) -> (r : WObj) ->
       clean-mor->mor (cm-lift-⊗ˡ l r) == clean-mor->mor l ⊗₁ (id C)
    clean-mor->mor-cm-lift-⊗ˡ = magic

    clean-path->mor-cp-lift-⊗ˡ : {o2 o3 : WObj} -> (l : CleanPath o2 o3) -> (r : WObj) ->
       clean-path->mor (cp-lift-⊗ˡ l r) == clean-path->mor l ⊗₁ (id C)
    clean-path->mor-cp-lift-⊗ˡ = magic


  private
    P : Pred WObj _
    P o1 = (o2 : WObj) -> (Clean o1 o2) ->
           (m1 m2 : CleanPath o1 o2) ->
           (clean-path->mor m1 == clean-path->mor m2)
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


  λλ-case : {o : WObj} -> CleanSubSolution (λ⇒' o , tt) (λ⇒' o , tt)
  λλ-case = clean-sub-solution (empty refl , tt) (empty refl , tt) refl

  λρ-case : CleanSubSolution (λ⇒' ε , tt) (ρ⇒' ε , tt)
  λρ-case = clean-sub-solution (empty refl , tt) (empty refl , tt) (⋆-left λ⇒=ρ⇒)

  λr-case : {o1 o2 : WObj} (m : CleanMor o1 o2) -> CleanSubSolution (λ⇒' o1 , tt) (cm-lift-⊗ʳ ε m)
  λr-case {o1} {o2} m = clean-sub-solution1 m (λ⇒' o2 , tt) λ⇒-swap

  clean-sub-solution-lift-⊗ˡ :
    {os o1 o2 : WObj} {cm1 : CleanMor os o1} {cm2 : CleanMor os o2} ->
    CleanSubSolution cm1 cm2 -> (or : WObj) ->
    CleanSubSolution (cm-lift-⊗ˡ cm1 or) (cm-lift-⊗ˡ cm2 or)
  clean-sub-solution-lift-⊗ˡ {cm1 = cm1} {cm2 = cm2} (clean-sub-solution p1 p2 q) or =
    clean-sub-solution (cp-lift-⊗ˡ p1 or) (cp-lift-⊗ˡ p2 or)
      (⋆-cong (clean-mor->mor-cm-lift-⊗ˡ cm1 or) (clean-path->mor-cp-lift-⊗ˡ p1 or) >=>
       sym split₁ˡ >=>
       (\i -> (q i ⊗₁ id C)) >=>
       split₁ˡ >=>
       sym (⋆-cong (clean-mor->mor-cm-lift-⊗ˡ cm2 or) (clean-path->mor-cp-lift-⊗ˡ p2 or)))


  clean-mor-preserves-Clean : {a b c : WObj} -> CleanMor a b -> Clean a c -> Clean b c
  clean-mor-preserves-Clean = magic


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



  λ-cases : {o1 o2 : WObj} -> (m : CleanMor (ε ⊗ o1) o2) ->
            CleanSubSolution (λ⇒' o1 , tt) m
  λ-cases (λ⇒' _   , tt) = λλ-case
  λ-cases (ρ⇒' _   , tt) = λρ-case
  λ-cases (_ ⊗ʳ' m , cm) = λr-case (m , cm)
  λ-cases ((λ⇐' _) ⊗ˡ' _ , ())
  λ-cases ((ρ⇐' _) ⊗ˡ' _ , ())
