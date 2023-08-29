{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal where

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
open import category.monoidal.formal-base


-- data PathFiller {ot : WObj} : {os : WObj} (m1 m2 : BasicPath os ot) -> Type₀ where
--   [] : PathFiller [] []
--   _::_ : {o1 o2 : WObj} -> (m : DirectedMor true o1 o2)
--          {p1 p2 : DirectedPath true o2 ot} -> (f : PathFiller p1 p2) ->
--          PathFiller (m :: p1) (m :: p2)


dir-⊗ˡ : {d : Boolean} {a b : WObj} ->
         DirectedMor d a b -> (w : WObj) ->
         DirectedMor d (a ⊗ w) (b ⊗ w)
dir-⊗ˡ = ?


module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C)
         (obj : Obj C) where
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
    transport (\i -> C [ inj₀ a , inj₀ (p i) ]) (id C)
  basic-path->mor (m :: p) = basic-mor->mor m ⋆ basic-path->mor p

  directed-path->mor : {d : Boolean} {a b : WObj} -> DirectedPath d a b -> C [ inj₀ a , inj₀ b ]
  directed-path->mor {d} {a} {b} (empty p) =
    transport (\i -> C [ inj₀ a , inj₀ (p i) ]) (id C)
  directed-path->mor ((m , _) :: p) = basic-mor->mor m ⋆ directed-path->mor p


  module _ (magic : Magic) where
    isSet-WObj : isSet WObj
    isSet-WObj = magic




    rankP : Pred Nat _
    rankP n = (ls : LeafShape) ->
              (o1 o2 : WObj) ->
              (WObj-rank o1 ≤ n) ->
              (p1 p2 : DirectedPath true o1 o2) ->
              (directed-path->mor p1) == (directed-path->mor p2)

    module _ {bound : Nat} (rec : ({n : Nat} -> n < bound -> rankP n)) where
      left-case :
        (s m1 m2 t w : WObj) ->
        (WObj-rank (s ⊗ w)) ≤ bound ->
        (mor1 : DirectedMor true s m1) ->
        (mor2 : DirectedMor true s m2) ->
        (dp1 : DirectedPath true (m1 ⊗ w) t) ->
        (dp2 : DirectedPath true (m2 ⊗ w) t) ->
        (directed-path->mor (dir-⊗ˡ mor1 w :: dp1)) ==
        (directed-path->mor (dir-⊗ˡ mor2 w :: dp2))
      left-case = ?


    rank-rec : {m : Nat} -> ({n : Nat} -> n < m -> rankP n) -> rankP m
    rank-rec = magic

    rank-part : (n : Nat) -> rankP n
    rank-part = strong-induction' rank-rec




    final'-part : (o1 o2 : WObj) ->
                  (p1 p2 : DirectedPath true o1 o2) ->
                  (directed-path->mor p1) == (directed-path->mor p2)
    final'-part o1 o2 =
      rank-part (WObj-rank o1) o1 o2 refl-≤

    final-part : {o1 o2 : WObj} ->
                 (p1 p2 : DirectedPath true o1 o2) ->
                 (directed-path->mor p1) == (directed-path->mor p2)
    final-part = final'-part _ _


    --module _ {o2 : WObj} {n : Nat}
    --         (rec : {o1 : WObj} -> (WObj-rank o1 < n) ->
    --                (p1 p2 : DirectedPath true o1 o2) ->
    --                (directed-path->mor p1) == (directed-path->mor p2))
    --         where

    --  length-part :



    --  left-case : (m1 m2 : WObj) ->
    --              (mor1 : DirectedMor o1 m1 )

    {-
    parallel-dirpaths->filler :
      {n : Nat}
      {o1 o2 : WObj} ->
      (WObj-rank o1 ≤ n) ->
      (m1 m2 : DirectedPath true o1 o2) ->
      (directed-path->mor m1) == (directed-path->mor m2)
    parallel-dirpaths->filler lt m1@(empty p1) m2@(empty p2) =
      cong directed-path->mor m1=m2
      where
      m1=m2 : m1 == m2
      m1=m2 i = empty (isSet-WObj _ _ p1 p2 i)
    parallel-dirpaths->filler lt (empty o1=o2) (dm :: dp) =
      bot-elim (irrefl-path-< (sym (cong WObj-rank o1=o2))
                              (trans-≤-< (dirpath->rank≤ dp) (dirmor->rank< dm)))
    parallel-dirpaths->filler lt (dm :: dp) (empty o1=o2) =
      bot-elim (irrefl-path-< (sym (cong WObj-rank o1=o2))
                              (trans-≤-< (dirpath->rank≤ dp) (dirmor->rank< dm)))

    parallel-dirpaths->filler lt
      (dm@(m@(α⇒' a b c) , (α⇒' a b c)) :: dp1)
      (((α⇒' a b c) , (α⇒' a b c)) :: dp2)
      i = basic-mor->mor m ⋆
          parallel-dirpaths->filler (trans-≤ (weaken-< (assoc-rank< a b c)) lt) dp1 dp2 i
    parallel-dirpaths->filler lt
      (((α⇒' a b c) , (α⇒' a b c)) :: dp1)
      (((m ⊗ˡ' d) , (dm ⊗ˡ' d)) :: dp2)
      = magic
    parallel-dirpaths->filler lt
      (((α⇒' a b c) , (α⇒' a b c)) :: dp1)
      (((d ⊗ʳ' m) , (d ⊗ʳ' dm)) :: dp2)
      = magic
    parallel-dirpaths->filler lt
      (((m ⊗ˡ' d) , (dm ⊗ˡ' d)) :: dp1)
      (((α⇒' a b c) , (α⇒' a b c)) :: dp2)
      = magic
    parallel-dirpaths->filler lt
      (((m1 ⊗ˡ' d) , (dm1 ⊗ˡ' d)) :: dp1)
      (((m2 ⊗ˡ' d) , (dm2 ⊗ˡ' d)) :: dp2)
      = magic
    parallel-dirpaths->filler lt
      (((m1 ⊗ˡ' d1) , (dm1 ⊗ˡ' d1)) :: dp1)
      (((d2 ⊗ʳ' m2) , (d2 ⊗ʳ' dm2)) :: dp2)
      = magic
    parallel-dirpaths->filler lt
      (((d1 ⊗ʳ' m1) , (d1 ⊗ʳ' dm1)) :: dp1)
      (((α⇒' a b c) , (α⇒' a b c)) :: dp2)
      = magic
    parallel-dirpaths->filler lt
      (((d1 ⊗ʳ' m1) , (d1 ⊗ʳ' dm1)) :: dp1)
      (((m2 ⊗ˡ' d2) , (dm2 ⊗ˡ' d2)) :: dp2)
      = magic
    parallel-dirpaths->filler lt
      (((d ⊗ʳ' m1) , (d ⊗ʳ' dm1)) :: dp1)
      (((d ⊗ʳ' m2) , (d ⊗ʳ' dm2)) :: dp2)
      = magic
    -}




  -- inj₁ : (a b : WObj) -> WMor a b -> C [ inj₀ a , inj₀ b ]
  -- inj₁ var var _ = id C
  -- inj₁ var ε (wmor l) = zero-suc-absurd (sym l)
  -- inj₁ ε ε _ = id C
  -- inj₁ ε var (wmor l) = zero-suc-absurd l
  -- inj₁ var (x ⊗ y) (wmor l) = ?




-- data αRawString : SType -> SType -> Type₀ where
--   id : (t : SType) -> αRawString t t
--   _⊗_ : {s₁ s₂ t₁ t₂ : SType} -> αRawString s₁ t₁ -> αRawString s₂ t₂ ->
--         αRawString (s₁ ⊗ s₂) (t₁ ⊗ t₂)
--   _⋆_ : {s t u : SType} -> αRawString s t -> αRawString t u ->
--         αRawString s u
--   α⇒ : {s t u : SType} -> αRawString (s ⊗ t) u -> αRawString s (t ⊗ u)
--   α⇐ : {s t u : SType} -> αRawString s (t ⊗ u) -> αRawString (s ⊗ t) u


-- data αBasicString : SType -> SType -> Type₀ where
--   _⊗ˡ_ : {s t : SType} -> αBasicString s t -> (u : SType) ->
--          αBasicString (s ⊗ u) (t ⊗ u)
--   _⊗ʳ_ : (s : SType) -> {t u : SType} -> αBasicString t u ->
--          αBasicString (s ⊗ t) (s ⊗ u)
--   α⇒ : (s t u :
