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






module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C)
         (obj : Obj C) where
  open CategoryHelpers C
  open MonoidalStrHelpers MC

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
  basic-path->mor [] = id C
  basic-path->mor (m :: p) = basic-mor->mor m ⋆ basic-path->mor p

  directed-path->mor : {d : Boolean} {a b : WObj} -> DirectedPath d a b -> C [ inj₀ a , inj₀ b ]
  directed-path->mor [] = id C
  directed-path->mor ((m , _) :: p) = basic-mor->mor m ⋆ directed-path->mor p


  --module _ (magic : Magic) where
  --  parallel-dirpaths->filler : {o1 o2 o3 : WObj} -> (o1 == o2) ->
  --                              (m1 : DirectedPath true o1 o3)
  --                              (m2 : DirectedPath true o2 o3) -> Top
  --  parallel-dirpaths->filler o1=o2 [] [] = ?
  --  parallel-dirpaths->filler o1=o2 [] (dm :: dp) =
  --    bot-elim (irrefl-path-< (cong WObj-rank o1=o2)
  --                            (trans-≤-< (dirpath->rank≤ dp) (dirmor->rank< dm)))
  --  parallel-dirpaths->filler o1=o2 (dm :: dp) [] =
  --    bot-elim (irrefl-path-< (sym (cong WObj-rank o1=o2))
  --                            (trans-≤-< (dirpath->rank≤ dp) (dirmor->rank< dm)))


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
