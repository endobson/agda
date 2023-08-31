{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal3 where

open import category.monoidal.formal-base hiding (DirectedPath ; DirectedMor)
open import category.monoidal.formal2
open import category.monoidal.base
open import category.base
open import base
open import relation
open import nat
open import equality
open import hlevel
open import order
open import order.instances.nat
open import nat.order
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import additive-group
open import additive-group.instances.nat


dm-cases : {ℓ : Level} {P : {o1 o2 : WObj} -> (BasicMor o1 o2) -> Type ℓ} ->
           (∀ a b c -> (P (α⇒' a b c))) ->
           (∀ {o1 o2} (m : BasicMor o1 o2) -> (w : WObj) -> (P (m ⊗ˡ' w))) ->
           (∀ {o1 o2} (m : BasicMor o1 o2) -> (w : WObj) -> (P (w ⊗ʳ' m))) ->
           {o1 o2 : WObj} (m : DirectedMor o1 o2) -> P (fst m)
dm-cases f1 f2 f3 (α⇒' a b c , _) = f1 a b c
dm-cases f1 f2 f3 (m ⊗ˡ' w , _) = f2 m w
dm-cases f1 f2 f3 (w ⊗ʳ' m , _) = f3 m w




-- cases : {o ol or : WObj} (m1 : DirectedMor o ol) (m2 : DirectedMor o or) -> Top
-- cases {o} {ol} {or}  m1F@(w1 ⊗ʳ' m1 , _) = sub3
--   where
--   sub3 : (m2 : DirectedMor o or) -> Top
--   sub3 (α⇒' a b c , _) = tt
--   sub3 (m2 ⊗ˡ' w2 , _) = tt
--   sub3 (w1 ⊗ʳ' m2 , _) = tt
-- cases {o} {ol} {or} m1F@(m1 ⊗ˡ' w2 , _) = sub2
--   where
--   sub2 : (m2 : DirectedMor o or) -> Top
--   sub2 (α⇒' a b c , _) = tt
--   sub2 (m2 ⊗ˡ' w2 , _) = tt
--   sub2 (w1 ⊗ʳ' m2 , _) = tt
-- cases {o} {ol} {or} m1F@(α⇒' a b c , _) = sub1
--   where
--   sub1 : (m2 : DirectedMor o or) -> Top
--   sub1 (α⇒' a b c , _) = tt
--   sub1 (m2 ⊗ˡ' w2 , _) = tt
--   sub1 (w1 ⊗ʳ' m2 , _) = tt


module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C)
         (obj : Obj C) (magic : Magic) where
  module _ (ol or ot : WObj) (p1 : BasicPath ol ot) (p2 : BasicPath or ot) where
    cases : {o : WObj}
            (m1 : DirectedMor o ol) (m2 : DirectedMor o or) ->
            basic-path->mor MC obj magic (fst m1 :: p1) ==
            basic-path->mor MC obj magic (fst m2 :: p2)
    cases {o} =
      dm-cases {P = \m1 -> (m2 : DirectedMor o or) ->
                     basic-path->mor MC obj magic (m1 :: p1) ==
                     basic-path->mor MC obj magic (fst m2 :: p2)}
        (\ a1 b1 c1 -> dm-cases (\a2 b2 c2 -> magic) (\m2 w2 -> magic) (\m2 w2 -> magic))
        (\ m1 w1 -> dm-cases (\a2 b2 c2 -> magic) (\m2 w2 -> magic) (\m2 w2 -> magic))
        (\ m1 w1 -> dm-cases (\a2 b2 c2 -> magic) (\m2 w2 -> magic) (\m2 w2 -> magic))


--    dm-cases : {ℓ : Level} {o1 o2 : WObj} {P : Pred (BasicMor o1 o) ℓ}
--               (∀ a b c -> (P (dm'->bm (α⇒ a b c)))) ->
--               (∀ m w -> (P (dm'->bm (m1 ⊗ˡ' w)))) ->
--               (∀ m w -> (P (dm'->bm (m1 ⊗ˡ' w)))) ->
--               {o: WObj} (m1 : DirectedMor o ol) (m2 : DirectedMor o or) ->

    -- cases : {o : WObj} (m1 : DirectedMor o ol) (m2 : DirectedMor o or) ->
    --         basic-path->mor MC obj magic (fst m1 :: p1) ==
    --         basic-path->mor MC obj magic (fst m2 :: p2)
    -- cases {o} m1F@(w1 ⊗ʳ' m1 , _) = sub3
    --   where
    --   sub3 : (m2 : DirectedMor o or) ->
    --         basic-path->mor MC obj magic (fst m1F :: p1) ==
    --         basic-path->mor MC obj magic (fst m2 :: p2)
    --   sub3 (α⇒' a b c , _) = magic
    --   sub3 (m2 ⊗ˡ' w2 , _) = magic
    --   sub3 (w1 ⊗ʳ' m2 , _) = magic
    -- cases {o} m1F@(m1 ⊗ˡ' w2 , _) = sub2
    --   where
    --   sub2 : (m2 : DirectedMor o or) ->
    --         basic-path->mor MC obj magic (fst m1F :: p1) ==
    --         basic-path->mor MC obj magic (fst m2 :: p2)
    --   sub2 (α⇒' a b c , _) = magic
    --   sub2 (m2 ⊗ˡ' w2 , _) = magic
    --   sub2 (w1 ⊗ʳ' m2 , _) = magic
    -- cases {o} m1F@(α⇒' a b c , _) = sub1
    --   where
    --   sub1 : (m2 : DirectedMor o or) ->
    --         basic-path->mor MC obj magic (fst m1F :: p1) ==
    --         basic-path->mor MC obj magic (fst m2 :: p2)
    --   sub1 (α⇒' a b c , _) = magic
    --   sub1 (m2 ⊗ˡ' w2 , _) = magic
    --   sub1 (w1 ⊗ʳ' m2 , _) = magic

    -- cases {o} (α⇒' a b c , _) (m2 ⊗ˡ' w2 , _) = magic
    -- cases {o} (α⇒' a b c , _) (w1 ⊗ʳ' m2 , _) = magic
    -- cases {o} (m1 ⊗ˡ' w2 , _) (m2 ⊗ˡ' w2 , _) = magic
    -- cases {o} (m1 ⊗ˡ' w2 , _) (w1 ⊗ʳ' m2 , _) = magic
    -- cases {o} (w1 ⊗ʳ' m1 , _) (m2 ⊗ˡ' w2 , _) = magic
    -- cases {o} (w1 ⊗ʳ' m1 , _) (w1 ⊗ʳ' m2 , _) = magic


    -- cases {o} (α⇒' a b c , _) (α⇒' a b c , _) = magic
    -- cases {o} (α⇒' a b c , _) (m2 ⊗ˡ' w2 , _) = magic
    -- cases {o} (α⇒' a b c , _) (w1 ⊗ʳ' m2 , _) = magic
    -- cases {o} (m1 ⊗ˡ' w2 , _) (α⇒' a b c , _) = magic
    -- cases {o} (m1 ⊗ˡ' w2 , _) (m2 ⊗ˡ' w2 , _) = magic
    -- cases {o} (m1 ⊗ˡ' w2 , _) (w1 ⊗ʳ' m2 , _) = magic
    -- cases {o} (w1 ⊗ʳ' m1 , _) (α⇒' a b c , _) = magic
    -- cases {o} (w1 ⊗ʳ' m1 , _) (m2 ⊗ˡ' w2 , _) = magic
    -- cases {o} (w1 ⊗ʳ' m1 , _) (w1 ⊗ʳ' m2 , _) = magic


      -- where
      -- sub : (m2 : DirectedMor o or) -> basic-path->mor ((α⇒' a b c) :: p1) ==
      --                                  basic-path->mor (fst m2 :: p2)
      -- sub = magic
