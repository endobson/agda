{-# OPTIONS --cubical --safe --exact-split #-}

module nat.binary-strong-induction where

open import base
open import nat
open import order
open import order.instances.nat
open import relation

private
  variable
    ℓ : Level

module _ {P : Nat -> Nat -> Type ℓ} where
  private
    data Table : Nat -> Nat -> Type ℓ where
      table-corner : (P 0 0) -> Table 0 0
      table-side-edge : {x : Nat} -> (P (suc x) 0) -> Table x 0 -> Table (suc x) 0
      table-top-edge : {x : Nat} -> (P 0 (suc x)) -> Table 0 x -> Table 0 (suc x)
      table-middle : {x y : Nat} -> (P (suc x) (suc y)) -> Table x (suc y) -> Table (suc x) y
                     -> Table (suc x) (suc y)

    data Table' : Nat -> Nat -> Type ℓ where
      table-corner : Table' 0 0
      table-side-edge : {x : Nat} -> Table' x 0 -> Table' (suc x) 0
      table-top-edge : {x : Nat} -> Table' 0 x -> Table' 0 (suc x)
      table-middle : {x y : Nat} -> Table' x (suc y) -> Table' (suc x) y
                     -> Table' (suc x) (suc y)


    table->prop : {x y : Nat} -> Table x y -> P x y
    table->prop (table-corner p) = p
    table->prop (table-side-edge p _) = p
    table->prop (table-top-edge p _) = p
    table->prop (table-middle p _ _) = p

    table->subtable1 : {x y a : Nat} -> Table x y -> a ≤s x -> Table a y
    table->subtable1 t                      refl-≤s       = t
    table->subtable1 (table-side-edge p t)  (step-≤s lt) = (table->subtable1 t lt)
    table->subtable1 (table-middle p t1 t2) (step-≤s lt) = (table->subtable1 t1 lt)

    table->subtable2 : {x y b : Nat} -> Table x y -> b ≤s y -> Table x b
    table->subtable2 t                      refl-≤s       = t
    table->subtable2 (table-top-edge p t)   (step-≤s lt) = (table->subtable2 t lt)
    table->subtable2 (table-middle p t1 t2) (step-≤s lt) = (table->subtable2 t2 lt)

    table->subtable : {x y a b : Nat} -> Table x y -> a ≤s x -> b ≤s y -> Table a b
    table->subtable t lt1 lt2 = (table->subtable2 (table->subtable1 t lt1) lt2)

    table'->subtable1 : {x y a : Nat} -> Table' x y -> a ≤s x -> Table' a y
    table'->subtable1 t                      refl-≤s       = t
    table'->subtable1 (table-side-edge t)  (step-≤s lt) = (table'->subtable1 t lt)
    table'->subtable1 (table-middle t1 t2) (step-≤s lt) = (table'->subtable1 t1 lt)

    table'->subtable2 : {x y b : Nat} -> Table' x y -> b ≤s y -> Table' x b
    table'->subtable2 t                      refl-≤s       = t
    table'->subtable2 (table-top-edge t)   (step-≤s lt) = (table'->subtable2 t lt)
    table'->subtable2 (table-middle t1 t2) (step-≤s lt) = (table'->subtable2 t2 lt)

    table'->subtable : {x y a b : Nat} -> Table' x y -> a ≤s x -> b ≤s y -> Table' a b
    table'->subtable t lt1 lt2 = (table'->subtable2 (table'->subtable1 t lt1) lt2)


    build-table' : (x y : Nat) -> Table' x y
    build-table' zero zero = table-corner
    build-table' (suc x) zero = table-side-edge (build-table' x zero)
    build-table' zero (suc y) = table-top-edge (build-table' zero y)
    build-table' (suc x) (suc y) = table-middle (build-table' x (suc y)) (build-table' (suc x) y)

    module _ (f : (x y : Nat)
                  -> (up   : ({a b : Nat} -> a <i x -> b ≤i y -> P a b))
                  -> (left : ({a b : Nat} -> a ≤i x -> b <i y -> P a b))
                  -> P x y) where
      table'->prop : {x y a b : Nat} -> Table' x y -> a ≤s x -> b ≤s y -> P a b
      table'->prop table-corner refl-≤s refl-≤s = (f zero zero up left)
        where
        up : ({a b : Nat} -> a <i zero -> b ≤i zero -> P a b)
        up ()
        left : ({a b : Nat} -> a ≤i zero -> b <i zero -> P a b)
        left _ ()
      table'->prop (table-side-edge {x} t) refl-≤s refl-≤s = (f (suc x) zero up left)
        where
        up : ({a b : Nat} -> a <i (suc x) -> b ≤i zero -> P a b)
        up (suc-≤i lt1) lt2 = table'->prop t (≤->≤s (≤i->≤ lt1)) (≤->≤s (≤i->≤ lt2))
        left : ({a b : Nat} -> a ≤i (suc x) -> b <i zero -> P a b)
        left _ ()
      table'->prop (table-top-edge {y} t) refl-≤s refl-≤s = (f zero (suc y) up left)
        where
        up : ({a b : Nat} -> a <i zero -> b ≤i (suc y) -> P a b)
        up ()
        left : ({a b : Nat} -> a ≤i zero -> b <i (suc y) -> P a b)
        left lt1 (suc-≤i lt2) =  table'->prop t (≤->≤s (≤i->≤ lt1)) (≤->≤s (≤i->≤ lt2))
      table'->prop (table-middle {x} {y} t1 t2) refl-≤s refl-≤s = (f (suc x) (suc y) up left)
        where
        up : ({a b : Nat} -> a <i (suc x) -> b ≤i (suc y) -> P a b)
        up (suc-≤i lt1) lt2 = table'->prop t1 (≤->≤s (≤i->≤ lt1)) (≤->≤s (≤i->≤ lt2))
        left : ({a b : Nat} -> a ≤i (suc x) -> b <i (suc y) -> P a b)
        left lt1 (suc-≤i lt2) =  table'->prop t2 (≤->≤s (≤i->≤ lt1)) (≤->≤s (≤i->≤ lt2))


      table'->prop (table-side-edge t) (step-≤s lt) refl-≤s =
        table'->prop t lt refl-≤s
      table'->prop (table-top-edge t) refl-≤s (step-≤s lt) =
        table'->prop t refl-≤s lt
      table'->prop (table-middle t1 t2) (step-≤s lt1) lt2 =
        table'->prop t1 lt1 lt2
      table'->prop (table-middle t1 t2) lt1@refl-≤s (step-≤s lt2) =
        table'->prop t2 lt1 lt2

  binary-strong-induction : (f : (x y : Nat)
                                 -> (up   : ({a b : Nat} -> a < x -> b ≤ y -> P a b))
                                 -> (left : ({a b : Nat} -> a ≤ x -> b < y -> P a b))
                                 -> P x y)
                            -> (x y : Nat) -> P x y
  binary-strong-induction f x y = table'->prop g (build-table' x y) refl-≤s refl-≤s
    where
    g : (x y : Nat)
        -> (up   : ({a b : Nat} -> a <i x -> b ≤i y -> P a b))
        -> (left : ({a b : Nat} -> a ≤i x -> b <i y -> P a b))
        -> P x y
    g x y up left = f x y up' left'
      where
      up' : {a b : Nat} -> a < x -> b ≤ y -> P a b
      up' a<x b≤y = up (≤->≤i a<x) (≤->≤i b≤y)
      left' : {a b : Nat} -> a ≤ x -> b < y -> P a b
      left' a≤x b<y = left (≤->≤i a≤x) (≤->≤i b<y)



module _ {P : Nat⁺ -> Nat⁺ -> Type ℓ} where
  binary-strong-induction⁺ : (f : (x y : Nat⁺)
                                  -> (up   : ({a b : Nat⁺} -> a <⁺ x -> b ≤⁺ y -> P a b))
                                  -> (left : ({a b : Nat⁺} -> a ≤⁺ x -> b <⁺ y -> P a b))
                                  -> P x y)
                            -> (x y : Nat⁺) -> P x y
  binary-strong-induction⁺ f (x , px) (y , py) = binary-strong-induction f' x y px py
    where
    P' : (a b : Nat) -> Type ℓ
    P' a b = (pa : Pos' a) -> (pb : Pos' b) -> P (a , pa) (b , pb)

    f' : (x y : Nat)
         -> (up   : ({a b : Nat} -> a < x -> b ≤ y -> P' a b))
         -> (left : ({a b : Nat} -> a ≤ x -> b < y -> P' a b))
         -> P' x y
    f' x y up left px py = f x⁺ y⁺ up' left'
      where
      x⁺ : Nat⁺
      x⁺ = x , px
      y⁺ : Nat⁺
      y⁺ = y , py
      up' : {a b : Nat⁺} -> a <⁺ x⁺ -> b ≤⁺ y⁺ -> P a b
      up' lt1 lt2 = up lt1 lt2 _ _
      left' : {a b : Nat⁺} -> a ≤⁺ x⁺ -> b <⁺ y⁺ -> P a b
      left' lt1 lt2 = left lt1 lt2 _ _

module _ {P : Nat -> Nat -> Type ℓ}
         (symP : Symmetric P)
         (f : (x y : Nat)
              -> x ≤ y
              -> (rec   : ({a b : Nat} -> a < y -> b < y -> P a b))
              -> P x y) where
  private

    sym-induction≤ : (y : Nat) {a b : Nat} -> a ≤ y -> b ≤ y -> P a b
    sym-induction≤' : {y a b : Nat} -> a ≤ b -> a ≤ y -> b ≤ y -> P a b

    sym-induction≤ y {a} {b} a≤y b≤y = handle (split-nat< a b)
      where
      handle : (a < b) ⊎ (b ≤ a) -> P a b
      handle (inj-l a<b) = sym-induction≤' (weaken-< a<b) a≤y b≤y
      handle (inj-r b≤a) = symP (sym-induction≤' b≤a b≤y a≤y)

    sym-induction≤' {zero}       {a} {b} a≤b a≤y b≤y =
      f a b a≤b (\ a2<b b2<b -> bot-elim (zero-≮ (trans-<-≤ a2<b b≤y)))
    sym-induction≤' {y@(suc y')} {a} {b} a≤b a≤y b≤y = f a b a≤b rec
      where
      rec : {a2 b2 : Nat} -> a2 < b -> b2 < b -> P a2 b2
      rec a2<b b2<b = sym-induction≤ y' (pred-≤ (trans-<-≤ a2<b b≤y)) (pred-≤ (trans-<-≤ b2<b b≤y))

  sym-binary-strong-induction : (x y : Nat) -> P x y
  sym-binary-strong-induction x y = sym-induction≤ (max x y) ≤-max-left ≤-max-right


module _ {P : Nat⁺ -> Nat⁺ -> Type ℓ}
         (symP : Symmetric P)
         (f : (x y : Nat⁺)
              -> x ≤⁺ y
              -> (rec   : ({a b : Nat⁺} -> a <⁺ y -> b <⁺ y -> P a b))
              -> P x y) where
  sym-binary-strong-induction⁺ : (x y : Nat⁺) -> P x y
  sym-binary-strong-induction⁺ (x , px) (y , py) = sym-binary-strong-induction symP' f' x y px py
    where
    P' : (a b : Nat) -> Type ℓ
    P' a b = (pa : Pos' a) -> (pb : Pos' b) -> P (a , pa) (b , pb)
    symP' : Symmetric P'
    symP' p' pb pa = symP (p' pa pb)

    f' : (x y : Nat)
         -> x ≤ y
         -> (rec : ({a b : Nat} -> a < y -> b < y -> P' a b))
         -> P' x y
    f' x y x≤y rec px py = f x⁺ y⁺ x≤y rec'
      where
      x⁺ : Nat⁺
      x⁺ = x , px
      y⁺ : Nat⁺
      y⁺ = y , py
      rec' : {a b : Nat⁺} -> a <⁺ y⁺ -> b <⁺ y⁺ -> P a b
      rec' {a , pos-a} {b , pos-b} a<y b<y = rec a<y b<y pos-a pos-b
