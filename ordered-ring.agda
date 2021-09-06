{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring where

open import base
open import equality
open import functions
open import hlevel
open import order
open import ordered-semiring
open import ring
open import semiring
open import truncation

private
  variable
    ℓD ℓ< ℓ≤ : Level

module _ {D : Type ℓD} {S : Semiring D} {O : LinearOrderStr D ℓ<}
         {{LOS : LinearlyOrderedSemiringStr S O}}
         {{R : Ring S}} where
  private
    module R = Ring R
    instance
      ILOS = LOS
      IS = S
      IO = O
      IR = R

  abstract
    minus-flips-< : (a b : D) -> (a < b) -> (- b) < (- a)
    minus-flips-< a b a<b =
      subst2 _<_
        (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+-left +-commute >=> +-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+₁-preserves-< ((- b) + (- a)) a b a<b)

    minus-flips-0< : {a : D} -> (0# < a) -> (- a) < 0#
    minus-flips-0< {a} 0<a = subst ((- a) <_) minus-zero (minus-flips-< _ _ 0<a)

    minus-flips-<0 : {a : D} -> (a < 0#) -> 0# < (- a)
    minus-flips-<0 {a} a<0 = subst (_< (- a)) minus-zero (minus-flips-< _ _ a<0)

    *₁-preserves-< : (a b c : D) -> (0# < a) -> (b < c) -> (a * b) < (a * c)
    *₁-preserves-< a b c 0<a b<c = ab<ac
      where
      0<cb : 0# < (c + (- b))
      0<cb = subst2 _<_ +-inverse refl (+₂-preserves-< b c (- b) b<c)

      0<acb : 0# < (a * (c + (- b)))
      0<acb = *-preserves-0< a (c + (- b)) 0<a 0<cb

      ab+acb=ac : (a * b) + (a * (c + (- b))) == a * c
      ab+acb=ac =
        sym *-distrib-+-left >=>
        *-right (+-right +-commute >=> sym +-assoc >=> +-left +-inverse >=> +-left-zero)

      ab<ac : (a * b) < (a * c)
      ab<ac = subst2 _<_ +-right-zero ab+acb=ac (+₁-preserves-< (a * b) _ _ 0<acb)

    *₂-preserves-< : (a b c : D) -> (a < b) -> (0# < c) -> (a * c) < (b * c)
    *₂-preserves-< a b c a<b 0<c =
      subst2 _<_ *-commute *-commute (*₁-preserves-< c a b 0<c a<b)

    *₁-flips-< : (a b c : D) -> (a < 0#) -> (b < c) -> (a * c) < (a * b)
    *₁-flips-< a b c a<0 b<c =
      subst2 _<_ (cong -_ minus-extract-left >=> minus-double-inverse)
                 (cong -_ minus-extract-left >=> minus-double-inverse)
                 (minus-flips-< _ _ (*₁-preserves-< (- a) b c 0<-a b<c))
      where
      0<-a : 0# < (- a)
      0<-a = subst (_< (- a)) minus-zero (minus-flips-< _ _ a<0)

    *₂-flips-< : (a b c : D) -> (a < b) -> (c < 0#) -> (b * c) < (a * c)
    *₂-flips-< a b c a<b c<0 =
      subst2 _<_ *-commute *-commute (*₁-flips-< c a b c<0 a<b)

  private
    case-≮' : (x y x' y' : D) -> (x < y -> y' ≮ x') -> (x == y -> x' == y') -> (y ≮ x -> y' ≮ x')
    case-≮' x y x' y' f< f= y≮x y'<x' = irrefl-< (subst (y' <_) x'==y' y'<x')
      where
      x≮y : x ≮ y
      x≮y x<y = f< x<y y'<x'

      x==y : x == y
      x==y = connected-< x≮y y≮x

      x'==y' : x' == y'
      x'==y' = f= x==y

    case-≮ : (x y x' y' : D) -> (x < y -> x' < y') -> (x == y -> x' == y') -> (y ≮ x -> y' ≮ x')
    case-≮ x y x' y' f< = case-≮' x y x' y' (asym-< ∘ f<)

    *₁-preserves-≮' : (a b c : D) -> (0# < a) -> (b ≮ c) -> (a * b) ≮ (a * c)
    *₁-preserves-≮' a b c 0<a = case-≮ c b (a * c) (a * b) (*₁-preserves-< a c b 0<a) (cong (a *_))

  abstract
    *₁-preserves-≮ : (a b c : D) -> (a ≮ 0#) -> (b ≮ c) -> (a * b) ≮ (a * c)
    *₁-preserves-≮ a b c a≮0 b≮c = case-≮' 0# a (a * c) (a * b) f< f= a≮0
      where
      f= : (0# == a) -> a * c == a * b
      f= p = *-left (sym p) >=> *-left-zero >=> (sym *-left-zero) >=> *-left p

      f< : (0# < a) -> (a * b) ≮ (a * c)
      f< 0<a = *₁-preserves-≮' a b c 0<a b≮c

    *₂-preserves-≮ : (a b c : D) -> (a ≮ b) -> (c ≮ 0#) -> (a * c) ≮ (b * c)
    *₂-preserves-≮ a b c a≮b c≮0 =
      subst2 _≮_ *-commute *-commute (*₁-preserves-≮ c a b c≮0 a≮b)


    *-preserves-≮0 : (a b : D) -> (a ≮ 0#) -> (b ≮ 0#) -> (a * b) ≮ 0#
    *-preserves-≮0 a b a≮0 b≮0 = subst ((a * b) ≮_) *-right-zero (*₁-preserves-≮ a b 0# a≮0 b≮0)

    +₁-preserves-≮ : (a b c : D) -> b ≮ c -> (a + b) ≮ (a + c)
    +₁-preserves-≮ a b c b≮c ab<ac =
      b≮c (subst2 _<_ (sym +-assoc >=> (+-left (+-commute >=> +-inverse)) >=> +-left-zero)
                      (sym +-assoc >=> (+-left (+-commute >=> +-inverse)) >=> +-left-zero)
                      (+₁-preserves-< (- a ) (a + b) (a + c) ab<ac))


    +-preserves-≮0 : (a b : D) -> a ≮ 0# -> b ≮ 0# -> (a + b) ≮ 0#
    +-preserves-≮0 a b a≮0 b≮0 ab<0 = unsquash isPropBot (∥-map handle (comparison-< ab a 0# ab<0))
      where
      ab = a + b
      handle : (ab < a) ⊎ (a < 0#) -> Bot
      handle (inj-r a<0) = a≮0 a<0
      handle (inj-l ab<a) =
        b≮0 (subst2 _<_ (sym +-assoc >=> +-left (+-commute >=> +-inverse) >=> +-left-zero)
                        (+-commute >=> +-inverse) (+₁-preserves-< (- a) ab a ab<a))

    1≮0# : 1# ≮ 0#
    1≮0# 1<0 = irrefl-< (trans-< -1<0 0<-1)
      where
      0<-1 = minus-flips-<0 1<0
      -1<0 = subst2 _<_ *-left-one *-left-one (*₁-flips-< 1# 0# (- 1#) 1<0 0<-1)


--    u1/-preserves-0< : (x : R.Unit) -> 0# < ⟨ x ⟩ -> 0# < ⟨ (R.u1/ x) ⟩
--    u1/-preserves-0< (x , (R.is-unit 1/x x/x=1)) = ?

module _ {D : Type ℓD} {S : Semiring D} {O : PartialOrderStr D ℓ<}
         {{POS : PartiallyOrderedSemiringStr S O}}
         {{R : Ring S}} where
  private
    instance
      IPOS = POS
      IS = S
      IO = O
      IR = R

  abstract
    minus-flips-≤ : (a b : D) -> (a ≤ b) -> (- b) ≤ (- a)
    minus-flips-≤ a b a≤b =
      subst2 _≤_
        (+-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+-left +-commute >=> +-assoc >=> +-right (+-commute >=> +-inverse) >=> +-right-zero)
        (+₁-preserves-≤ ((- b) + (- a)) a b a≤b)

    minus-flips-0≤ : {a : D} -> (0# ≤ a) -> (- a) ≤ 0#
    minus-flips-0≤ {a} 0≤a = subst ((- a) ≤_) minus-zero (minus-flips-≤ _ _ 0≤a)

    minus-flips-≤0 : {a : D} -> (a ≤ 0#) -> 0# ≤ (- a)
    minus-flips-≤0 {a} a≤0 = subst (_≤ (- a)) minus-zero (minus-flips-≤ _ _ a≤0)

    *₁-preserves-≤ : (a b c : D) -> (0# ≤ a) -> (b ≤ c) -> (a * b) ≤ (a * c)
    *₁-preserves-≤ a b c 0≤a b≤c = ab≤ac
      where
      0≤cb : 0# ≤ (c + (- b))
      0≤cb = subst2 _≤_ +-inverse refl (+₂-preserves-≤ b c (- b) b≤c)

      0≤acb : 0# ≤ (a * (c + (- b)))
      0≤acb = *-preserves-0≤ a (c + (- b)) 0≤a 0≤cb

      ab+acb=ac : (a * b) + (a * (c + (- b))) == a * c
      ab+acb=ac =
        sym *-distrib-+-left >=>
        *-right (+-right +-commute >=> sym +-assoc >=> +-left +-inverse >=> +-left-zero)

      ab≤ac : (a * b) ≤ (a * c)
      ab≤ac = subst2 _≤_ +-right-zero ab+acb=ac (+₁-preserves-≤ (a * b) _ _ 0≤acb)

    *₂-preserves-≤ : (a b c : D) -> (a ≤ b) -> (0# ≤ c) -> (a * c) ≤ (b * c)
    *₂-preserves-≤ a b c a≤b 0≤c =
      subst2 _≤_ *-commute *-commute (*₁-preserves-≤ c a b 0≤c a≤b)

    *₁-flips-≤ : (a b c : D) -> (a ≤ 0#) -> (b ≤ c) -> (a * c) ≤ (a * b)
    *₁-flips-≤ a b c a≤0 b≤c =
      subst2 _≤_ (cong -_ minus-extract-left >=> minus-double-inverse)
                 (cong -_ minus-extract-left >=> minus-double-inverse)
                 (minus-flips-≤ _ _ (*₁-preserves-≤ (- a) b c 0≤-a b≤c))
      where
      0≤-a : 0# ≤ (- a)
      0≤-a = subst (_≤ (- a)) minus-zero (minus-flips-≤ _ _ a≤0)

    *₂-flips-≤ : (a b c : D) -> (a ≤ b) -> (c ≤ 0#) -> (b * c) ≤ (a * c)
    *₂-flips-≤ a b c a≤b c≤0 =
      subst2 _≤_ *-commute *-commute (*₁-flips-≤ c a b c≤0 a≤b)


module _ {D : Type ℓD} {S : Semiring D} {O : PartialOrderStr D ℓ≤}
         {{TO : TotalOrderStr O}}
         {{POS : PartiallyOrderedSemiringStr S O}}
         {{R : Ring S}} where
  private
    instance
      IPOS = POS
      ITO = TO
      IS = S
      IO = O
      IR = R

  abstract
    0≤-square : {a : D} -> 0# ≤ (a * a)
    0≤-square {a} = unsquash (isProp-≤ _ _) (∥-map handle (connex-≤ 0# a))
      where
      handle : (0# ≤ a) ⊎ (a ≤ 0#) -> 0# ≤ (a * a)
      handle (inj-l 0≤a) = subst2 _≤_ *-right-zero refl (*₁-preserves-≤ a 0# a 0≤a 0≤a)
      handle (inj-r a≤0) = subst2 _≤_ *-right-zero refl (*₁-flips-≤ a a 0# a≤0 a≤0)


-- module _ {D : Type ℓD} {S : Semiring D} {LO : LinearOrderStr D ℓ<} {PO : PartialOrderStr D ℓ≤}
--          {{CO : CompatibleOrderStr LO PO}}
--   --       {{TO : TotalOrderStr PO}}
--          {{LOS : LinearlyOrderedSemiringStr S LO}}
--          {{POS : PartiallyOrderedSemiringStr S PO}}
--          {{R : Ring S}} where
--   private
--     instance
--       ILO = LO
--       IPOS = POS
--       IS = S
--       IR = R
--
--   abstract
--     *₁-reflects-0< : {a b : D} -> (0# < a) -> (0# < (a * b)) -> 0# < b
--     *₁-reflects-0< {a} {b} 0<a 0<ab = ?
--       where
--       ab = a * b
--       b<a : b < a
--       b<a = ?
--       b<ab : b < ab
--       b<ab = ?


      -- unsquash (isProp-< _ _) (∥-map2 handle (comparison-< 0# b 1# 0<1r) (comparison-< 0r b bb 0<bb))
      -- where
      -- aa = a * a
      -- ab = a * b
      -- bb = b * b
      -- 0≤bb : 0r ≤ bb
      -- 0≤bb = 0≤-square

      -- 0!=bb : 0r != bb
      -- 0!=bb 0=bb = irrefl-< (subst (0r <_) path (*-preserves-0< ab ab 0<ab 0<ab))
      --   where
      --   path : ab * ab == 0r
      --   path = *-assoc >=>
      --          *-right (*-commute >=>
      --                   *-assoc >=>
      --                   *-right (sym 0=bb) >=>
      --                   *-right-zero) >=>
      --          *-right-zero

      -- 0<bb = strengthen-ℚ≤-≠ 0≤bb 0!=bb

      -- handle : (0r < b) ⊎ (b < 1r) -> (0r < b) ⊎ (b < bb) -> 0r < b
      -- handle (inj-l 0<b) _            = 0<b
      -- handle (inj-r b<1) (inj-l 0<b)  = 0<b
      -- handle (inj-r b<1) (inj-r b<bb) = bot-elim (asym-< aab<aabb aabb<aab)
      --   where
      --   0<aa : 0r < aa
      --   0<aa = *-preserves-0< a a 0<a 0<a
      --   aab<aabb : ((a * a) * b) < ((a * a) * (b * b))
      --   aab<aabb = *₁-preserves-< aa b bb 0<aa b<bb
      --   0<aab : 0r < (aa * b)
      --   0<aab = subst (0r <_) (sym *-assoc) (*-preserves-0< a ab 0<a 0<ab)
      --   aabb<aab : ((a * a) * (b * b)) < ((a * a) * b)
      --   aabb<aab = subst2 _<_ *-assoc *-right-one (*₁-preserves-< (aa * b) b 1r 0<aab b<1)
