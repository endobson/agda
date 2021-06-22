{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.multiplication2 where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.factor-order
open import real
open import real.sequence
open import real.arithmetic.absolute-value
open import relation hiding (U)
open import ring.implementations.rational
open import sign
open import sign.instances.rational
open import truncation

--module _ (x y : ℝ)
--  (LU->Pos : (z : ℝ) -> (q : ℚ) -> (Real.L z (r- q)) -> (Real.U z q) -> Pos q)
--  (factor-order-flip : (a b c d : ℚ) (ab=cd : (a r* b) == (c r* d)) -> (Pos a ⊎ Neg c) ->
--                       a < c -> b > d)
--  where
--  private
--    ax = absℝ x
--    ay = absℝ y
--    module x = Real x
--    module y = Real y
--    module ax = Real ax
--    module ay = Real ay
--
--    data L' : (q : ℚ) -> Type₀ where
--      L'-pos : (q1 : ℚ⁺) (q2 : ℚ) -> (x.L 0r) -> x.L ⟨ q1 ⟩ -> y.L q2 -> L' (⟨ q1 ⟩ r* q2)
--      L'-neg : (q1 : ℚ⁻) (q2 : ℚ) -> (x.U 0r) -> x.U ⟨ q1 ⟩ -> y.U q2 -> L' (⟨ q1 ⟩ r* q2)
--      L'-small : (q1 : ℚ) (q2 : ℚ) -> (x.L (r- q1)) -> x.U q1 -> y.L (r- q2) -> y.U q2 -> L' (r- (q1 r* q2))
--
--    data U' : (q : ℚ) -> Type₀ where
--      U'-pos : (q1 : ℚ⁺) (q2 : ℚ) -> (x.L 0r) -> x.U ⟨ q1 ⟩ -> y.U q2 -> U' (⟨ q1 ⟩ r* q2)
--      U'-neg : (q1 : ℚ⁻) (q2 : ℚ) -> (x.U 0r) -> x.L ⟨ q1 ⟩ -> y.L q2 -> U' (⟨ q1 ⟩ r* q2)
--      U'-small : (q1 : ℚ) (q2 : ℚ) -> (x.L (r- q1)) -> x.U q1 -> y.L (r- q2) -> y.U q2 -> U' (q1 r* q2)
--
--    L : Pred ℚ ℓ-zero
--    L q = ∥ L' q ∥
--    U : Pred ℚ ℓ-zero
--    U q = ∥ U' q ∥
--
--    data SmallOrSigned (z : ℝ) (ε : ℚ⁺) : Type₁ where
--      sos-pos : (Real.L z 0r) -> SmallOrSigned z ε
--      sos-neg : (Real.U z 0r) -> SmallOrSigned z ε
--      sos-small : (Real.L z (r- ⟨ ε ⟩)) -> Real.U z ⟨ ε ⟩ -> SmallOrSigned z ε
--
--
--    small-or-signed : (z : ℝ) -> (ε : ℚ⁺) -> ∥ SmallOrSigned z ε ∥
--    small-or-signed z e⁺@(e , pos-e) =
--      ∥-map2 handle (z.located (r- e) 0r -e<0) (z.located 0r e 0<e)
--      where
--      module z = Real z
--      0<e : 0r < e
--      0<e = Pos-0< e pos-e
--      -e<0 : (r- e) < 0r
--      -e<0 = r--flips-order 0r e 0<e
--
--      handle : (z.L (r- e) ⊎ (z.U 0r)) -> (z.L 0r ⊎ (z.U e)) -> SmallOrSigned z e⁺
--      handle (inj-l l-e) (inj-l l-z) = sos-pos l-z
--      handle (inj-l l-e) (inj-r u-e) = sos-small l-e u-e
--      handle (inj-r u-z) (inj-l l-z) = bot-elim (z.disjoint 0r (l-z , u-z))
--      handle (inj-r u-z) (inj-r u-e) = sos-neg u-z
--
--    zero-ball : (z : ℝ) -> ∃[ q ∈ ℚ ] (Real.L z (r- q) × Real.U z q)
--    zero-ball z = Real.Inhabited-U (absℝ z)
--
--    1r⁺ : ℚ⁺
--    1r⁺ = 1r , Pos-1r
--
--    Inhabited-L : Inhabited L
--    Inhabited-L = ∥-bind2 handle (small-or-signed x 1r⁺) (zero-ball y)
--      where
--      handle : SmallOrSigned x 1r⁺ -> Σ[ q ∈ ℚ ] (Real.L y (r- q) × Real.U y q) -> Inhabited L
--      handle (sos-pos xl-0) (q , yl-q , yu-q) = ∥-map handle2 (x.isUpperOpen-L 0r xl-0)
--        where
--        handle2 : Σ[ r ∈ ℚ ] (0r < r × x.L r) -> Σ ℚ L
--        handle2 (r , 0<r , xl-r) = _ , ∣ L'-pos (r , pos-r) _ xl-0 xl-r yl-q ∣
--          where
--          pos-r : Pos r
--          pos-r = subst Pos (r+-right-zero r) 0<r
--      handle (sos-neg xu-0) (q , yl-q , yu-q) = ∥-map handle2 (x.isLowerOpen-U 0r xu-0)
--        where
--        handle2 : Σ[ r ∈ ℚ ] (r < 0r × x.U r) -> Σ ℚ L
--        handle2 (r , r<0 , xu-r) = _ , ∣ L'-neg (r , neg-r) _ xu-0 xu-r yu-q ∣
--          where
--          neg-r : Neg r
--          neg-r = subst Neg (cong r-_ (r+-left-zero (r- r)) >=> RationalRing.minus-double-inverse)
--                            (r--flips-sign _ _ r<0)
--      handle (sos-small xl-1 xu-1) (q , yl-q , yu-q) =
--        ∣ _ , ∣ L'-small 1r q xl-1 xu-1 yl-q yu-q ∣ ∣
--
--    -- LU->Pos : (z : ℝ) -> (q : ℚ) -> (Real.L z (r- q)) -> (Real.U z q) -> Pos q
--    -- LU->Pos = ?
--
--    PosNeg-absurd : {q : ℚ} -> Pos q -> Neg q -> Bot
--    PosNeg-absurd p n = NonNeg->¬Neg (Pos->NonNeg p) n
--
--    PosNeg-absurd' : {q r : ℚ} -> q == r -> Pos q -> Neg r -> Bot
--    PosNeg-absurd' q=r p n = NonNeg->¬Neg (Pos->NonNeg (subst Pos q=r p)) n
--
--
--    disjoint : Universal (Comp (L ∩ U))
--    disjoint q (lq , uq) = unsquash isPropBot (∥-map2 (handle refl) lq uq)
--      where
--      handle : {q r : ℚ} -> q == r -> L' q -> U' r ->  Bot
--      handle q=r (L'-pos a⁺@(a , pos-a) b _ xl-a yl-b) (U'-pos c⁺@(c , _) d _ xu-c yu-d) =
--        asym-< {b} {d} b<d b>d
--        where
--        a<c : a < c
--        a<c = ℝ-bounds->ℚ< x _ _ xl-a xu-c
--
--        b>d : b > d
--        b>d = factor-order-flip a b c d q=r (inj-l pos-a) a<c
--        b<d : b < d
--        b<d = ℝ-bounds->ℚ< y _ _ yl-b yu-d
--      handle q=r (L'-pos a⁺ b xl-0 xl-a yl-b) (U'-neg c⁻ d xu-0 xl-c yl-d) =
--        x.disjoint 0r (xl-0 , xu-0)
--      handle q=r (L'-pos a⁺@(a , pos-a) b _ xl-a yl-b) (U'-small c d xl-c xu-c yl-d yu-d) =
--        asym-< {b} {d} b<d b>d
--        where
--        a<c : a < c
--        a<c = ℝ-bounds->ℚ< x _ _ xl-a xu-c
--        b>d : b > d
--        b>d = factor-order-flip a b c d q=r (inj-l pos-a) a<c
--        b<d : b < d
--        b<d = ℝ-bounds->ℚ< y _ _ yl-b yu-d
--      handle q=r (L'-neg a⁻ b xu-0 xu-a yu-b) (U'-pos c⁺ d xl-0 xu-c yu-d) =
--        x.disjoint 0r (xl-0 , xu-0)
--      handle q=r (L'-neg a⁻@(a , neg-a) b _ xu-a yu-b) (U'-neg c⁻@(c , _) d _ xl-c yl-d) =
--        asym-< {d} {b} d<b d>b
--        where
--        c<a : c < a
--        c<a = ℝ-bounds->ℚ< x _ _ xl-c xu-a
--
--        d>b : d > b
--        d>b = factor-order-flip c d a b (sym q=r) (inj-r neg-a) c<a
--        d<b : d < b
--        d<b = ℝ-bounds->ℚ< y _ _ yl-d yu-b
--      handle q=r (L'-neg a⁻@(a , neg-a) b _ xu-a yu-b) (U'-small c d xl-c xu-c yl-d yu-d) =
--        asym-< {r- d} {b} d<b d>b
--        where
--        c<a : (r- c) < a
--        c<a = ℝ-bounds->ℚ< x _ _ xl-c xu-a
--
--        p : a r* b == (r- c) r* (r- d)
--        p = q=r >=> sym RationalRing.minus-double-inverse >=>
--            cong r-_ (sym (r*-minus-extract-left c d)) >=>
--            (sym (r*-minus-extract-right (r- c) d))
--
--
--        d>b : (r- d) > b
--        d>b = factor-order-flip (r- c) (r- d) a b (sym p) (inj-r neg-a) c<a
--        d<b : (r- d) < b
--        d<b = ℝ-bounds->ℚ< y _ _ yl-d yu-b
--
--      --handle q=r (L'-small a b xl-a xu-a yl-b yu-b) (U'-pos c⁺@(c , pos-c) d _ xu-c yu-d) = ?
--      --  where
--      --  -a<c : (r- a) < c
--      --  -a<c = ℝ-bounds->ℚ< x _ _ xl-a xu-c
--
--      --  -c<a : (r- c) < a
--      --  -c<a = subst ((r- c) <_) (RationalRing.minus-double-inverse {a}) (r--flips-order (r- a) c -a<c)
--
--      --  p : r- (a r* b) == c r* d
--      --  p = q=r
--
--      --  -b<d : (r- b) < d
--      --  -b<d = ℝ-bounds->ℚ< y _ _ yl-b yu-d
--
--      handle q=r (L'-small a b xl-a xu-a yl-b yu-b) (U'-neg c⁻@(c , neg-c) d _ xl-c yl-d) = ?
--        where
--        c<a : c < a
--        c<a = ℝ-bounds->ℚ< x _ _ xl-c xu-a
--
--        p : (b r* (r- a)) == d r* c
--        p = r*-commute b (r- a) >=>
--            (r*-minus-extract-left a b) >=> q=r >=>
--            r*-commute c d
--
--        pos-d : Pos d
--        pos-d = ?
--
--        d<b : d < b
--        d<b = ℝ-bounds->ℚ< y _ _ yl-d yu-b
--
--        -a<c : (r- a) < c
--        -a<c = factor-order-flip d c b (r- a) (sym p) (inj-l pos-d) d<b
--
--
--      -- handle q=r (L'-small a b xl-a xu-a yl-b yu-b) (U'-small c d xl-c xu-c yl-d yu-d) =
--      --   PosNeg-absurd' (sym q=r)
--      --     (r*-preserves-Pos _ _ (LU->Pos x c xl-c xu-c) (LU->Pos y d yl-d yu-d))
--      --     (r--flips-sign (a r* b) pos-sign
--      --       (r*-preserves-Pos _ _ (LU->Pos x a xl-a xu-a) (LU->Pos y b yl-b yu-b)))
