{-# OPTIONS --cubical --safe --exact-split #-}

module rational.squares where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import rational.difference
open import rational.minmax
open import rational.order
open import relation hiding (U)
open import ring
open import semiring
open import sign
open import sign.instances.rational
open import truncation



0≤-square : {q : ℚ} -> 0r ≤ (q * q)
0≤-square {q} = unsquash (isProp-≤ _ _) (∥-map handle (connex-≤ 0r q))
  where
  handle : (0r ≤ q) ⊎ (q ≤ 0r) -> 0r ≤ (q * q)
  handle (inj-l 0≤q) = subst2 _≤_ *-right-zero refl (*₁-preserves-≤ q 0r q 0≤q 0≤q)
  handle (inj-r q≤0) = subst2 _≤_ *-right-zero refl (*₁-flips-≤ q q 0r q≤0 q≤0)

private
  isSquareℚ : Pred ℚ ℓ-zero
  isSquareℚ q = Σ[ r ∈ ℚ ] ((0r ≤ r) × r * r == q)

  *₁-reflects-0< : {a b : ℚ} -> (0r < a) -> (0r < (a * b)) -> 0r < b
  *₁-reflects-0< {a} {b} 0<a 0<ab =
    unsquash (isProp-< _ _) (∥-map2 handle (comparison-< 0r b 1r 0<1r) (comparison-< 0r b bb 0<bb))
    where
    aa = a * a
    ab = a * b
    bb = b * b
    0≤bb : 0r ≤ bb
    0≤bb = 0≤-square

    0!=bb : 0r != bb
    0!=bb 0=bb = irrefl-< (subst (0r <_) path (*-preserves-0< ab ab 0<ab 0<ab))
      where
      path : ab * ab == 0r
      path = *-assoc >=>
             *-right (*-commute >=>
                      *-assoc >=>
                      *-right (sym 0=bb) >=>
                      *-right-zero) >=>
             *-right-zero

    0<bb = strengthen-≤-≠ 0≤bb 0!=bb

    handle : (0r < b) ⊎ (b < 1r) -> (0r < b) ⊎ (b < bb) -> 0r < b
    handle (inj-l 0<b) _            = 0<b
    handle (inj-r b<1) (inj-l 0<b)  = 0<b
    handle (inj-r b<1) (inj-r b<bb) = bot-elim (asym-< aab<aabb aabb<aab)
      where
      0<aa : 0r < aa
      0<aa = *-preserves-0< a a 0<a 0<a
      aab<aabb : ((a * a) * b) < ((a * a) * (b * b))
      aab<aabb = *₁-preserves-< aa b bb 0<aa b<bb
      0<aab : 0r < (aa * b)
      0<aab = subst (0r <_) (sym *-assoc) (*-preserves-0< a ab 0<a 0<ab)
      aabb<aab : ((a * a) * (b * b)) < ((a * a) * b)
      aabb<aab = subst2 _<_ *-assoc *-right-one (*₁-preserves-< (aa * b) b 1r 0<aab b<1)

  *₂-reflects-0< : {a b : ℚ} -> (0r < b) -> (0r < (a * b)) -> 0r < a
  *₂-reflects-0< 0<b 0<ab = *₁-reflects-0< 0<b (subst (0r <_) *-commute 0<ab)

  *₁-reflects-< : {a b c : ℚ} -> (0r < a) -> ((a * b) < (a * c)) -> b < c
  *₁-reflects-< {a} {b} {c} 0<a ab<ac =
    Pos-diffℚ⁻ _ _ (*₁-reflects-0< 0<a 0<acb)
    where
    p : diffℚ (a * b) (a * c) == a * (diffℚ b c)
    p = +-right (sym minus-extract-right) >=> sym *-distrib-+-left

    0<acb : 0r < (a * (diffℚ b c))
    0<acb = subst (0r <_) p (Pos-diffℚ _ _ ab<ac)


  *₁-reflects-<' : {a b c : ℚ} -> (0r ≤ a) -> ((a * b) < (a * c)) -> b < c
  *₁-reflects-<' {a} {b} {c} 0≤a ab<ac = *₁-reflects-< 0<a ab<ac
    where
    0!=a : 0r != a
    0!=a 0=a = irrefl-< (subst2 _<_ (*-left (sym 0=a) >=> *-left-zero)
                                    (*-left (sym 0=a) >=> *-left-zero) ab<ac)
    0<a = strengthen-≤-≠ 0≤a 0!=a

  *₂-reflects-<' : {a b c : ℚ} -> (0r ≤ c) -> ((a * c) < (b * c)) -> a < b
  *₂-reflects-<' 0≤c ac<bc = *₁-reflects-<' 0≤c (subst2 _<_ *-commute *-commute ac<bc)


abstract
  squares-ordered⁺ : {q r : ℚ} -> (0r ≤ q) -> (q < r) -> (q * q) < (r * r)
  squares-ordered⁺ {q} {r} 0≤q q<r =
    trans-≤-< (*₁-preserves-≤ q q r 0≤q (weaken-< q<r)) (*₂-preserves-< q r r q<r 0<r)
    where
    0<r = trans-≤-< 0≤q q<r

  squares-ordered : {q r : ℚ} -> (0r ≤ q) -> (0r ≤ r) -> (q * q) < (r * r) -> q < r
  squares-ordered {q} {r} 0≤q 0≤r qq<rr =
    unsquash (isProp-< _ _) (∥-map handle (comparison-< qq qr rr qq<rr))
    where
    qq = (q * q)
    qr = (q * r)
    rr = (r * r)

    r≮q : r ≮ q
    r≮q r<q = asym-< qq<rr (squares-ordered⁺ 0≤r r<q)

    handle : (qq < qr) ⊎ (qr < rr) -> q < r
    handle (inj-l qq<qr) = *₁-reflects-<' 0≤q qq<qr
    handle (inj-r qr<rr) = *₂-reflects-<' 0≤r qr<rr


private
  +-preserves-≤-< : (a b c d : ℚ) -> a ≤ b -> c < d -> (a + c) < (b + d)
  +-preserves-≤-< a b c d a≤b c<d =
    trans-<-≤ (+₁-preserves-< a c d c<d) (+₂-preserves-≤ a b d a≤b)


  squares-dense-0 : {q : ℚ} -> (0r < q) -> ∃[ s ∈ ℚ ] (isSquareℚ s × 0r < s × s < q)
  squares-dense-0 {q} 0<q = ∥-map handle (comparison-< 1/4r q 1r 1/4<1)
    where
    1/4r = 1/2r * 1/2r
    1/4<1 : 1/4r < 1r
    1/4<1 = trans-< (subst (1/4r <_) *-right-one (*₁-preserves-< _ _ _ Pos-1/2r 1/2r<1r)) 1/2r<1r

    handle : (1/4r < q) ⊎ (q < 1r) -> Σ[ s ∈ ℚ ] (isSquareℚ s × 0r < s × s < q)
    handle (inj-l 1/4<q) = 1/4r , (1/2r , weaken-< Pos-1/2r , refl) ,
                           *-preserves-0< _ _ Pos-1/2r Pos-1/2r , 1/4<q
    handle (inj-r q<1) = (q * q) , (q , weaken-< 0<q , refl) , 0<qq , qq<q
      where
      0<qq = r*-Pos-Pos 0<q 0<q
      qq<q = (subst ((q * q) <_) *-right-one (*₁-preserves-< _ _ _ 0<q q<1))

  squares-dense-1 : {q : ℚ} -> (1r < q) ->
                    ∃[ s ∈ ℚ ] (isSquareℚ s × 1r < s × s < q)
  squares-dense-1 {q} 1<q = ∥-bind handle (squares-dense-0 pos-d/2)
    where
    Ans = ∃[ s ∈ ℚ ] (isSquareℚ s × 1r < s × s < q)
    pos-d = Pos-diffℚ _ _ 1<q
    d/2 = (1/2r * (diffℚ 1r q))
    pos-d/2 = *-preserves-0< _ _ Pos-1/2r pos-d

    handle : Σ[ ε² ∈ ℚ ] (isSquareℚ ε² × (0r < ε²) × (ε² < d/2)) -> Ans
    handle (ε² , (ε' , 0≤ε' , ε'ε'=ε²) , 0<ε² , ε²<d/2) = ans
      where
      ε = minℚ ε' (d/2 * 1/2r)

      0!=ε' : 0r != ε'
      0!=ε' 0=ε' = irrefl-< (subst (_< ε²) (sym *-right-zero >=> *-right 0=ε' >=> ε'ε'=ε²) 0<ε²)

      0<ε' : 0r < ε'
      0<ε' = strengthen-≤-≠ 0≤ε' 0!=ε'

      0<ε : 0r < ε
      0<ε = minℚ-property {P = (0r <_)} _ _ 0<ε' (r*-preserves-Pos _ _ pos-d/2 Pos-1/2r)

      0<2r : 0r < 2r
      0<2r = Pos-ℕ⁺->ℚ (2 , tt)

      c1-ε≤ : ε ≤ ((1/2r * (diffℚ 1r q)) * 1/2r)
      c1-ε≤ = minℚ-≤-right _ _

      ε≤ε' : ε ≤ ε'
      ε≤ε' = minℚ-≤-left _ _
      εε≤ε'ε' : (ε * ε) ≤ (ε' * ε')
      εε≤ε'ε' = trans-≤ (*₁-preserves-≤ ε ε ε' (weaken-< 0<ε) ε≤ε')
                        (*₂-preserves-≤ ε ε' ε' ε≤ε' 0≤ε')

      c2-ε< : (ε * ε) < (1/2r * (diffℚ 1r q))
      c2-ε< = trans-≤-< εε≤ε'ε' (subst2 _<_ (sym ε'ε'=ε²) refl ε²<d/2)

      c1-2qε≤ : (2r * ε) ≤ (1/2r * (diffℚ 1r q))
      c1-2qε≤ = subst2 _≤_ *-commute p (*₂-preserves-≤ _ _ _ c1-ε≤ (weaken-< 0<2r))
        where
        p = *-assoc >=> *-right (*-commute >=> 2r-1/2r-path) >=> *-right-one

      2qε-ε²≤ : ((2r * ε) + (ε * ε)) < (diffℚ 1r q)
      2qε-ε²≤ = subst2 _<_ refl (1/2r-path' _) (+-preserves-≤-< _ _ _ _ c1-2qε≤ c2-ε<)
      1-2qε-ε²≤ : (1r + ((2r * ε) + (ε * ε))) < q
      1-2qε-ε²≤ = subst2 _<_ refl (diffℚ-step 1r q) (+₁-preserves-< 1r _ _ 2qε-ε²≤)

      s = (1r + ((2r * ε) + (ε * ε)))
      1<s : 1r < s
      1<s = subst2 _<_ +-right-zero refl (+₁-preserves-< 1r _ _ pos)
        where
        pos = (r+-preserves-Pos _ _ (*-preserves-0< _ _ 0<2r 0<ε) (*-preserves-0< _ _ 0<ε 0<ε))

      r = (1r + ε)
      0<r = r+-preserves-Pos _ _ 0<1r 0<ε


      r²=s : (r * r) == s
      r²=s = *-distrib-+-right >=>
             cong2 _+_ *-distrib-+-left *-distrib-+-left >=>
             +-assoc >=>
             +-left *-right-one >=>
             +-right (sym +-assoc >=>
                      +-left (cong2 _+_ *-left-one *-right-one >=>
                              2r-path ε))

      ans : ∃[ s ∈ ℚ ] (isSquareℚ s × 1r < s × s < q)
      ans = ∣ s , (r , weaken-< 0<r , r²=s) , 1<s , 1-2qε-ε²≤ ∣


  squares-dense-lower-square-0< :
    {q : ℚ} -> (0r < q) -> (r : ℚ) -> ((q * q) < r) -> ∃[ s ∈ ℚ ] (isSquareℚ s × (q * q) < s × s < r)
  squares-dense-lower-square-0< {q} 0<q r qq<r = ∥-map handle (squares-dense-1 1<r/qq)
    where
    pos-qq = (*-preserves-0< _ _ 0<q 0<q)
    1/qq : ℚ
    1/qq = r1/ (q * q) (Pos->Inv pos-qq)
    pos-1/qq : Pos 1/qq
    pos-1/qq = r1/-preserves-Pos _ _ pos-qq

    1<r/qq : 1r < (r * 1/qq)
    1<r/qq = subst2 _<_ (r1/-inverse _ _) *-commute (*₁-preserves-< _ _ _ pos-1/qq qq<r)

    handle : Σ[ s ∈ ℚ ] (isSquareℚ s × 1r < s × s < (r * 1/qq)) ->
             Σ[ s ∈ ℚ ] (isSquareℚ s × (q * q) < s × s < r)
    handle (s , (t , 0≤t , tt=s) , 1<s , s<r/qq) =
      (s * (q * q) , (t * q , tq≤0 , tqtq=sqq) , qq<sqq , sqq<r)
      where
      tq≤0 = *-preserves-0≤ _ _ 0≤t (weaken-< 0<q)
      tqtq=sqq = *-assoc >=> *-right (*-commute >=> *-assoc) >=> sym *-assoc >=> *-left tt=s
      qq<sqq = subst2 _<_ *-left-one refl (*₂-preserves-< _ _ _ 1<s pos-qq)
      sqq<r = subst2 _<_ refl (*-assoc >=> *-right (r1/-inverse _ _) >=> *-right-one)
                     (*₂-preserves-< _ _ _ s<r/qq pos-qq)

  squares-dense-lower-square-0= :
    {q : ℚ} -> (0r == q) -> (r : ℚ) -> ((q * q) < r) -> ∃[ s ∈ ℚ ] (isSquareℚ s × (q * q) < s × s < r)
  squares-dense-lower-square-0= {q} 0=q r qq<r = ∥-map handle (squares-dense-0 0<r)
    where
    qq=0 = (*-right (sym 0=q) >=> *-right-zero)
    0<r : 0r < r
    0<r = subst (_< r) qq=0 qq<r

    handle : Σ[ s ∈ ℚ ] (isSquareℚ s × 0r < s × s < r) ->
             Σ[ s ∈ ℚ ] (isSquareℚ s × (q * q) < s × s < r)
    handle (s , sq , 0<s , s<r) = (s , sq , (subst (_< s) (sym qq=0) 0<s) , s<r)


  squares-dense-upper-square-0< :
    {q : ℚ} -> (0r < q) -> {r : ℚ} -> (0r < r) -> (q < (r * r)) ->
    ∃[ s ∈ ℚ ] (isSquareℚ s × q < s × s < (r * r))
  squares-dense-upper-square-0< {q} 0<q {r} 0<r q<rr =
    ∥-map handle (squares-dense-lower-square-0< 0<1/r 1/q 1/r²<1/q)
    where
    rr = (r * r)
    0<rr = trans-< 0<q q<rr
    1/q = r1/ q (Pos->Inv 0<q)
    1/r = r1/ r (Pos->Inv 0<r)
    1/rr = r1/ rr (Pos->Inv 0<rr)

    1/rr<1/q : 1/rr < 1/q
    1/rr<1/q = r1/-Pos-flips-order (q , 0<q) (rr , 0<rr) q<rr
    1/rr=1/r² : 1/rr == 1/r * 1/r
    1/rr=1/r² = r1/-distrib-* r r (Pos->Inv 0<r) (Pos->Inv 0<r) (Pos->Inv 0<rr)

    1/r²<1/q : (1/r * 1/r) < 1/q
    1/r²<1/q = subst (_< 1/q) 1/rr=1/r² 1/rr<1/q

    0<1/q = r1/-preserves-Pos q (Pos->Inv 0<q) 0<q
    0<1/r = r1/-preserves-Pos r (Pos->Inv 0<r) 0<r
    0<1/rr = r1/-preserves-Pos rr (Pos->Inv 0<rr) 0<rr
    0<1/r² = *-preserves-0< _ _ 0<1/r 0<1/r

    handle : Σ[ s ∈ ℚ ] (isSquareℚ s × (1/r * 1/r) < s × s < 1/q) ->
             Σ[ s ∈ ℚ ] (isSquareℚ s × q < s × s < (r * r))
    handle (s , (t , 0≤t , tt=s) , 1/r²<s , s<1/q) =
      1/s , (1/t , weaken-< 0<1/t , 1/t²=1/s) , q<1/s , 1/s<rr
      where
      0<s = trans-< 0<1/r² 1/r²<s
      1/s = r1/ s (Pos->Inv 0<s)
      0<t = strengthen-≤-≠ 0≤t 0!=t
        where
        0!=t : 0r != t
        0!=t 0=t = irrefl-< (subst (0r <_) (sym tt=s >=> *-right (sym 0=t) >=> *-right-zero) 0<s)
      1/t = r1/ t (Pos->Inv 0<t)
      0<1/t = r1/-preserves-Pos t (Pos->Inv 0<t) 0<t
      0<tt = *-preserves-0< _ _ 0<t 0<t
      1/tt = r1/ (t * t) (Pos->Inv 0<tt)

      1/tt=1/s : 1/tt == 1/s
      1/tt=1/s = cong2-dep r1/ tt=s (isProp->PathP (\_ -> isProp-ℚInv) (Pos->Inv 0<tt) (Pos->Inv 0<s))
      1/t²=1/s = sym (r1/-distrib-* t t (Pos->Inv 0<t) (Pos->Inv 0<t) (Pos->Inv 0<tt)) >=> 1/tt=1/s

      q<1/s : q < 1/s
      q<1/s = subst (_< 1/s) (r1/-double-inverse q (Pos->Inv 0<q) (Pos->Inv 0<1/q))
                    (r1/-Pos-flips-order (s , 0<s) (1/q , 0<1/q) s<1/q)
      1/s<rr : 1/s < rr
      1/s<rr =
        subst (1/s <_) (r1/-double-inverse rr (Pos->Inv 0<rr) (Pos->Inv 0<1/rr))
              (r1/-Pos-flips-order (1/rr , 0<1/rr) (s , 0<s)
                (subst (_< s) (sym (r1/-distrib-* r r (Pos->Inv 0<r) (Pos->Inv 0<r) (Pos->Inv 0<rr)))
                       1/r²<s))

  squares-dense-upper-square-0= :
    {q : ℚ} -> (0r < q) -> {r : ℚ} -> (0r == r) -> (q < (r * r)) ->
    ∃[ s ∈ ℚ ] (isSquareℚ s × q < s × s < (r * r))
  squares-dense-upper-square-0= {q} 0<q {r} 0=r q<rr =
    bot-elim (asym-< 0<q (subst (q <_) (*-right (sym 0=r) >=> *-right-zero) q<rr))

abstract
  squares-dense-lower-square :
    {q r : ℚ} -> (0r ≤ q) -> ((q * q) < r) -> ∃[ s ∈ ℚ ] (isSquareℚ s × (q * q) < s × s < r)
  squares-dense-lower-square {q} {r} 0≤q =
    ℚ0≤-elim
      {P = \q -> (r : ℚ) -> ((q * q) < r) -> ∃[ s ∈ ℚ ] (isSquareℚ s × (q * q) < s × s < r)}
      (isPropΠ2 (\_ _ -> squash))
      squares-dense-lower-square-0<
      squares-dense-lower-square-0= _ 0≤q r

  squares-dense-upper-square :
    {q : ℚ} -> (0r < q) -> {r : ℚ} -> (0r ≤ r) -> (q < (r * r)) ->
    ∃[ s ∈ ℚ ] (isSquareℚ s × q < s × s < (r * r))
  squares-dense-upper-square {q} 0<q {r} 0≤r =
    ℚ0≤-elim
      {P = \r -> (q < (r * r)) -> ∃[ s ∈ ℚ ] (isSquareℚ s × q < s × s < (r * r))}
      (isPropΠ (\_ -> squash))
      (squares-dense-upper-square-0< 0<q)
      (squares-dense-upper-square-0= 0<q) r 0≤r
