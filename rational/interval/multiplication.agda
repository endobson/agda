{-# OPTIONS --cubical --safe --exact-split #-}

module rational.interval.multiplication where

open import base
open import equality
open import order.instances.rational
open import rational.order
open import rational.interval
open import rational.interval.multiplication-base
open import sign
open import sign.instances.rational

private
  Iℚ-class : Iℚ -> Type₀
  Iℚ-class a = ((NonNegI a ⊎ NonPosI a) ⊎ (ForwardZeroI a ⊎ BackwardZeroI a))


  classify-Iℚ : (a : Iℚ) -> Iℚ-class a
  classify-Iℚ a@(l , u) =
    handle (fst (decide-sign l)) (fst (decide-sign u)) (snd (decide-sign l)) (snd (decide-sign u))
    where
    handle : (s1 s2 : Sign) -> isSign s1 l -> isSign s2 u -> Iℚ-class a
    handle pos-sign  pos-sign  pl pu = inj-l (inj-l (inj-l pl , inj-l pu))
    handle pos-sign  zero-sign pl zu = inj-l (inj-l (inj-l pl , inj-r zu))
    handle pos-sign  neg-sign  pl nu = inj-r (inj-r (inj-l pl , inj-l nu))
    handle zero-sign pos-sign  zl pu = inj-l (inj-l (inj-r zl , inj-l pu))
    handle zero-sign zero-sign zl zu = inj-l (inj-l (inj-r zl , inj-r zu))
    handle zero-sign neg-sign  zl nu = inj-r (inj-r (inj-r zl , inj-l nu))
    handle neg-sign  pos-sign  nl pu = inj-r (inj-l (inj-l nl , inj-l pu))
    handle neg-sign  zero-sign nl zu = inj-l (inj-r (inj-l nl , inj-r zu))
    handle neg-sign  neg-sign  nl nu = inj-l (inj-r (inj-l nl , inj-l nu))

  abstract
    i*-full : (a b : Iℚ) -> Σ Iℚ (Imul a b)
    i*-full a b = handle (classify-Iℚ a) (classify-Iℚ b)
      where
      handle : (Iℚ-class a) -> (Iℚ-class b) -> Σ Iℚ (Imul a b)
      handle (inj-l (inj-l pa)) (inj-l (inj-l pb)) = _ , imul-nn-nn pa pb
      handle (inj-l (inj-l pa)) (inj-l (inj-r pb)) = _ , imul-nn-np pa pb
      handle (inj-l (inj-l pa)) (inj-r (inj-l pb)) = _ , imul-nn-fz pa pb
      handle (inj-l (inj-l pa)) (inj-r (inj-r pb)) = _ , imul-nn-bz pa pb

      handle (inj-l (inj-r pa)) (inj-l (inj-l pb)) = _ , imul-np-nn pa pb
      handle (inj-l (inj-r pa)) (inj-l (inj-r pb)) = _ , imul-np-np pa pb
      handle (inj-l (inj-r pa)) (inj-r (inj-l pb)) = _ , imul-np-fz pa pb
      handle (inj-l (inj-r pa)) (inj-r (inj-r pb)) = _ , imul-np-bz pa pb

      handle (inj-r (inj-l pa)) (inj-l (inj-l pb)) = _ , imul-fz-nn pa pb
      handle (inj-r (inj-l pa)) (inj-l (inj-r pb)) = _ , imul-fz-np pa pb
      handle (inj-r (inj-l pa)) (inj-r (inj-l pb)) = _ , imul-fz-fz pa pb
      handle (inj-r (inj-l pa)) (inj-r (inj-r pb)) = _ , imul-fz-bz pa pb

      handle (inj-r (inj-r pa)) (inj-l (inj-l pb)) = _ , imul-bz-nn pa pb
      handle (inj-r (inj-r pa)) (inj-l (inj-r pb)) = _ , imul-bz-np pa pb
      handle (inj-r (inj-r pa)) (inj-r (inj-l pb)) = _ , imul-bz-fz pa pb
      handle (inj-r (inj-r pa)) (inj-r (inj-r pb)) = _ , imul-bz-bz pa pb

_i*_ : Iℚ -> Iℚ -> Iℚ
_i*_ a b = fst (i*-full a b)

private
  Imul-i* : (a b : Iℚ) -> Imul a b (a i* b)
  Imul-i* a b = snd (i*-full a b)

  Imul-i*-path : {a b c : Iℚ} -> Imul a b c -> (a i* b) == c
  Imul-i*-path im = Imul-path (Imul-i* _ _) im

  Imul-commute : {a b c : Iℚ} -> Imul a b c -> Imul b a c
  Imul-commute {a} {b} (imul-nn-nn pa pb) = subst (Imul b a) (i∙-commute _ _) (imul-nn-nn pb pa)
  Imul-commute {a} {b} (imul-nn-np pa pb) = subst (Imul b a) (i∙-commute _ _) (imul-np-nn pb pa)
  Imul-commute {a} {b} (imul-nn-fz pa pb) = subst (Imul b a) (i∙-commute _ _) (imul-fz-nn pb pa)
  Imul-commute {a} {b} (imul-nn-bz pa pb) = subst (Imul b a) (i∙-commute _ _) (imul-bz-nn pb pa)

  Imul-commute {a} {b} (imul-np-nn pa pb) = subst (Imul b a) (i∙-commute _ _) (imul-nn-np pb pa)
  Imul-commute {a} {b} (imul-np-np pa pb) = subst (Imul b a) (i∙-commute _ _) (imul-np-np pb pa)
  Imul-commute {a} {b} (imul-np-fz pa pb) = subst (Imul b a) (i∙-commute _ _) (imul-fz-np pb pa)
  Imul-commute {a} {b} (imul-np-bz pa pb) = subst (Imul b a) (i∙-commute _ _) (imul-bz-np pb pa)

  Imul-commute {a} {b} (imul-fz-nn pa pb) = subst (Imul b a) (i∙-commute _ _) (imul-nn-fz pb pa)
  Imul-commute {a} {b} (imul-fz-np pa pb) = subst (Imul b a) (i∙-commute _ _) (imul-np-fz pb pa)
  Imul-commute {a} {b} (imul-fz-fz pa pb) = subst (Imul b a) (i-cross-commute _ _) (imul-fz-fz pb pa)
  Imul-commute {a} {b} (imul-fz-bz pa pb) = (imul-bz-fz pb pa)

  Imul-commute {a} {b} (imul-bz-nn pa pb) = subst (Imul b a) (i∙-commute _ _) (imul-nn-bz pb pa)
  Imul-commute {a} {b} (imul-bz-np pa pb) = subst (Imul b a) (i∙-commute _ _) (imul-np-bz pb pa)
  Imul-commute {a} {b} (imul-bz-fz pa pb) = (imul-fz-bz pb pa)
  Imul-commute {a} {b} (imul-bz-bz pa pb) = subst (Imul b a) (cong i-conj (i-cross-commute _ _))
                                                  (imul-bz-bz pb pa)

i*-commute : {a b : Iℚ} -> (a i* b) == (b i* a)
i*-commute = Imul-path (Imul-i* _ _) (Imul-commute (Imul-i* _ _))

i*-left-zero : {b : Iℚ} -> (0i i* b) == 0i
i*-left-zero {b} = handle (classify-Iℚ b)
  where
  nn-0 : NonNegI 0i
  nn-0 = (inj-r Zero-0r , inj-r Zero-0r)

  handle : Iℚ-class b -> _
  handle (inj-l (inj-l p)) = Imul-path (Imul-i* _ _) (imul-nn-nn nn-0 p) >=> i∙-left-zero _
  handle (inj-l (inj-r p)) = Imul-path (Imul-i* _ _) (imul-nn-np nn-0 p) >=> i∙-left-zero _
  handle (inj-r (inj-l p)) = Imul-path (Imul-i* _ _) (imul-nn-fz nn-0 p) >=> i∙-left-zero _
  handle (inj-r (inj-r p)) = Imul-path (Imul-i* _ _) (imul-nn-bz nn-0 p) >=> i∙-left-zero _

i*-right-zero : {b : Iℚ} -> (b i* 0i) == 0i
i*-right-zero = i*-commute >=> i*-left-zero


private
  i*-NonNeg-NonNeg : {a b : Iℚ} -> NonNegI a -> NonNegI b -> NonNegI (a i* b)
  i*-NonNeg-NonNeg nn-a nn-b =
    subst NonNegI (sym (Imul-i*-path (imul-nn-nn nn-a nn-b)))
                  (i∙-NonNeg-NonNeg _ _ nn-a nn-b)

  i*-NonNeg-NonPos : {a b : Iℚ} -> NonNegI a -> NonPosI b -> NonPosI (a i* b)
  i*-NonNeg-NonPos nn-a np-b =
    subst NonPosI (sym (Imul-i*-path (imul-nn-np nn-a np-b)))
                  (i∙-NonNeg-NonPos _ _ (i-conj-NonNeg _ nn-a) np-b)

  i*-NonNeg-ForwardZero : {a b : Iℚ} -> NonNegI a -> ForwardZeroI b -> ForwardZeroI (a i* b)
  i*-NonNeg-ForwardZero nn-a@(nn-al , nn-au) fz-b =
    subst ForwardZeroI (sym (Imul-i*-path (imul-nn-fz nn-a fz-b)))
                       (i∙-NonNeg-ForwardZero _ _ (nn-au , nn-au) fz-b)

  i*-NonNeg-BackwardZero : {a b : Iℚ} -> NonNegI a -> BackwardZeroI b -> BackwardZeroI (a i* b)
  i*-NonNeg-BackwardZero nn-a@(nn-al , nn-au) bz-b =
    subst BackwardZeroI (sym (Imul-i*-path (imul-nn-bz nn-a bz-b)))
                        (i∙-NonNeg-BackwardZero _ _ (nn-al , nn-al) bz-b)

  i*-NonPos-NonNeg : {a b : Iℚ} -> NonPosI a -> NonNegI b -> NonPosI (a i* b)
  i*-NonPos-NonNeg np-a nn-b = subst NonPosI i*-commute (i*-NonNeg-NonPos nn-b np-a)




--
--  i*-assoc
