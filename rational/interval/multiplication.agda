{-# OPTIONS --cubical --safe --exact-split #-}

module rational.interval.multiplication where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.minmax
open import rational.interval
open import rational.interval.multiplication-base
open import relation
open import sign
open import sign.instances.rational

private
  Iℚ-class : Iℚ -> Type₀
  Iℚ-class a = ((NonNegI a ⊎ NonPosI a) ⊎ (ForwardZeroI a ⊎ BackwardZeroI a))


  classify-Iℚ : (a : Iℚ) -> Iℚ-class a
  classify-Iℚ a@(l , u) = handle (isSign-self l) (isSign-self u)
    where
    handle : {s1 s2 : Sign} -> isSign s1 l -> isSign s2 u -> Iℚ-class a
    handle {pos-sign}  {pos-sign}  pl pu = inj-l (inj-l (inj-l pl , inj-l pu))
    handle {pos-sign}  {zero-sign} pl zu = inj-l (inj-l (inj-l pl , inj-r zu))
    handle {pos-sign}  {neg-sign}  pl nu = inj-r (inj-r (inj-l pl , inj-l nu))
    handle {zero-sign} {pos-sign}  zl pu = inj-l (inj-l (inj-r zl , inj-l pu))
    handle {zero-sign} {zero-sign} zl zu = inj-l (inj-l (inj-r zl , inj-r zu))
    handle {zero-sign} {neg-sign}  zl nu = inj-r (inj-r (inj-r zl , inj-l nu))
    handle {neg-sign}  {pos-sign}  nl pu = inj-r (inj-l (inj-l nl , inj-l pu))
    handle {neg-sign}  {zero-sign} nl zu = inj-l (inj-r (inj-l nl , inj-r zu))
    handle {neg-sign}  {neg-sign}  nl nu = inj-l (inj-r (inj-l nl , inj-l nu))

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
