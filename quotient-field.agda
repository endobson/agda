{-# OPTIONS --cubical --safe --exact-split #-}

module quotient-field where

open import additive-group
open import apartness
open import base
open import cubical
open import equality
open import equivalence
open import functions
open import funext
open import heyting-field
open import hlevel
open import integral-domain
open import isomorphism
open import relation
open import ring
open import semiring
open import set-quotient
open import sigma.base
open import sum
open import truncation
open import univalence

module _ {ℓ : Level} {D : Type ℓ} {D# : Rel D ℓ} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM} {AG : AdditiveGroup ACM}
         {R : Ring S AG} {A : isTightApartness D#} (ID : IntegralDomain R A) where
  private
    module R = Ring R
    module ID = IntegralDomain ID
    instance
      IACM = ACM
      IAG = AG
      IS = S
      IR = R
      IA = A
      IID = ID

    record Fraction : Type ℓ where
      no-eta-equality ; pattern
      constructor frac
      field
        n : D
        d : D
        d#0 : d # 0#
    F = Fraction
    module F = Fraction

    record SameFraction (a b : Fraction) : Type ℓ where
      no-eta-equality ; pattern
      constructor same-fraction
      private
        na = F.n a
        da = F.d a
        nb = F.n b
        db = F.d b

      field
        path : na * db == nb * da

    _~_ = SameFraction

    sym-~ : (a b : F) -> a ~ b -> b ~ a
    sym-~ _ _ (same-fraction p) = (same-fraction (sym p))

    D->F : D -> F
    D->F x = frac x 1# ID.1#0

    0f : F
    0f = D->F 0#

    1f : F
    1f = D->F 1#

    nd-path : (f1 f2 : F) -> F.n f1 == F.n f2 -> F.d f1 == F.d f2 -> f1 == f2
    nd-path (frac _ _ d1#0) (frac _ _ d2#0) n d i =
      frac (n i) (d i) (isProp->PathPᵉ p d1#0 d2#0 i)
      where
      p : (i : I) -> isProp (d i # 0#)
      p i = isProp-#

    _f+_ : F -> F -> F
    _f+_ (frac na da da#0) (frac nb db db#0) = frac (na * db + nb * da) (da * db) dadb#0
      where
      dadb#0 = eqFun ID.*-#0-equiv (da#0 , db#0)

    _f*_ : F -> F -> F
    _f*_ (frac na da da#0) (frac nb db db#0) = frac (na * nb) (da * db) dadb#0
      where
      dadb#0 = eqFun ID.*-#0-equiv (da#0 , db#0)

    f-_ : F -> F
    f-_ (frac n d d#0) = (frac (- n) d d#0)

    module f-arith where
      abstract
        f+-commute : (a b : F) -> (a f+ b) == (b f+ a)
        f+-commute a@(frac _ _ _) b@(frac _ _ _) = nd-path (a f+ b) (b f+ a) +-commute *-commute

        f*-commute : (a b : F) -> (a f* b) == (b f* a)
        f*-commute a@(frac _ _ _) b@(frac _ _ _) = nd-path (a f* b) (b f* a) *-commute *-commute

        f+-left-zero : (a : F) -> (0f f+ a) == a
        f+-left-zero a@(frac _ _ _) =
          nd-path (0f f+ a) a (+-cong *-left-zero *-right-one >=> +-left-zero) *-left-one

        f*-left-zero : (a : F) -> (0f f* a) ~ 0f
        f*-left-zero a@(frac _ _ _) =
          same-fraction (*-left *-left-zero >=> *-left-zero >=> sym *-left-zero)

        f*-left-one : (a : F) -> (1f f* a) == a
        f*-left-one a@(frac _ _ _) = nd-path (1f f* a) a *-left-one *-left-one

        f+-assoc : (a b c : F) -> (a f+ b) f+ c == a f+ (b f+ c)
        f+-assoc a@(frac na da _) b@(frac nb db _) c@(frac nc dc _) =
          nd-path ((a f+ b) f+ c) (a f+ (b f+ c)) p *-assoc
          where
          p : (na * db + nb * da) * dc + nc * (da * db) == na * (db * dc) + (nb * dc + nc * db) * da
          p = +-left *-distrib-+-right >=>
              +-left (+-left *-assoc) >=>
              +-left (+-right (*-assoc >=> *-right *-commute >=> sym *-assoc)) >=>
              +-right (*-right *-commute >=> sym *-assoc) >=>
              +-assoc >=>
              +-right (sym *-distrib-+-right)

        f*-assoc : (a b c : F) -> (a f* b) f* c == a f* (b f* c)
        f*-assoc a@(frac _ _ _) b@(frac _ _ _) c@(frac _ _ _) =
          nd-path ((a f* b) f* c) (a f* (b f* c)) *-assoc *-assoc


        f*-distrib-+-right : (a b c : F) -> ((a f+ b) f* c) ~ ((a f* c) f+ (b f* c))
        f*-distrib-+-right (frac na da _) (frac nb db _) (frac nc dc _) = same-fraction p
          where
          p3 : ((na * db) * nc) * dc == (na * nc) * (db * dc)
          p3 = *-left (*-assoc >=> *-right *-commute >=> sym *-assoc) >=> *-assoc

          p4 : ((nb * da) * nc) * dc == ((nb * nc) * (da * dc))
          p4 = *-left (*-assoc >=> *-right *-commute >=> sym *-assoc) >=> *-assoc

          p1 : ((na * db + nb * da) * nc) * dc ==
               (((na * nc) * (db * dc)) + ((nb * nc) * (da * dc)))
          p1 = *-left *-distrib-+-right >=>
               *-distrib-+-right >=>
               +-cong p3 p4

          p2 : ((da * dc) * (db * dc)) == dc * ((da * db) * dc)
          p2 = *-left *-commute >=>
               *-assoc >=>
               *-right (sym *-assoc)

          p : ((na * db + nb * da) * nc) * ((da * dc) * (db * dc)) ==
              (((na * nc) * (db * dc)) + ((nb * nc) * (da * dc))) * ((da * db) * dc)
          p = *-right p2 >=> sym *-assoc >=> *-left p1

        +₁-preserves-~ : (a b c : F) -> b ~ c -> (a f+ b) ~ (a f+ c)
        +₁-preserves-~ (frac na da _) (frac nb db _) (frac nc dc _) (same-fraction b~c) = same-fraction p
          where

          p1 : (na * db) * (da * dc) == (na * dc) * (da * db)
          p1 = *-right *-commute >=> *-assoc >=>
               *-right (sym *-assoc >=> *-left *-commute >=> *-assoc) >=>
               sym *-assoc >=> *-right *-commute

          p2 : (nb * da) * (da * dc) == (nc * da) * (da * db)
          p2 = *-left *-commute >=> *-right *-commute >=> *-assoc >=>
               *-right (sym *-assoc >=> *-left b~c >=> *-assoc) >=>
               sym *-assoc >=> *-right *-commute >=> *-left *-commute

          p : (na * db + nb * da) * (da * dc) == (na * dc + nc * da) * (da * db)
          p = *-distrib-+-right >=> +-cong p1 p2 >=> sym *-distrib-+-right

        +₂-preserves-~ : (a b c : F) -> a ~ b -> (a f+ c) ~ (b f+ c)
        +₂-preserves-~ a b c a~b =
          subst2 _~_ (f+-commute c a) (f+-commute c b) (+₁-preserves-~ c a b a~b)

        *₁-preserves-~ : (a b c : F) -> b ~ c -> (a f* b) ~ (a f* c)
        *₁-preserves-~ (frac na da _) (frac nb db _) (frac nc dc _) (same-fraction b~c) = (same-fraction p)
          where

          p : (na * nb) * (da * dc) == (na * nc) * (da * db)
          p = *-right *-commute >=> *-assoc >=>
              *-right (sym *-assoc >=> *-left b~c >=> *-assoc) >=>
              sym *-assoc >=> *-right *-commute

        *₂-preserves-~ : (a b c : F) -> a ~ b -> (a f* c) ~ (b f* c)
        *₂-preserves-~ a b c a~b =
          subst2 _~_ (f*-commute c a) (f*-commute c b) (*₁-preserves-~ c a b a~b)

        f+-inverse : (a : F) -> (a f+ (f- a)) ~ 0f
        f+-inverse (frac n d d#0) = same-fraction p
          where
          p : (n * d + (- n) * d) * 1# == 0# * (d * d)
          p = *-right-one >=> (sym *-distrib-+-right) >=> *-left +-inverse >=>
              *-left-zero >=> sym *-left-zero

        minus-preserves-~ : (a b : F) -> a ~ b -> (f- a) ~ (f- b)
        minus-preserves-~ a@(frac _ _ _) b@(frac _ _ _) (same-fraction a~b) =
          same-fraction (minus-extract-left >=> cong -_ a~b >=> sym minus-extract-left)
    open f-arith

    record _f#_ (a b : F) : Type ℓ where
      no-eta-equality ; pattern
      constructor f#-cons
      private
        na = F.n a
        da = F.d a
        nb = F.n b
        db = F.d b

      field
        apart : (na * db) # (nb * da)

    isProp-f# : {a b : F} -> isProp (a f# b)
    isProp-f# (f#-cons ap1) (f#-cons ap2) = cong f#-cons (isProp-# ap1 ap2)

    _f#'_ : F -> F -> hProp ℓ
    _f#'_ a b = (a f# b) , isProp-f#

    module f-apart where
      abstract
        sym-f# : (a b : F) -> a f# b -> b f# a
        sym-f# _ _ (f#-cons ap) = f#-cons (sym-# ap)

        irrefl-f# : (a : F) -> ¬ (a f# a)
        irrefl-f# a (f#-cons a#a) = irrefl-# a#a

        comparison-f# : Comparison _f#_
        comparison-f# a@(frac na da _) b@(frac nb db _) c@(frac nc dc _) (f#-cons a#c) =
          ∥-map (⊎-map (f#-cons ∘ case1) (f#-cons ∘ case2)) (comparison-# _ _ _ ans3)
          where
          module _ where
            ans3 : (db * (na * dc)) # (db * (nc * da))
            ans3 = *₁-preserves-# (F.d#0 b) a#c

            case1 : (db * (na * dc)) # (nb * (dc * da)) -> (na * db) # (nb * da)
            case1 a1 = *₁-reflects-# (subst2 _#_ p1 p2 a1)
              where
              p1 = *-commute >=> *-left *-commute >=> *-assoc
              p2 = sym *-assoc >=> *-left *-commute >=> *-assoc


            case2 : (nb * (dc * da)) # (db * (nc * da)) -> (nb * dc) # (nc * db)
            case2 a1 = *₁-reflects-# (subst2 _#_ p1 p2 a1)
              where
              p1 = sym *-assoc >=> *-commute
              p2 = sym *-assoc >=> *-commute >=> *-right *-commute

        #₁-~-forward : (a b c : F) -> b ~ c -> (a f# b) -> (a f# c)
        #₁-~-forward (frac na da _) (frac nb db _) c@(frac nc dc _) (same-fraction b~c) (f#-cons a#b) = (f#-cons ans)
          where
          module _ where
            ans5 : (dc * diff (na * db) (nb * da)) # 0#
            ans5 = eqFun ID.*-#0-equiv (F.d#0 c , eqFun ID.diff-#-equiv a#b)

            ans4 : diff (dc * (na * db)) (dc * (nb * da)) # 0#
            ans4 = subst (_# 0#) *-distrib-diff-left ans5

            ans3 : diff (db * (na * dc)) (db * (nc * da)) # 0#
            ans3 = subst2 (\x y -> diff x y # 0#) lp rp ans4
              where
              lp = *-right *-commute >=> sym *-assoc >=> *-left *-commute >=> *-assoc >=> *-right *-commute
              rp = sym *-assoc >=> *-left (*-commute >=> b~c >=> *-commute) >=> *-assoc

            ans2 : (db * diff (na * dc) (nc * da)) # 0#
            ans2 = subst (_# 0#) (sym *-distrib-diff-left) ans3

            ans1 : diff (na * dc) (nc * da) # 0#
            ans1 = snd (eqInv ID.*-#0-equiv ans2)

            ans : (na * dc) # (nc * da)
            ans = eqInv ID.diff-#-equiv ans1

        #₂-~-forward : (a b c : F) -> a ~ b -> (a f# c) -> (b f# c)
        #₂-~-forward a b c a~b a#c = sym-f# c b (#₁-~-forward c a b a~b (sym-f# a c a#c))

        #₁-~ : (a b c : F) -> b ~ c -> (a f# b) == (a f# c)
        #₁-~ a b c b~c =
          ua (isoToEquiv (isProp->iso a#b->a#c a#c->a#b isProp-f# isProp-f#))
          where
          a#b->a#c : (a f# b) -> (a f# c)
          a#b->a#c = #₁-~-forward a b c b~c

          a#c->a#b : (a f# c) -> (a f# b)
          a#c->a#b = #₁-~-forward a c b (sym-~ b c b~c)

        #₂-~ : (a b c : F) -> a ~ b -> (a f# c) == (b f# c)
        #₂-~ a b c a~b =
          ua (isoToEquiv (isProp->iso a#c->b#c b#c->a#c isProp-f# isProp-f#))
          where
          a#c->b#c : (a f# c) -> (b f# c)
          a#c->b#c = #₂-~-forward a b c a~b

          b#c->a#c : (b f# c) -> (a f# c)
          b#c->a#c = #₂-~-forward b a c (sym-~ a b a~b)

        #'₁-~ : (a b c : F) -> b ~ c -> (a f#' b) == (a f#' c)
        #'₁-~ a b c b~c =
          ΣProp-path isProp-isProp (#₁-~ a b c b~c)

        #'₂-~ : (a b c : F) -> a ~ b -> (a f#' c) == (b f#' c)
        #'₂-~ a b c a~b =
          ΣProp-path isProp-isProp (#₂-~ a b c a~b)

        1f#0 : 1f f# 0f
        1f#0 = f#-cons (subst2 _#_ (sym *-right-one) (sym *-right-one) ID.1#0)

        #0->inverse : (a : F) -> a f# 0f -> Σ[ b ∈ F ] (SameFraction (a f* b) 1f)
        #0->inverse a@(frac na da da#0) (f#-cons a#0) = (frac da na na#0) , (same-fraction p)
          where
          module _ where
            p : (na * da) * 1# == 1# * (da * na)
            p = *-commute >=> *-right *-commute
            na#0 : na # 0#
            na#0 = subst2 _#_ *-right-one *-left-zero a#0

        f*₁-preserves-# : (a b c : F) -> a f# 0f -> b f# c -> (a f* b) f# (a f* c)
        f*₁-preserves-# a@(frac na da _) (frac nb db _) c@(frac nc dc _) (f#-cons a#0) (f#-cons b#c) =
          (f#-cons ans)
          where
          module _ where
            da#0 = F.d#0 a
            na#0 : na # 0#
            na#0 = subst2 _#_ *-right-one *-left-zero a#0

            apart1 : ((na * da) * (nb * dc)) # ((na * da) * (nc * db))
            apart1 = *₁-preserves-# (eqFun ID.*-#0-equiv (na#0 , da#0)) b#c

            ans : ((na * nb) * (da * dc)) # ((na * nc) * (da * db))
            ans = subst2 _#_ p1 p2 apart1
              where
              p1 = *-assoc >=> *-right (sym *-assoc >=> *-left *-commute >=> *-assoc) >=> sym *-assoc
              p2 = *-assoc >=> *-right (sym *-assoc >=> *-left *-commute >=> *-assoc) >=> sym *-assoc

        f*₁-reflects-# : (a b c : F) -> (a f* b) f# (a f* c) -> b f# c
        f*₁-reflects-# (frac na da _) (frac nb db _) (frac nc dc _) (f#-cons ab#ac) = (f#-cons ans)
          where
          module _ where
            apart1 : ((na * da) * (nb * dc)) # ((na * da) * (nc * db))
            apart1 = subst2 _#_ (sym p1) (sym p2) ab#ac
              where
              p1 = *-assoc >=> *-right (sym *-assoc >=> *-left *-commute >=> *-assoc) >=> sym *-assoc
              p2 = *-assoc >=> *-right (sym *-assoc >=> *-left *-commute >=> *-assoc) >=> sym *-assoc

            ans : (nb * dc) # (nc * db)
            ans = *₁-reflects-# apart1

        diff-f#-equiv : (a b : F) -> (a f# b) ≃ ((b f+ (f- a)) f# 0f)
        diff-f#-equiv a@(frac na da _) b@(frac nb db _) =
          isoToEquiv (isProp->iso forward backward isProp-f# isProp-f#)
          where
          module _ where
            forward : (a f# b) -> (b f+ (f- a)) f# 0f
            forward (f#-cons a#b) = (f#-cons ans)
              where
              d-apart : diff (na * db) (nb * da) # 0#
              d-apart = eqFun ID.diff-#-equiv a#b

              ans : ((nb * da + ((- na) * db)) * 1#) # (0# * (db * da))
              ans = subst2 _#_ (+-right (sym minus-extract-left) >=> sym *-right-one) (sym *-left-zero) d-apart


            backward : (b f+ (f- a)) f# 0f -> (a f# b)
            backward (f#-cons d#0) = (f#-cons a#b)
              where
              d-apart : diff (na * db) (nb * da) # 0#
              d-apart = subst2 _#_ (sym (+-right (sym minus-extract-left) >=> sym *-right-one))
                                   *-left-zero d#0

              a#b : (na * db) # (nb * da)
              a#b = eqInv ID.diff-#-equiv d-apart
    open f-apart



  QuotientField : Type ℓ
  QuotientField = Fraction / SameFraction

  module QuotientField where
    private
      Q = QuotientField

      isSet-Q : isSet Q
      isSet-Q = squash/


    0q : Q
    0q = [ 0f ]

    1q : Q
    1q = [ 1f ]

    _q+_ : Q -> Q -> Q
    _q+_ = SetQuotientElim.rec2 isSet-Q (\a b -> [ a f+ b ])
             (\a b c a~b -> eq/ _ _ (+₂-preserves-~ a b c a~b))
             (\a b c b~c -> eq/ _ _ (+₁-preserves-~ a b c b~c))

    _q*_ : Q -> Q -> Q
    _q*_ = SetQuotientElim.rec2 isSet-Q (\a b -> [ a f* b ])
             (\a b c a~b -> eq/ _ _ (*₂-preserves-~ a b c a~b))
             (\a b c b~c -> eq/ _ _ (*₁-preserves-~ a b c b~c))

    q-_ : Q -> Q
    q-_ = SetQuotientElim.rec isSet-Q (\a -> [ (f- a) ]) (\a b a~b -> eq/ _ _ (minus-preserves-~ a b a~b))

    abstract
      q+-commute : (a b : Q) -> a q+ b == b q+ a
      q+-commute = SetQuotientElim.elimProp2 {C2 = \a b -> a q+ b == b q+ a}
                     (\a b -> isSet-Q (a q+ b) (b q+ a))
                     (\a b -> cong [_] (f+-commute a b))

      q*-commute : (a b : Q) -> a q* b == b q* a
      q*-commute = SetQuotientElim.elimProp2 {C2 = \a b -> a q* b == b q* a}
                     (\a b -> isSet-Q (a q* b) (b q* a))
                     (\a b -> cong [_] (f*-commute a b))


      q+-left-zero : (a : Q) -> 0q q+ a == a
      q+-left-zero = SetQuotientElim.elimProp {C = \a -> 0q q+ a == a}
                       (\a -> isSet-Q (0q q+ a) a)
                       (\a -> cong [_] (f+-left-zero a))

      q*-left-zero : (a : Q) -> 0q q* a == 0q
      q*-left-zero = SetQuotientElim.elimProp {C = \a -> 0q q* a == 0q}
                       (\a -> isSet-Q (0q q* a) 0q)
                       (\a -> eq/ _ _ (f*-left-zero a))

      q*-left-one : (a : Q) -> 1q q* a == a
      q*-left-one = SetQuotientElim.elimProp {C = \a -> 1q q* a == a}
                       (\a -> isSet-Q (1q q* a) a)
                       (\a -> cong [_] (f*-left-one a))

      q+-assoc : (a b c : Q) -> (a q+ b) q+ c == a q+ (b q+ c)
      q+-assoc = SetQuotientElim.elimProp3 {C3 = \a b c -> (a q+ b) q+ c == a q+ (b q+ c)}
                   (\a b c -> isSet-Q ((a q+ b) q+ c) (a q+ (b q+ c)))
                   (\a b c -> cong [_] (f+-assoc a b c))

      q*-assoc : (a b c : Q) -> (a q* b) q* c == a q* (b q* c)
      q*-assoc = SetQuotientElim.elimProp3 {C3 = \a b c -> (a q* b) q* c == a q* (b q* c)}
                   (\a b c -> isSet-Q ((a q* b) q* c) (a q* (b q* c)))
                   (\a b c -> cong [_] (f*-assoc a b c))

      q*-distrib-+-right : (a b c : Q) -> ((a q+ b) q* c) == ((a q* c) q+ (b q* c))
      q*-distrib-+-right = SetQuotientElim.elimProp3 {C3 = \a b c -> (a q+ b) q* c == (a q* c) q+ (b q* c)}
                             (\a b c -> isSet-Q ((a q+ b) q* c) ((a q* c) q+ (b q* c)))
                             (\a b c -> eq/ _ _ (f*-distrib-+-right a b c))

      q+-inverse : (a : Q) -> a q+ (q- a) == 0q
      q+-inverse = SetQuotientElim.elimProp {C = \a -> a q+ (q- a)== 0q}
                     (\a -> isSet-Q (a q+ (q- a)) 0q)
                     (\a -> eq/ _ _ (f+-inverse a))

    instance
      AdditiveCommMonoid-Q : AdditiveCommMonoid Q
      AdditiveCommMonoid-Q = record
        { comm-monoid = record
          { monoid = record
            { ε = 0q
            ; _∙_ = _q+_
            ; ∙-assoc = \{a} {b} {c} -> q+-assoc a b c
            ; ∙-left-ε = \{a} -> q+-left-zero a
            ; ∙-right-ε = \{a} -> q+-commute a 0q >=> q+-left-zero a
            ; isSet-Domain = isSet-Q
            }
          ; ∙-commute = \{a} {b} -> q+-commute a b
          }
        }

      AdditiveGroup-Q : AdditiveGroup AdditiveCommMonoid-Q
      AdditiveGroup-Q = record
        { -_ = q-_
        ; +-inverse = \{a} -> q+-inverse a
        }

      Semiring-Q : Semiring AdditiveCommMonoid-Q
      Semiring-Q = record
        { 1# = 1q
        ; _*_ = _q*_
        ; *-assoc = \{a} {b} {c} -> q*-assoc a b c
        ; *-commute = \{a} {b} -> q*-commute a b
        ; *-left-zero = \{a} -> q*-left-zero a
        ; *-left-one = \{a} -> q*-left-one a
        ; *-distrib-+-right = \{a} {b} {c} -> q*-distrib-+-right a b c
        ; isSet-Domain = isSet-Q
        }


    Ring-Q : Ring Semiring-Q AdditiveGroup-Q
    Ring-Q = record {}
    module Ring-Q = Ring Ring-Q
    private
      instance
        IRing-Q = Ring-Q

    _q#'_ : Q -> Q -> hProp ℓ
    _q#'_ = SetQuotientElim.rec2 isSet-hProp _f#'_ #'₂-~ #'₁-~

    _q#_ : Rel Q ℓ
    _q#_ a b = fst (a q#' b)

    abstract
      isProp-q# : (a b : Q) -> isProp (a q# b)
      isProp-q# a b = snd (_q#'_ a b)

      irrefl-q# : Irreflexive _q#_
      irrefl-q# {a} = SetQuotientElim.elimProp {C = \a -> ¬ (a q# a)} (\_ -> isProp¬) irrefl-f# a

      sym-q# : Symmetric _q#_
      sym-q# {a} {b} =
        SetQuotientElim.elimProp2 {C2 = \a b -> a q# b -> b q# a}
          (\a b -> isPropΠ (\_ -> isProp-q# b a))
          (\a b -> sym-f# a b) a b

      comparison-q# : Comparison _q#_
      comparison-q# =
        SetQuotientElim.elimProp3 {C3 = \a b c -> a q# c -> ∥ (a q# b) ⊎ (b q# c) ∥}
          (\a b c -> isPropΠ (\_ -> squash))
          comparison-f#

      apartness-q# : Apartness _q#_
      apartness-q# = (\{a} -> irrefl-q# {a}) , (\{a} {b} -> sym-q# {a} {b}) , comparison-q#

      tight-q# : Tight _q#_
      tight-q# {a} {b} =
        SetQuotientElim.elimProp2 {C2 = \a b -> ¬ (a q# b) -> a == b}
          (\a b -> isPropΠ (\_ -> isSet-Q a b))
          (\a b ¬a#b -> eq/ a b (same-fraction (tight-# (¬a#b ∘ f#-cons)))) a b

      TightApartness-q# : TightApartness _q#_
      TightApartness-q# = tight-q# , apartness-q#

    instance
      isTightApartness-q# : isTightApartness _q#_
      isTightApartness-q# = record
        { tight-# = tight-q#
        ; irrefl-# = \{a} -> irrefl-q# {a}
        ; sym-# = \{a} {b} -> sym-q# {a} {b}
        ; comparison-# = comparison-q#
        ; isProp-# = \{a} {b} -> isProp-q# a b
        }

    1q#0 : 1# q# 0#
    1q#0 = 1f#0

    q*₁-preserves-# : (a b c : Q) -> a # 0# -> b # c -> (a * b) # (a * c)
    q*₁-preserves-# =
      SetQuotientElim.elimProp3 {C3 = \a b c -> (a q# 0#) -> b q# c -> (a * b) # (a * c)}
        (\a b c -> isPropΠ2 (\_ _ -> isProp-q# (a * b) (a * c)))
        f*₁-preserves-#

    q*₁-reflects-# : (a b c : Q) -> (a * b) # (a * c) -> b # c
    q*₁-reflects-# =
      SetQuotientElim.elimProp3 {C3 = \a b c -> (a * b) # (a * c) -> b q# c}
        (\a b c -> isPropΠ (\_ -> isProp-q# b c))
        f*₁-reflects-#

    diff-q#-equiv : (a b : Q) -> (a # b) ≃ (diff a b # 0#)
    diff-q#-equiv =
      SetQuotientElim.elimProp2 {C2 = \a b -> (a # b) ≃ (diff a b # 0#)}
        (\a b -> isProp-≃ (isProp-q# a b) (isProp-q# (diff a b) 0#))
        diff-f#-equiv

    q#0->isUnit : {a : Q} -> a q# 0q -> Ring-Q.isUnit a
    q#0->isUnit {a} a#0 = f inverse
      where
      f : Σ[ b ∈ Q ] (a * b == 1#) -> Ring-Q.isUnit a
      f (b , p) = Ring-Q.is-unit b p

      inverse : Σ[ b ∈ Q ] (a * b == 1#)
      inverse =
        SetQuotientElim.elimProp {C = \a -> a q# 0# -> Σ[ b ∈ Q ] (a * b == 1#)}
          (\a -> isPropΠ (\a#0 -> isProp-inverse a a#0))
          compute-inverse a a#0
        where
        compute-inverse : (a : F) -> (a f# 0f) -> Σ[ b ∈ Q ] ([ a ] * b == 1#)
        compute-inverse a a#0 = [ fst inv ] , eq/ _ _ (snd inv)
          where
          inv : Σ[ b ∈ F ] (SameFraction (a f* b) 1f)
          inv = #0->inverse a a#0

        isProp-inverse : (a : Q) -> a # 0q -> (i1 i2 : Σ[ b ∈ Q ] (a * b == 1#)) -> i1 == i2
        isProp-inverse a a#0 (b1 , p1) (b2 , p2) =
          ΣProp-path (isSet-Q _ 1#) b1=b2
          where
          ¬b1#b2 : ¬ (b1 # b2)
          ¬b1#b2 b1#b2 = irrefl-path-# (p1 >=> sym p2) (q*₁-preserves-# a b1 b2 a#0 b1#b2)

          b1=b2 : b1 == b2
          b1=b2 = tight-# ¬b1#b2

    q#->isUnit : (a b : Q) -> a q# b -> Ring-Q.isUnit (diff a b)
    q#->isUnit a b a#b = q#0->isUnit (eqFun (diff-q#-equiv a b) a#b)

    isUnit->q#0 : {a : Q} -> Ring-Q.isUnit a -> a # 0#
    isUnit->q#0 {a} (Ring-Q.is-unit b p) = q*₁-reflects-# b a 0# ba#b0
      where

      ba#b0 : (b * a) # (b * 0#)
      ba#b0 = subst2 _#_ (sym p >=> q*-commute a b) 0=b0 1q#0
        where
        0=b0 : 0# == b * 0#
        0=b0 = sym (*-right-zero {_} {_} {_} {b})

    isUnit->q# : (a b : Q) -> Ring-Q.isUnit (diff a b) -> a # b
    isUnit->q# a b = eqInv (diff-q#-equiv a b) ∘ isUnit->q#0

    isUnit-q#-equiv : (a b : Q) -> Ring-Q.isUnit (diff a b) ≃ (a # b)
    isUnit-q#-equiv a b =
      isoToEquiv (isProp->iso (isUnit->q# a b) (q#->isUnit a b)
                              Ring-Q.isProp-isUnit (isProp-q# a b))

    field#-q#-path : (\x y -> Ring-Q.isUnit (diff x y)) == _q#_
    field#-q#-path = funExt (\x -> (funExt (\y -> (ua (isUnit-q#-equiv x y)))))

    Field-Q : Field Ring-Q isTightApartness-q#
    Field-Q = record { f#-path = field#-q#-path }
