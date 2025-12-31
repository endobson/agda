{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-field where

open import additive-group
open import apartness
open import base
open import equality
open import equivalence
open import functions
open import heyting-field
open import hlevel
open import nat
open import nat.order
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.initial
open import ordered-semiring.semidomain
open import relation
open import ring
open import ring.unit
open import semidomain.heyting-field
open import semiring
open import semiring.initial
open import semiring.unit
open import sigma.base
open import sum
open import truncation

private
  variable
    ℓD ℓ< : Level

module _ {D : Type ℓD} {D# : Rel D ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D} {AG : AdditiveGroup ACM}
         {{S : Semiring ACM}} {LO : isLinearOrder D<}
         {R : Ring S AG} {A : isTightApartness D#}
         {{_ : ℕ->Semiring-Op D}}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
         {LOS : LinearlyOrderedSemiringStr S LO}
         {{NTO : NonTrivialLinearlyOrderedSemiringStr LOS}}
         {{F : Field R A}}
         {{AL : ApartLinearOrderStr A LO}}
         where
  private
    module F = Field F
    instance
      ILOS = LOS
      IACM = ACM
      IAG = AG
      IS = S
      ILO = LO
      IR = R
      IA = A
      ISD = Semidomain-Field
      ISOS = StronglyLinearlyOrderedSemiringStr-Semidomain

    isSet-D : isSet D
    isSet-D = Semiring.isSet-Domain S

  private
    iℕ : Nat -> D
    iℕ = ℕ->Semiring

    opaque
      0<iℕ : (n : Nat⁺) -> 0# < iℕ ⟨ n ⟩
      0<iℕ (suc n , _) =
        trans-=-<
          (sym ℕ->Semiring-preserves-0#)
          (ℕ->Semiring-preserves-< zero-<)

  opaque
    ∃!1/ℕ : (n : Nat⁺) -> ∃![ d ∈ D ] (iℕ ⟨ n ⟩ * d == 1#)
    ∃!1/ℕ n = (isUnit.inv u , isUnit.path u) , p _
      where
      u : isUnit (iℕ ⟨ n ⟩)
      u = (F.#0->isUnit (eqFun <>-equiv-# (inj-r (0<iℕ n))))
      p : isProp (Σ[ d ∈ D ] (iℕ ⟨ n ⟩ * d == 1#))
      p (d1 , p1) (d2 , p2) = ΣProp-path (isSet-D _ _) p3
        where
        p3 : d1 == d2
        p3 = sym (*-left-one) >=>
             (cong (_* d1) (sym p2 >=> *-commute)) >=>
             *-assoc >=> *-commute >=>
             (cong (_* d2) p1) >=> *-left-one

  1/ℕ : (n : Nat⁺) -> D
  1/ℕ n = ∃!-val (∃!1/ℕ n)

  opaque
    0<1/ℕ : (n : Nat⁺) -> 0# < 1/ℕ n
    0<1/ℕ n = *₁-reflects-0< (asym-< (0<iℕ n)) (trans-<-= 0<1 (sym (∃!-prop (∃!1/ℕ n))))

  opaque
    1/ℕ-flips-< : (a b : Nat⁺) -> ⟨ a ⟩ < ⟨ b ⟩ -> 1/ℕ b < 1/ℕ a
    1/ℕ-flips-< a⁺@(a' , _) b⁺@(b' , _) a'<b' =
      subst2 _<_ (sym *-assoc >=> *-left (∃!-prop (∃!1/ℕ a⁺)) >=> *-left-one)
                 (*-right *-commute >=> sym *-assoc >=> *-left (∃!-prop (∃!1/ℕ b⁺)) >=> *-left-one)
            a/ab<b/ab
      where
      a<b : iℕ a' < iℕ b'
      a<b = ℕ->Semiring-preserves-<  a'<b'
      1/a 1/b 1/ab : D
      1/a = 1/ℕ a⁺
      1/b = 1/ℕ b⁺
      1/ab = 1/a * 1/b
      0<1/ab : 0# < (1/a * 1/b)
      0<1/ab = *-preserves-0< (0<1/ℕ a⁺) (0<1/ℕ b⁺)
      a/ab<b/ab : (iℕ a' * (1/a * 1/b)) < (iℕ b' * (1/a * 1/b))
      a/ab<b/ab = *₂-preserves-< a<b 0<1/ab

  module _ {ℓ≤ : Level} {D≤ : Rel D ℓ≤} {PO : isPartialOrder D≤}
           {{POA : PartiallyOrderedAdditiveStr ACM PO}}
           {{POS : PartiallyOrderedSemiringStr S PO}}
           {{CO : CompatibleOrderStr LO PO}} where
    private
      instance
        IPO = PO

    opaque
      1/ℕ-flips-≤ : (a b : Nat⁺) -> ⟨ a ⟩ ≤ ⟨ b ⟩ -> 1/ℕ b ≤ 1/ℕ a
      1/ℕ-flips-≤ a⁺@(a' , _) b⁺@(b' , _) a'≤b' =
        subst2 _≤_ (sym *-assoc >=> *-left (∃!-prop (∃!1/ℕ a⁺)) >=> *-left-one)
                   (*-right *-commute >=> sym *-assoc >=> *-left (∃!-prop (∃!1/ℕ b⁺)) >=> *-left-one)
              a/ab≤b/ab
        where
        a≤b : iℕ a' ≤ iℕ b'
        a≤b = ℕ->Semiring-preserves-≤ a'≤b'
        1/a 1/b 1/ab : D
        1/a = 1/ℕ a⁺
        1/b = 1/ℕ b⁺
        1/ab = 1/a * 1/b
        0<1/ab : 0# < (1/a * 1/b)
        0<1/ab = *-preserves-0< (0<1/ℕ a⁺) (0<1/ℕ b⁺)
        a/ab≤b/ab : (iℕ a' * (1/a * 1/b)) ≤ (iℕ b' * (1/a * 1/b))
        a/ab≤b/ab = *₂-preserves-≤ a≤b (weaken-< 0<1/ab)


  opaque
    1/ℕ-distrib-* : (a b : Nat⁺) -> 1/ℕ ( a *⁺ b ) == 1/ℕ a * 1/ℕ b
    1/ℕ-distrib-* a b = ∃!-unique (∃!1/ℕ (a *⁺ b)) (1/ℕ a * 1/ℕ b) path
      where
      path : iℕ (⟨ a *⁺ b ⟩) * (1/ℕ a * 1/ℕ b) == 1#
      path = *-left (Semiringʰ.preserves-* (∃!-prop ∃!ℕ->Semiring) ⟨ a ⟩ ⟨ b ⟩) >=>
             *-swap >=>
             *-cong (∃!-prop (∃!1/ℕ a)) (∃!-prop (∃!1/ℕ b)) >=>
             *-right-one

  1/1-path : 1/ℕ 1⁺ == 1#
  1/1-path = sym *-left-one >=>
             *-left (sym ℕ->Semiring-preserves-1#) >=>
             (∃!-prop (∃!1/ℕ 1⁺))


  1/2 : D
  1/2 = 1/ℕ (2 , tt)

  0<1/2 : 0# < 1/2
  0<1/2 = 0<1/ℕ (2 , tt)

  opaque
    1/2<1 : 1/2 < 1#
    1/2<1 = trans-<-= (1/ℕ-flips-< (1 , tt) (2 , tt) refl-≤) 1/1-path

  opaque
    1/2-+-path : 1/2 + 1/2 == 1#
    1/2-+-path = sym 2*-path >=> *-left (sym i2-path) >=> ∃!-prop (∃!1/ℕ (2 , tt))
      where
      module h = Semiringʰ (∃!-prop ∃!ℕ->Semiring)
      i2-path : iℕ 2 == 2#
      i2-path = h.preserves-+ 1 1 >=> cong2 _+_ h.preserves-1# h.preserves-1#

    1/2-path : {x : D} -> (1/2 * x) + (1/2 * x) == x
    1/2-path = sym *-distrib-+-right >=> *-left 1/2-+-path >=> *-left-one

    2*1/2-path : 2# * 1/2 == 1#
    2*1/2-path = 2*-path >=> 1/2-+-path


module _ {ℓD₁ ℓD₂ ℓ<₁ ℓ<₂ : Level}
         {D₁ : Type ℓD₁} {D₁# : Rel D₁ ℓD₁} {D₁< : Rel D₁ ℓ<₁}
         {ACM₁ : AdditiveCommMonoid D₁} {AG₁ : AdditiveGroup ACM₁}
         {{S₁ : Semiring ACM₁}} {LO₁ : isLinearOrder D₁<}
         {R₁ : Ring S₁ AG₁} {A₁ : isTightApartness D₁#}
         {{_ : ℕ->Semiring-Op D₁}}
         {{LOA₁ : LinearlyOrderedAdditiveStr ACM₁ LO₁}}
         {LOS₁ : LinearlyOrderedSemiringStr S₁ LO₁}
         {{NTO₁ : NonTrivialLinearlyOrderedSemiringStr LOS₁}}
         {{F₁ : Field R₁ A₁}}
         {{AL₁ : ApartLinearOrderStr A₁ LO₁}}
         {D₂ : Type ℓD₂} {D₂# : Rel D₂ ℓD₂} {D₂< : Rel D₂ ℓ<₂}
         {ACM₂ : AdditiveCommMonoid D₂} {AG₂ : AdditiveGroup ACM₂}
         {{S₂ : Semiring ACM₂}} {LO₂ : isLinearOrder D₂<}
         {R₂ : Ring S₂ AG₂} {A₂ : isTightApartness D₂#}
         {{_ : ℕ->Semiring-Op D₂}}
         {{LOA₂ : LinearlyOrderedAdditiveStr ACM₂ LO₂}}
         {LOS₂ : LinearlyOrderedSemiringStr S₂ LO₂}
         {{NTO₂ : NonTrivialLinearlyOrderedSemiringStr LOS₂}}
         {{F₂ : Field R₂ A₂}}
         {{AL₂ : ApartLinearOrderStr A₂ LO₂}}
         where
  private
    instance
      IS₁ = S₁
      IS₂ = S₂

  Semiringʰ-preserves-1/ℕ : {f : D₁ -> D₂} ->
    Semiringʰ f -> (n : Nat⁺) -> f (1/ℕ n) == 1/ℕ n
  Semiringʰ-preserves-1/ℕ {f} h n@(n' , _) = sym (∃!-unique (∃!1/ℕ n) (f (1/ℕ n)) path2)
    where
    path1 : ℕ->Semiring == f ∘ ℕ->Semiring
    path1 = ∃!-unique ∃!ℕ->Semiring (f ∘ ℕ->Semiring) (Semiringʰ-∘ h (∃!-prop ∃!ℕ->Semiring))
    path2 : ℕ->Semiring n' * (f (1/ℕ n)) == 1#
    path2 = *-left (\i -> path1 i n') >=>
            sym (Semiringʰ.preserves-* h _ _) >=>
            cong f (∃!-prop (∃!1/ℕ n)) >=>
            (Semiringʰ.preserves-1# h)
