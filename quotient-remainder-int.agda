{-# OPTIONS --cubical --safe --exact-split #-}

module quotient-remainder-int where

open import base
open import equality
open import nat
open import int
open import abs
open import fin
open import functions
open import hlevel
open import sigma

import quotient-remainder as qr
import hit-int as h

record QuotientRemainder (d : Nat⁺) (n : Int) : Type₀ where
  private
    d' = ⟨ d ⟩

  field
    q : Int
    r : Fin d'

  ri = int ⟨ r ⟩

  field
    path : q * (int d') + ri == n

private
  flip-fin : {n : Nat} -> Fin n -> Fin n
  flip-fin (i , (j , path)) =
    j , (i , +'-right-suc >=> cong suc (+'-commute {i} {j}) >=> sym +'-right-suc >=> path)

  flip-fin-twice : {n : Nat} -> (i : Fin n) -> flip-fin (flip-fin i) == i
  flip-fin-twice _ = ΣProp-path isProp≤ refl

  flip-fin-path : {n : Nat} -> (i : Fin n) -> (int n) + (- (int ⟨ flip-fin i ⟩)) == (add1 (int ⟨ i ⟩))
  flip-fin-path {n} (i , (j , p)) =
    begin
     (int n) + (- (int j))
    ==< +-left (cong int (sym p >=> +'-commute {j} {suc i})) >
     (int (suc i +' j)) + (- (int j))
    ==< +-left int-inject-+' >
     (int (suc i) + (int j)) + (- (int j))
    ==< +-assoc >
     int (suc i) + ((int j) + (- (int j)))
    ==< +-right add-minus-zero >=> +-right-zero >
     (add1 (int i))
    end

  flip-fin-path' : {n : Nat} -> (i : Fin n) -> int ⟨ flip-fin i ⟩ == (int n) + (- (add1 (int ⟨ i ⟩)))
  flip-fin-path' {n} (i , (j , p)) =
    begin
      (int j)
    ==< sym +-right-zero >=> +-right (sym add-minus-zero) >
      (int j) + ((int (suc i)) + (- (add1 (int i))))
    ==< sym +-assoc >
      ((int j) + (int (suc i))) + (- (add1 (int i)))
    ==< +-left (sym int-inject-+') >
      (int (j +' suc i)) + (- (add1 (int i)))
    ==< +-left (cong int p) >
      (int n) + (- (add1 (int i)))
    end

  fin-small : {n : Nat} -> (i : Fin n) -> Neg ((int ⟨ i ⟩) + (- (int n)))
  fin-small {zero} i = bot-elim (¬fin-zero i)
  fin-small {suc n} (zero , lt) = subst Neg (sym +-left-zero) tt
  fin-small {suc n} (suc i , lt) =
    subst Neg (sym p) rec
    where
    p : (int (suc i)) + (- (int (suc n))) == (int i) + (- (int n))
    p = add1-extract-left >=> sym add1-extract-right >=> +-right add1-minus->minus-sub1
    rec : Neg ((int i) + (- (int n)))
    rec = fin-small {n} (i , pred-≤ lt)


remainder : (n : Int) (d : Nat⁺) -> Fin ⟨ d ⟩
remainder (nonneg n) d = qr.remainder n d
remainder (neg n)    d = flip-fin (qr.remainder n d)

quotient : (n : Int) (d : Nat⁺) -> Int
quotient (nonneg n) d = int (qr.quotient n d)
quotient (neg n)    d = - (int (suc (qr.quotient n d)))




private
  qr-path : (d : Nat⁺) (n : Int) ->
            (quotient n d) * (int ⟨ d ⟩) + (int ⟨ (remainder n d) ⟩) == n
  qr-path d (nonneg n) = ans
    where
    path : (int ((qr.quotient n d) *' ⟨ d ⟩ +' ⟨ qr.remainder n d ⟩)) ==
           (int (qr.quotient n d) * (int ⟨ d ⟩)) + (int ⟨ (qr.remainder n d) ⟩)
    path = int-inject-+' >=> +-left int-inject-*'

    ans : (quotient (nonneg n) d) * (int ⟨ d ⟩) + (int ⟨ (remainder (nonneg n) d) ⟩) == (nonneg n)
    ans = sym path >=> cong nonneg (qr.QuotientRemainder.path (qr.quotient-remainder d n))
  qr-path d (neg n) = ans
    where
    path : (neg ((qr.quotient n d) *' ⟨ d ⟩ +' ⟨ qr.remainder n d ⟩)) ==
           ((- (int (suc (qr.quotient n d)))) * (int ⟨ d ⟩)
            + (int ⟨ (flip-fin (qr.remainder n d)) ⟩))
    path =
      begin
        (neg ((qr.quotient n d) *' ⟨ d ⟩ +' ⟨ qr.remainder n d ⟩))
      ==<>
        (- (add1 (int (((qr.quotient n d) *' ⟨ d ⟩) +' ⟨ (qr.remainder n d)⟩))))
      ==< cong -_ (cong add1 int-inject-+') >
        (- (add1 ((int ((qr.quotient n d) *' ⟨ d ⟩)) + (int ⟨ (qr.remainder n d)⟩))))
      ==< cong -_ (sym add1-extract-right) >
        (- ((int ((qr.quotient n d) *' ⟨ d ⟩)) + (add1 (int ⟨ (qr.remainder n d)⟩))))
      ==< minus-distrib-+ >
        (- (int ((qr.quotient n d) *' ⟨ d ⟩))) + (- (add1 (int ⟨ (qr.remainder n d)⟩ )))
      ==<>
        (- (int ((qr.quotient n d) *' ⟨ d ⟩))) + (neg ⟨ (qr.remainder n d)⟩ )
      ==< +-left (cong -_ int-inject-*') >
        (- ((int (qr.quotient n d)) * (int ⟨ d ⟩))) + (neg ⟨ (qr.remainder n d)⟩ )
      ==< +-left (sym (+-left add-minus-zero >=> +-left-zero)) >
        ((((int ⟨ d ⟩) + (- (int ⟨ d ⟩))) + (- ((int (qr.quotient n d)) * (int ⟨ d ⟩))))
          + (neg ⟨ (qr.remainder n d)⟩ ))
      ==< +-left +-assoc >
        (((int ⟨ d ⟩) + ((- (int ⟨ d ⟩)) + (- ((int (qr.quotient n d)) * (int ⟨ d ⟩)))))
          + (neg ⟨ (qr.remainder n d)⟩ ))
      ==< +-left (+-right (sym minus-distrib-+)) >
        (((int ⟨ d ⟩) + (- ((int ⟨ d ⟩) + ((int (qr.quotient n d)) * (int ⟨ d ⟩)))))
          + (neg ⟨ (qr.remainder n d)⟩ ))
      ==< +-left +-commute >
        ((- ((int ⟨ d ⟩) + ((int (qr.quotient n d)) * (int ⟨ d ⟩)))
          + (int ⟨ d ⟩)) + (neg ⟨ (qr.remainder n d)⟩ ))
      ==< +-assoc >
        (- ((int ⟨ d ⟩) + ((int (qr.quotient n d)) * (int ⟨ d ⟩)))
         + ((int ⟨ d ⟩) + (neg ⟨ (qr.remainder n d)⟩ )))
      ==< +-left (cong -_ (sym add1-extract-*)) >
        (- ((int (suc (qr.quotient n d))) * (int ⟨ d ⟩))
         + ((int ⟨ d ⟩) + (neg ⟨ (qr.remainder n d)⟩ )))
      ==< +-left (sym minus-extract-left) >
        ((- (int (suc (qr.quotient n d)))) * (int ⟨ d ⟩)
         + ((int ⟨ d ⟩) + (neg ⟨ (qr.remainder n d)⟩ )))
      ==<>
        ((neg (qr.quotient n d)) * (int ⟨ d ⟩)
         + ((int ⟨ d ⟩) + (- (add1 (int ⟨ (qr.remainder n d)⟩ )))))
      ==< +-right (sym (flip-fin-path' (qr.remainder n d))) >
        ((neg (qr.quotient n d)) * (int ⟨ d ⟩)
         + (int ⟨ (flip-fin (qr.remainder n d))⟩))
      ==<>
        ((- (int (suc (qr.quotient n d)))) * (int ⟨ d ⟩)
         + (int ⟨ (flip-fin (qr.remainder n d))⟩))
      end


    ans : (quotient (neg n) d) * (int ⟨ d ⟩) + (int ⟨ (remainder (neg n) d) ⟩) == (neg n)
    ans = sym path >=>
          cong neg (qr.QuotientRemainder.path (qr.quotient-remainder d n))

quotient-remainder : (d : Nat⁺) (n : Int) -> QuotientRemainder d n
quotient-remainder d n = record
  { q = quotient n d
  ; r = remainder n d
  ; path = (qr-path d n)
  }




private
  quotient-unique : (d : Nat⁺) (n : Int) -> (qr2 : QuotientRemainder d n) ->
                     (QuotientRemainder.q qr2) == (quotient n d)
  quotient-unique d (nonneg n) qr2 = f qr2.path
    where
    module qr1 = qr.QuotientRemainder (qr.quotient-remainder d n)
    module qr2 = QuotientRemainder qr2
    d' = ⟨ d ⟩

    f : {q : Int} -> q * (int d') + (int ⟨ qr2.r ⟩) == (int n) -> q == (quotient (nonneg n) d)
    f {nonneg q'} p =
      cong (nonneg ∘ qr.QuotientRemainder.q) (sym (qr.isContr-QuotientRemainder .snd qr3))
      where
      p2 : n == (q' *' d' +' ⟨ qr2.r ⟩)
      p2 = nonneg-injective ((sym p) >=> +-left (sym int-inject-*') >=> sym int-inject-+')
      qr3 : qr.QuotientRemainder d n
      qr3 = record { q = q' ; r = qr2.r ; path = sym p2 }
    f {neg q'} p = bot-elim (subst Neg (sym p2) neg1)
      where
      p2 : (nonneg n) == ((int ⟨ qr2.r ⟩) + (- (int d'))) + (- ((int q') * (int d')))
      p2 = (sym p) >=>
           +-left (minus-extract-left >=> cong -_ add1-extract-* >=> minus-distrib-+) >=>
           +-commute >=> sym +-assoc

      neg1 : Neg (((int ⟨ qr2.r ⟩) + (- (int d'))) + (- ((int q') * (int d'))))
      neg1 = +-Neg-NonPos (fin-small qr2.r) (minus-NonNeg (*-NonNeg-NonNeg tt tt))
  quotient-unique d (neg n) qr2 = f qr2.path
    where
    module qr2 = QuotientRemainder qr2
    d' = ⟨ d ⟩

    f : {q : Int} -> q * (int d') + (int ⟨ qr2.r ⟩) == (neg n) -> q == (quotient (neg n) d)
    f {nonneg q'} p = bot-elim (subst NonNeg p nonneg1)
      where
      nonneg1 : NonNeg ((int q') * (int d') + (int ⟨ qr2.r ⟩))
      nonneg1 = +-NonNeg-NonNeg (*-NonNeg-NonNeg _ _) _
    f {neg q'} p =
      cong (neg ∘ qr.QuotientRemainder.q) (sym (qr.isContr-QuotientRemainder .snd qr3))
      where
      check : (quotient (neg n) d) == (neg (qr.quotient n d))
      check = refl

      p2 : (neg n) == neg (q' *' d' +' ⟨ flip-fin qr2.r ⟩)
      p2 =
        begin
          (neg n)
        ==< sym p >
          (neg q' * (int d') + (int ⟨ qr2.r ⟩))
        ==<>
          (- (add1 (int q')) * (int d') + (int ⟨ qr2.r ⟩))
        ==< +-left (minus-extract-left >=> cong -_ add1-extract-*) >
          (- ((int d') + ((int q') * (int d'))) + (int ⟨ qr2.r ⟩))
        ==< +-right (sym minus-double-inverse) >
          (- ((int d') + ((int q') * (int d'))) + (- (- (int ⟨ qr2.r ⟩))))
        ==< sym minus-distrib-+ >
          (- (((int d') + ((int q') * (int d'))) + (- (int ⟨ qr2.r ⟩))))
        ==< cong -_ (+-left +-commute >=> +-assoc) >
          (- (((int q') * (int d')) + ((int d') + (- (int ⟨ qr2.r ⟩)))))
        ==< cong -_ (+-left (sym int-inject-*')) >
          (- (int (q' *' d') + ((int d') + (- (int ⟨ qr2.r ⟩)))))
        ==<>
          (- (int (q' *' d') + ((int d') + (- (sub1 (add1 (int ⟨ qr2.r ⟩)))))))
        ==< cong -_ (+-right (+-right (sym add1-minus->minus-sub1))) >
          (- (int (q' *' d') + ((int d') + (add1 (- (add1 (int ⟨ qr2.r ⟩)))))))
        ==< cong -_ (+-right add1-extract-right) >
          (- (int (q' *' d') + add1 ((int d') + (- (add1 (int ⟨ qr2.r ⟩))))))
        ==< cong (\x -> (- (int (q' *' d') + add1 x))) (sym (flip-fin-path' qr2.r)) >
          (- (int (q' *' d') + add1 (int ⟨ flip-fin qr2.r ⟩)))
        ==< cong -_ add1-extract-right >
          (- (add1 (int (q' *' d') + int (⟨ flip-fin qr2.r ⟩))))
        ==< cong -_ (cong add1 (sym int-inject-+')) >
          (- (add1 (int (q' *' d' +' ⟨ flip-fin qr2.r ⟩))))
        ==<>
          neg (q' *' d' +' ⟨ flip-fin qr2.r ⟩)
        end


      qr3 : qr.QuotientRemainder d n
      qr3 = record { q = q' ; r = flip-fin qr2.r ; path = (sym (neg-injective p2)) }


  remainder-unique : (d : Nat⁺) (n : Int) -> (qr2 : QuotientRemainder d n) ->
                     (QuotientRemainder.r qr2) == (remainder n d)
  remainder-unique d n qr2 =
    ΣProp-path isProp≤ (nonneg-injective (+-left-injective (qr1.q * d') p2))
    where
    module qr1 = QuotientRemainder (quotient-remainder d n)
    module qr2 = QuotientRemainder qr2
    d' = int ⟨ d ⟩

    p1 : (qr2.q * d' + (int ⟨ qr2.r ⟩)) == (qr1.q * d' + (int ⟨ qr1.r ⟩))
    p1 = qr2.path >=> sym qr1.path

    p2 : (qr1.q * d' + (int ⟨ qr2.r ⟩)) == (qr1.q * d' + (int ⟨ qr1.r ⟩))
    p2 = (\ i -> (quotient-unique d n qr2 (~ i)) * d' + (int ⟨ qr2.r ⟩)) >=> p1



isContr-QuotientRemainder : {d : Nat⁺} {n : Int} -> isContr (QuotientRemainder d n)
isContr-QuotientRemainder {d} {n} .fst = quotient-remainder d n
isContr-QuotientRemainder {d} {n} .snd qr2 = (\i -> record
  { q = quotient-unique d n qr2 (~ i)
  ; r = remainder-unique d n qr2 (~ i)
  ; path = p-path i
  })
  where
  module qr1 = QuotientRemainder (quotient-remainder d n)
  module qr2 = QuotientRemainder qr2

  p-path : PathP (\i -> (quotient-unique d n qr2 (~ i)) * (int ⟨ d ⟩) +
                        (int ⟨ remainder-unique d n qr2 (~ i) ⟩) == n)
                 qr1.path qr2.path
  p-path = isProp->PathP (\i -> isSetInt _ _) _ _


isProp-QuotientRemainder : {d : Nat⁺} {n : Int} -> isProp (QuotientRemainder d n)
isProp-QuotientRemainder = isContr->isProp isContr-QuotientRemainder
