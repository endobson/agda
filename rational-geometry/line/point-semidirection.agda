{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.line.point-semidirection where

open import base
open import additive-group
open import set-quotient
open import hlevel.base
open import hlevel.sigma
open import rational-geometry.line
open import rational
open import relation
open import sigma.base
open import semiring
open import truncation
open import equality-path
open import rational-geometry.line-segment
open import rational-geometry.point
open import rational-geometry.direction
open import rational-geometry.translation

private
  isEquivRel-SameSemiDirection : isEquivRel SameSemiDirection
  isEquivRel-SameSemiDirection = record
    { reflexive = inj-l refl
    ; symmetric = sym-SameSemiDirection
    ; transitive = trans-SameSemiDirection
    }
    where
    trans-SameSemiDirection : Transitive SameSemiDirection
    trans-SameSemiDirection (inj-l ab) (inj-l bc) = inj-l (ab >=> bc)
    trans-SameSemiDirection (inj-l ab) (inj-r bc) = inj-r (ab >=> bc)
    trans-SameSemiDirection (inj-r ab) (inj-l bc) = inj-r (ab >=> cong reverse-direction bc)
    trans-SameSemiDirection (inj-r ab) (inj-r bc) =
      inj-l (ab >=> cong reverse-direction bc >=> reverse-direction-twice)



  point-semi-direction->Σline :
    (p : Point) -> (sd : SemiDirection) ->
      isContr (Σ[ l ∈ Line ] (OnLine p l × line->semi-direction l == sd))
  point-semi-direction->Σline p = SetQuotientElim.liftContr dir->Σline
    where
    dir->Σline : (d : Direction) ->
      isContr (Σ[ l ∈ Line ] (OnLine p l × line->semi-direction l == [ d ]))
    dir->Σline d = center , all-same
      where
      line : Line
      line = [ line' p d ]

      opaque
        P-line : (OnLine p line × line->semi-direction line == [ d ])
        P-line = (0# , point-path) , refl
          where
          point-path : shift-point (scale-direction 0# d) p == p
          point-path = cong2 _,_ (+-right *-left-zero >=> +-right-zero)
                                 (+-right *-left-zero >=> +-right-zero)

      center : Σ[ l ∈ Line ] (OnLine p l × line->semi-direction l == [ d ])
      center = line , P-line


      module _ (line₂ : Line' ) (p∈l₂ : OnLine p [ line₂ ]) where
        private
          p₂ : Point
          p₂ = Line'.p line₂
          d₂ : Direction
          d₂ = Line'.dir line₂
          k : ℚ
          k = fst p∈l₂

        all-same'2 :
         (sd₂-eq : SameSemiDirection (Line'.dir line₂) d) ->
         center == ([ line₂ ] , p∈l₂ , eq/ _ _ sd₂-eq)
        all-same'2 (inj-l d-path) =
          ΣProp-path (\{l} -> (isProp× (isProp-OnLine p l) (isSet-SemiDirection _ _)))
            (sym (eq/ _ _ (p₂∈l , p∈l₂ , (inj-l d-path))))
          where
          path : shift-point (scale-direction (- k) d) p == p₂
          path =
            (\i -> shift-point (scale-direction (- k) (d-path (~ i))) (snd p∈l₂ (~ i))) >=>
            sym shift-point-+ >=>
            cong (\t -> shift-point t p₂) inner >=>
            shift-point-zero
            where
            inner : (scale-direction (- k) d₂) + (scale-direction k d₂) == 0#
            inner = cong2 _,_ (sym *-distrib-+-right >=> *-left (+-commute >=> +-inverse) >=> *-left-zero)
                              (sym *-distrib-+-right >=> *-left (+-commute >=> +-inverse) >=> *-left-zero)

          p₂∈l : OnLine (Line'.p line₂) line
          p₂∈l = - (fst p∈l₂) , path

        all-same'2 (inj-r d-path) =
          ΣProp-path (\{l} -> (isProp× (isProp-OnLine p l) (isSet-SemiDirection _ _)))
            (sym (eq/ _ _ (p₂∈l , p∈l₂ , (inj-r d-path))))
          where
          path : shift-point (scale-direction k d) p == p₂
          path =
            cong (\t -> shift-point t p)
                 (cong (scale-direction k) (sym (reverse-direction-twice {d})) >=>
                  sym (scale-direction-minus {k} {reverse-direction d}) >=>
                  cong (scale-direction (- k)) (sym d-path)) >=>
            cong (shift-point (scale-direction (- k) d₂)) (sym (snd p∈l₂)) >=>
            sym shift-point-+ >=>
            cong (\t -> shift-point t p₂) inner >=>
            shift-point-zero
            where

            inner : (scale-direction (- k) d₂) + (scale-direction k d₂) == 0#
            inner = cong2 _,_ (sym *-distrib-+-right >=> *-left (+-commute >=> +-inverse) >=> *-left-zero)
                               (sym *-distrib-+-right >=> *-left (+-commute >=> +-inverse) >=> *-left-zero)



          p₂∈l : OnLine (Line'.p line₂) line
          p₂∈l = k , path


        all-same' :
         (sd₂-path : line->semi-direction [ line₂ ] == [ d ]) ->
         center == ([ line₂ ] , p∈l₂ , sd₂-path)
        all-same' p =
          all-same'2 eq >=> (\i -> [ line₂ ] , p∈l₂ , isSet-SemiDirection _ _ (eq/ _ _ eq) p i)
          where
          eq : SameSemiDirection (Line'.dir line₂) d
          eq =
            SetQuotientElim.pathRec
              (\_ _ -> isProp-SameSemiDirection)
              isEquivRel-SameSemiDirection
              _ _ p

      opaque
        all-same : ∀ (other : (Σ[ l ∈ Line ] (OnLine p l × line->semi-direction l == [ d ]))) ->
                   center == other
        all-same (l , o , sd) =
          SetQuotientElim.elimProp
            (\l -> isPropΠ2 \ (o : OnLine p l) (sd : line->semi-direction l == [ d ]) ->
                (isSetΣ isSet-Line (\l -> isSet× (isProp->isSet (isProp-OnLine p l))
                                                 (isProp->isSet (isSet-SemiDirection _ _))))
                center (l , o , sd))
            all-same'
            l o sd


point-semi-direction->line : (p : Point) -> (sd : SemiDirection) -> Line
point-semi-direction->line p sd = ∃!-val (point-semi-direction->Σline p sd)
