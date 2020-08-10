{-# OPTIONS --cubical --safe --exact-split #-}

module unordered-list.powerset where

open import base
open import commutative-monoid
open import equality
open import unordered-list.base
open import unordered-list.operations
open import nat

private
  variable
    ℓ : Level
    A : Type ℓ

powerset : UList A -> UList (UList A)
powerset as = UListElim.rec trunc []* _::*_ swap* as
  where
  []* : UList (UList A)
  []* = [ [] ]

  _::*_ : A -> UList (UList A) -> UList (UList A)
  _::*_ a as = as ++ (map (a ::_) as)

  swap* : (a1 a2 : A) (as : UList (UList A)) -> a1 ::* (a2 ::* as) == a2 ::* (a1 ::* as)
  swap* a1 a2 as =
    begin
      (as ++ (map (a2 ::_) as)) ++ (map (a1 ::_) (as ++ (map (a2 ::_) as)))
    ==< ++-assoc as _ _ >
      as ++ ((map (a2 ::_) as) ++ (map (a1 ::_) (as ++ (map (a2 ::_) as))))
    ==< cong (as ++_) path2 >
      as ++ ((map (a1 ::_) as) ++ (map (a2 ::_) (as ++ (map (a1 ::_) as))))
    ==< sym (++-assoc as _ _) >
      (as ++ (map (a1 ::_) as)) ++ (map (a2 ::_) (as ++ (map (a1 ::_) as)))
    end
    where
    path3 : (map (a1 ::_) (map (a2 ::_) as)) ==
            (map (a2 ::_) (map (a1 ::_) as))
    path3 =
      begin
        (map (a1 ::_) (map (a2 ::_) as))
      ==< double-map (a1 ::_) (a2 ::_) as >
        (map (\x -> (a1 :: (a2 :: x))) as)
      ==< (\i -> (map (\x -> (swap a1 a2 x i)) as)) >
        (map (\x -> (a2 :: (a1 :: x))) as)
      ==< sym (double-map (a2 ::_) (a1 ::_) as) >
        (map (a2 ::_) (map (a1 ::_) as))
      end

    path2 : ((map (a2 ::_) as) ++ (map (a1 ::_) (as ++ (map (a2 ::_) as)))) ==
            ((map (a1 ::_) as) ++ (map (a2 ::_) (as ++ (map (a1 ::_) as))))
    path2 =
      begin
        (map (a2 ::_) as) ++ (map (a1 ::_) (as ++ (map (a2 ::_) as)))
      ==< cong ((map (a2 ::_) as) ++_) (CommMonoidʰ.preserves-∙ (mapʰ {f = (a1 ::_)}) as _) >
        (map (a2 ::_) as) ++ ((map (a1 ::_) as) ++ (map (a1 ::_) (map (a2 ::_) as)))
      ==< sym (++-assoc (map (a2 ::_) as) (map (a1 ::_) as) _) >
        ((map (a2 ::_) as) ++ (map (a1 ::_) as)) ++ (map (a1 ::_) (map (a2 ::_) as))
      ==< cong (_++ (map (a1 ::_) (map (a2 ::_) as)))
               (++-commute (map (a2 ::_) as) (map (a1 ::_) as)) >
        ((map (a1 ::_) as) ++ (map (a2 ::_) as)) ++ (map (a1 ::_) (map (a2 ::_) as))
      ==< cong (((map (a1 ::_) as) ++ (map (a2 ::_) as)) ++_) path3 >
        ((map (a1 ::_) as) ++ (map (a2 ::_) as)) ++ (map (a2 ::_) (map (a1 ::_) as))
      ==< (++-assoc (map (a1 ::_) as) (map (a2 ::_) as) _) >
        (map (a1 ::_) as) ++ ((map (a2 ::_) as) ++ (map (a2 ::_) (map (a1 ::_) as)))
      ==< cong ((map (a1 ::_) as) ++_) (sym (CommMonoidʰ.preserves-∙ (mapʰ {f = (a2 ::_)}) as _)) >
        (map (a1 ::_) as) ++ (map (a2 ::_) (as ++ (map (a1 ::_) as)))
      end
