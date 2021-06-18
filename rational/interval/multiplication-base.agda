{-# OPTIONS --cubical --safe --exact-split #-}

module rational.interval.multiplication-base where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import rational.minmax
open import rational.interval
open import relation
open import sign
open import sign.instances.rational

data Imul (a b : Iℚ) : Iℚ -> Type₀ where
  imul-nn-nn : NonNegI a -> NonNegI b       -> Imul a b (a                i∙ b)
  imul-nn-np : NonNegI a -> NonPosI b       -> Imul a b ((i-conj a)       i∙ b)
  imul-nn-fz : NonNegI a -> ForwardZeroI b  -> Imul a b ((ℚ->Iℚ (Iℚ-u a)) i∙ b)
  imul-nn-bz : NonNegI a -> BackwardZeroI b -> Imul a b ((ℚ->Iℚ (Iℚ-l a)) i∙ b)

  imul-np-nn : NonPosI a -> NonNegI b       -> Imul a b (a                i∙ (i-conj b))
  imul-np-np : NonPosI a -> NonPosI b       -> Imul a b ((i-conj a)       i∙ (i-conj b))
  imul-np-fz : NonPosI a -> ForwardZeroI b  -> Imul a b ((ℚ->Iℚ (Iℚ-l a)) i∙ (i-conj b))
  imul-np-bz : NonPosI a -> BackwardZeroI b -> Imul a b ((ℚ->Iℚ (Iℚ-u a)) i∙ (i-conj b))

  imul-fz-nn : ForwardZeroI a -> NonNegI b        -> Imul a b (a          i∙ (ℚ->Iℚ (Iℚ-u b)))
  imul-fz-np : ForwardZeroI a -> NonPosI b        -> Imul a b ((i-conj a) i∙ (ℚ->Iℚ (Iℚ-l b)))
  imul-fz-fz : ForwardZeroI a -> ForwardZeroI b   -> Imul a b (i-cross a b)
  imul-fz-bz : ForwardZeroI a -> BackwardZeroI b  -> Imul a b 0i

  imul-bz-nn : BackwardZeroI a -> NonNegI b       -> Imul a b (a          i∙ (ℚ->Iℚ (Iℚ-l b)))
  imul-bz-np : BackwardZeroI a -> NonPosI b       -> Imul a b ((i-conj a) i∙ (ℚ->Iℚ (Iℚ-u b)))
  imul-bz-fz : BackwardZeroI a -> ForwardZeroI b  -> Imul a b 0i
  imul-bz-bz : BackwardZeroI a -> BackwardZeroI b -> Imul a b (i-conj (i-cross a b))

private
  right-zero-path : {x y z : ℚ} -> z == 0r -> x r* z == y r* z
  right-zero-path {x} {y} {z} p =
    cong (x r*_) p >=> (r*-right-zero x) >=>
    sym (r*-right-zero y) >=> (cong (y r*_) (sym p))

  left-zero-path : {x y z : ℚ} -> z == 0r -> z r* x == z r* y
  left-zero-path {x} {y} {z} p =
    cong (_r* x) p >=> (r*-left-zero x) >=>
    sym (r*-left-zero y) >=> (cong (_r* y) (sym p))

  rl-zero-path : {x y z w : ℚ} -> z == 0r -> w == 0r -> x r* z == w r* y
  rl-zero-path {x} {y} p q =
    cong (x r*_) p >=> (r*-right-zero x) >=>
    sym (r*-left-zero y) >=> (cong (_r* y) (sym q))

  i∙-right-zero' : {a b : Iℚ} -> b == 0i -> a i∙ b == 0i
  i∙-right-zero' {a = a} p = cong (a i∙_) p >=> i∙-right-zero a

  i∙-left-zero' : {a b : Iℚ} -> a == 0i -> a i∙ b == 0i
  i∙-left-zero' {b = b} p = cong (_i∙ b) p >=> i∙-left-zero b

  r*-right-zero' : {a b : ℚ} -> b == 0r -> a r* b == 0r
  r*-right-zero' {a = a} p = cong (a r*_) p >=> r*-right-zero a

  r*-left-zero' : {a b : ℚ} -> a == 0r -> a r* b == 0r
  r*-left-zero' {b = b} p = cong (_r* b) p >=> r*-left-zero b

module _ where
  private
    nn-fz = NonNeg-ForwardZero-path
    nn-bz = NonNeg-BackwardZero-path
    nn-np1 = NonNeg-NonPos-path₁
    nn-np2 = NonNeg-NonPos-path₂
    nn-np = NonNeg-NonPos-path

    np-fz = NonPos-ForwardZero-path
    np-bz = NonPos-BackwardZero-path

    fz-bz1 = ForwardZero-BackwardZero-path₁
    fz-bz2 = ForwardZero-BackwardZero-path₂
    fz-bz = ForwardZero-BackwardZero-path

    _>=<_ : {ℓ : Level} -> {A : Type ℓ} {a b c : A} -> a == b -> c == b -> a == c
    p >=< q = p >=> (sym q)

    Imul-za-path : {b c : Iℚ} -> Imul 0i b c -> c == 0i
    Imul-za-path (imul-nn-nn _ _) = (i∙-left-zero _)
    Imul-za-path (imul-nn-np _ _) = (i∙-left-zero _)
    Imul-za-path (imul-nn-fz _ _) = (i∙-left-zero _)
    Imul-za-path (imul-nn-bz _ _) = (i∙-left-zero _)
    Imul-za-path (imul-np-nn _ _) = (i∙-left-zero _)
    Imul-za-path (imul-np-np _ _) = (i∙-left-zero _)
    Imul-za-path (imul-np-fz _ _) = (i∙-left-zero _)
    Imul-za-path (imul-np-bz _ _) = (i∙-left-zero _)
    Imul-za-path (imul-fz-nn _ _) = (i∙-left-zero _)
    Imul-za-path (imul-fz-np _ _) = (i∙-left-zero _)
    Imul-za-path (imul-fz-fz _ _) =
      cong2 _,_ (cong2 minℚ (r*-left-zero _) (r*-right-zero _) >=> minℚ-same)
                (cong2 maxℚ (r*-left-zero _) (r*-left-zero _) >=> maxℚ-same)
    Imul-za-path (imul-fz-bz _ _) = refl
    Imul-za-path (imul-bz-nn _ _) = (i∙-left-zero _)
    Imul-za-path (imul-bz-np _ _) = (i∙-left-zero _)
    Imul-za-path (imul-bz-fz _ _) = refl
    Imul-za-path (imul-bz-bz _ _) =
      cong2 _,_ (cong2 maxℚ (r*-left-zero _) (r*-left-zero _) >=> maxℚ-same)
                (cong2 minℚ (r*-left-zero _) (r*-right-zero _) >=> minℚ-same)

    Imul-zb-path : {a c : Iℚ} -> Imul a 0i c -> c == 0i
    Imul-zb-path (imul-nn-nn _ _) = (i∙-right-zero _)
    Imul-zb-path (imul-nn-np _ _) = (i∙-right-zero _)
    Imul-zb-path (imul-nn-fz _ _) = (i∙-right-zero _)
    Imul-zb-path (imul-nn-bz _ _) = (i∙-right-zero _)
    Imul-zb-path (imul-np-nn _ _) = (i∙-right-zero _)
    Imul-zb-path (imul-np-np _ _) = (i∙-right-zero _)
    Imul-zb-path (imul-np-fz _ _) = (i∙-right-zero _)
    Imul-zb-path (imul-np-bz _ _) = (i∙-right-zero _)
    Imul-zb-path (imul-fz-nn _ _) = (i∙-right-zero _)
    Imul-zb-path (imul-fz-np _ _) = (i∙-right-zero _)
    Imul-zb-path (imul-fz-fz _ _) =
      cong2 _,_ (cong2 minℚ (r*-right-zero _) (r*-left-zero _) >=> minℚ-same)
                (cong2 maxℚ (r*-right-zero _) (r*-right-zero _) >=> maxℚ-same)
    Imul-zb-path (imul-fz-bz _ _) = refl
    Imul-zb-path (imul-bz-nn _ _) = (i∙-right-zero _)
    Imul-zb-path (imul-bz-np _ _) = (i∙-right-zero _)
    Imul-zb-path (imul-bz-fz _ _) = refl
    Imul-zb-path (imul-bz-bz _ _) =
      cong2 _,_ (cong2 maxℚ (r*-right-zero _) (r*-right-zero _) >=> maxℚ-same)
                (cong2 minℚ (r*-right-zero _) (r*-left-zero _) >=> minℚ-same)

    za-case : {a b c d : Iℚ} -> a == 0i -> Imul a b c -> Imul a b d -> c == d
    za-case {a} {b} {c} {d} p i1 i2 =
      (Imul-za-path (subst (\x -> Imul x b c) p i1)) >=<
      (Imul-za-path (subst (\x -> Imul x b d) p i2))

    zb-case : {a b c d : Iℚ} -> b == 0i -> Imul a b c -> Imul a b d -> c == d
    zb-case {a} {b} {c} {d} p i1 i2 =
      (Imul-zb-path (subst (\x -> Imul a x c) p i1)) >=<
      (Imul-zb-path (subst (\x -> Imul a x d) p i2))

    module _ {a b c : Iℚ} (fz-a : ForwardZeroI a) (fz-b : ForwardZeroI b) where
      private
        al = fst a
        au = snd a
        bl = fst b
        bu = snd b
        np-al = fst fz-a
        nn-au = snd fz-a
        np-bl = fst fz-b
        nn-bu = snd fz-b

        np-al-bu = r*-NonPos-NonNeg np-al nn-bu
        np-bl-au = r*-NonPos-NonNeg np-bl nn-au
        nn-al-bl = r*-NonPos-NonPos np-al np-bl
        nn-au-bu = r*-NonNeg-NonNeg nn-au nn-bu

        min-side = minℚ (al r* bu) (bl r* au)
        max-side = maxℚ (al r* bl) (au r* bu)

        min-al : (al == 0r) -> min-side == (bl r* au)
        min-al z = minℚ-right _ _ (NonPos≤NonNeg np-bl-au
                                    (inj-r (subst Zero (sym (r*-left-zero' z)) Zero-0r)))

        min-bu : (bu == 0r) -> min-side == (bl r* au)
        min-bu z = minℚ-right _ _ (NonPos≤NonNeg np-bl-au
                                    (inj-r (subst Zero (sym (r*-right-zero' z)) Zero-0r)))

        min-bl : (bl == 0r) -> min-side == (al r* bu)
        min-bl z = minℚ-left _ _ (NonPos≤NonNeg np-al-bu
                                   (inj-r (subst Zero (sym (r*-left-zero' z)) Zero-0r)))

        min-au : (au == 0r) -> min-side == (al r* bu)
        min-au z = minℚ-left _ _ (NonPos≤NonNeg np-al-bu
                                   (inj-r (subst Zero (sym (r*-right-zero' z)) Zero-0r)))

        max-al : (al == 0r) -> max-side == (au r* bu)
        max-al z = maxℚ-right _ _ (NonPos≤NonNeg
                                    (inj-r (subst Zero (sym (r*-left-zero' z)) Zero-0r))
                                    nn-au-bu)
        max-bl : (bl == 0r) -> max-side == (au r* bu)
        max-bl z = maxℚ-right _ _ (NonPos≤NonNeg
                                    (inj-r (subst Zero (sym (r*-right-zero' z)) Zero-0r))
                                    nn-au-bu)
        max-au : (au == 0r) -> max-side == (al r* bl)
        max-au z = maxℚ-left _ _ (NonPos≤NonNeg
                                   (inj-r (subst Zero (sym (r*-left-zero' z)) Zero-0r))
                                   nn-al-bl)
        max-bu : (bu == 0r) -> max-side == (al r* bl)
        max-bu z = maxℚ-left _ _ (NonPos≤NonNeg
                                   (inj-r (subst Zero (sym (r*-right-zero' z)) Zero-0r))
                                   nn-al-bl)

        min-l : (al == 0r) -> (bl == 0r) -> min-side == 0r
        min-l za zb = (cong2 minℚ (r*-left-zero' za) (r*-left-zero' zb) >=> minℚ-same)

        min-u : (au == 0r) -> (bu == 0r) -> min-side == 0r
        min-u za zb = (cong2 minℚ (r*-right-zero' zb) (r*-right-zero' za) >=> minℚ-same)

        min-a : (a == 0i) -> min-side == 0r
        min-a z = (cong2 minℚ (r*-left-zero' (cong Iℚ-l z)) (r*-right-zero' (cong Iℚ-u z)) >=> minℚ-same)

        min-b : (b == 0i) -> min-side == 0r
        min-b z = (cong2 minℚ (r*-right-zero' (cong Iℚ-u z)) (r*-left-zero' (cong Iℚ-l z)) >=> minℚ-same)

        max-fs : (al == 0r) -> (bu == 0r) -> max-side == 0r
        max-fs za zb = (cong2 maxℚ (r*-left-zero' za) (r*-right-zero' zb) >=> maxℚ-same)

        max-bs : (au == 0r) -> (bl == 0r) -> max-side == 0r
        max-bs za zb = (cong2 maxℚ (r*-right-zero' zb) (r*-left-zero' za) >=> maxℚ-same)

        max-a : (a == 0i) -> max-side == 0r
        max-a z = (cong2 maxℚ (r*-left-zero' (cong Iℚ-l z)) (r*-left-zero' (cong Iℚ-u z)) >=> maxℚ-same)

        max-b : (b == 0i) -> max-side == 0r
        max-b z = (cong2 maxℚ (r*-right-zero' (cong Iℚ-l z)) (r*-right-zero' (cong Iℚ-u z)) >=> maxℚ-same)



      Imul-FZ-FZ-path : Imul a b c -> c == i-cross a b
      Imul-FZ-FZ-path (imul-nn-nn nn-a nn-b) =
        cong2 _,_ (r*-left-zero' pa >=< min-l pa pb) (refl >=< max-bl pb)
        where
        pa = nn-fz nn-a fz-a
        pb = nn-fz nn-b fz-b
      Imul-FZ-FZ-path (imul-nn-np nn-a np-b) =
        cong2 _,_ (r*-commute au bl >=< min-al pa) (r*-left-zero' pa >=< max-fs pa pb)
        where
        pa = nn-fz nn-a fz-a
        pb = np-fz np-b fz-b
      Imul-FZ-FZ-path (imul-nn-fz nn-a fz-b) =
        cong2 _,_ (r*-commute au bl >=< min-al pa) (refl >=< max-al pa)
        where
        pa = nn-fz nn-a fz-a
      Imul-FZ-FZ-path (imul-nn-bz nn-a bz-b) =
        cong2 _,_ (r*-right-zero' (cong Iℚ-l pb) >=< min-b pb)
                  (r*-right-zero' (cong Iℚ-u pb) >=< max-b pb)
        where
        pb = fz-bz fz-b bz-b

      Imul-FZ-FZ-path (imul-np-nn np-a nn-b) =
        cong2 _,_ (refl >=< min-bl pb) (r*-left-zero' pa >=< max-bs pa pb)
        where
        pa = np-fz np-a fz-a
        pb = nn-fz nn-b fz-b
      Imul-FZ-FZ-path (imul-np-np np-a np-b) =
        cong2 _,_ (r*-left-zero' pa >=< min-u pa pb) (refl >=< max-bu pb)
        where
        pa = np-fz np-a fz-a
        pb = np-fz np-b fz-b
      Imul-FZ-FZ-path (imul-np-fz np-a fz-b) =
        cong2 _,_ (refl >=< min-au pa) (refl >=< max-au pa)
        where
        pa = np-fz np-a fz-a
      Imul-FZ-FZ-path (imul-np-bz np-a bz-b) =
        cong2 _,_ (r*-right-zero' (cong Iℚ-u pb) >=< min-b pb)
                  (r*-right-zero' (cong Iℚ-l pb) >=< max-b pb)
        where
        pb = fz-bz fz-b bz-b


      Imul-FZ-FZ-path (imul-fz-nn fz-a nn-b) =
        cong2 _,_ (refl >=< min-bl pb) (refl >=< max-bl pb)
        where
        pb = nn-fz nn-b fz-b
      Imul-FZ-FZ-path (imul-fz-np fz-a np-b) =
        cong2 _,_ (r*-commute au bl >=< min-bu pb) (refl >=< max-bu pb)
        where
        pb = np-fz np-b fz-b
      Imul-FZ-FZ-path (imul-fz-fz _ _) = refl
      Imul-FZ-FZ-path (imul-fz-bz fz-a bz-b) =
        cong2 _,_ (refl >=< min-b pb)
                  (refl >=< max-b pb)
        where
        pb = fz-bz fz-b bz-b

      Imul-FZ-FZ-path (imul-bz-nn bz-a nn-b) =
        cong2 _,_ (r*-left-zero' (cong Iℚ-l pa) >=< min-a pa)
                  (r*-left-zero' (cong Iℚ-u pa) >=< max-a pa)
        where
        pa = fz-bz fz-a bz-a
      Imul-FZ-FZ-path (imul-bz-np bz-a np-b) =
        cong2 _,_ (r*-left-zero' (cong Iℚ-u pa) >=< min-a pa)
                  (r*-left-zero' (cong Iℚ-l pa) >=< max-a pa)
        where
        pa = fz-bz fz-a bz-a
      Imul-FZ-FZ-path (imul-bz-fz bz-a fz-b) =
        cong2 _,_ (refl >=< min-a pa)
                  (refl >=< max-a pa)
        where
        pa = fz-bz fz-a bz-a
      Imul-FZ-FZ-path (imul-bz-bz bz-a bz-b) =
        cong2 _,_ (max-a pa >=< min-a pa)
                  (min-a pa >=< max-a pa)
        where
        pa = fz-bz fz-a bz-a

    module _ {a b c : Iℚ} (bz-a : BackwardZeroI a) (bz-b : BackwardZeroI b) where
      private
        al = fst a
        au = snd a
        bl = fst b
        bu = snd b
        nn-al = fst bz-a
        np-au = snd bz-a
        nn-bl = fst bz-b
        np-bu = snd bz-b

        np-al-bu = r*-NonNeg-NonPos nn-al np-bu
        np-bl-au = r*-NonNeg-NonPos nn-bl np-au
        nn-al-bl = r*-NonNeg-NonNeg nn-al nn-bl
        nn-au-bu = r*-NonPos-NonPos np-au np-bu

        min-side = minℚ (al r* bu) (bl r* au)
        max-side = maxℚ (al r* bl) (au r* bu)

        min-al : (al == 0r) -> min-side == (bl r* au)
        min-al z = minℚ-right _ _ (NonPos≤NonNeg np-bl-au
                                    (inj-r (subst Zero (sym (r*-left-zero' z)) Zero-0r)))

        min-bu : (bu == 0r) -> min-side == (bl r* au)
        min-bu z = minℚ-right _ _ (NonPos≤NonNeg np-bl-au
                                    (inj-r (subst Zero (sym (r*-right-zero' z)) Zero-0r)))

        min-bl : (bl == 0r) -> min-side == (al r* bu)
        min-bl z = minℚ-left _ _ (NonPos≤NonNeg np-al-bu
                                   (inj-r (subst Zero (sym (r*-left-zero' z)) Zero-0r)))

        min-au : (au == 0r) -> min-side == (al r* bu)
        min-au z = minℚ-left _ _ (NonPos≤NonNeg np-al-bu
                                   (inj-r (subst Zero (sym (r*-right-zero' z)) Zero-0r)))

        max-al : (al == 0r) -> max-side == (au r* bu)
        max-al z = maxℚ-right _ _ (NonPos≤NonNeg
                                    (inj-r (subst Zero (sym (r*-left-zero' z)) Zero-0r))
                                    nn-au-bu)
        max-bl : (bl == 0r) -> max-side == (au r* bu)
        max-bl z = maxℚ-right _ _ (NonPos≤NonNeg
                                    (inj-r (subst Zero (sym (r*-right-zero' z)) Zero-0r))
                                    nn-au-bu)
        max-au : (au == 0r) -> max-side == (al r* bl)
        max-au z = maxℚ-left _ _ (NonPos≤NonNeg
                                   (inj-r (subst Zero (sym (r*-left-zero' z)) Zero-0r))
                                   nn-al-bl)
        max-bu : (bu == 0r) -> max-side == (al r* bl)
        max-bu z = maxℚ-left _ _ (NonPos≤NonNeg
                                   (inj-r (subst Zero (sym (r*-right-zero' z)) Zero-0r))
                                   nn-al-bl)

        min-l : (al == 0r) -> (bl == 0r) -> min-side == 0r
        min-l za zb = (cong2 minℚ (r*-left-zero' za) (r*-left-zero' zb) >=> minℚ-same)

        min-u : (au == 0r) -> (bu == 0r) -> min-side == 0r
        min-u za zb = (cong2 minℚ (r*-right-zero' zb) (r*-right-zero' za) >=> minℚ-same)

        min-a : (a == 0i) -> min-side == 0r
        min-a z = (cong2 minℚ (r*-left-zero' (cong Iℚ-l z)) (r*-right-zero' (cong Iℚ-u z)) >=> minℚ-same)

        min-b : (b == 0i) -> min-side == 0r
        min-b z = (cong2 minℚ (r*-right-zero' (cong Iℚ-u z)) (r*-left-zero' (cong Iℚ-l z)) >=> minℚ-same)

        max-fs : (al == 0r) -> (bu == 0r) -> max-side == 0r
        max-fs za zb = (cong2 maxℚ (r*-left-zero' za) (r*-right-zero' zb) >=> maxℚ-same)

        max-bs : (au == 0r) -> (bl == 0r) -> max-side == 0r
        max-bs za zb = (cong2 maxℚ (r*-right-zero' zb) (r*-left-zero' za) >=> maxℚ-same)

        max-a : (a == 0i) -> max-side == 0r
        max-a z = (cong2 maxℚ (r*-left-zero' (cong Iℚ-l z)) (r*-left-zero' (cong Iℚ-u z)) >=> maxℚ-same)

        max-b : (b == 0i) -> max-side == 0r
        max-b z = (cong2 maxℚ (r*-right-zero' (cong Iℚ-l z)) (r*-right-zero' (cong Iℚ-u z)) >=> maxℚ-same)


      Imul-BZ-BZ-path : Imul a b c -> c == i-conj (i-cross a b)
      Imul-BZ-BZ-path (imul-nn-nn nn-a nn-b) =
        cong2 _,_ (refl >=< max-bu pb) (r*-left-zero' pa >=< min-u pa pb)
        where
        pa = nn-bz nn-a bz-a
        pb = nn-bz nn-b bz-b
      Imul-BZ-BZ-path (imul-nn-np nn-a np-b) =
        cong2 _,_  (r*-right-zero' pb >=< max-bs pa pb) (refl >=< min-au pa)
        where
        pa = nn-bz nn-a bz-a
        pb = np-bz np-b bz-b
      Imul-BZ-BZ-path (imul-nn-fz nn-a fz-b) =
        cong2 _,_  (r*-right-zero' (cong Iℚ-l pb) >=< max-b pb)
                   (r*-right-zero' (cong Iℚ-u pb) >=< min-b pb)
        where
        pb = fz-bz fz-b bz-b
      Imul-BZ-BZ-path (imul-nn-bz nn-a bz-b) =
        cong2 _,_ (refl >=< max-au pa) (refl >=< min-au pa)
        where
        pa = nn-bz nn-a bz-a

      Imul-BZ-BZ-path (imul-np-nn np-a nn-b) =
        cong2 _,_ (r*-right-zero' pb >=< max-fs pa pb) (r*-commute au bl >=< min-al pa)
        where
        pa = np-bz np-a bz-a
        pb = nn-bz nn-b bz-b
      Imul-BZ-BZ-path (imul-np-np np-a np-b) =
        cong2 _,_ (refl >=< max-bl pb) (r*-right-zero' pb >=< min-l pa pb)
        where
        pa = np-bz np-a bz-a
        pb = np-bz np-b bz-b
      Imul-BZ-BZ-path (imul-np-fz np-a fz-b) =
        cong2 _,_  (r*-right-zero' (cong Iℚ-u pb) >=< max-b pb)
                   (r*-right-zero' (cong Iℚ-l pb) >=< min-b pb)
        where
        pb = fz-bz fz-b bz-b
      Imul-BZ-BZ-path (imul-np-bz np-a bz-b) =
        cong2 _,_ (refl >=< max-al pa) (r*-commute au bl >=< min-al pa)
        where
        pa = np-bz np-a bz-a

      Imul-BZ-BZ-path (imul-fz-nn fz-a nn-b) =
        cong2 _,_  (r*-left-zero' (cong Iℚ-l pa) >=< max-a pa)
                   (r*-left-zero' (cong Iℚ-u pa) >=< min-a pa)
        where
        pa = fz-bz fz-a bz-a
      Imul-BZ-BZ-path (imul-fz-np fz-a np-b) =
        cong2 _,_ (r*-left-zero' (cong Iℚ-u pa) >=< max-a pa)
                  (r*-left-zero' (cong Iℚ-l pa) >=< min-a pa)
        where
        pa = fz-bz fz-a bz-a
      Imul-BZ-BZ-path (imul-fz-fz fz-a fz-b) =
        cong2 _,_ (min-a pa >=< max-a pa)
                  (max-a pa >=< min-a pa)
        where
        pa = fz-bz fz-a bz-a
      Imul-BZ-BZ-path (imul-fz-bz fz-a bz-b) =
        cong2 _,_ (refl >=< max-a pa)
                  (refl >=< min-a pa)
        where
        pa = fz-bz fz-a bz-a



      Imul-BZ-BZ-path (imul-bz-nn bz-a nn-b) =
        cong2 _,_ (refl >=< max-bu pb) (r*-commute au bl >=< min-bu pb)
        where
        pb = nn-bz nn-b bz-b
      Imul-BZ-BZ-path (imul-bz-np bz-a np-b) =
        cong2 _,_  (refl >=< max-bl pb) (refl >=< min-bl pb)
        where
        pb = np-bz np-b bz-b
      Imul-BZ-BZ-path (imul-bz-fz bz-a fz-b) =
        cong2 _,_ (refl >=< max-b pb)
                  (refl >=< min-b pb)
        where
        pb = fz-bz fz-b bz-b
      Imul-BZ-BZ-path (imul-bz-bz _ _) = refl


  Imul-path : {a b c d : Iℚ} -> Imul a b c -> Imul a b d -> c == d
  -- NN-NN
  Imul-path (imul-nn-nn _ _)    (imul-nn-nn _ _) = refl
  Imul-path (imul-nn-nn _ nn-b) (imul-nn-np _ np-b) =
    cong2 _,_ (right-zero-path (nn-np1 nn-b np-b)) (right-zero-path (nn-np2 nn-b np-b))
  Imul-path (imul-nn-nn _ nn-b) (imul-nn-fz _ fz-b) =
    cong2 _,_ (right-zero-path (nn-fz nn-b fz-b)) refl
  Imul-path (imul-nn-nn _ nn-b) (imul-nn-bz _ bz-b) =
    cong2 _,_ refl (right-zero-path (nn-bz nn-b bz-b))

  Imul-path i1@(imul-nn-nn nn-a _) i2@(imul-np-nn np-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-nn-nn nn-a _) i2@(imul-np-np np-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-nn-nn nn-a _) i2@(imul-np-fz np-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-nn-nn nn-a _) i2@(imul-np-bz np-a _) =
    za-case (nn-np nn-a np-a) i1 i2

  Imul-path i1@(imul-nn-nn nn-a _) i2@(imul-fz-nn fz-a _) =
    cong2 _,_ (left-zero-path (nn-fz nn-a fz-a)) refl
  Imul-path i1@(imul-nn-nn _ nn-b) i2@(imul-fz-np _ np-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path (imul-nn-nn nn-a nn-b) (imul-fz-bz fz-a bz-b) =
    cong2 _,_ (r*-left-zero' (nn-fz nn-a fz-a)) (r*-right-zero' (nn-bz nn-b bz-b))

  Imul-path i1@(imul-nn-nn nn-a _) i2@(imul-bz-nn bz-a _) =
    cong2 _,_ refl (left-zero-path (nn-bz nn-a bz-a))
  Imul-path i1@(imul-nn-nn _ nn-b) i2@(imul-bz-np _ np-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path (imul-nn-nn nn-a nn-b) (imul-bz-fz bz-a fz-b) =
    cong2 _,_ (r*-right-zero' (nn-fz nn-b fz-b)) (r*-left-zero' (nn-bz nn-a bz-a))


  -- NN-NP
  Imul-path (imul-nn-np _ np-b) (imul-nn-nn _ nn-b) =
    cong2 _,_ (right-zero-path (nn-np1 nn-b np-b)) (right-zero-path (nn-np2 nn-b np-b))
  Imul-path (imul-nn-np _ np-b) (imul-nn-np _ _)    = refl
  Imul-path (imul-nn-np _ np-b) (imul-nn-fz _ fz-b) =
    cong2 _,_ refl (right-zero-path (np-fz np-b fz-b))
  Imul-path (imul-nn-np _ np-b) (imul-nn-bz _ bz-b) =
    cong2 _,_ (right-zero-path (np-bz np-b bz-b)) refl

  Imul-path i1@(imul-nn-np nn-a _) i2@(imul-np-nn np-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-nn-np nn-a _) i2@(imul-np-np np-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-nn-np nn-a _) i2@(imul-np-fz np-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-nn-np nn-a _) i2@(imul-np-bz np-a _) =
    za-case (nn-np nn-a np-a) i1 i2

  Imul-path i1@(imul-nn-np _ np-b) i2@(imul-fz-nn _ nn-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-nn-np nn-a _) i2@(imul-fz-np fz-a _) =
    cong2 _,_ refl (left-zero-path (nn-fz nn-a fz-a))
  Imul-path (imul-nn-np nn-a np-b) (imul-fz-bz fz-a bz-b) =
    cong2 _,_ (r*-right-zero' (np-bz np-b bz-b)) (r*-left-zero' (nn-fz nn-a fz-a))

  Imul-path i1@(imul-nn-np _ np-b) i2@(imul-bz-nn _ nn-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-nn-np nn-a _) i2@(imul-bz-np bz-a _) =
    cong2 _,_ (left-zero-path (nn-bz nn-a bz-a)) refl
  Imul-path (imul-nn-np nn-a np-b) (imul-bz-fz bz-a fz-b) =
    cong2 _,_ (r*-left-zero' (nn-bz nn-a bz-a)) (r*-right-zero' (np-fz np-b fz-b))

  -- NN-FZ
  Imul-path (imul-nn-fz _ fz-b) (imul-nn-nn _ nn-b) =
    cong2 _,_ (right-zero-path (nn-fz nn-b fz-b)) refl
  Imul-path (imul-nn-fz _ fz-b) (imul-nn-np _ np-b) =
    cong2 _,_ refl (right-zero-path (np-fz np-b fz-b))
  Imul-path (imul-nn-fz _ fz-b) (imul-nn-fz _ _) = refl
  Imul-path (imul-nn-fz _ fz-b) (imul-nn-bz _ bz-b) =
    cong2 _,_ (right-zero-path (fz-bz1 fz-b bz-b)) (right-zero-path (fz-bz2 fz-b bz-b))

  Imul-path i1@(imul-nn-fz nn-a _) i2@(imul-np-nn np-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-nn-fz nn-a _) i2@(imul-np-np np-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-nn-fz nn-a _) i2@(imul-np-fz np-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-nn-fz nn-a _) i2@(imul-np-bz np-a _) =
    za-case (nn-np nn-a np-a) i1 i2


  Imul-path i1@(imul-nn-fz nn-a fz-b) i2@(imul-fz-nn fz-a nn-b) =
    cong2 _,_ (right-zero-path (nn-fz nn-b fz-b) >=< left-zero-path (nn-fz nn-a fz-a)) refl
  Imul-path i1@(imul-nn-fz nn-a fz-b) i2@(imul-fz-np fz-a np-b) =
    cong2 _,_ refl (right-zero-path (np-fz np-b fz-b) >=< left-zero-path (nn-fz nn-a fz-a))
  Imul-path (imul-nn-fz _ fz-b) (imul-fz-bz _ bz-b) =
    (i∙-right-zero' (fz-bz fz-b bz-b))

  Imul-path i1@(imul-nn-fz nn-a fz-b) i2@(imul-bz-nn bz-a nn-b) =
    cong2 _,_ (right-zero-path (nn-fz nn-b fz-b)) (left-zero-path (nn-bz nn-a bz-a))
  Imul-path i1@(imul-nn-fz nn-a fz-b) i2@(imul-bz-np bz-a np-b) =
    cong2 _,_ (left-zero-path (nn-bz nn-a bz-a)) (right-zero-path (np-fz np-b fz-b))
  Imul-path (imul-nn-fz nn-a _) (imul-bz-fz bz-a _) =
    cong2 _,_ (r*-left-zero' (nn-bz nn-a bz-a)) (r*-left-zero' (nn-bz nn-a bz-a))

  -- NN-BZ
  Imul-path (imul-nn-bz _ bz-b) (imul-nn-nn _ nn-b) =
    cong2 _,_ refl (right-zero-path (nn-bz nn-b bz-b))
  Imul-path (imul-nn-bz _ bz-b) (imul-nn-np _ np-b) =
    cong2 _,_ (right-zero-path (np-bz np-b bz-b)) refl
  Imul-path (imul-nn-bz _ bz-b) (imul-nn-fz _ fz-b) =
    cong2 _,_ (right-zero-path (fz-bz1 fz-b bz-b)) (right-zero-path (fz-bz2 fz-b bz-b))
  Imul-path (imul-nn-bz _ bz-b) (imul-nn-bz _ _) = refl

  Imul-path i1@(imul-nn-bz nn-a _) i2@(imul-np-nn np-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-nn-bz nn-a _) i2@(imul-np-np np-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-nn-bz nn-a _) i2@(imul-np-fz np-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-nn-bz nn-a _) i2@(imul-np-bz np-a _) =
    za-case (nn-np nn-a np-a) i1 i2


  Imul-path i1@(imul-nn-bz nn-a bz-b) i2@(imul-fz-nn fz-a nn-b) =
    cong2 _,_ (left-zero-path (nn-fz nn-a fz-a)) (right-zero-path (nn-bz nn-b bz-b))
  Imul-path i1@(imul-nn-bz nn-a bz-b) i2@(imul-fz-np fz-a np-b) =
    cong2 _,_ (right-zero-path (np-bz np-b bz-b)) (left-zero-path (nn-fz nn-a fz-a))
  Imul-path (imul-nn-bz nn-a _) (imul-fz-bz fz-a _) =
    cong2 _,_ (r*-left-zero' (nn-fz nn-a fz-a)) (r*-left-zero' (nn-fz nn-a fz-a))

  Imul-path i1@(imul-nn-bz nn-a bz-b) i2@(imul-bz-nn bz-a nn-b) =
    cong2 _,_ refl (right-zero-path (nn-bz nn-b bz-b) >=< left-zero-path (nn-bz nn-a bz-a))
  Imul-path i1@(imul-nn-bz nn-a bz-b) i2@(imul-bz-np bz-a np-b) =
    cong2 _,_ (right-zero-path (np-bz np-b bz-b) >=< left-zero-path (nn-bz nn-a bz-a)) refl
  Imul-path (imul-nn-bz _ bz-b) (imul-bz-fz _ fz-b) =
    (i∙-right-zero' (fz-bz fz-b bz-b))


  -- NP-NN
  Imul-path i1@(imul-np-nn np-a _) i2@(imul-nn-nn nn-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-np-nn np-a nn-b) i2@(imul-nn-np nn-a np-b) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-np-nn np-a _) i2@(imul-nn-fz nn-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-np-nn np-a _) i2@(imul-nn-bz nn-a _) =
    za-case (nn-np nn-a np-a) i1 i2

  Imul-path (imul-np-nn _ _) (imul-np-nn _ _) = refl
  Imul-path i1@(imul-np-nn _ nn-b) i2@(imul-np-np _ np-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path (imul-np-nn _ nn-b) (imul-np-fz _ fz-b) =
    cong2 _,_ refl (right-zero-path (nn-fz nn-b fz-b))
  Imul-path (imul-np-nn _ nn-b) (imul-np-bz _ bz-b) =
    cong2 _,_ (right-zero-path (nn-bz nn-b bz-b)) refl

  Imul-path i1@(imul-np-nn np-a _) i2@(imul-fz-nn fz-a _) =
    cong2 _,_ refl (left-zero-path (np-fz np-a fz-a))
  Imul-path i1@(imul-np-nn np-a nn-b) i2@(imul-fz-np fz-a np-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path {a} (imul-np-nn np-a nn-b) (imul-fz-bz fz-a bz-b) =
    cong2 _,_ (r*-right-zero' (nn-bz nn-b bz-b)) (r*-left-zero' (np-fz np-a fz-a))

  Imul-path i1@(imul-np-nn np-a _) i2@(imul-bz-nn bz-a _) =
    cong2 _,_ (left-zero-path (np-bz np-a bz-a)) refl
  Imul-path i1@(imul-np-nn np-a nn-b) i2@(imul-bz-np bz-a np-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path (imul-np-nn np-a nn-b) (imul-bz-fz bz-a fz-b) =
    cong2 _,_ (r*-left-zero' (np-bz np-a bz-a)) (r*-right-zero' (nn-fz nn-b fz-b))

  -- NP-NP
  Imul-path i1@(imul-np-np np-a _) i2@(imul-nn-nn nn-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-np-np np-a nn-b) i2@(imul-nn-np nn-a np-b) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-np-np np-a _) i2@(imul-nn-fz nn-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-np-np np-a _) i2@(imul-nn-bz nn-a _) =
    za-case (nn-np nn-a np-a) i1 i2

  Imul-path i1@(imul-np-np _ np-b) i2@(imul-np-nn _ nn-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path (imul-np-np _ _) (imul-np-np _ _) = refl
  Imul-path (imul-np-np _ np-b) (imul-np-fz _ fz-b) =
    cong2 _,_ (right-zero-path (np-fz np-b fz-b)) refl
  Imul-path (imul-np-np _ np-b) (imul-np-bz _ bz-b) =
    cong2 _,_ refl (right-zero-path (np-bz np-b bz-b))

  Imul-path i1@(imul-np-np _ np-b) i2@(imul-fz-nn _ nn-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-np-np np-a _) i2@(imul-fz-np fz-a _) =
    cong2 _,_ (left-zero-path (np-fz np-a fz-a)) refl
  Imul-path (imul-np-np np-a np-b) (imul-fz-bz fz-a bz-b) =
    cong2 _,_ (r*-left-zero' (np-fz np-a fz-a)) (r*-right-zero' (np-bz np-b bz-b))

  Imul-path i1@(imul-np-np _ np-b) i2@(imul-bz-nn _ nn-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-np-np np-a _) i2@(imul-bz-np bz-a _) =
    cong2 _,_ refl (left-zero-path (np-bz np-a bz-a))
  Imul-path (imul-np-np np-a np-b) (imul-bz-fz bz-a fz-b) =
    cong2 _,_ (r*-right-zero' (np-fz np-b fz-b)) (r*-left-zero' (np-bz np-a bz-a))


  -- NP-FZ
  Imul-path i1@(imul-np-fz np-a _) i2@(imul-nn-nn nn-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-np-fz np-a nn-b) i2@(imul-nn-np nn-a np-b) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-np-fz np-a _) i2@(imul-nn-fz nn-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-np-fz np-a _) i2@(imul-nn-bz nn-a _) =
    za-case (nn-np nn-a np-a) i1 i2

  Imul-path (imul-np-fz _ fz-b) (imul-np-nn _ nn-b) =
    cong2 _,_ refl (right-zero-path (nn-fz nn-b fz-b))
  Imul-path (imul-np-fz _ fz-b) (imul-np-np _ np-b) =
    cong2 _,_ (right-zero-path (np-fz np-b fz-b)) refl
  Imul-path (imul-np-fz _ _)    (imul-np-fz _ _)    = refl
  Imul-path i1@(imul-np-fz _ fz-b) i2@(imul-np-bz _ bz-b) =
    zb-case (fz-bz fz-b bz-b) i1 i2

  Imul-path i1@(imul-np-fz np-a fz-b) i2@(imul-fz-nn fz-a nn-b) =
    cong2 _,_ refl (right-zero-path (nn-fz nn-b fz-b) >=< left-zero-path (np-fz np-a fz-a))
  Imul-path i1@(imul-np-fz np-a fz-b) i2@(imul-fz-np fz-a np-b) =
    cong2 _,_ (right-zero-path (np-fz np-b fz-b) >=< left-zero-path (np-fz np-a fz-a)) refl
  Imul-path (imul-np-fz _ fz-b) (imul-fz-bz _ bz-b) =
    cong i-conj (i∙-right-zero' (fz-bz fz-b bz-b))

  Imul-path i1@(imul-np-fz np-a fz-b) i2@(imul-bz-nn bz-a nn-b) =
    cong2 _,_ (left-zero-path (np-bz np-a bz-a)) (right-zero-path (nn-fz nn-b fz-b))
  Imul-path i1@(imul-np-fz np-a fz-b) i2@(imul-bz-np bz-a np-b) =
    cong2 _,_ (right-zero-path (np-fz np-b fz-b)) (left-zero-path (np-bz np-a bz-a))
  Imul-path (imul-np-fz np-a _) (imul-bz-fz bz-a _) =
    cong2 _,_ (r*-left-zero' (np-bz np-a bz-a)) (r*-left-zero' (np-bz np-a bz-a))

  -- NP-BZ
  Imul-path i1@(imul-np-bz np-a _) i2@(imul-nn-nn nn-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-np-bz np-a nn-b) i2@(imul-nn-np nn-a np-b) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-np-bz np-a _) i2@(imul-nn-fz nn-a _) =
    za-case (nn-np nn-a np-a) i1 i2
  Imul-path i1@(imul-np-bz np-a _) i2@(imul-nn-bz nn-a _) =
    za-case (nn-np nn-a np-a) i1 i2

  Imul-path (imul-np-bz _ bz-b) (imul-np-nn _ nn-b) =
    cong2 _,_ (right-zero-path (nn-bz nn-b bz-b)) refl
  Imul-path (imul-np-bz _ bz-b) (imul-np-np _ np-b) =
    cong2 _,_ refl (right-zero-path (np-bz np-b bz-b))
  Imul-path i1@(imul-np-bz _ bz-b) i2@(imul-np-fz _ fz-b) =
    zb-case (fz-bz fz-b bz-b) i1 i2
  Imul-path (imul-np-bz _ _)    (imul-np-bz _ _)    = refl

  Imul-path i1@(imul-np-bz np-a bz-b) i2@(imul-fz-nn fz-a nn-b) =
    cong2 _,_ (right-zero-path (nn-bz nn-b bz-b)) (left-zero-path (np-fz np-a fz-a))
  Imul-path i1@(imul-np-bz np-a bz-b) i2@(imul-fz-np fz-a np-b) =
    cong2 _,_ (left-zero-path (np-fz np-a fz-a)) (right-zero-path (np-bz np-b bz-b))
  Imul-path (imul-np-bz np-a _) (imul-fz-bz fz-a _) =
    cong2 _,_ (r*-left-zero' (np-fz np-a fz-a)) (r*-left-zero' (np-fz np-a fz-a))

  Imul-path i1@(imul-np-bz np-a bz-b) i2@(imul-bz-nn bz-a nn-b) =
    cong2 _,_ (right-zero-path (nn-bz nn-b bz-b) >=< left-zero-path (np-bz np-a bz-a)) refl
  Imul-path i1@(imul-np-bz np-a bz-b) i2@(imul-bz-np bz-a np-b) =
    cong2 _,_ refl (right-zero-path (np-bz np-b bz-b) >=< left-zero-path (np-bz np-a bz-a))
  Imul-path (imul-np-bz _ bz-b) (imul-bz-fz _ fz-b) =
    cong i-conj (i∙-right-zero' (fz-bz fz-b bz-b))

  -- FZ-NN
  Imul-path    (imul-fz-nn fz-a _)    (imul-nn-nn nn-a _) =
    cong2 _,_ (left-zero-path (nn-fz nn-a fz-a)) refl
  Imul-path i1@(imul-fz-nn _ nn-b) i2@(imul-nn-np _ np-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-fz-nn fz-a nn-b) i2@(imul-nn-fz nn-a fz-b) =
    cong2 _,_ (left-zero-path (nn-fz nn-a fz-a) >=< right-zero-path (nn-fz nn-b fz-b)) refl
  Imul-path i1@(imul-fz-nn fz-a nn-b) i2@(imul-nn-bz nn-a bz-b) =
    cong2 _,_ (left-zero-path (nn-fz nn-a fz-a)) (right-zero-path (nn-bz nn-b bz-b))

  Imul-path (imul-fz-nn fz-a _) (imul-np-nn np-a _) =
    cong2 _,_ refl (left-zero-path (np-fz np-a fz-a))
  Imul-path i1@(imul-fz-nn _ nn-b) i2@(imul-np-np _ np-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-fz-nn fz-a nn-b) i2@(imul-np-fz np-a fz-b) =
    cong2 _,_ refl (left-zero-path (np-fz np-a fz-a) >=< right-zero-path (nn-fz nn-b fz-b))
  Imul-path (imul-fz-nn fz-a nn-b)    (imul-np-bz np-a bz-b)    =
    cong2 _,_ (right-zero-path (nn-bz nn-b bz-b)) (left-zero-path (np-fz np-a fz-a))

  Imul-path i1@(imul-fz-nn _ _) i2@(imul-fz-nn _ _) = refl
  Imul-path i1@(imul-fz-nn _ nn-b) i2@(imul-fz-np _ np-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-fz-nn _ nn-b) i2@(imul-fz-bz _ bz-b) =
    cong2 _,_ (r*-right-zero' (nn-bz nn-b bz-b)) (r*-right-zero' (nn-bz nn-b bz-b))

  Imul-path i1@(imul-fz-nn fz-a _) i2@(imul-bz-nn bz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2
  Imul-path i1@(imul-fz-nn fz-a _) i2@(imul-bz-np bz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2
  Imul-path i1@(imul-fz-nn fz-a _) i2@(imul-bz-fz bz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2

  -- FZ-NP
  Imul-path i1@(imul-fz-np _ np-b) i2@(imul-nn-nn _ nn-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-fz-np fz-a _) i2@(imul-nn-np nn-a _) =
    cong2 _,_ refl (left-zero-path (nn-fz nn-a fz-a))
  Imul-path i1@(imul-fz-np fz-a np-b) i2@(imul-nn-fz nn-a fz-b) =
    cong2 _,_ refl (left-zero-path (nn-fz nn-a fz-a) >=< right-zero-path (np-fz np-b fz-b))
  Imul-path i1@(imul-fz-np fz-a np-b) i2@(imul-nn-bz nn-a bz-b) =
    cong2 _,_ (right-zero-path (np-bz np-b bz-b)) (left-zero-path (nn-fz nn-a fz-a))

  Imul-path i1@(imul-fz-np _ np-b) i2@(imul-np-nn _ nn-b) =
     zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-fz-np fz-a _) i2@(imul-np-np np-a _) =
    cong2 _,_ (left-zero-path (np-fz np-a fz-a)) refl
  Imul-path i1@(imul-fz-np fz-a np-b) i2@(imul-np-fz np-a fz-b) =
    cong2 _,_ (left-zero-path (np-fz np-a fz-a) >=< right-zero-path (np-fz np-b fz-b)) refl
  Imul-path (imul-fz-np fz-a np-b)    (imul-np-bz np-a bz-b)    =
    cong2 _,_ (left-zero-path (np-fz np-a fz-a)) (right-zero-path (np-bz np-b bz-b))

  Imul-path i1@(imul-fz-np _ np-b) i2@(imul-fz-nn _ nn-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-fz-np _ _) i2@(imul-fz-np _ _) = refl
  Imul-path i1@(imul-fz-np _ np-b) i2@(imul-fz-bz _ bz-b) =
    cong2 _,_ (r*-right-zero' (np-bz np-b bz-b)) (r*-right-zero' (np-bz np-b bz-b))

  Imul-path i1@(imul-fz-np fz-a _) i2@(imul-bz-nn bz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2
  Imul-path i1@(imul-fz-np fz-a _) i2@(imul-bz-np bz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2
  Imul-path i1@(imul-fz-np fz-a _) i2@(imul-bz-fz bz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2

  -- FZ-BZ
  Imul-path i1@(imul-fz-bz fz-a bz-b) i2@(imul-nn-nn nn-a nn-b) =
    sym (cong2 _,_ (r*-left-zero' (nn-fz nn-a fz-a)) (r*-right-zero' (nn-bz nn-b bz-b)))
  Imul-path i1@(imul-fz-bz fz-a bz-b) i2@(imul-nn-np nn-a np-b) =
    sym (cong2 _,_ (r*-right-zero' (np-bz np-b bz-b)) (r*-left-zero' (nn-fz nn-a fz-a)))
  Imul-path i1@(imul-fz-bz _ bz-b) i2@(imul-nn-fz _ fz-b) =
    zb-case (fz-bz fz-b bz-b) i1 i2
  Imul-path i1@(imul-fz-bz fz-a _) i2@(imul-nn-bz nn-a _) =
    sym (cong2 _,_ (r*-left-zero' (nn-fz nn-a fz-a)) (r*-left-zero' (nn-fz nn-a fz-a)))

  Imul-path i1@(imul-fz-bz fz-a bz-b) i2@(imul-np-nn np-a nn-b) =
    sym (cong2 _,_ (r*-right-zero' (nn-bz nn-b bz-b)) (r*-left-zero' (np-fz np-a fz-a)))
  Imul-path i1@(imul-fz-bz fz-a bz-b) i2@(imul-np-np np-a np-b) =
    sym (cong2 _,_ (r*-left-zero' (np-fz np-a fz-a)) (r*-right-zero' (np-bz np-b bz-b)))
  Imul-path i1@(imul-fz-bz fz-a bz-b) i2@(imul-np-fz np-a fz-b) =
    sym (cong i-conj (i∙-right-zero' (fz-bz fz-b bz-b)))
  Imul-path (imul-fz-bz fz-a _)    (imul-np-bz np-a _)    =
    sym (cong2 _,_ (r*-left-zero' (np-fz np-a fz-a)) (r*-left-zero' (np-fz np-a fz-a)))

  Imul-path i1@(imul-fz-bz _ bz-b) i2@(imul-fz-nn _ nn-b) =
    sym (cong2 _,_ (r*-right-zero' (nn-bz nn-b bz-b)) (r*-right-zero' (nn-bz nn-b bz-b)))
  Imul-path i1@(imul-fz-bz _ bz-b) i2@(imul-fz-np _ np-b) =
    sym (cong2 _,_ (r*-right-zero' (np-bz np-b bz-b)) (r*-right-zero' (np-bz np-b bz-b)))
  Imul-path i1@(imul-fz-bz _ _) i2@(imul-fz-bz _ _) = refl

  Imul-path i1@(imul-fz-bz fz-a _) i2@(imul-bz-nn bz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2
  Imul-path i1@(imul-fz-bz fz-a _) i2@(imul-bz-np bz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2
  Imul-path i1@(imul-fz-bz fz-a _) i2@(imul-bz-fz bz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2

  -- BZ-NN
  Imul-path    (imul-bz-nn bz-a _)    (imul-nn-nn nn-a _) =
    cong2 _,_ refl (left-zero-path (nn-bz nn-a bz-a))
  Imul-path i1@(imul-bz-nn _ nn-b) i2@(imul-nn-np _ np-b) =
     zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-bz-nn bz-a nn-b) i2@(imul-nn-fz nn-a fz-b) =
    cong2 _,_ (right-zero-path (nn-fz nn-b fz-b)) (left-zero-path (nn-bz nn-a bz-a))
  Imul-path i1@(imul-bz-nn bz-a nn-b) i2@(imul-nn-bz nn-a bz-b) =
    cong2 _,_ refl (left-zero-path (nn-bz nn-a bz-a) >=< right-zero-path (nn-bz nn-b bz-b))

  Imul-path (imul-bz-nn bz-a _) (imul-np-nn np-a _) =
    cong2 _,_ (left-zero-path (np-bz np-a bz-a)) refl
  Imul-path i1@(imul-bz-nn _ nn-b) i2@(imul-np-np _ np-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-bz-nn bz-a nn-b) i2@(imul-np-fz np-a fz-b) =
    cong2 _,_ (left-zero-path (np-bz np-a bz-a)) (right-zero-path (nn-fz nn-b fz-b))
  Imul-path (imul-bz-nn bz-a nn-b)    (imul-np-bz np-a bz-b)    =
    cong2 _,_ (left-zero-path (np-bz np-a bz-a) >=< right-zero-path (nn-bz nn-b bz-b)) refl

  Imul-path i1@(imul-bz-nn bz-a _) i2@(imul-fz-nn fz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2
  Imul-path i1@(imul-bz-nn bz-a _) i2@(imul-fz-np fz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2
  Imul-path i1@(imul-bz-nn bz-a _) i2@(imul-fz-bz fz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2

  Imul-path i1@(imul-bz-nn _ _) i2@(imul-bz-nn _ _) = refl
  Imul-path i1@(imul-bz-nn _ nn-b) i2@(imul-bz-np _ np-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-bz-nn _ nn-b) i2@(imul-bz-fz _ fz-b) =
    cong2 _,_ (r*-right-zero' (nn-fz nn-b fz-b)) (r*-right-zero' (nn-fz nn-b fz-b))

  -- BZ-NP
  Imul-path i1@(imul-bz-np _ np-b) i2@(imul-nn-nn _ nn-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-bz-np bz-a _) i2@(imul-nn-np nn-a _) =
    cong2 _,_ (left-zero-path (nn-bz nn-a bz-a)) refl
  Imul-path i1@(imul-bz-np bz-a np-b) i2@(imul-nn-fz nn-a fz-b) =
    cong2 _,_ (left-zero-path (nn-bz nn-a bz-a)) (right-zero-path (np-fz np-b fz-b))
  Imul-path i1@(imul-bz-np bz-a np-b) i2@(imul-nn-bz nn-a bz-b) =
    cong2 _,_ (left-zero-path (nn-bz nn-a bz-a) >=< right-zero-path (np-bz np-b bz-b)) refl

  Imul-path i1@(imul-bz-np _ np-b) i2@(imul-np-nn _ nn-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path (imul-bz-np bz-a _) (imul-np-np np-a _) =
    cong2 _,_ refl (left-zero-path (np-bz np-a bz-a))
  Imul-path i1@(imul-bz-np bz-a np-b) i2@(imul-np-fz np-a fz-b) =
    cong2 _,_ (right-zero-path (np-fz np-b fz-b)) (left-zero-path (np-bz np-a bz-a))
  Imul-path (imul-bz-np bz-a np-b)    (imul-np-bz np-a bz-b)    =
    cong2 _,_ refl (left-zero-path (np-bz np-a bz-a) >=< right-zero-path (np-bz np-b bz-b))

  Imul-path i1@(imul-bz-np bz-a _) i2@(imul-fz-nn fz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2
  Imul-path i1@(imul-bz-np bz-a _) i2@(imul-fz-np fz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2
  Imul-path i1@(imul-bz-np bz-a _) i2@(imul-fz-bz fz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2

  Imul-path i1@(imul-bz-np _ np-b) i2@(imul-bz-nn _ nn-b) =
    zb-case (nn-np nn-b np-b) i1 i2
  Imul-path i1@(imul-bz-np _ _) i2@(imul-bz-np _ _) = refl
  Imul-path i1@(imul-bz-np _ np-b) i2@(imul-bz-fz _ fz-b) =
    cong2 _,_ (r*-right-zero' (np-fz np-b fz-b)) (r*-right-zero' (np-fz np-b fz-b))

  -- BZ-FZ

  Imul-path i1@(imul-bz-fz bz-a fz-b) i2@(imul-nn-nn nn-a nn-b) =
    sym (cong2 _,_ (r*-right-zero' (nn-fz nn-b fz-b)) (r*-left-zero' (nn-bz nn-a bz-a)))
  Imul-path i1@(imul-bz-fz bz-a fz-b) i2@(imul-nn-np nn-a np-b) =
    sym (cong2 _,_ (r*-left-zero' (nn-bz nn-a bz-a)) (r*-right-zero' (np-fz np-b fz-b)))
  Imul-path i1@(imul-bz-fz bz-a _) i2@(imul-nn-fz nn-a _) =
    sym (cong2 _,_ (r*-left-zero' (nn-bz nn-a bz-a)) (r*-left-zero' (nn-bz nn-a bz-a)))
  Imul-path (imul-bz-fz _ fz-b) (imul-nn-bz _ bz-b)    =
    sym (i∙-right-zero' (fz-bz fz-b bz-b))

  Imul-path i1@(imul-bz-fz bz-a fz-b) i2@(imul-np-nn np-a nn-b) =
    sym (cong2 _,_ (r*-left-zero' (np-bz np-a bz-a)) (r*-right-zero' (nn-fz nn-b fz-b)))
  Imul-path i1@(imul-bz-fz bz-a fz-b) i2@(imul-np-np np-a np-b) =
    sym (cong2 _,_ (r*-right-zero' (np-fz np-b fz-b)) (r*-left-zero' (np-bz np-a bz-a)))
  Imul-path i1@(imul-bz-fz bz-a _) i2@(imul-np-fz np-a _) =
    sym (cong2 _,_ (r*-left-zero' (np-bz np-a bz-a)) (r*-left-zero' (np-bz np-a bz-a)))
  Imul-path i1@(imul-bz-fz _ fz-b) i2@(imul-np-bz _ bz-b) =
    zb-case (fz-bz fz-b bz-b) i1 i2

  Imul-path i1@(imul-bz-fz bz-a _) i2@(imul-fz-nn fz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2
  Imul-path i1@(imul-bz-fz bz-a _) i2@(imul-fz-np fz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2
  Imul-path i1@(imul-bz-fz bz-a _) i2@(imul-fz-bz fz-a _) =
    za-case (fz-bz fz-a bz-a) i1 i2

  Imul-path i1@(imul-bz-fz _ fz-b) i2@(imul-bz-nn _ nn-b) =
    sym (cong2 _,_ (r*-right-zero' (nn-fz nn-b fz-b)) (r*-right-zero' (nn-fz nn-b fz-b)))
  Imul-path i1@(imul-bz-fz _ fz-b) i2@(imul-bz-np _ np-b) =
    sym (cong2 _,_ (r*-right-zero' (np-fz np-b fz-b)) (r*-right-zero' (np-fz np-b fz-b)))
  Imul-path i1@(imul-bz-fz _ _) i2@(imul-bz-fz _ _) = refl


  -- FZ-FZ
  Imul-path (imul-fz-fz fz-a fz-b) i2 = sym (Imul-FZ-FZ-path fz-a fz-b i2)
  Imul-path (imul-bz-bz bz-a bz-b) i2 = sym (Imul-BZ-BZ-path bz-a bz-b i2)


  Imul-path i1@(imul-nn-nn _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-nn-np _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-nn-fz _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-nn-bz _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-np-nn _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-np-np _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-np-fz _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-np-bz _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-fz-nn _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-fz-np _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-fz-bz _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-bz-nn _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-bz-np _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)
  Imul-path i1@(imul-bz-fz _ _) (imul-fz-fz fz-a fz-b) = (Imul-FZ-FZ-path fz-a fz-b i1)

  Imul-path i1@(imul-nn-nn _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-nn-np _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-nn-fz _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-nn-bz _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-np-nn _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-np-np _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-np-fz _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-np-bz _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-fz-nn _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-fz-np _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-fz-bz _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-bz-nn _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-bz-np _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
  Imul-path i1@(imul-bz-fz _ _) (imul-bz-bz bz-a bz-b) = (Imul-BZ-BZ-path bz-a bz-b i1)
