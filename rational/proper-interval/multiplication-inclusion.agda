{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.multiplication-inclusion where

open import additive-group
open import base
open import equality
open import functions
open import order
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-semiring
open import rational
open import rational.order
open import rational.proper-interval
open import rational.proper-interval.classify
open import semiring
open import sum

private
  cz*-l : (a b : Iℚ) -> CrossZeroI a ->
          Iℚ.l (a i* b) == min (Iℚ.l a * Iℚ.u b) (Iℚ.u a * Iℚ.l b)
  cz*-l (Iℚ-cons al au al≤au) (Iℚ-cons bl bu bl≤bu) (al≤0 , 0≤au) =
    cong2 min (min-≥-path (*₁-flips-≤ al≤0 bl≤bu)) (min-≤-path (*₁-preserves-≤ 0≤au bl≤bu))

  cz*-u : (a b : Iℚ) (cz-a : CrossZeroI a) ->
          Iℚ.u (a i* b) == max (Iℚ.l a * Iℚ.l b) (Iℚ.u a * Iℚ.u b)
  cz*-u (Iℚ-cons al au al≤au) (Iℚ-cons bl bu bl≤bu) (al≤0 , 0≤au) =
    cong2 max (max-≥-path (*₁-flips-≤ al≤0 bl≤bu)) (max-≤-path (*₁-preserves-≤ 0≤au bl≤bu))


  nn*-l : (a b : Iℚ) -> NonNegI a ->
          Iℚ.l (a i* b) == min (Iℚ.l a * Iℚ.l b) (Iℚ.u a * Iℚ.l b)
  nn*-l (Iℚ-cons al au al≤au) (Iℚ-cons bl bu bl≤bu) 0≤al =
    cong2 min (min-≤-path (*₁-preserves-≤ 0≤al bl≤bu))
              (min-≤-path (*₁-preserves-≤ (trans-≤ 0≤al al≤au) bl≤bu))

  nn*-u : (a b : Iℚ) -> NonNegI a ->
          Iℚ.u (a i* b) == max (Iℚ.l a * Iℚ.u b) (Iℚ.u a * Iℚ.u b)
  nn*-u (Iℚ-cons al au al≤au) (Iℚ-cons bl bu bl≤bu) 0≤al =
    cong2 max (max-≤-path (*₁-preserves-≤ 0≤al bl≤bu))
              (max-≤-path (*₁-preserves-≤ (trans-≤ 0≤al al≤au) bl≤bu))

  i*-preserves-⊂-CZ-NN :
    {a b c d : Iℚ} -> (a i⊂ b) -> (c i⊂ d) ->
    (StrictCrossZeroI b) -> (StrictCrossZeroI d) -> NonNegI a ->
    (a i* c) i⊂ (b i* d)
  i*-preserves-⊂-CZ-NN
    {a@(Iℚ-cons al au al≤au)} {b@(Iℚ-cons bl bu bl≤bu)}
    {c@(Iℚ-cons cl cu cl≤cu)} {d@(Iℚ-cons dl du dl≤du)}
    (i⊂-cons bl<al au<bu) (i⊂-cons dl<cl cu<du)
    (bl<0 , 0<bu) (dl<0 , 0<du) 0≤al = i⊂-cons bsds<ascs ascs<bsds
    where
    min-ascs = min (min (al * cl) (al * cu)) (min (au * cl) (au * cu))
    max-ascs = max (max (al * cl) (al * cu)) (max (au * cl) (au * cu))
    min-bsds = min (min (bl * dl) (bl * du)) (min (bu * dl) (bu * du))
    max-bsds = max (max (bl * dl) (bl * du)) (max (bu * dl) (bu * du))

    bl≤0 = weaken-< bl<0
    0≤bu = weaken-< 0<bu
    dl≤0 = weaken-< dl<0
    0≤du = weaken-< 0<du

    bsds<ascs : min-bsds < min-ascs
    bsds<ascs =
      trans-=-< bsds=bds
        (trans-≤-< min-≤-right
          (trans-<-=
            (min-greatest-< budl<alcl budl<aucl)
            (sym ascs=ascl)))
      where
      bsds=bds : min-bsds == min (bl * du) (bu * dl)
      bsds=bds = cz*-l b d (bl≤0 , 0≤bu)

      budl<audl : (bu * dl) < (au * dl)
      budl<audl = *₂-flips-< au<bu dl<0

      0≤au = trans-≤ 0≤al al≤au
      dl≤cl = weaken-< dl<cl

      ascs=ascl : min-ascs == min (al * cl) (au * cl)
      ascs=ascl = nn*-l a c 0≤al

      aldl≤alcl : (al * dl) ≤ (al * cl)
      aldl≤alcl = *₁-preserves-≤ 0≤al dl≤cl
      audl≤aldl = *₂-flips-≤ al≤au dl≤0
      budl<alcl = trans-<-≤ (trans-<-≤ budl<audl audl≤aldl) aldl≤alcl

      audl≤aucl : (au * dl) ≤ (au * cl)
      audl≤aucl = *₁-preserves-≤ 0≤au dl≤cl
      budl<aucl = trans-<-≤ budl<audl audl≤aucl

    ascs<bsds : max-ascs < max-bsds
    ascs<bsds =
      trans-=-< ascs=ascl
        (trans-<-≤ (max-least-< alcu<budu aucu<budu)
          (trans-≤-= max-≤-right
            (sym bsds=bds)))
      where
      bsds=bds : max-bsds == max (bl * dl) (bu * du)
      bsds=bds = cz*-u b d (bl≤0 , 0≤bu)

      audu<budu : (au * du) < (bu * du)
      audu<budu = *₂-preserves-< au<bu 0<du

      0≤au = trans-≤ 0≤al al≤au
      cu≤du = weaken-< cu<du

      ascs=ascl : max-ascs == max (al * cu) (au * cu)
      ascs=ascl = nn*-u a c 0≤al

      alcu≤aldu : (al * cu) ≤ (al * du)
      alcu≤aldu = *₁-preserves-≤ 0≤al cu≤du
      aldu≤audu = *₂-preserves-≤ al≤au 0≤du
      alcu<budu = trans-≤-< (trans-≤ alcu≤aldu aldu≤audu) audu<budu

      aucu≤audu : (au * cu) ≤ (au * du)
      aucu≤audu = *₁-preserves-≤ 0≤au cu≤du
      aucu<budu = trans-≤-< aucu≤audu audu<budu

  -- TODO move
  i--preserves-⊂ : {a b : Iℚ} -> a i⊂ b -> (i- a) i⊂ (i- b)
  i--preserves-⊂ (i⊂-cons bl<al au<bu) = i⊂-cons (minus-flips-< au<bu) (minus-flips-< bl<al)

  i*-preserves-⊂-CZ-NP :
    {a b c d : Iℚ} -> (a i⊂ b) -> (c i⊂ d) ->
    (StrictCrossZeroI b) -> (StrictCrossZeroI d) -> NonPosI a ->
    (a i* c) i⊂ (b i* d)
  i*-preserves-⊂-CZ-NP {a} {b} {c} {d} a⊂b c⊂d (bl<0 , 0<bu) (dl<0 , 0<du) al≤0 =
    subst2 _i⊂_ (i--extract-both a c) (i--extract-both b d)
      (i*-preserves-⊂-CZ-NN
        (i--preserves-⊂ a⊂b) (i--preserves-⊂ c⊂d)
        (minus-flips-0< 0<bu , minus-flips-<0 bl<0)
        (minus-flips-0< 0<du , minus-flips-<0 dl<0)
        (minus-flips-≤0 al≤0))

  i*-preserves-⊂-CZ-CZ :
    {a b c d : Iℚ} -> (a i⊂ b) -> (c i⊂ d) ->
    (StrictCrossZeroI b) -> (StrictCrossZeroI d) ->
    (StrictCrossZeroI a) -> (StrictCrossZeroI c) ->
    (a i* c) i⊂ (b i* d)
  i*-preserves-⊂-CZ-CZ
    {a@(Iℚ-cons al au al≤au)} {b@(Iℚ-cons bl bu bl≤bu)}
    {c@(Iℚ-cons cl cu cl≤cu)} {d@(Iℚ-cons dl du dl≤du)}
    (i⊂-cons bl<al au<bu) (i⊂-cons dl<cl cu<du)
    (bl<0 , 0<bu) (dl<0 , 0<du) (al<0 , 0<au) (cl<0 , 0<cu) =
    i⊂-cons bsds<ascs ascs<bsds
    where
    min-ascs = min (min (al * cl) (al * cu)) (min (au * cl) (au * cu))
    max-ascs = max (max (al * cl) (al * cu)) (max (au * cl) (au * cu))
    min-bsds = min (min (bl * dl) (bl * du)) (min (bu * dl) (bu * du))
    max-bsds = max (max (bl * dl) (bl * du)) (max (bu * dl) (bu * du))

    bl≤0 = weaken-< bl<0
    0≤bu = weaken-< 0<bu
    dl≤0 = weaken-< dl<0
    0≤du = weaken-< 0<du
    al≤0 = weaken-< al<0
    0≤au = weaken-< 0<au
    cl≤0 = weaken-< cl<0
    0≤cu = weaken-< 0<cu

    bsds<ascs : min-bsds < min-ascs
    bsds<ascs = trans-=-< bsds=bds (trans-<-= bds<acs (sym ascs=acs))
      where
      bsds=bds : min-bsds == min (bl * du) (bu * dl)
      bsds=bds = cz*-l b d (bl≤0 , 0≤bu)
      ascs=acs : min-ascs == min (al * cu) (au * cl)
      ascs=acs = cz*-l a c (al≤0 , 0≤au)

      bldu<alcu : (bl * du) < (al * cu)
      bldu<alcu = trans-< (*₁-flips-< bl<0 cu<du) (*₂-preserves-< bl<al 0<cu)
      budl<aucl : (bu * dl) < (au * cl)
      budl<aucl = trans-< (*₁-preserves-< 0<bu dl<cl) (*₂-flips-< au<bu cl<0)

      bds<acs = min-preserves-< bldu<alcu budl<aucl


    ascs<bsds : max-ascs < max-bsds
    ascs<bsds = trans-=-< ascs=acs (trans-<-= acs<bds (sym bsds=bds))
      where
      bsds=bds : max-bsds == max (bl * dl) (bu * du)
      bsds=bds = cz*-u b d (bl≤0 , 0≤bu)
      ascs=acs : max-ascs == max (al * cl) (au * cu)
      ascs=acs = cz*-u a c (al≤0 , 0≤au)

      alcl<bldl : (al * cl) < (bl * dl)
      alcl<bldl = trans-< (*₁-flips-< al<0 dl<cl) (*₂-flips-< bl<al dl<0)

      aucu<budu : (au * cu) < (bu * du)
      aucu<budu = trans-< (*₁-preserves-< 0<au cu<du) (*₂-preserves-< au<bu 0<du)

      acs<bds = max-preserves-< alcl<bldl aucu<budu

  i*-preserves-⊂-NN :
    {a b c d : Iℚ} -> a i⊂ b -> c i⊂ d ->
    (NonNegI b) -> (a i* c) i⊂ (b i* d)
  i*-preserves-⊂-NN
    {a@(Iℚ-cons al au al≤au)} {b@(Iℚ-cons bl bu bl≤bu)}
    {c@(Iℚ-cons cl cu cl≤cu)} {d@(Iℚ-cons dl du dl≤du)}
    (i⊂-cons bl<al au<bu) (i⊂-cons dl<cl cu<du) 0≤bl =
    (i⊂-cons min-path max-path)
    where
    0<al = trans-≤-< 0≤bl bl<al
    0<au = trans-<-≤ 0<al al≤au

    0≤al = weaken-< 0<al
    0≤au = weaken-< 0<au
    0≤bu = trans-≤ 0≤bl bl≤bu
    bl≤al = weaken-< bl<al
    au≤bu = weaken-< au<bu

    module _ where
      private
        ascs=ascl : min (min (al * cl) (al * cu)) (min (au * cl) (au * cu)) ==
                    min (al * cl) (au * cl)
        ascs=ascl = nn*-l a c 0≤al

        asdl<ascl : min (al * dl) (au * dl) < min (al * cl) (au * cl)
        asdl<ascl = min-preserves-< lt4 lt5
          where
          lt4 : (al * dl) < (al * cl)
          lt4 = *₁-preserves-< 0<al dl<cl
          lt5 : (au * dl) < (au * cl)
          lt5 = *₁-preserves-< 0<au dl<cl

        bsdl≤asdl : min (bl * dl) (bu * dl) ≤ min (al * dl) (au * dl)
        bsdl≤asdl = either (0≤-case ∘ weaken-<) ≤0-case (split-< 0# dl)
          where
          0≤-case : 0# ≤ dl -> _
          0≤-case 0≤dl =
            trans-=-≤ (min-≤-path (*₂-preserves-≤ bl≤bu 0≤dl))
              (trans-≤-= (*₂-preserves-≤ bl≤al 0≤dl)
                (sym (min-≤-path (*₂-preserves-≤ al≤au 0≤dl))))
          ≤0-case : dl ≤ 0# -> _
          ≤0-case dl≤0 =
            trans-=-≤ (min-≥-path (*₂-flips-≤ bl≤bu dl≤0))
              (trans-≤-= (*₂-flips-≤ au≤bu dl≤0)
                (sym (min-≥-path (*₂-flips-≤ al≤au dl≤0))))


        bsds=bsdl : min (min (bl * dl) (bl * du)) (min (bu * dl) (bu * du)) ==
                    min (bl * dl) (bu * dl)
        bsds=bsdl = nn*-l b d 0≤bl

      min-path = trans-=-< bsds=bsdl (trans-<-= (trans-≤-< bsdl≤asdl asdl<ascl) (sym ascs=ascl))

    module _ where
      private
        ascs=ascu : max (max (al * cl) (al * cu)) (max (au * cl) (au * cu)) ==
                    max (al * cu) (au * cu)
        ascs=ascu = nn*-u a c 0≤al

        ascu<asdu : max (al * cu) (au * cu) < max (al * du) (au * du)
        ascu<asdu = max-preserves-< lt4 lt5
          where
          lt4 : (al * cu) < (al * du)
          lt4 = *₁-preserves-< 0<al cu<du
          lt5 : (au * cu) < (au * du)
          lt5 = *₁-preserves-< 0<au cu<du

        asdu≤bsdu : max (al * du) (au * du) ≤ max (bl * du) (bu * du)
        asdu≤bsdu = either (0≤-case ∘ weaken-<) ≤0-case (split-< 0# du)
          where
          0≤-case : 0# ≤ du -> _
          0≤-case 0≤du =
            trans-=-≤ (max-≤-path (*₂-preserves-≤ al≤au 0≤du))
              (trans-≤-= (*₂-preserves-≤ au≤bu 0≤du)
                (sym (max-≤-path (*₂-preserves-≤ bl≤bu 0≤du))))
          ≤0-case : du ≤ 0# -> _
          ≤0-case du≤0 =
            trans-=-≤ (max-≥-path (*₂-flips-≤ al≤au du≤0))
              (trans-≤-= (*₂-flips-≤ bl≤al du≤0)
                (sym (max-≥-path (*₂-flips-≤ bl≤bu du≤0))))


        bsds=bsdu : max (max (bl * dl) (bl * du)) (max (bu * dl) (bu * du)) ==
                    max (bl * du) (bu * du)
        bsds=bsdu = nn*-u b d 0≤bl

      max-path = trans-=-< ascs=ascu (trans-<-= (trans-<-≤ ascu<asdu asdu≤bsdu) (sym bsds=bsdu))

  i*-preserves-⊂-NP :
    {a b c d : Iℚ} -> (a i⊂ b) -> (c i⊂ d) ->
    NonPosI b -> (a i* c) i⊂ (b i* d)
  i*-preserves-⊂-NP {a} {b} {c} {d} a⊂b c⊂d al≤0 =
    subst2 _i⊂_ (i--extract-both a c) (i--extract-both b d)
      (i*-preserves-⊂-NN
        (i--preserves-⊂ a⊂b) (i--preserves-⊂ c⊂d)
        (minus-flips-≤0 al≤0))

opaque
  i*-preserves-⊂ : {a b c d : Iℚ} -> (a i⊂ b) -> (c i⊂ d) -> (a i* c) i⊂ (b i* d)
  i*-preserves-⊂ {a} {b} {c} {d} a⊂b c⊂d =
    handle (strict-classify' b) (strict-classify' d)
           (strict-classify' a) (strict-classify' c)
    where
    swap : (c i* a) i⊂ (d i* b) -> (a i* c) i⊂ (b i* d)
    swap = subst2 _i⊂_ (i*-commute c a) (i*-commute d b)


    handle : StrictClass' b -> StrictClass' d -> StrictClass' a -> StrictClass' c ->
             (a i* c) i⊂ (b i* d)
    handle (nn-c bn) _         _         _         = i*-preserves-⊂-NN a⊂b c⊂d bn
    handle (np-c bp) _         _         _         = i*-preserves-⊂-NP a⊂b c⊂d bp
    handle (cz-c bz) (nn-c dn) _         _         = swap (i*-preserves-⊂-NN c⊂d a⊂b dn)
    handle (cz-c bz) (np-c dp) _         _         = swap (i*-preserves-⊂-NP c⊂d a⊂b dp)
    handle (cz-c bz) (cz-c dz) (nn-c an) _         = i*-preserves-⊂-CZ-NN a⊂b c⊂d bz dz an
    handle (cz-c bz) (cz-c dz) (np-c ap) _         = i*-preserves-⊂-CZ-NP a⊂b c⊂d bz dz ap
    handle (cz-c bz) (cz-c dz) (cz-c az) (nn-c cn) = swap (i*-preserves-⊂-CZ-NN c⊂d a⊂b dz bz cn)
    handle (cz-c bz) (cz-c dz) (cz-c az) (np-c cp) = swap (i*-preserves-⊂-CZ-NP c⊂d a⊂b dz bz cp)
    handle (cz-c bz) (cz-c dz) (cz-c az) (cz-c cz) = i*-preserves-⊂-CZ-CZ a⊂b c⊂d bz dz az cz
