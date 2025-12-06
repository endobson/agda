{-# OPTIONS --cubical --safe --exact-split #-}

module discrete.instances.top where

open import base
open import decision
open import discrete

instance
  Discrete'-Top : Discrete' Top
  Discrete'-Top = record { f = \tt tt -> yes refl }
