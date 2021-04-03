{-# OPTIONS --cubical --safe --exact-split #-}

-- Command to generate imports
-- find . -name '*.agda' | sed -E -e 's|^\./(.*)\.agda|\1|' -e 's|/|.|g' | grep -v 'everything' | sort | sed -E -e 's/(.*)/open import \1 using ()/' | pbcopy

module everything where

open import abs using ()
open import base using ()
open import chapter1 using ()
open import chapter2 using ()
open import chapter2.divisors using ()
open import chapter2.mobius using ()
open import chapter2.partition using ()
open import chapter2.square-free using ()
open import chapter2.totient using ()
open import chapter2.unordered-divisors using ()
open import commutative-monoid using ()
open import cubical using ()
open import div using ()
open import equality using ()
open import equivalence using ()
open import fin using ()
open import fin-algebra using ()
open import finset using ()
open import finsum using ()
open import functions using ()
open import gcd.computational using ()
open import gcd.euclidean-algorithm using ()
open import gcd.properties using ()
open import gcd.propositional using ()
open import hlevel using ()
open import hlevel.base using ()
open import int using ()
open import isomorphism using ()
open import lattice using ()
open import lattice.instances.nat-div using ()
open import lattice.instances.nat-order using ()
open import lcm using ()
open import lcm.exists using ()
open import linear-combo using ()
open import list using ()
open import list.append using ()
open import list.base using ()
open import list.discrete using ()
open import list.filter using ()
open import list.nat using ()
open import list.permutation using ()
open import list.powerset using ()
open import list.sorted using ()
open import list.unordered using ()
open import monoid using ()
open import nat using ()
open import nat.arithmetic using ()
open import nat.binary-strong-induction using ()
open import nat.order using ()
open import nat.properties using ()
open import new-permutation using ()
open import pigeonhole using ()
open import prime using ()
open import prime-div-count using ()
open import prime-div-count.computational using ()
open import prime-factorization using ()
open import prime-gcd using ()
open import prime-power-factorization using ()
open import quotient using ()
open import relation using ()
open import relatively-prime using ()
open import ring using ()
open import ring.implementations using ()
open import ring.lists using ()
open import sigma using ()
open import solver using ()
open import sum using ()
open import swap-permutation using ()
open import truncation using ()
open import type-algebra using ()
open import unique-prime-factorization using ()
open import unordered-list using ()
open import unordered-list.base using ()
open import unordered-list.count-extensionality using ()
open import unordered-list.discrete using ()
open import unordered-list.operations using ()
open import unordered-list.powerset using ()
open import vec using ()
