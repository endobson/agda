{-# OPTIONS --cubical --safe --exact-split #-}

-- Command to generate imports
-- find . -name '*.agda' | sed -E -e 's|^\./(.*)\.agda|\1|' -e 's|/|.|g' | grep -v 'everything' | sort | sed -E -e 's/(.*)/open import \1 using ()/' | pbcopy

module everything where

open import abs using ()
open import additive-group using ()
open import additive-group.instances.int using ()
open import additive-group.instances.nat using ()
open import additive-group.instances.reader using ()
open import additive-group.instances.real using ()
open import apartness using ()
open import apartness.discrete using ()
open import base using ()
open import cartesian-geometry using ()
open import cartesian-geometry.intersect2 using ()
open import cartesian-geometry.line using ()
open import cartesian-geometry.line-apartness using ()
open import cartesian-geometry.matrix using ()
open import cartesian-geometry.point-line-apartness using ()
open import cartesian-geometry.rotation using ()
open import cartesian-geometry.semi-direction using ()
open import cartesian-geometry.semi-direction.apartness using ()
open import cartesian-geometry.semi-rotation using ()
open import cartesian-geometry.vector using ()
open import category.base using ()
open import category.discrete using ()
open import category.order using ()
open import category.order.nat using ()
open import category.set using ()
open import category.slice using ()
open import chapter1 using ()
open import chapter2 using ()
open import chapter2.dirichlet using ()
open import chapter2.divisors using ()
open import chapter2.id-function using ()
open import chapter2.mobius using ()
open import chapter2.multiplicative using ()
open import chapter2.partition using ()
open import chapter2.prime-divisors using ()
open import chapter2.square-free using ()
open import chapter2.totient using ()
open import chapter2.totient-rational using ()
open import chapter2.unordered-divisors using ()
open import commutative-monoid using ()
open import commutative-monoid.binary-product using ()
open import commutative-monoid.int using ()
open import commutative-monoid.pi using ()
open import commutative-monoid.subtype using ()
open import cubical using ()
open import diff-int using ()
open import direct-product using ()
open import direct-product.standard-basis using ()
open import div using ()
open import equality using ()
open import equality-path using ()
open import equivalence using ()
open import fin using ()
open import fin-algebra using ()
open import finite-commutative-monoid using ()
open import finite-commutative-monoid.instances using ()
open import finite-commutative-monoid.partition using ()
open import finite-commutative-monoid.sigma using ()
open import finite-product using ()
open import finset using ()
open import finset.detachable using ()
open import finset.instances using ()
open import finset.partition using ()
open import finset.search using ()
open import finsubset using ()
open import finsum using ()
open import finsum.arithmetic using ()
open import finsum.cardnality using ()
open import finsum.sigma using ()
open import fraction.order using ()
open import fraction.sign using ()
open import functions using ()
open import funext using ()
open import gcd.computational using ()
open import gcd.euclidean-algorithm using ()
open import gcd.properties using ()
open import gcd.propositional using ()
open import group using ()
open import group.int using ()
open import haequiv using ()
open import heyting-field using ()
open import hit-int using ()
open import hlevel using ()
open import hlevel.base using ()
open import hlevel.pi using ()
open import hlevel.sigma using ()
open import int using ()
open import int.base using ()
open import int.order using ()
open import int.sign using ()
open import integral-domain using ()
open import integral-domain.instances.heyting-field using ()
open import integral-domain.instances.real using ()
open import isomorphism using ()
open import isomorphism.base using ()
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
open import maybe using ()
open import metric-space using ()
open import modular-integers using ()
open import modular-integers.binary-product using ()
open import monoid using ()
open import monoid.binary-product using ()
open import monoid.int using ()
open import monoid.pi using ()
open import monoid.subtype using ()
open import multiplicative-disjunction using ()
open import nat using ()
open import nat.arithmetic using ()
open import nat.binary-strong-induction using ()
open import nat.bounded using ()
open import nat.order using ()
open import nat.properties using ()
open import new-permutation using ()
open import order using ()
open import order.instances.int using ()
open import order.instances.nat using ()
open import order.instances.rational using ()
open import order.instances.real using ()
open import ordered-field using ()
open import ordered-integral-domain using ()
open import ordered-ring using ()
open import ordered-semiring using ()
open import ordered-semiring.instances.rational using ()
open import ordered-semiring.instances.real using ()
open import permutation.insert using ()
open import permutation.swap using ()
open import permutation.swap-tree using ()
open import pigeonhole using ()
open import prime using ()
open import prime-div-count using ()
open import prime-div-count.computational using ()
open import prime-factorization using ()
open import prime-gcd using ()
open import prime-power-factorization using ()
open import quotient using ()
open import quotient-field using ()
open import quotient-remainder using ()
open import quotient-remainder-int using ()
open import rational using ()
open import rational-prime using ()
open import rational.difference using ()
open import rational.factor-order using ()
open import rational.heyting-field using ()
open import rational.integral-domain using ()
open import rational.interval using ()
open import rational.interval.multiplication using ()
open import rational.interval.multiplication-base using ()
open import rational.minmax using ()
open import rational.order using ()
open import rational.proper-interval using ()
open import rational.proper-interval.abs using ()
open import rational.proper-interval.maxabs-multiplication using ()
open import rational.proper-interval.multiplication-assoc using ()
open import rational.proper-interval.multiplication-distributive using ()
open import rational.proper-interval.multiplication-inverse using ()
open import rational.proper-interval.multiplication-strict-cross-zero using ()
open import rational.squares using ()
open import real using ()
open import real.arithmetic using ()
open import real.arithmetic.absolute-value using ()
open import real.arithmetic.multiplication using ()
open import real.arithmetic.multiplication.associative using ()
open import real.arithmetic.multiplication.distributive using ()
open import real.arithmetic.multiplication.inverse using ()
open import real.arithmetic.order using ()
open import real.arithmetic.sqrt using ()
open import real.arithmetic.sqrt.base using ()
open import real.heyting-field using ()
open import real.interval using ()
open import real.linear-combo using ()
open import real.sequence using ()
open import real.series using ()
open import relation using ()
open import relatively-prime using ()
open import ring using ()
open import ring.arithmetic using ()
open import ring.implementations using ()
open import ring.implementations.rational using ()
open import ring.implementations.real using ()
open import ring.lists using ()
open import semiring using ()
open import set-quotient using ()
open import sigma using ()
open import sigma.base using ()
open import sign using ()
open import sign.instances.fraction using ()
open import sign.instances.int using ()
open import sign.instances.rational using ()
open import solver using ()
open import subset using ()
open import sum using ()
open import truncation using ()
open import type-algebra using ()
open import unique-prime-factorization using ()
open import univalence using ()
open import unordered-list using ()
open import unordered-list.base using ()
open import unordered-list.count-extensionality using ()
open import unordered-list.discrete using ()
open import unordered-list.operations using ()
open import unordered-list.powerset using ()
open import vec using ()
open import vector-space using ()
open import vector-space.finite using ()
open import vector-space.infinite using ()
