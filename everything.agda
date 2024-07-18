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
open import binomial-coefficients using ()
open import boolean using ()
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
open import category.adjunction using ()
open import category.adjunction.unique using ()
open import category.base using ()
open import category.bicategory using ()
open import category.bicategory.cat using ()
open import category.constructions.arrow using ()
open import category.constructions.comma using ()
open import category.constructions.cone using ()
open import category.constructions.cone.univalent using ()
open import category.constructions.full using ()
open import category.constructions.functor-cat using ()
open import category.constructions.functor-cat.univalent using ()
open import category.constructions.group using ()
open import category.constructions.isomorphism using ()
open import category.constructions.iterated-product using ()
open import category.constructions.lift using ()
open import category.constructions.opposite using ()
open import category.constructions.power using ()
open import category.constructions.product using ()
open import category.constructions.slice using ()
open import category.constructions.triple-product using ()
open import category.constructions.union using ()
open import category.displayed using ()
open import category.endofunctor-algebra using ()
open import category.functor using ()
open import category.hom-functor using ()
open import category.instances.discrete using ()
open import category.instances.finset using ()
open import category.instances.free using ()
open import category.instances.group using ()
open import category.instances.order using ()
open import category.instances.quiver using ()
open import category.instances.set using ()
open import category.instances.square-diagram using ()
open import category.instances.terminal using ()
open import category.isomorphism using ()
open import category.limits using ()
open import category.limits-old using ()
open import category.monoidal.base using ()
open import category.monoidal.cartesian using ()
open import category.monoidal.constructions.cartesian using ()
open import category.morphism using ()
open import category.natural-isomorphism using ()
open import category.natural-transformation using ()
open import category.object.group using ()
open import category.object.monoid using ()
open import category.object.product using ()
open import category.object.product.limit using ()
open import category.object.pullback using ()
open import category.object.pullback.limit using ()
open import category.object.pullback.limit-category using ()
open import category.object.terminal using ()
open import category.univalent using ()
open import category.zipper using ()
open import chain using ()
open import chapter1 using ()
open import chapter2 using ()
open import chapter2.dirichlet using ()
open import chapter2.dirichlet.indicator using ()
open import chapter2.divisors using ()
open import chapter2.id-function using ()
open import chapter2.indicator using ()
open import chapter2.mobius using ()
open import chapter2.multiplicative using ()
open import chapter2.partition using ()
open import chapter2.prime-divisors using ()
open import chapter2.problem1 using ()
open import chapter2.problem1-b using ()
open import chapter2.square-free using ()
open import chapter2.totient using ()
open import chapter2.totient-rational using ()
open import chapter2.unordered-divisors using ()
open import coequalizer using ()
open import coequalizer.singleton using ()
open import commutative-monoid using ()
open import commutative-monoid.binary-product using ()
open import commutative-monoid.hprop using ()
open import commutative-monoid.int using ()
open import commutative-monoid.pi using ()
open import commutative-monoid.subtype using ()
open import container.finmap using ()
open import container.finmap.all-entries using ()
open import container.finmap.composition using ()
open import container.finmap.entry-map using ()
open import container.finmap.entry-recursion using ()
open import container.finmap.entry-recursion2 using ()
open import container.finmap.filter-map using ()
open import container.finmap.partition-keys using ()
open import container.finmap.remove using ()
open import container.finmap.remove-entry using ()
open import container.finmap.structure using ()
open import container.finmap.trunc-path using ()
open import container.finmap.unique-entries using ()
open import container.finmap.v2 using ()
open import container.finmap.v3 using ()
open import container.finmap.v4 using ()
open import container.finmap.v4.inverse using ()
open import countable-set using ()
open import countable-set.binary-product using ()
open import cubical using ()
open import diff-int using ()
open import direct-product using ()
open import direct-product.standard-basis using ()
open import discrete using ()
open import div using ()
open import dominance using ()
open import equality using ()
open import equality-path using ()
open import equality.fundamental using ()
open import equality.identity-system using ()
open import equality.inductive-data using ()
open import equality.pathp-iso using ()
open import equality.prop-identity-system using ()
open import equality.square using ()
open import equivalence using ()
open import equivalence.base using ()
open import factorial using ()
open import fin using ()
open import fin-algebra using ()
open import fin.functions using ()
open import fin.list using ()
open import fin.list.sorted using ()
open import fin.list.sorted-merge using ()
open import fin.without-point using ()
open import fin2 using ()
open import finite-commutative-monoid using ()
open import finite-commutative-monoid.extension using ()
open import finite-commutative-monoid.instances using ()
open import finite-commutative-monoid.maximum using ()
open import finite-commutative-monoid.partition using ()
open import finite-commutative-monoid.same-fibers using ()
open import finite-commutative-monoid.sigma using ()
open import finite-commutative-monoid.small using ()
open import finite-commutative-monoid.without-point using ()
open import finite-product using ()
open import finite-product.arithmetic using ()
open import finitely-indexed using ()
open import finitely-indexed.order using ()
open import finitely-indexed.order2 using ()
open import finset using ()
open import finset.cardinality using ()
open import finset.choice using ()
open import finset.detachable using ()
open import finset.finitely-indexed using ()
open import finset.instances using ()
open import finset.instances.base using ()
open import finset.instances.boolean using ()
open import finset.instances.sigma using ()
open import finset.instances.sum using ()
open import finset.optimize using ()
open import finset.order using ()
open import finset.order.base using ()
open import finset.partition using ()
open import finset.search using ()
open import finset.without-point using ()
open import finsubset using ()
open import finsum using ()
open import finsum.absolute-value using ()
open import finsum.arithmetic using ()
open import finsum.cardinality using ()
open import finsum.indicator using ()
open import finsum.order using ()
open import finsum.sigma using ()
open import fint.list using ()
open import fint.list.equality using ()
open import fint.list.sorted using ()
open import fint.list.sorted-merge using ()
open import fint.list.sorted-order using ()
open import fint.same-index using ()
open import fraction.order using ()
open import fraction.sign using ()
open import functions using ()
open import functions.embedding using ()
open import functions.injective using ()
open import functions.sections using ()
open import funext using ()
open import gcd.computational using ()
open import gcd.euclidean-algorithm using ()
open import gcd.properties using ()
open import gcd.propositional using ()
open import group using ()
open import group.int using ()
open import haequiv using ()
open import heyting-field using ()
open import heyting-field.instances.rational using ()
open import heyting-field.instances.real using ()
open import hit-int using ()
open import hlevel using ()
open import hlevel.base using ()
open import hlevel.order using ()
open import hlevel.pi using ()
open import hlevel.retract using ()
open import hlevel.sigma using ()
open import infinity-monoid using ()
open import infinity-monoid.endomorphism using ()
open import int using ()
open import int.base using ()
open import int.monoid-homomorphism using ()
open import int.order using ()
open import int.sign using ()
open import integral-domain using ()
open import integral-domain.apart-linear-order using ()
open import integral-domain.instances.heyting-field using ()
open import integral-domain.instances.real using ()
open import isomorphism using ()
open import isomorphism.base using ()
open import lattice using ()
open import lcm using ()
open import lcm.exists using ()
open import linear-combo using ()
open import list using ()
open import list.append using ()
open import list.base using ()
open import list.discrete using ()
open import list.filter using ()
open import list.fin-list-eq using ()
open import list.nat using ()
open import list.permutation using ()
open import list.powerset using ()
open import list.sorted using ()
open import list.unordered using ()
open import maybe using ()
open import metric-space using ()
open import metric-space.continuous using ()
open import metric-space.instances.real using ()
open import metric-space.instances.subspace using ()
open import metric-space.limit using ()
open import metric-space.net-limit using ()
open import modular-integers using ()
open import modular-integers.binary-product using ()
open import monoid using ()
open import monoid.binary-product using ()
open import monoid.endomorphism using ()
open import monoid.int using ()
open import monoid.pi using ()
open import monoid.subtype using ()
open import multiplicative-disjunction using ()
open import nat using ()
open import nat.arithmetic using ()
open import nat.binary-strong-induction using ()
open import nat.bounded using ()
open import nat.even-odd using ()
open import nat.exponentiation using ()
open import nat.half-induction using ()
open import nat.monoid-homomorphism using ()
open import nat.order using ()
open import nat.order.base using ()
open import nat.properties using ()
open import net using ()
open import new-permutation using ()
open import non-empty-finset using ()
open import order using ()
open import order.continuous using ()
open import order.flipped using ()
open import order.homomorphism using ()
open import order.homomorphism.fin using ()
open import order.homomorphism.fint using ()
open import order.instances.fin using ()
open import order.instances.fint using ()
open import order.instances.int using ()
open import order.instances.integral-partition using ()
open import order.instances.nat using ()
open import order.instances.rational using ()
open import order.instances.real using ()
open import order.interval using ()
open import order.minmax using ()
open import order.minmax.commutative-monoid using ()
open import order.minmax.decidable using ()
open import order.minmax.instances.nat using ()
open import order.minmax.instances.rational using ()
open import order.minmax.instances.real using ()
open import order.partial-order using ()
open import order.subtype using ()
open import ordered-additive-group using ()
open import ordered-additive-group.absolute-value using ()
open import ordered-additive-group.continuous using ()
open import ordered-additive-group.decidable using ()
open import ordered-additive-group.group using ()
open import ordered-additive-group.instances.int using ()
open import ordered-additive-group.instances.nat using ()
open import ordered-additive-group.instances.rational using ()
open import ordered-additive-group.instances.real using ()
open import ordered-additive-group.minmax using ()
open import ordered-additive-group.negated using ()
open import ordered-field using ()
open import ordered-field.archimedean using ()
open import ordered-field.mean using ()
open import ordered-ring using ()
open import ordered-ring.absolute-value using ()
open import ordered-ring.exponentiation using ()
open import ordered-ring.exponentiation.all-ones using ()
open import ordered-ring.exponentiation.isomorphism using ()
open import ordered-ring.exponentiation.poly-index using ()
open import ordered-ring.exponentiation.poly-index.ends using ()
open import ordered-ring.exponentiation.poly-index.eval using ()
open import ordered-ring.sqrt using ()
open import ordered-semiring using ()
open import ordered-semiring.archimedean using ()
open import ordered-semiring.archimedean.instances.int using ()
open import ordered-semiring.archimedean.instances.nat using ()
open import ordered-semiring.archimedean.instances.rational using ()
open import ordered-semiring.archimedean.instances.real using ()
open import ordered-semiring.decidable using ()
open import ordered-semiring.exponentiation using ()
open import ordered-semiring.initial using ()
open import ordered-semiring.instances.int using ()
open import ordered-semiring.instances.nat using ()
open import ordered-semiring.instances.rational using ()
open import ordered-semiring.instances.real using ()
open import ordered-semiring.instances.real-strong using ()
open import ordered-semiring.integral-domain using ()
open import ordered-semiring.minmax using ()
open import ordered-semiring.negated using ()
open import ordered-semiring.ring using ()
open import ordered-semiring.squares using ()
open import ordered-set using ()
open import ordered-set.fin using ()
open import ordered-set.glist using ()
open import partial-map using ()
open import partial-map.spheres using ()
open import permutation.insert using ()
open import permutation.swap using ()
open import permutation.swap-tree using ()
open import pigeonhole using ()
open import polynomial using ()
open import power-series using ()
open import power-series.real using ()
open import prime using ()
open import prime-div-count using ()
open import prime-div-count.computational using ()
open import prime-factorization using ()
open import prime-gcd using ()
open import prime-power-factorization using ()
open import programming-languages.alpha-caml using ()
open import programming-languages.alpha-caml.alpha-equiv using ()
open import programming-languages.alpha-caml.multi-swap using ()
open import programming-languages.alpha-caml.single-swap using ()
open import programming-languages.july2023.lambda-calc using ()
open import programming-languages.nom-pa using ()
open import programming-languages.renamings using ()
open import programming-languages.renamings2 using ()
open import programming-languages.stx using ()
open import quotient using ()
open import quotient-field using ()
open import quotient-remainder using ()
open import quotient-remainder-int using ()
open import rational using ()
open import rational-prime using ()
open import rational.factor-order using ()
open import rational.integer using ()
open import rational.integral-domain using ()
open import rational.non-standard-interval.base using ()
open import rational.non-standard-interval.multiplication using ()
open import rational.non-standard-interval.multiplication-base using ()
open import rational.open-interval using ()
open import rational.open-interval.containment using ()
open import rational.open-interval.maxabs-multiplication using ()
open import rational.open-interval.multiplication-assoc using ()
open import rational.open-interval.multiplication-distributive using ()
open import rational.open-interval.multiplication-inclusion using ()
open import rational.open-interval.multiplication-strict-cross-zero using ()
open import rational.open-interval.sequence using ()
open import rational.order using ()
open import rational.proper-interval using ()
open import rational.proper-interval.abs using ()
open import rational.proper-interval.base using ()
open import rational.proper-interval.classify using ()
open import rational.proper-interval.containment using ()
open import rational.proper-interval.maxabs-multiplication using ()
open import rational.proper-interval.multiplication-assoc using ()
open import rational.proper-interval.multiplication-distributive using ()
open import rational.proper-interval.multiplication-inclusion using ()
open import rational.proper-interval.multiplication-inverse using ()
open import rational.proper-interval.multiplication-strict-cross-zero using ()
open import rational.squares using ()
open import real using ()
open import real.apartness using ()
open import real.arithmetic using ()
open import real.arithmetic.multiplication using ()
open import real.arithmetic.multiplication.associative using ()
open import real.arithmetic.multiplication.distributive using ()
open import real.arithmetic.multiplication.inverse using ()
open import real.arithmetic.nth-root using ()
open import real.arithmetic.nth-root.base using ()
open import real.arithmetic.nth-root.bound-sequence using ()
open import real.arithmetic.nth-root.odd using ()
open import real.arithmetic.order using ()
open import real.arithmetic.rational using ()
open import real.arithmetic.sqrt using ()
open import real.arithmetic.sqrt.base using ()
open import real.caratheodory-derivative using ()
open import real.caratheodory-derivative.addition using ()
open import real.caratheodory-derivative.constant using ()
open import real.caratheodory-derivative.identity using ()
open import real.complete using ()
open import real.continuous.arithmetic using ()
open import real.continuous.arithmetic.multiplication using ()
open import real.continuous.arithmetic.multiplication-inverse using ()
open import real.continuous.bounds using ()
open import real.derivative using ()
open import real.derivative.addition using ()
open import real.derivative.constant using ()
open import real.derivative.identity using ()
open import real.distance using ()
open import real.epsilon-bounded using ()
open import real.epsilon-bounded.base using ()
open import real.exponential-series using ()
open import real.gluing.overlap-at-zero using ()
open import real.gluing.overlap-at-zero.continuous using ()
open import real.gluing.overlap-at-zero.extension using ()
open import real.infinite-sum using ()
open import real.integral.delta-fine-partition using ()
open import real.integral.instances.polynomial using ()
open import real.integral.is-integral using ()
open import real.integral.partition using ()
open import real.integral.partition-index using ()
open import real.integral.partition-refinement using ()
open import real.integral.partition-refinement-delta-fine using ()
open import real.integral.partition-refinement-join using ()
open import real.integral.tagged-partition using ()
open import real.interval using ()
open import real.linear-combo using ()
open import real.maximum using ()
open import real.metric-space using ()
open import real.minimum using ()
open import real.open-interval using ()
open import real.order using ()
open import real.rational using ()
open import real.sequence using ()
open import real.sequence.absolute-convergence using ()
open import real.sequence.cauchy using ()
open import real.sequence.harmonic using ()
open import real.sequence.limit using ()
open import real.sequence.limit-point using ()
open import real.sequence.limit.arithmetic using ()
open import real.sequence.limit.zero using ()
open import real.sequence.open-interval using ()
open import real.sequence.ratio-test using ()
open import real.series using ()
open import real.series.base using ()
open import real.series.geometric using ()
open import real.subspace using ()
open import relation using ()
open import relatively-prime using ()
open import ring using ()
open import ring.arithmetic using ()
open import ring.exponentiation using ()
open import ring.implementations.int using ()
open import ring.implementations.rational using ()
open import ring.implementations.reader using ()
open import ring.implementations.real using ()
open import ring.initial-integers using ()
open import ring.lists using ()
open import ring.solver-equations using ()
open import semiring using ()
open import semiring.exponentiation using ()
open import semiring.initial using ()
open import semiring.instances.nat using ()
open import sequence using ()
open import sequence.drop using ()
open import sequence.partial-sums using ()
open import sequence.permutation using ()
open import set-quotient using ()
open import sigma using ()
open import sigma.base using ()
open import sign using ()
open import sign.instances.fraction using ()
open import sign.instances.int using ()
open import sign.instances.rational using ()
open import solver using ()
open import spheres using ()
open import spheres2 using ()
open import subfinite using ()
open import subfinite.discrete using ()
open import subset using ()
open import subset.indicator using ()
open import subset.subspace using ()
open import sum using ()
open import transport using ()
open import truncation using ()
open import type-algebra using ()
open import type-algebra.boolean using ()
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
open import without-point using ()
