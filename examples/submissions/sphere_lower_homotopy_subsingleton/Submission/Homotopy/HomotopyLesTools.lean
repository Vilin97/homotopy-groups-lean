/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homotopy.RelGroup
import Submission.Homotopy.Connected
import Submission.ForMathlib.HomotopyGroup.Contractible

/-!
# Reading isomorphisms off the long exact sequence of a pair

This is the homotopy-theoretic analogue of `Submission/Homology/LesTools.lean`: it packages the
"vanishing ⟹ isomorphism" consequences of the long exact sequence

`⋯ → π_i(A) → π_i(X) → π_i(X, A) → π_{i-1}(A) → π_{i-1}(X) → ⋯`

of a pair `(X, A)`, together with the connectivity statement they feed.  Nothing here is specific
to spheres.

Two conventions of the vendored `WhiteheadTheorem` library matter.  First, the sequence is
available both as pointed sets (`RelHomotopyGroup.isExactAt_*`) and, in degrees where the group
structures exist, as `Function.MulExact` between `MonoidHom`s (`Submission/Homotopy/RelGroup.lean`).
`nonempty_unique_relHomotopyGroup` uses the *pointed-set* form and therefore applies in degree `1`
as well, where `π_rel 1` carries no group structure; the two bijectivity statements need genuine
injectivity and so use the group form, which restricts them to degrees `≥ 2`.  Second, a pair is
`n`-connected in the sense of `Submission.IsNConnectedPair` when its relative homotopy groups
vanish up to degree `n` *and* `π₀(A) → π₀(X)` is surjective.

## Main results

* `Submission.nonempty_unique_relHomotopyGroup` — `π_{n+1}(X, A)` is trivial as soon as
  `π_{n+1}(X)` and `π_n(A)` are;
* `Submission.bijective_bd_of_subsingleton` — if `X` is weakly contractible then
  `∂ : π_{n+2}(X, A) → π_{n+1}(A)` is bijective;
* `Submission.bijective_jStar_of_subsingleton` — if `A` is weakly contractible then
  `j_* : π_{n+2}(X) → π_{n+2}(X, A)` is bijective;
* `Submission.subsingleton_homotopyGroup_of_homotopyEquiv` — vanishing of homotopy groups
  transports along a homotopy equivalence;
* `Submission.isNConnectedPair_of_contractible` — a pair whose ambient space is weakly
  contractible is as connected as its subspace.
-/

open scoped Topology Topology.Homotopy

namespace Submission

/-! ### Pairs one of whose two spaces is weakly contractible

All three results below are read off the long exact sequence of a pair.  They are stated for an
arbitrary pair `(X, A)`; only the vanishing of the relevant absolute homotopy groups is used, so
"weakly contractible" is never a hypothesis, merely the way the hypotheses get discharged. -/

variable {X : Type*} [TopologicalSpace X] {A : Set X}

/-- **A relative homotopy group vanishes when its two neighbours do.**  If `π_{n+1}(X)` and
`π_n(A)` are trivial then so is `π_{n+1}(X, A)`.

This is exactness of `π_{n+1}(X) → π_{n+1}(X, A) → π_n(A)` at the middle term, in the pointed-set
form supplied by the vendored library, so it applies in degree `1` as well, where there is no
group structure.  Note that only *one* neighbour has to be trivial for each of the two halves:
`π_n(A) = 0` makes `j_*` surjective and `π_{n+1}(X) = 0` collapses its image, so no bijectivity of
`i_*` — and hence no group structure — is ever needed. -/
theorem nonempty_unique_relHomotopyGroup (n : ℕ) (a : A)
    (hX : Subsingleton (π_ (n + 1) X (a : X))) (hA : Subsingleton (π_ n A a)) :
    Nonempty (Unique (π_rel (n + 1) X A a)) := by
  refine ⟨⟨⟨default⟩, fun z => ?_⟩⟩
  have hz : z ∈ Set.range (RelHomotopyGroup.jStar (n + 1) X A a) := by
    rw [← RelHomotopyGroup.isExactAt_jStar_bd n X A a]
    exact Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (hA.elim _ _))
  obtain ⟨w, rfl⟩ := hz
  rw [hX.elim w default]
  exact (RelHomotopyGroup.jStar_isPointedMap (n + 1) X A a).map_default

/-- **The boundary map of a pair with weakly contractible ambient space is bijective.**  If
`π_{n+2}(X)` and `π_{n+1}(X)` are trivial then `∂ : π_{n+2}(X, A) → π_{n+1}(A)` is a bijection. -/
theorem bijective_bd_of_subsingleton (n : ℕ) (a : A)
    (h₁ : Subsingleton (π_ (n + 2) X (a : X))) (h₂ : Subsingleton (π_ (n + 1) X (a : X))) :
    Function.Bijective (RelHomotopyGroup.bd (n + 1) X A a) := by
  constructor
  · refine (injective_iff_map_eq_one (RelHomotopyGroup.bdHom n X A a)).mpr fun z hz => ?_
    obtain ⟨w, rfl⟩ := (RelHomotopyGroup.mulExact_jStarHom_bdHom n X A a z).mp hz
    rw [h₁.elim w 1, map_one]
  · exact fun y => (RelHomotopyGroup.mulExact_bdHom_iStarHom n X A a y).mp (h₂.elim _ _)

/-- **The map `j_*` of a pair with weakly contractible subspace is bijective.**  If `π_{n+2}(A)`
and `π_{n+1}(A)` are trivial then `j_* : π_{n+2}(X) → π_{n+2}(X, A)` is a bijection. -/
theorem bijective_jStar_of_subsingleton (n : ℕ) (a : A)
    (h₁ : Subsingleton (π_ (n + 2) A a)) (h₂ : Subsingleton (π_ (n + 1) A a)) :
    Function.Bijective (RelHomotopyGroup.jStar (n + 2) X A a) := by
  constructor
  · refine (injective_iff_map_eq_one (RelHomotopyGroup.jStarHom n X A a)).mpr fun z hz => ?_
    obtain ⟨w, rfl⟩ := (RelHomotopyGroup.mulExact_iStarHom_jStarHom n X A a z).mp hz
    rw [h₁.elim w 1, map_one]
  · exact fun y => (RelHomotopyGroup.mulExact_jStarHom_bdHom n X A a y).mp (h₂.elim _ _)

/-! ### Connectivity of a pair with weakly contractible ambient space -/

/-- **Vanishing of homotopy groups transports along a homotopy equivalence.**  No compatibility
of basepoints is needed, since the hypothesis is imposed at every basepoint of the target.

Beware that `N` must be nonempty, so this says nothing about `π₀`; for `π₀` use path
connectedness and `Submission.subsingleton_homotopyGroup_zero` instead. -/
theorem subsingleton_homotopyGroup_of_homotopyEquiv {N : Type*} [DecidableEq N] [Nonempty N]
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] (e : ContinuousMap.HomotopyEquiv Y Z)
    (hZ : ∀ z : Z, Subsingleton (HomotopyGroup N Z z)) (y : Y) :
    Subsingleton (HomotopyGroup N Y y) := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_of_homotopyEquiv' (N := N) e y
  haveI := hZ (e y)
  exact φ.toEquiv.subsingleton

/-- **A pair with weakly contractible ambient space is as connected as its subspace.**  If `Y` is
contractible and `π_k(C) = 0` for every `k < m`, then the pair `(Y, C)` is `m`-connected. -/
theorem isNConnectedPair_of_contractible {Y : Type} [TopologicalSpace Y] [ContractibleSpace Y]
    (C : Set Y) (m : ℕ) (hC : ∀ k : ℕ, k < m → ∀ c : C, Subsingleton (π_ k C c)) :
    IsNConnectedPair m Y C where
  surjective_iStar_zero a y :=
    ⟨default, ((RelHomotopyGroup.iStar_isPointedMap 0 Y C a).map_default).trans
      ((subsingleton_homotopyGroup_zero (a : Y)).elim _ y)⟩
  unique_piRel k hk a :=
    nonempty_unique_relHomotopyGroup k a
      (subsingleton_homotopyGroup_of_contractible (N := Fin (k + 1)) (a : Y))
      (hC k (by omega) a)

end Submission
