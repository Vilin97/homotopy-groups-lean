/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.BistellarSphereRealization
import Submission.ForMathlib.HomotopyGroup.Homeomorph
import Submission.Hurewicz.SphereDiagonalGeneric
import Submission.Model.SphereConnected

/-!
# Homotopy groups of certified bistellar spheres

The realization homeomorphism for an `IsBistellarSphere` certificate transports homotopy groups
to the exact metric sphere.  Consequently all groups below the certified dimension are trivial,
and the diagonal group in every positive dimension is infinite cyclic.

## Main results

* `IsBistellarSphere.realizationHomotopyGroupEquivSphere`;
* `IsBistellarSphere.subsingleton_realizationHomotopyGroup_of_lt`;
* `IsBistellarSphere.nonempty_realizationDiagonalMulEquivInt`.
-/

noncomputable section

namespace Submission.FiniteOrderedComplex

open CategoryTheory Simplicial

variable {V : Type} [LinearOrder V]

/-- A chosen homeomorphism from a certified bistellar sphere realization to the exact metric
sphere. -/
noncomputable def IsBistellarSphere.realizationHomeomorphSphere
    {facets : Finset (Finset V)} {dimension : ℕ}
    (h : IsBistellarSphere facets dimension) :
    SSet.toTop.obj (orderedSSet facets) ≃ₜ SphereSpace dimension :=
  h.nonempty_realizationHomeomorphSphere.some

/-- Homotopy groups of a certified bistellar sphere realization agree with those of the exact
metric sphere, at the transported basepoint. -/
noncomputable def IsBistellarSphere.realizationHomotopyGroupEquivSphere
    {facets : Finset (Finset V)} {dimension k : ℕ}
    (h : IsBistellarSphere facets dimension)
    (x : SSet.toTop.obj (orderedSSet facets)) :
    HomotopyGroup.Pi k (SSet.toTop.obj (orderedSSet facets)) x ≃
      HomotopyGroup.Pi k (SphereSpace dimension)
        (h.realizationHomeomorphSphere x) :=
  HomotopyGroup.homeomorphEquiv h.realizationHomeomorphSphere x

/-- Below the certified dimension, every homotopy group of the realization is trivial. -/
theorem IsBistellarSphere.subsingleton_realizationHomotopyGroup_of_lt
    {facets : Finset (Finset V)} {dimension k : ℕ}
    (h : IsBistellarSphere facets dimension) (hk : k < dimension)
    (x : SSet.toTop.obj (orderedSSet facets)) :
    Subsingleton (HomotopyGroup.Pi k
      (SSet.toTop.obj (orderedSSet facets)) x) := by
  let e := h.realizationHomotopyGroupEquivSphere (k := k) x
  haveI := subsingleton_homotopyGroup_sphere_of_lt k dimension hk
    (h.realizationHomeomorphSphere x)
  exact ⟨fun a b ↦ e.injective (Subsingleton.elim _ _)⟩

/-- In every positive certified dimension, the diagonal homotopy group of the realization is
infinite cyclic. -/
theorem IsBistellarSphere.nonempty_realizationDiagonalMulEquivInt
    {facets : Finset (Finset V)} {n : ℕ}
    (h : IsBistellarSphere facets (n + 1))
    (x : SSet.toTop.obj (orderedSSet facets)) :
    Nonempty (HomotopyGroup.Pi (n + 1)
      (SSet.toTop.obj (orderedSSet facets)) x ≃* Multiplicative ℤ) := by
  rcases sphere_diagonal_sph_at_mulEquiv_int n
    (h.realizationHomeomorphSphere x) with ⟨d⟩
  exact ⟨(HomotopyGroup.homeomorphMulEquiv
    h.realizationHomeomorphSphere x).trans d⟩

end Submission.FiniteOrderedComplex
