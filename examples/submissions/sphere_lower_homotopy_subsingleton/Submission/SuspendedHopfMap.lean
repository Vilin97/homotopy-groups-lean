/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.CellAttachmentSqTwo
import Submission.Cohomology.Sphere
import Submission.HopfMap
import Submission.SphereSuspension

/-!
# The suspended Hopf map and its mapping cone

This file suspends the concrete quadratic Hopf map using the explicit reduced-suspension sphere
homeomorphisms.  It names the resulting continuous map `S⁴ ⟶ S³`, its `TopCat` incarnation,
and its mapping cone.  The sphere-side square vanishes because `H⁵(S³; F₂) = 0`.  The general
degree-three `Sq²` obstruction therefore specializes to a precise finite target: produce the
bottom class on this cone and prove that its square is nonzero.

## Main definitions and results

* `Submission.suspendedHopfMap : C(Sph 4, Sph 3)`;
* `Submission.suspendedHopfTopCat` and `Submission.suspendedHopfMappingCone`;
* `Submission.suspendedHopfMap_not_nullhomotopic_of_sqTwo`.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- The geometric suspension `S⁴ ⟶ S³` of the concrete quadratic Hopf map. -/
noncomputable def suspendedHopfMap : C(Sph 4, Sph 3) :=
  sphereSuspensionMap 3 2 hopfMap

/-- The suspended Hopf map preserves the chosen sphere basepoints. -/
@[simp]
theorem suspendedHopfMap_basepoint :
    suspendedHopfMap (sphereBasepoint 4) = sphereBasepoint 3 :=
  sphereSuspensionMap_basepoint 3 2 hopfMap hopfMap_basepoint

/-- The suspended Hopf map as a morphism of topological spaces. -/
noncomputable def suspendedHopfTopCat :
    TopCat.of (Sph 4) ⟶ TopCat.of (Sph 3) :=
  TopCat.ofHom suspendedHopfMap

/-- The topological mapping cone of the suspended Hopf map. -/
noncomputable abbrev suspendedHopfMappingCone : TopCat.{0} :=
  topologicalMappingCone suspendedHopfTopCat

/-- The inclusion of the bottom `S³` into the suspended-Hopf mapping cone. -/
noncomputable abbrev suspendedHopfMappingConeIncl :
    TopCat.of (Sph 3) ⟶ suspendedHopfMappingCone :=
  topologicalMappingConeIncl suspendedHopfTopCat

/-- A degree-three class on the suspended-Hopf cone with nonzero `Sq²` proves that the concrete
suspended Hopf map is not based-nullhomotopic. -/
theorem suspendedHopfMap_not_nullhomotopic_of_sqTwo
    (x : Hsing 3 (TopCat.of (Sph 3)) (ZMod 2))
    (u : Hsing 3 suspendedHopfMappingCone (ZMod 2))
    (hu : Hsing.map suspendedHopfMappingConeIncl 3 u = x)
    (hi : Function.Injective
      (Hsing.map (R := ZMod 2) suspendedHopfMappingConeIncl 3))
    (huSq : sqTwoHsingDegreeThree u ≠ 0) :
    ¬ Nonempty
      (TopCat.Homotopy suspendedHopfTopCat
        (TopCat.const (sphereBasepoint 3))) := by
  intro H
  apply not_exists_nullhomotopy_of_mappingCone_sqTwoDegreeThree
    suspendedHopfTopCat x u hu hi (sqTwoHsingDegreeThree_sphere_three x) huSq
  let p : 𝟙_ TopCat.{0} ⟶ TopCat.of (Sph 3) :=
    TopCat.const (sphereBasepoint 3)
  have hp : toUnit (TopCat.of (Sph 4)) ≫ p =
      TopCat.const (sphereBasepoint 3) := by
    ext z
    rfl
  exact ⟨p, H.map fun K ↦ K.cast rfl
    (congrArg
      (fun q : TopCat.of (Sph 4) ⟶ TopCat.of (Sph 3) ↦ q.hom)
      hp.symm)⟩

/-- Once the suspended-Hopf mapping-cone pair vanishes in degrees three and four, the bottom
restriction is bijective. -/
theorem suspendedHopfMappingConeIncl_bijective_of_relative_vanishing
    (h₃ : IsZero (HrelCoh suspendedHopfMappingConeIncl
      (AddCommGrpCat.of (ZMod 2)) 3))
    (h₄ : IsZero (HrelCoh suspendedHopfMappingConeIncl
      (AddCommGrpCat.of (ZMod 2)) 4)) :
    Function.Bijective
      (Hsing.map (R := ZMod 2) suspendedHopfMappingConeIncl 3) :=
  bijective_Hsing_map_of_isZero_HrelCoh
    suspendedHopfMappingConeIncl (ZMod 2) 3 h₃ h₄

end Submission
