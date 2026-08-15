/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneProjectiveLineCofiberComparison
import Submission.SphereReducedSuspensionBijective

/-!
# The point-pair target of the projective-line collapse

The target pair `(S⁴, {basepoint})` of the canonical projective-line collapse has completely
normalized fourth relative homotopy and homology.  Its relative Hurewicz map is an isomorphism,
and the relative class obtained from the canonical cubical sphere generator has unit integral
Hurewicz coordinate.  The final theorem uses naturality to reduce bijectivity of the canonical
relative `π₄` collapse to a single homological composite.
-/

open CategoryTheory
open scoped Topology Topology.Homotopy TopCat

noncomputable section

namespace Submission

/-- Fourth relative homotopy of the point pair `(S⁴, {basepoint})` in the canonical sphere
Hurewicz coordinate. -/
noncomputable def sphereFourPointRelativePiFourMulEquivInt :
    π_rel 4 (Sph 4) sphereFourBasepointSet sphereFourBasepointInSet ≃*
      Multiplicative ℤ :=
  (homotopyGroupMulEquivRelSingleton 2 (sphereBasepoint 4)).symm.trans
    (sphereDiagonalHurewiczMulEquiv 2)

/-- Fourth relative integral homology of the point pair `(S⁴, {basepoint})`, normalized by the
maintained sphere orientation. -/
noncomputable def sphereFourPointRelativeHomologyFourIsoInt :
    HrelSet (Y := TopCat.of (Sph 4)) 4 sphereFourBasepointSet ≅
      AddCommGrpCat.of ℤ :=
  (homologyIsoRelSingleton 2 (sphereBasepoint 4)).symm ≪≫
    hgrpSphereSelfIsoZ 3

/-- The maintained top sphere class, viewed in relative homology of the point pair. -/
noncomputable def sphereFourPointRelativeHomologyFourGenerator :
    HrelSet (Y := TopCat.of (Sph 4)) 4 sphereFourBasepointSet :=
  relJ 4 (subIncl (Y := TopCat.of (Sph 4)) sphereFourBasepointSet)
    (sphereTopHomologyClass 3)

/-- The maintained relative top-homology generator of the point pair has coordinate one. -/
@[simp]
theorem sphereFourPointRelativeHomologyFourIsoInt_generator :
    sphereFourPointRelativeHomologyFourIsoInt.hom
        sphereFourPointRelativeHomologyFourGenerator =
      (1 : ℤ) := by
  change (hgrpSphereSelfIsoZ 3).hom
      ((homologyIsoRelSingleton 2 (sphereBasepoint 4)).inv
        ((homologyIsoRelSingleton 2 (sphereBasepoint 4)).hom
          (sphereTopHomologyClass 3))) =
    (1 : ℤ)
  rw [Iso.hom_inv_id_apply, hgrpSphereSelfIsoZ_sphereTopHomologyClass]

/-- Relative Hurewicz is bijective in degree four for the point pair of `S⁴`. -/
theorem sphereFourPointRelativeHurewiczAdd_bijective :
    Function.Bijective
      (relativeHurewiczAdd 2 sphereFourBasepointSet sphereFourBasepointInSet) := by
  letI : ContractibleSpace sphereFourBasepointSet := by
    change ContractibleSpace ({sphereBasepoint 4} : Set (Sph 4))
    infer_instance
  exact
    (isNConnected_sphere_succ_succ 2).relativeHurewiczAdd_bijective_of_contractibleSubspace
      sphereFourBasepointSet sphereFourBasepointInSet

/-- The degree-four relative Hurewicz isomorphism for the point pair of `S⁴`. -/
noncomputable def sphereFourPointRelativeHurewiczAddEquiv :
    Additive (π_rel 4 (Sph 4) sphereFourBasepointSet sphereFourBasepointInSet) ≃+
      (HrelSet (Y := TopCat.of (Sph 4)) 4 sphereFourBasepointSet : Type) :=
  AddEquiv.ofBijective
    (relativeHurewiczAdd 2 sphereFourBasepointSet sphereFourBasepointInSet)
    sphereFourPointRelativeHurewiczAdd_bijective

/-- The canonical cubical sphere generator, viewed in fourth relative homotopy of the point
pair. -/
noncomputable def sphereFourPointRelativePiFourGenerator :
    π_rel 4 (Sph 4) sphereFourBasepointSet sphereFourBasepointInSet :=
  RelHomotopyGroup.jStar 4 (Sph 4) sphereFourBasepointSet sphereFourBasepointInSet
    (sphereGeneratorClass 4)

/-- The Hurewicz image of the canonical relative sphere generator has the same normalized
integer coordinate as its absolute Hurewicz image. -/
theorem sphereFourPointRelativeHurewicz_generator_coordinate :
    sphereFourPointRelativeHomologyFourIsoInt.hom
        (relativeHurewiczAdd 2 sphereFourBasepointSet sphereFourBasepointInSet
          (Additive.ofMul sphereFourPointRelativePiFourGenerator)) =
      absoluteHurewiczSphereGeneratorCoordinate 2 := by
  rw [relativeHurewiczAdd_ofMul]
  change sphereFourPointRelativeHomologyFourIsoInt.hom
      (relativeHurewicz 2 sphereFourBasepointSet sphereFourBasepointInSet
        (RelHomotopyGroup.jStar 4 (Sph 4) sphereFourBasepointSet
          sphereFourBasepointInSet (sphereGeneratorClass 4))) = _
  rw [relativeHurewicz_jStar]
  change (hgrpSphereSelfIsoZ 3).hom
      ((homologyIsoRelSingleton 2 (sphereBasepoint 4)).inv
        ((homologyIsoRelSingleton 2 (sphereBasepoint 4)).hom
          (absoluteHurewiczAdd 2 (sphereBasepoint 4)
            (Additive.ofMul (sphereGeneratorClass 4))))) = _
  rw [Iso.hom_inv_id_apply]
  rfl

/-- The canonical relative sphere generator has unit Hurewicz coordinate. -/
theorem sphereFourPointRelativeHurewicz_generator_coordinate_eq_one_or_neg_one :
    sphereFourPointRelativeHomologyFourIsoInt.hom
          (relativeHurewiczAdd 2 sphereFourBasepointSet sphereFourBasepointInSet
            (Additive.ofMul sphereFourPointRelativePiFourGenerator)) =
        (1 : ℤ) ∨
      sphereFourPointRelativeHomologyFourIsoInt.hom
          (relativeHurewiczAdd 2 sphereFourBasepointSet sphereFourBasepointInSet
            (Additive.ofMul sphereFourPointRelativePiFourGenerator)) =
        (-1 : ℤ) := by
  rw [sphereFourPointRelativeHurewicz_generator_coordinate]
  exact absoluteHurewiczSphereGeneratorCoordinate_eq_one_or_neg_one 2

/-- Naturality and the target Hurewicz isomorphism reduce bijectivity of the canonical relative
`π₄` collapse to bijectivity of its source-Hurewicz/homology-collapse composite. -/
theorem complexProjectivePlaneProjectiveLineRelativePiFourCollapse_bijective_iff_hurewicz :
    Function.Bijective
        complexProjectivePlaneProjectiveLineRelativePiFourCollapseAddHom ↔
      Function.Bijective
        (fun x : Additive
            (π_rel 4 (ComplexProjectiveModel 2)
              complexProjectivePlaneProjectiveLine
              complexProjectivePlaneProjectiveLineBasepoint) ↦
          complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
            (relativeHurewiczAdd 2 complexProjectivePlaneProjectiveLine
              complexProjectivePlaneProjectiveLineBasepoint x)) := by
  let f := complexProjectivePlaneProjectiveLineRelativePiFourCollapseAddHom
  let hT := relativeHurewiczAdd 2 sphereFourBasepointSet sphereFourBasepointInSet
  have hTbij : Function.Bijective hT :=
    sphereFourPointRelativeHurewiczAdd_bijective
  have hcomm :
      (hT ∘ f) =
        (fun x : Additive
            (π_rel 4 (ComplexProjectiveModel 2)
              complexProjectivePlaneProjectiveLine
              complexProjectivePlaneProjectiveLineBasepoint) ↦
          complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
            (relativeHurewiczAdd 2 complexProjectivePlaneProjectiveLine
              complexProjectivePlaneProjectiveLineBasepoint x)) := by
    funext x
    exact
      (complexProjectivePlaneProjectiveLineCollapse_relativeHurewiczAdd_naturality x).symm
  calc
    Function.Bijective f ↔ Function.Bijective (hT ∘ f) :=
      (Function.Bijective.of_comp_iff' hTbij f).symm
    _ ↔ _ := by rw [hcomm]

end Submission
