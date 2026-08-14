/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.SphereSuspension
import Submission.Topology.PuppeExactness

/-!
# Mapping cones of homotopy equivalences

Suspension preserves homotopy equivalences.  Combining that fact with homotopy coexactness and
the Puppe nullhomotopy shows that the mapping cone of a homotopy equivalence is contractible.
As a consequence, the mapping cone of the canonical second-Puppe comparison is contractible.
-/

open CategoryTheory
open scoped ContinuousMap Topology TopCat

noncomputable section

namespace Submission

namespace Susp

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- Unreduced quotient suspension preserves homotopy equivalences. -/
noncomputable def homotopyEquiv (e : X ≃ₕ Y) : Susp X ≃ₕ Susp Y where
  toFun := Susp.map e.toFun
  invFun := Susp.map e.invFun
  left_inv := by
    exact ⟨by
      simpa only [Susp.map_comp, Susp.map_id] using
        Susp.mapHomotopy (Classical.choice e.left_inv)⟩
  right_inv := by
    exact ⟨by
      simpa only [Susp.map_comp, Susp.map_id] using
        Susp.mapHomotopy (Classical.choice e.right_inv)⟩

end Susp

universe u

variable {A X : TopCat.{u}}

/-- The maintained pushout suspension preserves homotopy equivalences. -/
noncomputable def topologicalSuspensionHomotopyEquiv
    [Nonempty A] [Nonempty X]
    (e : ContinuousMap.HomotopyEquiv A X) :
    topologicalSuspension A ≃ₕ topologicalSuspension X :=
  (topologicalSuspensionHomeomorphSusp A).toHomotopyEquiv.trans
    ((Susp.homotopyEquiv e).trans
      (topologicalSuspensionHomeomorphSusp X).symm.toHomotopyEquiv)

/-- The forward map of the suspended homotopy equivalence is the maintained pushout map. -/
theorem topologicalSuspensionHomotopyEquiv_toFun
    [Nonempty A] [Nonempty X]
    (e : ContinuousMap.HomotopyEquiv A X) :
    (topologicalSuspensionHomotopyEquiv e).toFun =
      (topologicalSuspensionMap A (TopCat.ofHom e.toFun)).hom := by
  apply ContinuousMap.ext
  intro z
  apply (topologicalSuspensionHomeomorphSusp X).injective
  have h := ConcreteCategory.congr_hom
    (topologicalSuspensionToSusp_natural A (TopCat.ofHom e.toFun)) z
  change (topologicalSuspensionHomeomorphSusp X)
      ((topologicalSuspensionHomeomorphSusp X).symm
        (Susp.map e.toFun ((topologicalSuspensionHomeomorphSusp A) z))) =
    (topologicalSuspensionHomeomorphSusp X)
      (topologicalSuspensionMap A (TopCat.ofHom e.toFun) z)
  rw [Homeomorph.apply_symm_apply]
  exact h.symm

/-- Precomposition by a homotopy equivalence reflects and preserves nullhomotopies. -/
theorem nullhomotopic_homotopyEquiv_comp_iff
    {W : Type u} {Y Z : Type*}
    [TopologicalSpace W] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : W ≃ₕ Y) (f : C(Y, Z)) :
    (f.comp e.toFun).Nullhomotopic ↔ f.Nullhomotopic := by
  constructor
  · intro h
    have hback : ((f.comp e.toFun).comp e.invFun).Nullhomotopic :=
      h.comp_left e.invFun
    rw [ContinuousMap.comp_assoc] at hback
    have H : (f.comp (e.toFun.comp e.invFun)).Homotopic f := by
      exact ⟨by
        simpa using (ContinuousMap.Homotopy.refl f).comp
          (Classical.choice e.right_inv)⟩
    obtain ⟨z, hz⟩ := hback
    exact ⟨z, H.symm.trans hz⟩
  · exact fun h ↦ h.comp_left e.toFun

/-- The mapping cone of a homotopy equivalence is contractible. -/
theorem contractibleSpace_topologicalMappingCone_of_homotopyEquiv
    [Nonempty A] [Nonempty X]
    (e : ContinuousMap.HomotopyEquiv A X) :
    ContractibleSpace
      (topologicalMappingCone (TopCat.ofHom e.toFun)) := by
  let f : A ⟶ X := TopCat.ofHom e.toFun
  apply (contractible_iff_id_nullhomotopic (topologicalMappingCone f)).mpr
  have hcone :
      (topologicalConeBaseIncl A ≫
        topologicalMappingConeConeIncl f).hom.Nullhomotopic :=
    ((id_nullhomotopic (topologicalCone A)).comp_left
      (topologicalConeBaseIncl A).hom).comp_right
        (topologicalMappingConeConeIncl f).hom
  have hrestrictComp :
      (f ≫ topologicalMappingConeIncl f).hom.Nullhomotopic := by
    rw [topologicalMappingCone_condition]
    exact hcone
  have hrestrict : (topologicalMappingConeIncl f).hom.Nullhomotopic :=
    (nullhomotopic_homotopyEquiv_comp_iff e
      (topologicalMappingConeIncl f).hom).mp hrestrictComp
  obtain ⟨k, ⟨Hfactor⟩⟩ :=
    (exists_topologicalSuspension_homotopy_factorization_iff_nullhomotopic_restriction
      f (𝟙 (topologicalMappingCone f))).mpr (by
        simpa only [Category.comp_id] using hrestrict)
  let eSusp := topologicalSuspensionHomotopyEquiv e
  have hPuppe :
      (eSusp.toFun.comp (topologicalMappingConeCollapse f).hom).Nullhomotopic := by
    change ((topologicalSuspensionHomotopyEquiv e).toFun.comp
      (topologicalMappingConeCollapse f).hom).Nullhomotopic
    rw [topologicalSuspensionHomotopyEquiv_toFun]
    exact topologicalMappingConeCollapse_suspensionMap_nullhomotopic f
  have hcollapse :
      (topologicalMappingConeCollapse f).hom.Nullhomotopic :=
    (nullhomotopic_comp_homotopyEquiv_iff
      (topologicalMappingConeCollapse f).hom eSusp).mp hPuppe
  have hfactor : (topologicalMappingConeCollapse f ≫ k).hom.Nullhomotopic :=
    hcollapse.comp_right k.hom
  obtain ⟨z, hz⟩ := hfactor
  exact ⟨z, ⟨Hfactor.symm.trans (Classical.choice hz)⟩⟩

/-- A morphism whose underlying continuous map is the forward map of a homotopy equivalence
has contractible mapping cone. -/
theorem contractibleSpace_topologicalMappingCone_of_homotopyEquiv_toFun_eq
    [Nonempty A] [Nonempty X]
    (f : A ⟶ X) (e : ContinuousMap.HomotopyEquiv A X)
    (he : e.toFun = f.hom) :
    ContractibleSpace (topologicalMappingCone f) := by
  have hmap : TopCat.ofHom e.toFun = f := by
    apply TopCat.hom_ext
    exact he
  rw [← hmap]
  exact contractibleSpace_topologicalMappingCone_of_homotopyEquiv e

/-- The next mapping cone after the second Puppe comparison is contractible. -/
theorem contractibleSpace_topologicalThirdMappingCone
    (f : A ⟶ X) :
    ContractibleSpace
      (topologicalMappingCone (topologicalSecondMappingConeToSuspension f)) := by
  letI : Nonempty (topologicalSuspension X) :=
    ⟨topologicalSuspensionPointIncl X PUnit.unit⟩
  letI : Nonempty
      (topologicalMappingCone (topologicalMappingConeCollapse f)) :=
    ⟨topologicalMappingConeIncl (topologicalMappingConeCollapse f)
      (topologicalSuspensionPointIncl A PUnit.unit)⟩
  exact contractibleSpace_topologicalMappingCone_of_homotopyEquiv_toFun_eq
    (topologicalSecondMappingConeToSuspension f)
    (topologicalSecondMappingConeHomotopyEquivSuspension f) rfl

/-- The mapping cone after the second Puppe comparison is path connected. -/
theorem pathConnectedSpace_topologicalThirdMappingCone
    (f : A ⟶ X) :
    PathConnectedSpace
      (topologicalMappingCone (topologicalSecondMappingConeToSuspension f)) := by
  letI : ContractibleSpace
      (topologicalMappingCone (topologicalSecondMappingConeToSuspension f)) :=
    contractibleSpace_topologicalThirdMappingCone f
  infer_instance

end Submission
