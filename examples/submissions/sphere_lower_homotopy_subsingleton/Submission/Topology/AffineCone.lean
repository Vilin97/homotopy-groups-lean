/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.MappingCone
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Radial affine models of compact topological cones

Let `A` be a compact nonempty subset of a finite standard simplex, contained in the face opposite
a chosen vertex.  This file identifies the abstract topological cone on `A` with the radial affine
cone from that vertex to `A`.  Barycentric evaluation at the chosen vertex recovers the cone
height, which gives injectivity without constructing a discontinuous-looking normalized inverse.

The comparison has explicit formulas on the cylinder, cone point, and base.  It is the point-set
bridge needed to compare realized finite combinatorial cones with abstract topological cones once
their affine carriers have been identified.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology TopCat

namespace Submission

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The point at height `t` on the affine segment from `a` to the chosen simplex vertex. -/
def affineConePoint (A : Set (stdSimplex ℝ V)) (apex : V)
    (a : A) (t : TopCat.I.{0}) : stdSimplex ℝ V :=
  ⟨AffineMap.lineMap a.1.1 (stdSimplex.vertex apex).1
      (TopCat.I.homeomorph t : ℝ),
    (convex_stdSimplex ℝ V).lineMap_mem a.1.2
      (stdSimplex.vertex apex).2 (TopCat.I.homeomorph t).2⟩

/-- Coordinate formula for a radial affine-cone point. -/
theorem affineConePoint_apply (A : Set (stdSimplex ℝ V)) (apex : V)
    (a : A) (t : TopCat.I.{0}) (i : V) :
    affineConePoint A apex a t i =
      (1 - (TopCat.I.homeomorph t : ℝ)) * a.1 i +
        (TopCat.I.homeomorph t : ℝ) * (stdSimplex.vertex apex : V → ℝ) i := by
  change AffineMap.lineMap a.1.1 (stdSimplex.vertex apex).1
      (TopCat.I.homeomorph t : ℝ) i = _
  rw [AffineMap.lineMap_apply_module]
  rfl

/-- When the base lies opposite `apex`, its apex coordinate is exactly the cone height. -/
theorem affineConePoint_apex (A : Set (stdSimplex ℝ V)) (apex : V)
    (hA : ∀ a ∈ A, a apex = 0) (a : A) (t : TopCat.I.{0}) :
    affineConePoint A apex a t apex = (TopCat.I.homeomorph t : ℝ) := by
  rw [affineConePoint_apply, hA a.1 a.2]
  simp

/-- Height zero recovers the base point. -/
theorem affineConePoint_zero (A : Set (stdSimplex ℝ V)) (apex : V)
    (a : A) : affineConePoint A apex a 0 = a.1 := by
  apply Subtype.ext
  ext i
  change AffineMap.lineMap a.1.1 (stdSimplex.vertex apex).1
      (TopCat.I.homeomorph (0 : TopCat.I.{0}) : ℝ) i = a.1.1 i
  rw [AffineMap.lineMap_apply_module, TopCat.I.homeomorph_zero]
  simp

/-- Height one is the chosen simplex vertex. -/
theorem affineConePoint_one (A : Set (stdSimplex ℝ V)) (apex : V)
    (a : A) : affineConePoint A apex a 1 = stdSimplex.vertex apex := by
  apply Subtype.ext
  ext i
  change AffineMap.lineMap a.1.1 (stdSimplex.vertex apex).1
      (TopCat.I.homeomorph (1 : TopCat.I.{0}) : ℝ) i =
    (stdSimplex.vertex apex).1 i
  rw [AffineMap.lineMap_apply_module, TopCat.I.homeomorph_one]
  simp

/-- The radial affine cone from a simplex vertex to a subset of the simplex. -/
abbrev affineConeCarrier (A : Set (stdSimplex ℝ V)) (apex : V) :=
  {x : stdSimplex ℝ V // ∃ a : A, ∃ t : TopCat.I.{0}, x = affineConePoint A apex a t}

/-- The radial map from the cone cylinder onto its affine carrier. -/
def affineConeCylinderToCarrier (A : Set (stdSimplex ℝ V)) (apex : V)
    (p : A × TopCat.I.{0}) : affineConeCarrier A apex :=
  ⟨affineConePoint A apex p.1 p.2, p.1, p.2, rfl⟩

/-- The radial cone-cylinder map is continuous. -/
theorem continuous_affineConeCylinderToCarrier
    (A : Set (stdSimplex ℝ V)) (apex : V) :
    Continuous (affineConeCylinderToCarrier A apex) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous fun p : A × TopCat.I.{0} ↦
    AffineMap.lineMap p.1.1.1 (stdSimplex.vertex apex).1
      (TopCat.I.homeomorph p.2 : ℝ) i
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

/-- The radial cone-cylinder map as a morphism of topological spaces. -/
def affineConeCylinderToCarrierTopCat
    (A : Set (stdSimplex ℝ V)) (apex : V) :
    TopCat.of A ⊗ TopCat.I.{0} ⟶ TopCat.of (affineConeCarrier A apex) :=
  TopCat.ofHom ⟨affineConeCylinderToCarrier A apex,
    continuous_affineConeCylinderToCarrier A apex⟩

/-- The common affine image of the collapsed top of a nonempty cone cylinder. -/
def affineConeVertex (A : Set (stdSimplex ℝ V)) (apex : V)
    (hA : A.Nonempty) : affineConeCarrier A apex :=
  ⟨stdSimplex.vertex apex, ⟨hA.choose, hA.choose_spec⟩, 1,
    (affineConePoint_one A apex ⟨hA.choose, hA.choose_spec⟩).symm⟩

/-- Descend the radial cylinder map through the abstract topological cone. -/
def affineTopologicalConeToCarrier
    (A : Set (stdSimplex ℝ V)) (apex : V) (hA : A.Nonempty) :
    topologicalCone (TopCat.of A) ⟶ TopCat.of (affineConeCarrier A apex) :=
  topologicalConeDesc (TopCat.of A)
    (affineConeCylinderToCarrierTopCat A apex)
    (TopCat.const (affineConeVertex A apex hA))
    (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro a
      apply Subtype.ext
      exact affineConePoint_one A apex a)

/-- Formula for the descended map on a cone-cylinder point. -/
@[simp]
theorem affineTopologicalConeToCarrier_cylinder
    (A : Set (stdSimplex ℝ V)) (apex : V) (hA : A.Nonempty)
    (a : A) (t : TopCat.I.{0}) :
    affineTopologicalConeToCarrier A apex hA
        (topologicalConeCylinderIncl (TopCat.of A) (a, t)) =
      affineConeCylinderToCarrier A apex (a, t) := by
  exact ConcreteCategory.congr_hom
    (topologicalConeCylinderIncl_desc (TopCat.of A)
      (affineConeCylinderToCarrierTopCat A apex)
      (TopCat.const (affineConeVertex A apex hA)) _) (a, t)

/-- Formula for the descended map on the cone point. -/
@[simp]
theorem affineTopologicalConeToCarrier_point
    (A : Set (stdSimplex ℝ V)) (apex : V) (hA : A.Nonempty)
    (u : PUnit) :
    affineTopologicalConeToCarrier A apex hA
        (topologicalConePointIncl (TopCat.of A) u) =
      affineConeVertex A apex hA := by
  exact ConcreteCategory.congr_hom
    (topologicalConePointIncl_desc (TopCat.of A)
      (affineConeCylinderToCarrierTopCat A apex)
      (TopCat.const (affineConeVertex A apex hA)) _) u

/-- Every point of the affine cone carrier has radial cylinder coordinates. -/
theorem affineConeCylinderToCarrier_surjective
    (A : Set (stdSimplex ℝ V)) (apex : V) :
    Function.Surjective (affineConeCylinderToCarrier A apex) := by
  intro x
  obtain ⟨a, t, hx⟩ := x.2
  refine ⟨(a, t), ?_⟩
  apply Subtype.ext
  exact hx.symm

/-- The descended radial map is surjective. -/
theorem affineTopologicalConeToCarrier_surjective
    (A : Set (stdSimplex ℝ V)) (apex : V) (hA : A.Nonempty) :
    Function.Surjective (affineTopologicalConeToCarrier A apex hA) := by
  intro x
  obtain ⟨c, rfl⟩ := affineConeCylinderToCarrier_surjective A apex x
  exact ⟨topologicalConeCylinderIncl (TopCat.of A) c, by
    rcases c with ⟨a, t⟩
    exact affineTopologicalConeToCarrier_cylinder A apex hA a t⟩

omit [DecidableEq V] in
/-- The topological cone on a compact simplex subset is compact. -/
theorem affineConeCompactSpace
    (A : Set (stdSimplex ℝ V)) [CompactSpace A] :
    CompactSpace (topologicalCone (TopCat.of A)) := by
  letI : CompactSpace TopCat.I.{0} :=
    TopCat.I.homeomorph.symm.compactSpace
  letI : CompactSpace
      ((TopCat.of A ⊗ TopCat.I.{0} : TopCat.{0}) : Type) := by
    change CompactSpace (A × TopCat.I.{0})
    infer_instance
  letI : CompactSpace
      (((TopCat.of A ⊗ TopCat.I.{0} : TopCat.{0}) : Type) ⊕
        ((𝟙_ TopCat.{0} : TopCat.{0}) : Type)) := by
    change CompactSpace ((A × TopCat.I.{0}) ⊕ PUnit)
    infer_instance
  exact Function.Surjective.compactSpace
    (topologicalConeSumDesc_isQuotientMap (TopCat.of A)).continuous
    (topologicalConeSumDesc_isQuotientMap (TopCat.of A)).surjective

/-- A cylinder point mapping to the affine vertex is the abstract cone point. -/
theorem affineConeCylinderIncl_eq_point_of_map_eq_vertex
    (A : Set (stdSimplex ℝ V)) (apex : V)
    (hzero : ∀ a ∈ A, a apex = 0) (hA : A.Nonempty)
    (c : A × TopCat.I.{0})
    (h : affineConeCylinderToCarrier A apex c =
      affineConeVertex A apex hA) :
    topologicalConeCylinderIncl (TopCat.of A) c =
      topologicalConePointIncl (TopCat.of A) PUnit.unit := by
  have hapex := congrArg
    (fun x : affineConeCarrier A apex ↦ (x.1 : V → ℝ) apex) h
  have htReal : (TopCat.I.homeomorph c.2 : ℝ) = 1 := by
    simpa [affineConeCylinderToCarrier, affineConeVertex,
      affineConePoint_apex A apex hzero] using hapex
  have ht : c.2 = 1 := by
    apply TopCat.I.homeomorph.injective
    apply Subtype.ext
    simpa using htReal
  have htop :
      (TopCat.ι₁ : TopCat.of A ⟶ TopCat.of A ⊗ TopCat.I.{0}) ≫
          topologicalConeCylinderIncl (TopCat.of A) =
        toUnit (TopCat.of A) ≫
          topologicalConePointIncl (TopCat.of A) :=
    pushout.condition
  have hc : c = (c.1, (1 : TopCat.I.{0})) := Prod.ext rfl ht
  rw [hc]
  change (topologicalConeCylinderIncl (TopCat.of A)).hom
      (c.1, (1 : TopCat.I.{0})) =
    (topologicalConePointIncl (TopCat.of A)).hom PUnit.unit
  convert ConcreteCategory.congr_hom htop c.1 using 1 <;> rfl

/-- Away from the affine vertex, radial cylinder coordinates are unique. -/
theorem affineConeCylinderToCarrier_eq_imp_of_ne_vertex
    (A : Set (stdSimplex ℝ V)) (apex : V)
    (hzero : ∀ a ∈ A, a apex = 0) (hA : A.Nonempty)
    (c d : A × TopCat.I.{0})
    (h : affineConeCylinderToCarrier A apex c =
      affineConeCylinderToCarrier A apex d)
    (hc : affineConeCylinderToCarrier A apex c ≠
      affineConeVertex A apex hA) :
    c = d := by
  have hapex := congrArg
    (fun x : affineConeCarrier A apex ↦ (x.1 : V → ℝ) apex) h
  have hreal : (TopCat.I.homeomorph c.2 : ℝ) =
      (TopCat.I.homeomorph d.2 : ℝ) := by
    simpa [affineConeCylinderToCarrier,
      affineConePoint_apex A apex hzero] using hapex
  have ht : c.2 = d.2 := by
    apply TopCat.I.homeomorph.injective
    apply Subtype.ext
    exact hreal
  have hcoef : 1 - (TopCat.I.homeomorph c.2 : ℝ) ≠ 0 := by
    intro hcoef
    have htReal : (TopCat.I.homeomorph c.2 : ℝ) = 1 :=
      (sub_eq_zero.mp hcoef).symm
    have htOne : c.2 = 1 := by
      apply TopCat.I.homeomorph.injective
      apply Subtype.ext
      simpa using htReal
    apply hc
    apply Subtype.ext
    change affineConePoint A apex c.1 c.2 = stdSimplex.vertex apex
    rw [htOne]
    exact affineConePoint_one A apex c.1
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    funext i
    have hi := congrArg
      (fun x : affineConeCarrier A apex ↦ (x.1 : V → ℝ) i) h
    simp only [affineConeCylinderToCarrier, affineConePoint_apply] at hi
    rw [← hreal] at hi
    exact mul_left_cancel₀ hcoef (add_right_cancel hi)
  · exact ht

/-- Barycentric height and radial uniqueness make the descended map injective. -/
theorem affineTopologicalConeToCarrier_injective
    (A : Set (stdSimplex ℝ V)) (apex : V)
    (hzero : ∀ a ∈ A, a apex = 0) (hA : A.Nonempty) :
    Function.Injective (affineTopologicalConeToCarrier A apex hA) := by
  intro x y h
  obtain ⟨sx, rfl⟩ := (topologicalConeSumDesc_isQuotientMap (TopCat.of A)).surjective x
  obtain ⟨sy, rfl⟩ := (topologicalConeSumDesc_isQuotientMap (TopCat.of A)).surjective y
  rcases sx with c | u <;> rcases sy with d | v
  · rcases c with ⟨a, t⟩
    rcases d with ⟨b, s⟩
    have hrad : affineConeCylinderToCarrier A apex (a, t) =
        affineConeCylinderToCarrier A apex (b, s) := by
      exact (affineTopologicalConeToCarrier_cylinder A apex hA a t).symm.trans
        (h.trans (affineTopologicalConeToCarrier_cylinder A apex hA b s))
    by_cases hc : affineConeCylinderToCarrier A apex (a, t) = affineConeVertex A apex hA
    · have hd : affineConeCylinderToCarrier A apex (b, s) = affineConeVertex A apex hA :=
        hrad.symm.trans hc
      exact (affineConeCylinderIncl_eq_point_of_map_eq_vertex
        A apex hzero hA (a, t) hc).trans
        (affineConeCylinderIncl_eq_point_of_map_eq_vertex
          A apex hzero hA (b, s) hd).symm
    · have hcd := affineConeCylinderToCarrier_eq_imp_of_ne_vertex
        A apex hzero hA (a, t) (b, s) hrad hc
      cases hcd
      rfl
  · rcases c with ⟨a, t⟩
    have hrad : affineConeCylinderToCarrier A apex (a, t) =
        affineConeVertex A apex hA := by
      exact (affineTopologicalConeToCarrier_cylinder A apex hA a t).symm.trans
        (h.trans (affineTopologicalConeToCarrier_point A apex hA v))
    cases v
    exact affineConeCylinderIncl_eq_point_of_map_eq_vertex
      A apex hzero hA (a, t) hrad
  · rcases d with ⟨b, s⟩
    have hrad : affineConeVertex A apex hA =
        affineConeCylinderToCarrier A apex (b, s) := by
      exact (affineTopologicalConeToCarrier_point A apex hA u).symm.trans
        (h.trans (affineTopologicalConeToCarrier_cylinder A apex hA b s))
    cases u
    exact (affineConeCylinderIncl_eq_point_of_map_eq_vertex
      A apex hzero hA (b, s) hrad.symm).symm
  · cases u
    cases v
    rfl

/-- A compact abstract topological cone is homeomorphic to its radial affine carrier. -/
def affineTopologicalConeHomeomorphCarrier
    (A : Set (stdSimplex ℝ V)) (apex : V)
    [CompactSpace A] (hzero : ∀ a ∈ A, a apex = 0) (hA : A.Nonempty) :
    topologicalCone (TopCat.of A) ≃ₜ affineConeCarrier A apex := by
  letI : CompactSpace (topologicalCone (TopCat.of A)) :=
    affineConeCompactSpace A
  letI : T2Space (affineConeCarrier A apex) := by infer_instance
  exact IsHomeomorph.homeomorph (affineTopologicalConeToCarrier A apex hA) <|
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨(affineTopologicalConeToCarrier A apex hA).hom.continuous,
        affineTopologicalConeToCarrier_injective A apex hzero hA,
        affineTopologicalConeToCarrier_surjective A apex hA⟩

/-- The affine-cone homeomorphism has the stated radial cylinder formula. -/
@[simp]
theorem affineTopologicalConeHomeomorphCarrier_cylinder
    (A : Set (stdSimplex ℝ V)) (apex : V) [CompactSpace A]
    (hzero : ∀ a ∈ A, a apex = 0) (hA : A.Nonempty)
    (a : A) (t : TopCat.I.{0}) :
    affineTopologicalConeHomeomorphCarrier A apex hzero hA
        (topologicalConeCylinderIncl (TopCat.of A) (a, t)) =
      affineConeCylinderToCarrier A apex (a, t) := by
  change affineTopologicalConeToCarrier A apex hA
      (topologicalConeCylinderIncl (TopCat.of A) (a, t)) = _
  exact affineTopologicalConeToCarrier_cylinder A apex hA a t

/-- The affine-cone homeomorphism sends the abstract cone point to the simplex vertex. -/
@[simp]
theorem affineTopologicalConeHomeomorphCarrier_point
    (A : Set (stdSimplex ℝ V)) (apex : V) [CompactSpace A]
    (hzero : ∀ a ∈ A, a apex = 0) (hA : A.Nonempty) (u : PUnit) :
    affineTopologicalConeHomeomorphCarrier A apex hzero hA
        (topologicalConePointIncl (TopCat.of A) u) =
      affineConeVertex A apex hA := by
  change affineTopologicalConeToCarrier A apex hA
      (topologicalConePointIncl (TopCat.of A) u) = _
  exact affineTopologicalConeToCarrier_point A apex hA u

/-- The affine-cone homeomorphism restricts at height zero to the base carrier. -/
@[simp]
theorem affineTopologicalConeHomeomorphCarrier_base
    (A : Set (stdSimplex ℝ V)) (apex : V) [CompactSpace A]
    (hzero : ∀ a ∈ A, a apex = 0) (hA : A.Nonempty) (a : A) :
    affineTopologicalConeHomeomorphCarrier A apex hzero hA
        (topologicalConeBaseIncl (TopCat.of A) a) =
      affineConeCylinderToCarrier A apex (a, 0) := by
  exact affineTopologicalConeHomeomorphCarrier_cylinder A apex hzero hA a 0

end Submission
