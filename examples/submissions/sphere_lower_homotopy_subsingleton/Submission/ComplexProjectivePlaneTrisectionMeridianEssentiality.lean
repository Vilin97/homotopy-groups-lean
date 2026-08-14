/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionMeridianTopology
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting

/-!
# Circle-valued cocycle realizations and essential trisection meridians

An alternating integral edge cocycle that is closed on every triangle determines compatible
affine real potentials on the facets of a finite ordered complex.  Reducing those potentials
modulo the integers glues them into a continuous map from the geometric realization to the unit
additive circle.  On an oriented realized edge, the resulting map is exactly
`t ↦ t * cochain first second` modulo integers.

The covering `ℝ → ℝ ⧸ ℤ` detects the winding of these edge paths.  Applied to the two explicit
central-torus cocycles, it proves that all three trisection meridian circuits are essential on the
central interface: their detected windings are respectively `1`, `1`, and `-1`.  The file records
nonidentity witnesses both in `FundamentalGroup` and in the cubical `HomotopyGroup.Pi 1`, first on
the affine carrier and then on the actual simplicial realization.  For each exact boundary-circle
subcomplex, its concrete meridian class maps to a nonidentity class under the inclusion into the
central interface, in both fundamental-group presentations.  Since the already-constructed disk
nullhomotopies kill these same classes in the pairwise solid tori, all three induced maps from the
central-interface `π₁` are noninjective.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace Submission.FiniteOrderedComplex

variable {V : Type} [Fintype V] [LinearOrder V]

omit [Fintype V] in
theorem edgeCochain_triangle_sum_eq_zero_of_subset_facet
    {facets : Finset (Finset V)} {cochain : V → V → ℤ}
    (halternating : ComplexProjectivePlaneTriangulation.IsAlternatingEdgeCochain cochain)
    (hclosed : ComplexProjectivePlaneTriangulation.IsClosedEdgeCochain facets cochain)
    (first second third : V) (facet : Finset V) (hfacet : facet ∈ facets)
    (hsubset : {first, second, third} ⊆ facet) :
    cochain first second + cochain second third + cochain third first = 0 := by
  by_cases hfirstSecond : first = second
  · subst second
    have hself : cochain first first = 0 := by
      have h := halternating first first
      omega
    rw [hself, zero_add, halternating third first]
    omega
  by_cases hsecondThird : second = third
  · subst third
    have hself : cochain second second = 0 := by
      have h := halternating second second
      omega
    rw [hself, add_zero, halternating second first]
    omega
  by_cases hthirdFirst : third = first
  · subst third
    have hself : cochain first first = 0 := by
      have h := halternating first first
      omega
    rw [hself, add_zero, halternating second first]
    omega
  apply hclosed first second third
  apply mem_facesOfCard_of_isFace
  · exact ⟨facet, hfacet, hsubset⟩
  · have hfirstNotMem : first ∉ ({second, third} : Finset V) := by
      simp [hfirstSecond, Ne.symm hthirdFirst]
    have hsecondNotMem : second ∉ ({third} : Finset V) := by
      simp [hsecondThird]
    rw [Finset.card_insert_of_notMem hfirstNotMem,
      Finset.card_insert_of_notMem hsecondNotMem]
    simp

variable {facets : Finset (Finset V)}

def facetCocycleBase (i : NonemptyFacetIndex facets) : V :=
  i.1.min' i.2.2

omit [Fintype V] in
theorem facetCocycleBase_mem (i : NonemptyFacetIndex facets) :
    facetCocycleBase i ∈ i.1 :=
  Finset.min'_mem i.1 i.2.2

def facetCocycleLift (cochain : V → V → ℤ)
    (i : NonemptyFacetIndex facets) (y : simplexFaceCarrier i.1) : ℝ :=
  ∑ v, y.1.1 v * (cochain (facetCocycleBase i) v : ℝ)

theorem continuous_facetCocycleLift (cochain : V → V → ℤ)
    (i : NonemptyFacetIndex facets) :
    Continuous (facetCocycleLift cochain i) := by
  apply continuous_finsetSum
  intro v _
  exact ((continuous_apply v).comp
    (continuous_subtype_val.comp continuous_subtype_val)).mul continuous_const

def facetCocycleCircleMap (cochain : V → V → ℤ)
    (i : NonemptyFacetIndex facets) :
    C(simplexFaceCarrier i.1, UnitAddCircle) :=
  ⟨fun y ↦ (facetCocycleLift cochain i y : UnitAddCircle),
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      (continuous_facetCocycleLift cochain i)⟩

theorem exists_common_nonzero_vertex
    (i k : NonemptyFacetIndex facets)
    (y : simplexFaceCarrier i.1) (z : simplexFaceCarrier k.1)
    (hyz : y.1 = z.1) :
    ∃ w, w ∈ i.1 ∧ w ∈ k.1 ∧ y.1.1 w ≠ 0 := by
  have hexists : ∃ w, y.1.1 w ≠ 0 := by
    have hsum : (∑ w, y.1.1 w) ≠ 0 := by
      have hsumEq : (∑ w, y.1.1 w) = 1 := y.1.2.2
      rw [hsumEq]
      norm_num
    obtain ⟨w, _, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    exact ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hexists
  refine ⟨w, ?_, ?_, hw⟩
  · by_contra hwi
    exact hw (y.2 w hwi)
  · by_contra hwk
    apply hw
    rw [hyz]
    exact z.2 w hwk

omit [Fintype V] in
theorem facetCocycleBase_difference
    {cochain : V → V → ℤ}
    (halternating : ComplexProjectivePlaneTriangulation.IsAlternatingEdgeCochain cochain)
    (hclosed : ComplexProjectivePlaneTriangulation.IsClosedEdgeCochain facets cochain)
    (i k : NonemptyFacetIndex facets) (w v : V)
    (hwi : w ∈ i.1) (hwk : w ∈ k.1) (hvi : v ∈ i.1) (hvk : v ∈ k.1) :
    cochain (facetCocycleBase i) v -
        cochain (facetCocycleBase k) v =
      cochain (facetCocycleBase i) w -
        cochain (facetCocycleBase k) w := by
  have hi := edgeCochain_triangle_sum_eq_zero_of_subset_facet
    halternating hclosed (facetCocycleBase i) w v i.1 i.2.1
      (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with (rfl | rfl | rfl)
        · exact facetCocycleBase_mem i
        · exact hwi
        · exact hvi)
  have hk := edgeCochain_triangle_sum_eq_zero_of_subset_facet
    halternating hclosed (facetCocycleBase k) w v k.1 k.2.1
      (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with (rfl | rfl | rfl)
        · exact facetCocycleBase_mem k
        · exact hwk
        · exact hvk)
  rw [halternating v (facetCocycleBase i)] at hi
  rw [halternating v (facetCocycleBase k)] at hk
  omega

theorem facetCocycleLift_sub_eq_int
    {cochain : V → V → ℤ}
    (halternating : ComplexProjectivePlaneTriangulation.IsAlternatingEdgeCochain cochain)
    (hclosed : ComplexProjectivePlaneTriangulation.IsClosedEdgeCochain facets cochain)
    (i k : NonemptyFacetIndex facets)
    (y : simplexFaceCarrier i.1) (z : simplexFaceCarrier k.1)
    (hyz : y.1 = z.1) (w : V) (hwi : w ∈ i.1) (hwk : w ∈ k.1) :
    facetCocycleLift cochain i y - facetCocycleLift cochain k z =
      ((cochain (facetCocycleBase i) w -
        cochain (facetCocycleBase k) w : ℤ) : ℝ) := by
  rw [facetCocycleLift, facetCocycleLift, ← Finset.sum_sub_distrib]
  calc
    ∑ v, (y.1.1 v * (cochain (facetCocycleBase i) v : ℝ) -
        z.1.1 v * (cochain (facetCocycleBase k) v : ℝ)) =
        ∑ v, y.1.1 v *
          ((cochain (facetCocycleBase i) w -
            cochain (facetCocycleBase k) w : ℤ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hvzero : y.1.1 v = 0
      · rw [hvzero]
        have hzv : z.1.1 v = 0 := by rw [← hyz, hvzero]
        rw [hzv]
        ring
      · have hvi : v ∈ i.1 := by
          by_contra hv
          exact hvzero (y.2 v hv)
        have hvk : v ∈ k.1 := by
          by_contra hv
          apply hvzero
          rw [hyz]
          exact z.2 v hv
        have hdiff := facetCocycleBase_difference
          halternating hclosed i k w v hwi hwk hvi hvk
        have hdiffReal :
            (cochain (facetCocycleBase i) v : ℝ) -
                (cochain (facetCocycleBase k) v : ℝ) =
              ((cochain (facetCocycleBase i) w -
                cochain (facetCocycleBase k) w : ℤ) : ℝ) := by
          exact_mod_cast hdiff
        rw [← hyz]
        calc
          y.1.1 v * (cochain (facetCocycleBase i) v : ℝ) -
              y.1.1 v * (cochain (facetCocycleBase k) v : ℝ) =
            y.1.1 v * ((cochain (facetCocycleBase i) v : ℝ) -
              (cochain (facetCocycleBase k) v : ℝ)) := by ring
          _ = _ := by rw [hdiffReal]
    _ = _ := by
      rw [← Finset.sum_mul]
      change (∑ v, y.1.1 v) *
          ((cochain (facetCocycleBase i) w -
            cochain (facetCocycleBase k) w : ℤ) : ℝ) = _
      have hsumEq : (∑ v, y.1.1 v) = 1 := y.1.2.2
      rw [hsumEq, one_mul]

theorem facetCocycleCircleMap_compatible
    {cochain : V → V → ℤ}
    (halternating : ComplexProjectivePlaneTriangulation.IsAlternatingEdgeCochain cochain)
    (hclosed : ComplexProjectivePlaneTriangulation.IsClosedEdgeCochain facets cochain)
    (i k : NonemptyFacetIndex facets)
    (y : simplexFaceCarrier i.1) (z : simplexFaceCarrier k.1)
    (hyz : y.1 = z.1) :
    facetCocycleCircleMap cochain i y =
      facetCocycleCircleMap cochain k z := by
  obtain ⟨w, hwi, hwk, _⟩ := exists_common_nonzero_vertex i k y z hyz
  change (facetCocycleLift cochain i y : UnitAddCircle) =
    (facetCocycleLift cochain k z : UnitAddCircle)
  rw [QuotientAddGroup.eq_iff_sub_mem,
    facetCocycleLift_sub_eq_int halternating hclosed i k y z hyz w hwi hwk]
  exact AddSubgroup.intCast_mem_zmultiples_one _

def integralCocycleCircleMap
    (cochain : V → V → ℤ)
    (halternating : ComplexProjectivePlaneTriangulation.IsAlternatingEdgeCochain cochain)
    (hclosed : ComplexProjectivePlaneTriangulation.IsClosedEdgeCochain facets cochain) :
    C(facetFamilyCarrier facets, UnitAddCircle) :=
  glueFacetFamily facets (facetCocycleCircleMap cochain)
    (facetCocycleCircleMap_compatible halternating hclosed)

/-- The cocycle circle map transported from the affine carrier to geometric realization. -/
def integralCocycleRealizationCircleMap
    (cochain : V → V → ℤ)
    (halternating : ComplexProjectivePlaneTriangulation.IsAlternatingEdgeCochain cochain)
  (hclosed : ComplexProjectivePlaneTriangulation.IsClosedEdgeCochain facets cochain) :
    C(SSet.toTop.obj (orderedSSet facets), UnitAddCircle) :=
  (integralCocycleCircleMap cochain halternating hclosed).comp
    ⟨orderedRealizationHomeomorphFacetFamilyCarrier facets,
      (orderedRealizationHomeomorphFacetFamilyCarrier facets).continuous⟩

/-- On a listed facet, the global cocycle map is represented by its affine local lift. -/
@[simp]
theorem integralCocycleCircleMap_face
    (cochain : V → V → ℤ)
    (halternating : ComplexProjectivePlaneTriangulation.IsAlternatingEdgeCochain cochain)
    (hclosed : ComplexProjectivePlaneTriangulation.IsClosedEdgeCochain facets cochain)
    (i : NonemptyFacetIndex facets) (y : simplexFaceCarrier i.1) :
    integralCocycleCircleMap cochain halternating hclosed
        (faceCarrierToFacetFamilyCarrier facets i y) =
      facetCocycleCircleMap cochain i y := by
  exact glueFacetFamily_face facets (facetCocycleCircleMap cochain)
    (facetCocycleCircleMap_compatible halternating hclosed) i y

/-- A vertex of an affine simplex face. -/
def simplexFaceVertex (facet : Finset V) (v : V) (hv : v ∈ facet) :
    simplexFaceCarrier facet :=
  ⟨stdSimplex.vertex v, by
    intro w hw
    rw [stdSimplex.vertex_coe]
    simp only [Pi.single_apply]
    rw [if_neg]
    exact fun hvw ↦ hw (hvw ▸ hv)⟩

/-- The straight affine path between two vertices of one face. -/
def simplexFaceEdgePath (facet : Finset V)
    (first second : V) (hfirst : first ∈ facet) (hsecond : second ∈ facet) :
    Path (simplexFaceVertex facet first hfirst)
      (simplexFaceVertex facet second hsecond) where
  toFun t := ⟨⟨AffineMap.lineMap (stdSimplex.vertex first).1
      (stdSimplex.vertex second).1 (t : ℝ),
      (convex_stdSimplex ℝ V).lineMap_mem (stdSimplex.vertex first).2
        (stdSimplex.vertex second).2 t.2⟩, by
    intro w hw
    have hfirstw : first ≠ w := fun h ↦ hw (h ▸ hfirst)
    have hsecondw : second ≠ w := fun h ↦ hw (h ▸ hsecond)
    change AffineMap.lineMap (stdSimplex.vertex first).1
      (stdSimplex.vertex second).1 (t : ℝ) w = 0
    rw [AffineMap.lineMap_apply_module]
    simp [hfirstw, hsecondw]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (Path.segment (stdSimplex.vertex first).1
      (stdSimplex.vertex second).1).continuous
  source' := by
    change (⟨_, _⟩ : simplexFaceCarrier facet) =
      simplexFaceVertex facet first hfirst
    apply Subtype.ext
    apply Subtype.ext
    ext w
    simp [AffineMap.lineMap_apply_module, simplexFaceVertex]
  target' := by
    change (⟨_, _⟩ : simplexFaceCarrier facet) =
      simplexFaceVertex facet second hsecond
    apply Subtype.ext
    apply Subtype.ext
    ext w
    simp [AffineMap.lineMap_apply_module, simplexFaceVertex]

@[simp]
theorem simplexFaceEdgePath_apply (facet : Finset V)
    (first second : V) (hfirst : first ∈ facet) (hsecond : second ∈ facet)
    (t : unitInterval) (w : V) :
    (simplexFaceEdgePath facet first second hfirst hsecond t).1.1 w =
      (1 - (t : ℝ)) * (stdSimplex.vertex first : V → ℝ) w +
        (t : ℝ) * (stdSimplex.vertex second : V → ℝ) w := by
  change AffineMap.lineMap (stdSimplex.vertex first).1
    (stdSimplex.vertex second).1 (t : ℝ) w = _
  rw [AffineMap.lineMap_apply_module]
  rfl

/-- A listed-facet vertex as a point of the full affine carrier. -/
def facetFamilyVertex (facet : Finset V) (hfacet : facet ∈ facets)
    (v : V) (hv : v ∈ facet) : facetFamilyCarrier facets :=
  faceCarrierToFacetFamilyCarrier facets
    ⟨facet, hfacet, ⟨v, hv⟩⟩ (simplexFaceVertex facet v hv)

/-- The straight affine path between two vertices of one listed facet. -/
def facetFamilyEdgePath (facet : Finset V) (hfacet : facet ∈ facets)
    (first second : V) (hfirst : first ∈ facet) (hsecond : second ∈ facet) :
    Path (facetFamilyVertex facet hfacet first hfirst)
      (facetFamilyVertex facet hfacet second hsecond) :=
  (simplexFaceEdgePath facet first second hfirst hsecond).map
    (Continuous.subtype_mk continuous_subtype_val _)

/-- On an oriented edge, the cocycle circle map is multiplication by that edge's integral
cochain value. -/
theorem integralCocycleCircleMap_edge
    {cochain : V → V → ℤ}
    (halternating : ComplexProjectivePlaneTriangulation.IsAlternatingEdgeCochain cochain)
    (hclosed : ComplexProjectivePlaneTriangulation.IsClosedEdgeCochain facets cochain)
    (facet : Finset V) (hfacet : facet ∈ facets)
    (first second : V) (hfirst : first ∈ facet) (hsecond : second ∈ facet)
    (t : unitInterval) :
    integralCocycleCircleMap cochain halternating hclosed
        (facetFamilyEdgePath facet hfacet first second hfirst hsecond t) =
      (((t : ℝ) * (cochain first second : ℝ) : ℝ) : UnitAddCircle) := by
  classical
  let i : NonemptyFacetIndex facets :=
    ⟨facet, hfacet, ⟨first, hfirst⟩⟩
  let y : simplexFaceCarrier facet :=
    simplexFaceEdgePath facet first second hfirst hsecond t
  have hpoint :
      facetFamilyEdgePath facet hfacet first second hfirst hsecond t =
        faceCarrierToFacetFamilyCarrier facets i y := by
    rfl
  rw [hpoint, integralCocycleCircleMap_face]
  change (facetCocycleLift cochain i y : UnitAddCircle) = _
  have hlift :
      facetCocycleLift cochain i y =
        (1 - (t : ℝ)) * (cochain (facetCocycleBase i) first : ℝ) +
          (t : ℝ) * (cochain (facetCocycleBase i) second : ℝ) := by
    rw [facetCocycleLift]
    change (∑ v, (simplexFaceEdgePath facet first second hfirst hsecond t).1.1 v *
      (cochain (facetCocycleBase i) v : ℝ)) = _
    simp_rw [simplexFaceEdgePath_apply]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    simp [Pi.single_apply]
  rw [hlift]
  have htriangle := edgeCochain_triangle_sum_eq_zero_of_subset_facet
    halternating hclosed (facetCocycleBase i) first second facet hfacet
      (by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with (rfl | rfl | rfl)
        · exact facetCocycleBase_mem i
        · exact hfirst
        · exact hsecond)
  rw [halternating second (facetCocycleBase i)] at htriangle
  have hdiff :
      (cochain (facetCocycleBase i) second : ℝ) -
          (cochain (facetCocycleBase i) first : ℝ) =
        (cochain first second : ℝ) := by
    exact_mod_cast (show
      cochain (facetCocycleBase i) second -
          cochain (facetCocycleBase i) first = cochain first second by omega)
  rw [show
    (1 - (t : ℝ)) * (cochain (facetCocycleBase i) first : ℝ) +
        (t : ℝ) * (cochain (facetCocycleBase i) second : ℝ) =
      (cochain (facetCocycleBase i) first : ℝ) +
        (t : ℝ) * (cochain first second : ℝ) by
          rw [← hdiff]
          ring]
  rw [AddCircle.coe_add]
  have hinteger :
      ((cochain (facetCocycleBase i) first : ℝ) : UnitAddCircle) = 0 := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact AddSubgroup.intCast_mem_zmultiples_one
      (cochain (facetCocycleBase i) first)
  rw [hinteger, zero_add]

omit [Fintype V] in
theorem isFace_singleton_left_of_pair {first second : V}
    (hface : IsFace facets {first, second}) : IsFace facets {first} := by
  obtain ⟨facet, hfacet, hsubset⟩ := hface
  exact ⟨facet, hfacet, fun v hv ↦ hsubset (by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    exact Or.inl hv)⟩

omit [Fintype V] in
theorem isFace_singleton_right_of_pair {first second : V}
    (hface : IsFace facets {first, second}) : IsFace facets {second} := by
  obtain ⟨facet, hfacet, hsubset⟩ := hface
  exact ⟨facet, hfacet, fun v hv ↦ hsubset (by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ⊢
    simp only [Finset.mem_singleton] at hv
    exact Or.inr hv)⟩

/-- A carrier vertex whose membership is supplied abstractly as a generated face. -/
def facetFamilyVertexOfIsFace (v : V) (hface : IsFace facets {v}) :
    facetFamilyCarrier facets :=
  ⟨stdSimplex.vertex v, (mem_facetFamilyCarrier_iff facets _).mpr
    ⟨hface.choose, hface.choose_spec.1, by
      intro w hw
      rw [stdSimplex.vertex_coe]
      simp only [Pi.single_apply]
      rw [if_neg]
      exact fun hvw ↦ hw (by
        rw [hvw]
        exact hface.choose_spec.2 (by simp))⟩⟩

/-- The canonical straight carrier edge attached to any generated one-simplex. -/
noncomputable def facetFamilyEdgePathOfIsFace {first second : V}
    (hface : IsFace facets {first, second}) :
    Path
      (facetFamilyVertexOfIsFace first
        (isFace_singleton_left_of_pair hface))
      (facetFamilyVertexOfIsFace second
        (isFace_singleton_right_of_pair hface)) :=
  (facetFamilyEdgePath hface.choose hface.choose_spec.1 first second
    (hface.choose_spec.2 (by simp)) (hface.choose_spec.2 (by simp))).cast rfl rfl

@[simp]
theorem integralCocycleCircleMap_edgeOfIsFace
    {cochain : V → V → ℤ}
    (halternating : ComplexProjectivePlaneTriangulation.IsAlternatingEdgeCochain cochain)
    (hclosed : ComplexProjectivePlaneTriangulation.IsClosedEdgeCochain facets cochain)
    {first second : V} (hface : IsFace facets {first, second})
    (t : unitInterval) :
    integralCocycleCircleMap cochain halternating hclosed
        (facetFamilyEdgePathOfIsFace hface t) =
      (((t : ℝ) * (cochain first second : ℝ) : ℝ) : UnitAddCircle) := by
  exact integralCocycleCircleMap_edge halternating hclosed
    hface.choose hface.choose_spec.1 first second
      (hface.choose_spec.2 (by simp)) (hface.choose_spec.2 (by simp)) t

/-- The standard based circle loop with integral winding `n`. -/
def addCircleIntegerPath (n : ℤ) : Path (0 : UnitAddCircle) 0 where
  toFun t := (((t : ℝ) * (n : ℝ) : ℝ) : UnitAddCircle)
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_subtype_val.mul continuous_const)
  source' := by simp
  target' := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    convert AddSubgroup.intCast_mem_zmultiples_one n using 1
    all_goals simp

/-- The evident real lift of the standard integral circle loop. -/
def addCircleIntegerPathRealLift (n : ℤ) : C(unitInterval, ℝ) :=
  ⟨fun t ↦ (t : ℝ) * (n : ℝ), continuous_subtype_val.mul continuous_const⟩

theorem addCircleIntegerPath_liftPath (n : ℤ) :
    (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath
        (addCircleIntegerPath n).toContinuousMap 0
          (by simp [addCircleIntegerPath]) =
      addCircleIntegerPathRealLift n := by
  symm
  apply ((AddCircle.isCoveringMap_coe (1 : ℝ)).eq_liftPath_iff'
    (by simp [addCircleIntegerPath])).mpr
  constructor
  · funext t
    rfl
  · simp [addCircleIntegerPathRealLift]

theorem addCircleIntegerPath_liftPath_one (n : ℤ) :
    (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath
        (addCircleIntegerPath n).toContinuousMap 0
          (by simp [addCircleIntegerPath]) 1 =
      (n : ℝ) := by
  rw [addCircleIntegerPath_liftPath]
  simp [addCircleIntegerPathRealLift]

/-- A nonzero integral circle loop is not homotopic relative to its endpoints to the constant
loop. -/
theorem addCircleIntegerPath_not_homotopic_refl {n : ℤ} (hn : n ≠ 0) :
    ¬ (addCircleIntegerPath n).Homotopic (Path.refl 0) := by
  intro h
  have hend := (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_apply_one_eq_of_homotopicRel
    h 0 (by simp [addCircleIntegerPath]) (by simp)
  rw [addCircleIntegerPath_liftPath_one] at hend
  have hrefl :
      (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath
          (Path.refl (0 : UnitAddCircle)).toContinuousMap 0 (by simp) =
        ContinuousMap.const unitInterval (0 : ℝ) := by
    exact (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_const (by simp)
  rw [hrefl] at hend
  have hend' : (n : ℝ) = 0 := by simpa using hend
  have : n = 0 := by exact_mod_cast hend'
  exact hn this

/-- The image of one generated carrier edge under the cocycle circle map, based at zero. -/
noncomputable def integralCocycleCircleEdgePath
    {cochain : V → V → ℤ}
    (halternating : ComplexProjectivePlaneTriangulation.IsAlternatingEdgeCochain cochain)
    (hclosed : ComplexProjectivePlaneTriangulation.IsClosedEdgeCochain facets cochain)
    {first second : V} (hface : IsFace facets {first, second}) :
    Path (0 : UnitAddCircle) 0 where
  toFun t := integralCocycleCircleMap cochain halternating hclosed
    (facetFamilyEdgePathOfIsFace hface t)
  continuous_toFun :=
    (integralCocycleCircleMap cochain halternating hclosed).continuous.comp
      (facetFamilyEdgePathOfIsFace hface).continuous
  source' := by
    rw [integralCocycleCircleMap_edgeOfIsFace]
    simp
  target' := by
    rw [integralCocycleCircleMap_edgeOfIsFace]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    convert AddSubgroup.intCast_mem_zmultiples_one (cochain first second) using 1
    all_goals simp

/-- A cocycle sends a generated edge to the standard circle loop with its integral edge value. -/
theorem integralCocycleCircleEdgePath_eq
    {cochain : V → V → ℤ}
    (halternating : ComplexProjectivePlaneTriangulation.IsAlternatingEdgeCochain cochain)
    (hclosed : ComplexProjectivePlaneTriangulation.IsClosedEdgeCochain facets cochain)
    {first second : V} (hface : IsFace facets {first, second}) :
    integralCocycleCircleEdgePath halternating hclosed hface =
      addCircleIntegerPath (cochain first second) := by
  ext t
  exact integralCocycleCircleMap_edgeOfIsFace
    halternating hclosed hface t

/-- A based loop is essential whenever a circle-valued detector sends it, after the canonical
basepoint cast, to an essential circle loop. -/
theorem path_not_homotopic_refl_of_circle_map
    {X : Type} [TopologicalSpace X] {x : X}
    (loop : Path x x) (f : C(X, UnitAddCircle)) (hfx : f x = 0)
    (circleLoop : Path (0 : UnitAddCircle) 0)
    (hcircle : (loop.map f.continuous).cast hfx.symm hfx.symm = circleLoop)
    (hessential : ¬ circleLoop.Homotopic (Path.refl 0)) :
    ¬ loop.Homotopic (Path.refl x) := by
  intro h
  have hmap := h.map f
  have hcast := hmap.pathCast hfx.symm hfx.symm
  rw [hcircle] at hcast
  have hrefl :
      (((Path.refl x).map f.continuous).cast hfx.symm hfx.symm) =
        Path.refl (0 : UnitAddCircle) := by
    ext t
    simpa using hfx
  rw [hrefl] at hcast
  exact hessential hcast

/-- An essential based path represents a nonidentity element of the fundamental group. -/
theorem fundamentalGroup_mk_ne_one_of_not_homotopic_refl
    {X : Type} [TopologicalSpace X] {x : X} (loop : Path x x)
    (hessential : ¬ loop.Homotopic (Path.refl x)) :
    (Path.Homotopic.Quotient.mk loop : FundamentalGroup X x) ≠
      (1 : FundamentalGroup X x) := by
  rw [FundamentalGroup.one_def]
  intro h
  exact hessential (Path.Homotopic.Quotient.exact h)

/-- The cubical π₁ class represented by a based path. -/
noncomputable def piOneClassOfPath
    {X : Type} [TopologicalSpace X] {x : X} (loop : Path x x) :
    HomotopyGroup.Pi 1 X x :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm
    (Path.Homotopic.Quotient.mk loop)

theorem piOneClassOfPath_ne_one_of_not_homotopic_refl
    {X : Type} [TopologicalSpace X] {x : X} (loop : Path x x)
    (hessential : ¬ loop.Homotopic (Path.refl x)) :
    piOneClassOfPath loop ≠ 1 := by
  intro h
  have hfund := congrArg
    (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x)) h
  have hfund' :
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop) =
        (1 : FundamentalGroup X x) := by
    simpa [piOneClassOfPath] using hfund
  have hpath := congrArg
    (fun q : FundamentalGroup X x ↦ FundamentalGroup.toPath q) hfund'
  change Path.Homotopic.Quotient.mk loop =
    Path.Homotopic.Quotient.refl x at hpath
  exact hessential (Path.Homotopic.Quotient.exact hpath)

/-- The canonical comparison from cubical `π₁` to the fundamental group intertwines the
map induced by a based continuous map with `FundamentalGroup.mapOfEq` on path classes. -/
theorem pi1MulEquivFundamentalGroup_map_piOneClassOfPath
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (loop : Path x x) (f : C(X, Y)) (hfx : f x = y) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
        (HomotopyGroup.map f hfx (piOneClassOfPath loop)) =
      FundamentalGroup.mapOfEq f hfx
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop)) := by
  rw [FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
      (_root_.genLoopEquivOfUnique (Fin 1)
        (GenLoop.map f hfx
          ((_root_.genLoopEquivOfUnique (Fin 1)).symm loop))) =
    (Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk loop) f).cast hfx.symm hfx.symm
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- Pulling an essential loop back through a homeomorphism preserves essentiality. -/
theorem homeomorph_symm_map_not_homotopic_refl
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {y : Y} (loop : Path y y)
    (hessential : ¬ loop.Homotopic (Path.refl y)) :
    ¬ (loop.map e.symm.continuous).Homotopic (Path.refl (e.symm y)) := by
  intro h
  have hmap := h.map ⟨e, e.continuous⟩
  have hcast := hmap.pathCast (e.apply_symm_apply y).symm
    (e.apply_symm_apply y).symm
  apply hessential
  convert hcast using 1
  · ext t
    exact (e.apply_symm_apply (loop t)).symm
  · ext t
    exact (e.apply_symm_apply y).symm

end Submission.FiniteOrderedComplex

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem centralEdge_one_seven :
    IsFace centralInterfaceFacets ({1, 7} : Finset TrisectionVertex) := by
  exact zeroFiveMeridianBoundaryFacets_le_centralInterface _ (by decide)

theorem centralEdge_seven_twelve :
    IsFace centralInterfaceFacets ({7, 12} : Finset TrisectionVertex) := by
  exact zeroFiveMeridianBoundaryFacets_le_centralInterface _ (by decide)

theorem centralEdge_twelve_one :
    IsFace centralInterfaceFacets ({12, 1} : Finset TrisectionVertex) := by
  exact zeroFiveMeridianBoundaryFacets_le_centralInterface _ (by decide)

theorem centralEdge_seven_three :
    IsFace centralInterfaceFacets ({7, 3} : Finset TrisectionVertex) := by
  exact fiveFourMeridianBoundaryFacets_le_centralInterface _ (by decide)

theorem centralEdge_three_twelve :
    IsFace centralInterfaceFacets ({3, 12} : Finset TrisectionVertex) := by
  exact fiveFourMeridianBoundaryFacets_le_centralInterface _ (by decide)

theorem centralEdge_twelve_seven :
    IsFace centralInterfaceFacets ({12, 7} : Finset TrisectionVertex) := by
  exact fiveFourMeridianBoundaryFacets_le_centralInterface _ (by decide)

theorem centralEdge_three_one :
    IsFace centralInterfaceFacets ({3, 1} : Finset TrisectionVertex) := by
  exact fourZeroMeridianBoundaryFacets_le_centralInterface _ (by decide)

theorem centralEdge_one_twelve :
    IsFace centralInterfaceFacets ({1, 12} : Finset TrisectionVertex) := by
  exact fourZeroMeridianBoundaryFacets_le_centralInterface _ (by decide)

theorem centralEdge_twelve_three :
    IsFace centralInterfaceFacets ({12, 3} : Finset TrisectionVertex) := by
  exact fourZeroMeridianBoundaryFacets_le_centralInterface _ (by decide)

/-- First cocycle evaluated on the realized zero-five three-edge circuit. -/
noncomputable def zeroFiveFirstCirclePath : Path (0 : UnitAddCircle) 0 :=
  (integralCocycleCircleEdgePath centralTorusFirstCochain_alternating
      centralTorusFirstCochain_closed centralEdge_one_seven).trans
    ((integralCocycleCircleEdgePath centralTorusFirstCochain_alternating
        centralTorusFirstCochain_closed centralEdge_seven_twelve).trans
      (integralCocycleCircleEdgePath centralTorusFirstCochain_alternating
        centralTorusFirstCochain_closed centralEdge_twelve_one))

theorem addCircleIntegerPath_zero :
    addCircleIntegerPath 0 = Path.refl (0 : UnitAddCircle) := by
  ext t
  simp [addCircleIntegerPath]

theorem zeroFiveFirstCirclePath_homotopic_one :
    zeroFiveFirstCirclePath.Homotopic (addCircleIntegerPath 1) := by
  rw [zeroFiveFirstCirclePath,
    integralCocycleCircleEdgePath_eq,
    integralCocycleCircleEdgePath_eq,
    integralCocycleCircleEdgePath_eq]
  have hfirst : centralTorusFirstCochain 1 7 = 0 := by decide
  have hsecond : centralTorusFirstCochain 7 12 = 1 := by decide
  have hthird : centralTorusFirstCochain 12 1 = 0 := by decide
  rw [hfirst, hsecond, hthird, addCircleIntegerPath_zero]
  exact (Path.Homotopic.refl_trans _).trans (Path.Homotopic.trans_refl _)

theorem zeroFiveFirstCirclePath_not_homotopic_refl :
    ¬ zeroFiveFirstCirclePath.Homotopic (Path.refl 0) := by
  intro h
  apply addCircleIntegerPath_not_homotopic_refl (by norm_num : (1 : ℤ) ≠ 0)
  exact zeroFiveFirstCirclePath_homotopic_one.symm.trans h

/-- The zero-five meridian as an actual three-edge loop in the affine central carrier. -/
noncomputable def zeroFiveCentralCarrierLoop :
    Path
      (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
        (isFace_singleton_left_of_pair centralEdge_one_seven))
      (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
        (isFace_singleton_left_of_pair centralEdge_one_seven)) :=
  ((facetFamilyEdgePathOfIsFace centralEdge_one_seven).trans
    ((facetFamilyEdgePathOfIsFace centralEdge_seven_twelve).trans
      (facetFamilyEdgePathOfIsFace centralEdge_twelve_one))).cast rfl rfl

theorem centralFirstCircleMap_vertex_one_eq_zero :
    integralCocycleCircleMap centralTorusFirstCochain
        centralTorusFirstCochain_alternating centralTorusFirstCochain_closed
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
          (isFace_singleton_left_of_pair centralEdge_one_seven)) = 0 := by
  simpa using integralCocycleCircleMap_edgeOfIsFace
    centralTorusFirstCochain_alternating centralTorusFirstCochain_closed
      centralEdge_one_seven (0 : unitInterval)

theorem zeroFiveCentralCarrierLoop_map_first_cast :
    ((zeroFiveCentralCarrierLoop.map
      (integralCocycleCircleMap centralTorusFirstCochain
        centralTorusFirstCochain_alternating
        centralTorusFirstCochain_closed).continuous).cast
          centralFirstCircleMap_vertex_one_eq_zero.symm
          centralFirstCircleMap_vertex_one_eq_zero.symm) =
      zeroFiveFirstCirclePath := by
  ext t
  simp only [zeroFiveCentralCarrierLoop, zeroFiveFirstCirclePath,
    integralCocycleCircleEdgePath, Path.cast_coe, Path.map_coe,
    Function.comp_apply]
  simp only [Path.trans_apply]
  split_ifs <;> rfl

theorem zeroFiveCentralCarrierLoop_not_homotopic_refl :
    ¬ zeroFiveCentralCarrierLoop.Homotopic
      (Path.refl
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
          (isFace_singleton_left_of_pair centralEdge_one_seven))) := by
  intro h
  have hmap := h.map
    (integralCocycleCircleMap centralTorusFirstCochain
      centralTorusFirstCochain_alternating centralTorusFirstCochain_closed)
  have hcast := hmap.pathCast
    centralFirstCircleMap_vertex_one_eq_zero.symm
    centralFirstCircleMap_vertex_one_eq_zero.symm
  apply zeroFiveFirstCirclePath_not_homotopic_refl
  rw [zeroFiveCentralCarrierLoop_map_first_cast] at hcast
  have hrefl :
      (((Path.refl
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
          (isFace_singleton_left_of_pair centralEdge_one_seven))).map
        (integralCocycleCircleMap centralTorusFirstCochain
          centralTorusFirstCochain_alternating
          centralTorusFirstCochain_closed).continuous).cast
            centralFirstCircleMap_vertex_one_eq_zero.symm
            centralFirstCircleMap_vertex_one_eq_zero.symm) =
        Path.refl (0 : UnitAddCircle) := by
    ext t
    simpa using centralFirstCircleMap_vertex_one_eq_zero
  rw [hrefl] at hcast
  exact hcast

/-- Second cocycle evaluated on the realized five-four three-edge circuit. -/
noncomputable def fiveFourSecondCirclePath : Path (0 : UnitAddCircle) 0 :=
  (integralCocycleCircleEdgePath centralTorusSecondCochain_alternating
      centralTorusSecondCochain_closed centralEdge_seven_three).trans
    ((integralCocycleCircleEdgePath centralTorusSecondCochain_alternating
        centralTorusSecondCochain_closed centralEdge_three_twelve).trans
      (integralCocycleCircleEdgePath centralTorusSecondCochain_alternating
        centralTorusSecondCochain_closed centralEdge_twelve_seven))

theorem fiveFourSecondCirclePath_homotopic_one :
    fiveFourSecondCirclePath.Homotopic (addCircleIntegerPath 1) := by
  rw [fiveFourSecondCirclePath,
    integralCocycleCircleEdgePath_eq,
    integralCocycleCircleEdgePath_eq,
    integralCocycleCircleEdgePath_eq]
  have hfirst : centralTorusSecondCochain 7 3 = 0 := by decide
  have hsecond : centralTorusSecondCochain 3 12 = 0 := by decide
  have hthird : centralTorusSecondCochain 12 7 = 1 := by decide
  rw [hfirst, hsecond, hthird, addCircleIntegerPath_zero]
  exact (Path.Homotopic.refl_trans _).trans
    ((Path.Homotopic.refl_trans _).trans (Path.Homotopic.refl _))

theorem fiveFourSecondCirclePath_not_homotopic_refl :
    ¬ fiveFourSecondCirclePath.Homotopic (Path.refl 0) := by
  intro h
  apply addCircleIntegerPath_not_homotopic_refl (by norm_num : (1 : ℤ) ≠ 0)
  exact fiveFourSecondCirclePath_homotopic_one.symm.trans h

/-- The five-four meridian as an actual three-edge loop in the affine central carrier. -/
noncomputable def fiveFourCentralCarrierLoop :
    Path
      (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
        (isFace_singleton_left_of_pair centralEdge_seven_three))
      (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
        (isFace_singleton_left_of_pair centralEdge_seven_three)) :=
  ((facetFamilyEdgePathOfIsFace centralEdge_seven_three).trans
    ((facetFamilyEdgePathOfIsFace centralEdge_three_twelve).trans
      (facetFamilyEdgePathOfIsFace centralEdge_twelve_seven))).cast rfl rfl

theorem centralSecondCircleMap_vertex_seven_eq_zero :
    integralCocycleCircleMap centralTorusSecondCochain
        centralTorusSecondCochain_alternating centralTorusSecondCochain_closed
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
          (isFace_singleton_left_of_pair centralEdge_seven_three)) = 0 := by
  simpa using integralCocycleCircleMap_edgeOfIsFace
    centralTorusSecondCochain_alternating centralTorusSecondCochain_closed
      centralEdge_seven_three (0 : unitInterval)

theorem fiveFourCentralCarrierLoop_map_second_cast :
    ((fiveFourCentralCarrierLoop.map
      (integralCocycleCircleMap centralTorusSecondCochain
        centralTorusSecondCochain_alternating
        centralTorusSecondCochain_closed).continuous).cast
          centralSecondCircleMap_vertex_seven_eq_zero.symm
          centralSecondCircleMap_vertex_seven_eq_zero.symm) =
      fiveFourSecondCirclePath := by
  ext t
  simp only [fiveFourCentralCarrierLoop, fiveFourSecondCirclePath,
    integralCocycleCircleEdgePath, Path.cast_coe, Path.map_coe,
    Function.comp_apply]
  simp only [Path.trans_apply]
  split_ifs <;> rfl

theorem fiveFourCentralCarrierLoop_not_homotopic_refl :
    ¬ fiveFourCentralCarrierLoop.Homotopic
      (Path.refl
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
          (isFace_singleton_left_of_pair centralEdge_seven_three))) :=
  path_not_homotopic_refl_of_circle_map
    fiveFourCentralCarrierLoop
    (integralCocycleCircleMap centralTorusSecondCochain
      centralTorusSecondCochain_alternating centralTorusSecondCochain_closed)
    centralSecondCircleMap_vertex_seven_eq_zero
    fiveFourSecondCirclePath
    fiveFourCentralCarrierLoop_map_second_cast
    fiveFourSecondCirclePath_not_homotopic_refl

/-- First cocycle evaluated on the realized four-zero three-edge circuit. -/
noncomputable def fourZeroFirstCirclePath : Path (0 : UnitAddCircle) 0 :=
  (integralCocycleCircleEdgePath centralTorusFirstCochain_alternating
      centralTorusFirstCochain_closed centralEdge_three_one).trans
    ((integralCocycleCircleEdgePath centralTorusFirstCochain_alternating
        centralTorusFirstCochain_closed centralEdge_one_twelve).trans
      (integralCocycleCircleEdgePath centralTorusFirstCochain_alternating
        centralTorusFirstCochain_closed centralEdge_twelve_three))

theorem fourZeroFirstCirclePath_homotopic_neg_one :
    fourZeroFirstCirclePath.Homotopic (addCircleIntegerPath (-1)) := by
  rw [fourZeroFirstCirclePath,
    integralCocycleCircleEdgePath_eq,
    integralCocycleCircleEdgePath_eq,
    integralCocycleCircleEdgePath_eq]
  have hfirst : centralTorusFirstCochain 3 1 = -1 := by decide
  have hsecond : centralTorusFirstCochain 1 12 = 0 := by decide
  have hthird : centralTorusFirstCochain 12 3 = 0 := by decide
  rw [hfirst, hsecond, hthird, addCircleIntegerPath_zero]
  exact (Path.Homotopic.hcomp
    (Path.Homotopic.refl (addCircleIntegerPath (-1)))
    (Path.Homotopic.refl_trans (Path.refl (0 : UnitAddCircle)))).trans
      (Path.Homotopic.trans_refl _)

theorem fourZeroFirstCirclePath_not_homotopic_refl :
    ¬ fourZeroFirstCirclePath.Homotopic (Path.refl 0) := by
  intro h
  apply addCircleIntegerPath_not_homotopic_refl (by norm_num : (-1 : ℤ) ≠ 0)
  exact fourZeroFirstCirclePath_homotopic_neg_one.symm.trans h

/-- The four-zero meridian as an actual three-edge loop in the affine central carrier. -/
noncomputable def fourZeroCentralCarrierLoop :
    Path
      (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
        (isFace_singleton_left_of_pair centralEdge_three_one))
      (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
        (isFace_singleton_left_of_pair centralEdge_three_one)) :=
  ((facetFamilyEdgePathOfIsFace centralEdge_three_one).trans
    ((facetFamilyEdgePathOfIsFace centralEdge_one_twelve).trans
      (facetFamilyEdgePathOfIsFace centralEdge_twelve_three))).cast rfl rfl

theorem centralFirstCircleMap_vertex_three_eq_zero :
    integralCocycleCircleMap centralTorusFirstCochain
        centralTorusFirstCochain_alternating centralTorusFirstCochain_closed
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
          (isFace_singleton_left_of_pair centralEdge_three_one)) = 0 := by
  simpa using integralCocycleCircleMap_edgeOfIsFace
    centralTorusFirstCochain_alternating centralTorusFirstCochain_closed
      centralEdge_three_one (0 : unitInterval)

theorem fourZeroCentralCarrierLoop_map_first_cast :
    ((fourZeroCentralCarrierLoop.map
      (integralCocycleCircleMap centralTorusFirstCochain
        centralTorusFirstCochain_alternating
        centralTorusFirstCochain_closed).continuous).cast
          centralFirstCircleMap_vertex_three_eq_zero.symm
          centralFirstCircleMap_vertex_three_eq_zero.symm) =
      fourZeroFirstCirclePath := by
  ext t
  simp only [fourZeroCentralCarrierLoop, fourZeroFirstCirclePath,
    integralCocycleCircleEdgePath, Path.cast_coe, Path.map_coe,
    Function.comp_apply]
  simp only [Path.trans_apply]
  split_ifs <;> rfl

theorem fourZeroCentralCarrierLoop_not_homotopic_refl :
    ¬ fourZeroCentralCarrierLoop.Homotopic
      (Path.refl
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
          (isFace_singleton_left_of_pair centralEdge_three_one))) :=
  path_not_homotopic_refl_of_circle_map
    fourZeroCentralCarrierLoop
    (integralCocycleCircleMap centralTorusFirstCochain
      centralTorusFirstCochain_alternating centralTorusFirstCochain_closed)
    centralFirstCircleMap_vertex_three_eq_zero
    fourZeroFirstCirclePath
    fourZeroCentralCarrierLoop_map_first_cast
    fourZeroFirstCirclePath_not_homotopic_refl

/-! The three essential carrier loops as explicit fundamental-group and cubical π₁ classes. -/

noncomputable def zeroFiveCentralCarrierFundamentalClass :
    FundamentalGroup (facetFamilyCarrier centralInterfaceFacets)
      (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
        (isFace_singleton_left_of_pair centralEdge_one_seven)) :=
  Path.Homotopic.Quotient.mk zeroFiveCentralCarrierLoop

theorem zeroFiveCentralCarrierFundamentalClass_ne_one :
    zeroFiveCentralCarrierFundamentalClass ≠ 1 :=
  fundamentalGroup_mk_ne_one_of_not_homotopic_refl
    zeroFiveCentralCarrierLoop
    zeroFiveCentralCarrierLoop_not_homotopic_refl

noncomputable def fiveFourCentralCarrierFundamentalClass :
    FundamentalGroup (facetFamilyCarrier centralInterfaceFacets)
      (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
        (isFace_singleton_left_of_pair centralEdge_seven_three)) :=
  Path.Homotopic.Quotient.mk fiveFourCentralCarrierLoop

theorem fiveFourCentralCarrierFundamentalClass_ne_one :
    fiveFourCentralCarrierFundamentalClass ≠ 1 :=
  fundamentalGroup_mk_ne_one_of_not_homotopic_refl
    fiveFourCentralCarrierLoop
    fiveFourCentralCarrierLoop_not_homotopic_refl

noncomputable def fourZeroCentralCarrierFundamentalClass :
    FundamentalGroup (facetFamilyCarrier centralInterfaceFacets)
      (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
        (isFace_singleton_left_of_pair centralEdge_three_one)) :=
  Path.Homotopic.Quotient.mk fourZeroCentralCarrierLoop

theorem fourZeroCentralCarrierFundamentalClass_ne_one :
    fourZeroCentralCarrierFundamentalClass ≠ 1 :=
  fundamentalGroup_mk_ne_one_of_not_homotopic_refl
    fourZeroCentralCarrierLoop
    fourZeroCentralCarrierLoop_not_homotopic_refl

noncomputable def zeroFiveCentralCarrierPiOneClass :
    HomotopyGroup.Pi 1 (facetFamilyCarrier centralInterfaceFacets)
      (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
        (isFace_singleton_left_of_pair centralEdge_one_seven)) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm
    zeroFiveCentralCarrierFundamentalClass

theorem zeroFiveCentralCarrierPiOneClass_ne_one :
    zeroFiveCentralCarrierPiOneClass ≠ 1 := by
  intro h
  apply zeroFiveCentralCarrierFundamentalClass_ne_one
  have := congrArg
    (HomotopyGroup.pi1MulEquivFundamentalGroup
      (X := facetFamilyCarrier centralInterfaceFacets)
      (x := facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
        (isFace_singleton_left_of_pair centralEdge_one_seven))) h
  simpa [zeroFiveCentralCarrierPiOneClass] using this

noncomputable def fiveFourCentralCarrierPiOneClass :
    HomotopyGroup.Pi 1 (facetFamilyCarrier centralInterfaceFacets)
      (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
        (isFace_singleton_left_of_pair centralEdge_seven_three)) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm
    fiveFourCentralCarrierFundamentalClass

theorem fiveFourCentralCarrierPiOneClass_ne_one :
    fiveFourCentralCarrierPiOneClass ≠ 1 := by
  intro h
  apply fiveFourCentralCarrierFundamentalClass_ne_one
  have := congrArg
    (HomotopyGroup.pi1MulEquivFundamentalGroup
      (X := facetFamilyCarrier centralInterfaceFacets)
      (x := facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
        (isFace_singleton_left_of_pair centralEdge_seven_three))) h
  simpa [fiveFourCentralCarrierPiOneClass] using this

noncomputable def fourZeroCentralCarrierPiOneClass :
    HomotopyGroup.Pi 1 (facetFamilyCarrier centralInterfaceFacets)
      (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
        (isFace_singleton_left_of_pair centralEdge_three_one)) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm
    fourZeroCentralCarrierFundamentalClass

theorem fourZeroCentralCarrierPiOneClass_ne_one :
    fourZeroCentralCarrierPiOneClass ≠ 1 := by
  intro h
  apply fourZeroCentralCarrierFundamentalClass_ne_one
  have := congrArg
    (HomotopyGroup.pi1MulEquivFundamentalGroup
      (X := facetFamilyCarrier centralInterfaceFacets)
      (x := facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
        (isFace_singleton_left_of_pair centralEdge_three_one))) h
  simpa [fourZeroCentralCarrierPiOneClass] using this

/-! Transport of the essential meridians to the actual simplicial realization. -/

noncomputable def zeroFiveCentralRealizationBase :
    SSet.toTop.obj (orderedSSet centralInterfaceFacets) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
    (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
      (isFace_singleton_left_of_pair centralEdge_one_seven))

noncomputable def zeroFiveCentralRealizationLoop :
    Path
      ((orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
          (isFace_singleton_left_of_pair centralEdge_one_seven)))
      ((orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
          (isFace_singleton_left_of_pair centralEdge_one_seven))) :=
  zeroFiveCentralCarrierLoop.map
    (orderedRealizationHomeomorphFacetFamilyCarrier
      centralInterfaceFacets).symm.continuous

theorem zeroFiveCentralRealizationLoop_not_homotopic_refl :
    ¬ zeroFiveCentralRealizationLoop.Homotopic
      (Path.refl
        ((orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
          (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
            (isFace_singleton_left_of_pair centralEdge_one_seven)))) :=
  homeomorph_symm_map_not_homotopic_refl
    (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets)
    zeroFiveCentralCarrierLoop
    zeroFiveCentralCarrierLoop_not_homotopic_refl

noncomputable def zeroFiveCentralRealizationPiOneClass :=
  piOneClassOfPath zeroFiveCentralRealizationLoop

theorem zeroFiveCentralRealizationPiOneClass_ne_one :
    zeroFiveCentralRealizationPiOneClass ≠ 1 :=
  piOneClassOfPath_ne_one_of_not_homotopic_refl
    zeroFiveCentralRealizationLoop
    zeroFiveCentralRealizationLoop_not_homotopic_refl

noncomputable def fiveFourCentralRealizationBase :
    SSet.toTop.obj (orderedSSet centralInterfaceFacets) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
    (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
      (isFace_singleton_left_of_pair centralEdge_seven_three))

noncomputable def fiveFourCentralRealizationLoop :
    Path
      ((orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
          (isFace_singleton_left_of_pair centralEdge_seven_three)))
      ((orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
          (isFace_singleton_left_of_pair centralEdge_seven_three))) :=
  fiveFourCentralCarrierLoop.map
    (orderedRealizationHomeomorphFacetFamilyCarrier
      centralInterfaceFacets).symm.continuous

theorem fiveFourCentralRealizationLoop_not_homotopic_refl :
    ¬ fiveFourCentralRealizationLoop.Homotopic
      (Path.refl
        ((orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
          (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
            (isFace_singleton_left_of_pair centralEdge_seven_three)))) :=
  homeomorph_symm_map_not_homotopic_refl
    (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets)
    fiveFourCentralCarrierLoop
    fiveFourCentralCarrierLoop_not_homotopic_refl

noncomputable def fiveFourCentralRealizationPiOneClass :=
  piOneClassOfPath fiveFourCentralRealizationLoop

theorem fiveFourCentralRealizationPiOneClass_ne_one :
    fiveFourCentralRealizationPiOneClass ≠ 1 :=
  piOneClassOfPath_ne_one_of_not_homotopic_refl
    fiveFourCentralRealizationLoop
    fiveFourCentralRealizationLoop_not_homotopic_refl

noncomputable def fourZeroCentralRealizationBase :
    SSet.toTop.obj (orderedSSet centralInterfaceFacets) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
    (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
      (isFace_singleton_left_of_pair centralEdge_three_one))

noncomputable def fourZeroCentralRealizationLoop :
    Path
      ((orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
          (isFace_singleton_left_of_pair centralEdge_three_one)))
      ((orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
          (isFace_singleton_left_of_pair centralEdge_three_one))) :=
  fourZeroCentralCarrierLoop.map
    (orderedRealizationHomeomorphFacetFamilyCarrier
      centralInterfaceFacets).symm.continuous

theorem fourZeroCentralRealizationLoop_not_homotopic_refl :
    ¬ fourZeroCentralRealizationLoop.Homotopic
      (Path.refl
        ((orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
          (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
            (isFace_singleton_left_of_pair centralEdge_three_one)))) :=
  homeomorph_symm_map_not_homotopic_refl
    (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets)
    fourZeroCentralCarrierLoop
    fourZeroCentralCarrierLoop_not_homotopic_refl

noncomputable def fourZeroCentralRealizationPiOneClass :=
  piOneClassOfPath fourZeroCentralRealizationLoop

theorem fourZeroCentralRealizationPiOneClass_ne_one :
    fourZeroCentralRealizationPiOneClass ≠ 1 :=
  piOneClassOfPath_ne_one_of_not_homotopic_refl
    fourZeroCentralRealizationLoop
    fourZeroCentralRealizationLoop_not_homotopic_refl

/-! The zero-five boundary inclusion carries its explicit circle circuit to the essential
central meridian. -/

theorem zeroFiveBoundaryEdge_one_seven :
    IsFace zeroFiveMeridianBoundaryFacets ({1, 7} : Finset TrisectionVertex) :=
  ⟨{1, 7}, by decide, Finset.Subset.rfl⟩

theorem zeroFiveBoundaryEdge_seven_twelve :
    IsFace zeroFiveMeridianBoundaryFacets ({7, 12} : Finset TrisectionVertex) :=
  ⟨{7, 12}, by decide, Finset.Subset.rfl⟩

theorem zeroFiveBoundaryEdge_twelve_one :
    IsFace zeroFiveMeridianBoundaryFacets ({12, 1} : Finset TrisectionVertex) :=
  ⟨{12, 1}, by decide, Finset.Subset.rfl⟩

noncomputable def zeroFiveBoundaryCarrierLoop :
    Path
      (facetFamilyVertexOfIsFace (facets := zeroFiveMeridianBoundaryFacets) 1
        (isFace_singleton_left_of_pair zeroFiveBoundaryEdge_one_seven))
      (facetFamilyVertexOfIsFace (facets := zeroFiveMeridianBoundaryFacets) 1
        (isFace_singleton_left_of_pair zeroFiveBoundaryEdge_one_seven)) :=
  ((facetFamilyEdgePathOfIsFace zeroFiveBoundaryEdge_one_seven).trans
    ((facetFamilyEdgePathOfIsFace zeroFiveBoundaryEdge_seven_twelve).trans
      (facetFamilyEdgePathOfIsFace zeroFiveBoundaryEdge_twelve_one))).cast rfl rfl

theorem zeroFiveBoundaryCarrierBase_map_eq_centralBase :
    facetFamilyCarrierMapOfFacetFamilyLE
        zeroFiveMeridianBoundaryFacets_le_centralInterface
        (facetFamilyVertexOfIsFace (facets := zeroFiveMeridianBoundaryFacets) 1
          (isFace_singleton_left_of_pair zeroFiveBoundaryEdge_one_seven)) =
      facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
        (isFace_singleton_left_of_pair centralEdge_one_seven) := by
  rfl

theorem zeroFiveBoundaryCarrierLoop_map_central_cast :
    ((zeroFiveBoundaryCarrierLoop.map
      (continuous_facetFamilyCarrierMapOfFacetFamilyLE
        zeroFiveMeridianBoundaryFacets_le_centralInterface)).cast
          zeroFiveBoundaryCarrierBase_map_eq_centralBase.symm
          zeroFiveBoundaryCarrierBase_map_eq_centralBase.symm) =
      zeroFiveCentralCarrierLoop := by
  ext t
  simp only [zeroFiveBoundaryCarrierLoop, zeroFiveCentralCarrierLoop,
    facetFamilyEdgePathOfIsFace, facetFamilyEdgePath, Path.cast_coe,
    Path.map_coe, Function.comp_apply]
  simp only [Path.trans_apply]
  split_ifs <;> rfl

noncomputable def zeroFiveBoundaryRealizationBase :
    SSet.toTop.obj (orderedSSet zeroFiveMeridianBoundaryFacets) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
    zeroFiveMeridianBoundaryFacets).symm
      (facetFamilyVertexOfIsFace (facets := zeroFiveMeridianBoundaryFacets) 1
        (isFace_singleton_left_of_pair zeroFiveBoundaryEdge_one_seven))

noncomputable def zeroFiveBoundaryRealizationLoop :
    Path
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        zeroFiveMeridianBoundaryFacets).symm
          (facetFamilyVertexOfIsFace (facets := zeroFiveMeridianBoundaryFacets) 1
            (isFace_singleton_left_of_pair zeroFiveBoundaryEdge_one_seven)))
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        zeroFiveMeridianBoundaryFacets).symm
          (facetFamilyVertexOfIsFace (facets := zeroFiveMeridianBoundaryFacets) 1
            (isFace_singleton_left_of_pair zeroFiveBoundaryEdge_one_seven))) :=
  zeroFiveBoundaryCarrierLoop.map
    (orderedRealizationHomeomorphFacetFamilyCarrier
      zeroFiveMeridianBoundaryFacets).symm.continuous

theorem zeroFiveBoundaryRealizationBase_map_central_eq :
    (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
        ((orderedRealizationHomeomorphFacetFamilyCarrier
          zeroFiveMeridianBoundaryFacets).symm
            (facetFamilyVertexOfIsFace (facets := zeroFiveMeridianBoundaryFacets) 1
              (isFace_singleton_left_of_pair zeroFiveBoundaryEdge_one_seven))) =
      (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
          (isFace_singleton_left_of_pair centralEdge_one_seven)) := by
  apply (orderedRealizationHomeomorphFacetFamilyCarrier
    centralInterfaceFacets).injective
  rw [(orderedRealizationHomeomorphFacetFamilyCarrier
    centralInterfaceFacets).apply_symm_apply]
  have hnat := ConcreteCategory.congr_hom
    (orderedRealizationToFacetFamilyCarrier_naturality
      zeroFiveMeridianBoundaryFacets_le_centralInterface)
    ((orderedRealizationHomeomorphFacetFamilyCarrier
      zeroFiveMeridianBoundaryFacets).symm
        (facetFamilyVertexOfIsFace (facets := zeroFiveMeridianBoundaryFacets) 1
          (isFace_singleton_left_of_pair zeroFiveBoundaryEdge_one_seven)))
  change (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets)
      ((SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
        ((orderedRealizationHomeomorphFacetFamilyCarrier
          zeroFiveMeridianBoundaryFacets).symm
            (facetFamilyVertexOfIsFace (facets := zeroFiveMeridianBoundaryFacets) 1
              (isFace_singleton_left_of_pair zeroFiveBoundaryEdge_one_seven)))) =
    facetFamilyCarrierMapOfFacetFamilyLE
      zeroFiveMeridianBoundaryFacets_le_centralInterface
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        zeroFiveMeridianBoundaryFacets)
          ((orderedRealizationHomeomorphFacetFamilyCarrier
            zeroFiveMeridianBoundaryFacets).symm
              (facetFamilyVertexOfIsFace (facets := zeroFiveMeridianBoundaryFacets) 1
                (isFace_singleton_left_of_pair zeroFiveBoundaryEdge_one_seven)))) at hnat
  rw [(orderedRealizationHomeomorphFacetFamilyCarrier
    zeroFiveMeridianBoundaryFacets).apply_symm_apply] at hnat
  exact hnat.trans zeroFiveBoundaryCarrierBase_map_eq_centralBase

theorem zeroFiveBoundaryRealizationLoop_map_central_cast :
    ((zeroFiveBoundaryRealizationLoop.map
      (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom.continuous).cast
        zeroFiveBoundaryRealizationBase_map_central_eq.symm
        zeroFiveBoundaryRealizationBase_map_central_eq.symm) =
      zeroFiveCentralRealizationLoop := by
  ext t
  change (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
      (zeroFiveBoundaryRealizationLoop t) = zeroFiveCentralRealizationLoop t
  apply (orderedRealizationHomeomorphFacetFamilyCarrier
    centralInterfaceFacets).injective
  have hnat := ConcreteCategory.congr_hom
    (orderedRealizationToFacetFamilyCarrier_naturality
      zeroFiveMeridianBoundaryFacets_le_centralInterface)
    (zeroFiveBoundaryRealizationLoop t)
  change (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets)
      ((SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
        (zeroFiveBoundaryRealizationLoop t)) =
    facetFamilyCarrierMapOfFacetFamilyLE
      zeroFiveMeridianBoundaryFacets_le_centralInterface
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        zeroFiveMeridianBoundaryFacets) (zeroFiveBoundaryRealizationLoop t)) at hnat
  rw [show (orderedRealizationHomeomorphFacetFamilyCarrier
      zeroFiveMeridianBoundaryFacets) (zeroFiveBoundaryRealizationLoop t) =
      zeroFiveBoundaryCarrierLoop t by
    exact (orderedRealizationHomeomorphFacetFamilyCarrier
      zeroFiveMeridianBoundaryFacets).apply_symm_apply _] at hnat
  have hcarrier := congrArg (fun p => p t)
    zeroFiveBoundaryCarrierLoop_map_central_cast
  change facetFamilyCarrierMapOfFacetFamilyLE
      zeroFiveMeridianBoundaryFacets_le_centralInterface
        (zeroFiveBoundaryCarrierLoop t) = zeroFiveCentralCarrierLoop t at hcarrier
  exact (hnat.trans hcarrier).trans (by
    exact ((orderedRealizationHomeomorphFacetFamilyCarrier
      centralInterfaceFacets).apply_symm_apply (zeroFiveCentralCarrierLoop t)).symm)

theorem zeroFiveBoundaryRealizationLoop_map_central_not_homotopic_refl :
    ¬ (zeroFiveBoundaryRealizationLoop.map
      (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom.continuous).Homotopic
        (Path.refl
          ((SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
            ((orderedRealizationHomeomorphFacetFamilyCarrier
              zeroFiveMeridianBoundaryFacets).symm
                (facetFamilyVertexOfIsFace
                  (facets := zeroFiveMeridianBoundaryFacets) 1
                    (isFace_singleton_left_of_pair
                      zeroFiveBoundaryEdge_one_seven))))) := by
  intro h
  have hcast := h.pathCast zeroFiveBoundaryRealizationBase_map_central_eq.symm
    zeroFiveBoundaryRealizationBase_map_central_eq.symm
  rw [zeroFiveBoundaryRealizationLoop_map_central_cast] at hcast
  apply zeroFiveCentralRealizationLoop_not_homotopic_refl
  convert hcast using 1
  ext t
  exact zeroFiveBoundaryRealizationBase_map_central_eq.symm

noncomputable def zeroFiveBoundaryRealizationFundamentalClass :
    FundamentalGroup
      (SSet.toTop.obj (orderedSSet zeroFiveMeridianBoundaryFacets))
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        zeroFiveMeridianBoundaryFacets).symm
          (facetFamilyVertexOfIsFace (facets := zeroFiveMeridianBoundaryFacets) 1
            (isFace_singleton_left_of_pair zeroFiveBoundaryEdge_one_seven))) :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk zeroFiveBoundaryRealizationLoop)

theorem zeroFiveBoundaryInclCentral_fundamentalGroup_map_ne_one :
    FundamentalGroup.mapOfEq
      (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
      zeroFiveBoundaryRealizationBase_map_central_eq
      zeroFiveBoundaryRealizationFundamentalClass ≠ 1 := by
  have hmap :
      FundamentalGroup.mapOfEq
        (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
        zeroFiveBoundaryRealizationBase_map_central_eq
        zeroFiveBoundaryRealizationFundamentalClass =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk zeroFiveCentralRealizationLoop) := by
    rw [FundamentalGroup.mapOfEq_apply]
    change (Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk zeroFiveBoundaryRealizationLoop)
        (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom).cast
          zeroFiveBoundaryRealizationBase_map_central_eq.symm
          zeroFiveBoundaryRealizationBase_map_central_eq.symm =
      Path.Homotopic.Quotient.mk zeroFiveCentralRealizationLoop
    rw [← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast,
      zeroFiveBoundaryRealizationLoop_map_central_cast]
  rw [hmap]
  exact fundamentalGroup_mk_ne_one_of_not_homotopic_refl
    zeroFiveCentralRealizationLoop
    zeroFiveCentralRealizationLoop_not_homotopic_refl

noncomputable def zeroFiveBoundaryRealizationPiOneClass :=
  piOneClassOfPath zeroFiveBoundaryRealizationLoop

theorem zeroFiveBoundaryInclCentral_piOne_map_ne_one :
    HomotopyGroup.map
      (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
      zeroFiveBoundaryRealizationBase_map_central_eq
      zeroFiveBoundaryRealizationPiOneClass ≠ 1 := by
  intro h
  have hfund := congrArg
    (HomotopyGroup.pi1MulEquivFundamentalGroup
      (X := SSet.toTop.obj (orderedSSet centralInterfaceFacets))) h
  simp only [zeroFiveBoundaryRealizationPiOneClass] at hfund
  rw [pi1MulEquivFundamentalGroup_map_piOneClassOfPath] at hfund
  apply zeroFiveBoundaryInclCentral_fundamentalGroup_map_ne_one
  simpa [zeroFiveBoundaryRealizationPiOneClass,
    zeroFiveBoundaryRealizationFundamentalClass] using hfund

theorem zeroFiveCentralRealizationBase_map_pairwise_eq :
    (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
        zeroFiveCentralRealizationBase =
      (SSet.toTop.map
        (zeroFiveMeridianBoundaryInclCentral ≫
          zeroFiveCentralInterfaceInclPairwise)).hom
        zeroFiveBoundaryRealizationBase := by
  rw [show zeroFiveCentralRealizationBase =
      (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
        zeroFiveBoundaryRealizationBase by
    exact zeroFiveBoundaryRealizationBase_map_central_eq.symm]
  exact (ConcreteCategory.congr_hom
    (SSet.toTop.map_comp zeroFiveMeridianBoundaryInclCentral
      zeroFiveCentralInterfaceInclPairwise)
    zeroFiveBoundaryRealizationBase).symm

/-- The zero-five meridian is a nonzero kernel class for the central-to-pairwise map on `π₁`. -/
theorem zeroFiveCentralInterfaceInclPairwise_piOne_map_not_injective :
    ¬ Function.Injective
      (HomotopyGroup.map (N := Fin 1)
        (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
        zeroFiveCentralRealizationBase_map_pairwise_eq) := by
  intro hinjective
  apply zeroFiveBoundaryInclCentral_piOne_map_ne_one
  apply hinjective
  have hcomp := HomotopyGroup.map_comp_apply (N := Fin 1)
    (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
    zeroFiveCentralRealizationBase_map_pairwise_eq
    (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
    zeroFiveBoundaryRealizationBase_map_central_eq
    zeroFiveBoundaryRealizationPiOneClass
  have hcontinuous :
      (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom.comp
          (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom =
        (SSet.toTop.map
          (zeroFiveMeridianBoundaryInclCentral ≫
            zeroFiveCentralInterfaceInclPairwise)).hom := by
    apply ContinuousMap.ext
    intro z
    exact (ConcreteCategory.congr_hom
      (SSet.toTop.map_comp zeroFiveMeridianBoundaryInclCentral
        zeroFiveCentralInterfaceInclPairwise) z).symm
  have hcontinuousBase :
      ((SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom.comp
          (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom)
          zeroFiveBoundaryRealizationBase =
        (SSet.toTop.map
          (zeroFiveMeridianBoundaryInclCentral ≫
            zeroFiveCentralInterfaceInclPairwise)).hom
          zeroFiveBoundaryRealizationBase :=
    congrArg (fun k => k zeroFiveBoundaryRealizationBase) hcontinuous
  have hcongr := HomotopyGroup.map_congr (N := Fin 1)
    hcontinuous hcontinuousBase rfl zeroFiveBoundaryRealizationPiOneClass
  have htrivial := zeroFiveMeridianViaCentralInclPairwise_piOne_trivial
    zeroFiveBoundaryRealizationBase
    zeroFiveBoundaryRealizationPiOneClass
  have hkill :
      HomotopyGroup.map
        (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
        zeroFiveCentralRealizationBase_map_pairwise_eq
        (HomotopyGroup.map
          (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
          zeroFiveBoundaryRealizationBase_map_central_eq
          zeroFiveBoundaryRealizationPiOneClass) = 1 :=
    hcomp.trans (hcongr.trans htrivial)
  exact hkill.trans
    ((HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
      zeroFiveCentralRealizationBase_map_pairwise_eq).map_one).symm

/-! The five-four boundary inclusion carries its explicit circle circuit to the essential
central meridian. -/

theorem fiveFourBoundaryEdge_seven_three :
    IsFace fiveFourMeridianBoundaryFacets ({7, 3} : Finset TrisectionVertex) :=
  ⟨{7, 3}, by decide, Finset.Subset.rfl⟩

theorem fiveFourBoundaryEdge_three_twelve :
    IsFace fiveFourMeridianBoundaryFacets ({3, 12} : Finset TrisectionVertex) :=
  ⟨{3, 12}, by decide, Finset.Subset.rfl⟩

theorem fiveFourBoundaryEdge_twelve_seven :
    IsFace fiveFourMeridianBoundaryFacets ({12, 7} : Finset TrisectionVertex) :=
  ⟨{12, 7}, by decide, Finset.Subset.rfl⟩

noncomputable def fiveFourBoundaryCarrierLoop :
    Path
      (facetFamilyVertexOfIsFace (facets := fiveFourMeridianBoundaryFacets) 7
        (isFace_singleton_left_of_pair fiveFourBoundaryEdge_seven_three))
      (facetFamilyVertexOfIsFace (facets := fiveFourMeridianBoundaryFacets) 7
        (isFace_singleton_left_of_pair fiveFourBoundaryEdge_seven_three)) :=
  ((facetFamilyEdgePathOfIsFace fiveFourBoundaryEdge_seven_three).trans
    ((facetFamilyEdgePathOfIsFace fiveFourBoundaryEdge_three_twelve).trans
      (facetFamilyEdgePathOfIsFace fiveFourBoundaryEdge_twelve_seven))).cast rfl rfl

theorem fiveFourBoundaryCarrierBase_map_eq_centralBase :
    facetFamilyCarrierMapOfFacetFamilyLE
        fiveFourMeridianBoundaryFacets_le_centralInterface
        (facetFamilyVertexOfIsFace (facets := fiveFourMeridianBoundaryFacets) 7
          (isFace_singleton_left_of_pair fiveFourBoundaryEdge_seven_three)) =
      facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
        (isFace_singleton_left_of_pair centralEdge_seven_three) := by
  rfl

theorem fiveFourBoundaryCarrierLoop_map_central_cast :
    ((fiveFourBoundaryCarrierLoop.map
      (continuous_facetFamilyCarrierMapOfFacetFamilyLE
        fiveFourMeridianBoundaryFacets_le_centralInterface)).cast
          fiveFourBoundaryCarrierBase_map_eq_centralBase.symm
          fiveFourBoundaryCarrierBase_map_eq_centralBase.symm) =
      fiveFourCentralCarrierLoop := by
  ext t
  simp only [fiveFourBoundaryCarrierLoop, fiveFourCentralCarrierLoop,
    facetFamilyEdgePathOfIsFace, facetFamilyEdgePath, Path.cast_coe,
    Path.map_coe, Function.comp_apply]
  simp only [Path.trans_apply]
  split_ifs <;> rfl

noncomputable def fiveFourBoundaryRealizationBase :
    SSet.toTop.obj (orderedSSet fiveFourMeridianBoundaryFacets) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
    fiveFourMeridianBoundaryFacets).symm
      (facetFamilyVertexOfIsFace (facets := fiveFourMeridianBoundaryFacets) 7
        (isFace_singleton_left_of_pair fiveFourBoundaryEdge_seven_three))

noncomputable def fiveFourBoundaryRealizationLoop :
    Path
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        fiveFourMeridianBoundaryFacets).symm
          (facetFamilyVertexOfIsFace (facets := fiveFourMeridianBoundaryFacets) 7
            (isFace_singleton_left_of_pair fiveFourBoundaryEdge_seven_three)))
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        fiveFourMeridianBoundaryFacets).symm
          (facetFamilyVertexOfIsFace (facets := fiveFourMeridianBoundaryFacets) 7
            (isFace_singleton_left_of_pair fiveFourBoundaryEdge_seven_three))) :=
  fiveFourBoundaryCarrierLoop.map
    (orderedRealizationHomeomorphFacetFamilyCarrier
      fiveFourMeridianBoundaryFacets).symm.continuous

theorem fiveFourBoundaryRealizationBase_map_central_eq :
    (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
        ((orderedRealizationHomeomorphFacetFamilyCarrier
          fiveFourMeridianBoundaryFacets).symm
            (facetFamilyVertexOfIsFace (facets := fiveFourMeridianBoundaryFacets) 7
              (isFace_singleton_left_of_pair fiveFourBoundaryEdge_seven_three))) =
      (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
          (isFace_singleton_left_of_pair centralEdge_seven_three)) := by
  apply (orderedRealizationHomeomorphFacetFamilyCarrier
    centralInterfaceFacets).injective
  rw [(orderedRealizationHomeomorphFacetFamilyCarrier
    centralInterfaceFacets).apply_symm_apply]
  have hnat := ConcreteCategory.congr_hom
    (orderedRealizationToFacetFamilyCarrier_naturality
      fiveFourMeridianBoundaryFacets_le_centralInterface)
    ((orderedRealizationHomeomorphFacetFamilyCarrier
      fiveFourMeridianBoundaryFacets).symm
        (facetFamilyVertexOfIsFace (facets := fiveFourMeridianBoundaryFacets) 7
          (isFace_singleton_left_of_pair fiveFourBoundaryEdge_seven_three)))
  change (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets)
      ((SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
        ((orderedRealizationHomeomorphFacetFamilyCarrier
          fiveFourMeridianBoundaryFacets).symm
            (facetFamilyVertexOfIsFace (facets := fiveFourMeridianBoundaryFacets) 7
              (isFace_singleton_left_of_pair fiveFourBoundaryEdge_seven_three)))) =
    facetFamilyCarrierMapOfFacetFamilyLE
      fiveFourMeridianBoundaryFacets_le_centralInterface
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        fiveFourMeridianBoundaryFacets)
          ((orderedRealizationHomeomorphFacetFamilyCarrier
            fiveFourMeridianBoundaryFacets).symm
              (facetFamilyVertexOfIsFace (facets := fiveFourMeridianBoundaryFacets) 7
                (isFace_singleton_left_of_pair fiveFourBoundaryEdge_seven_three)))) at hnat
  rw [(orderedRealizationHomeomorphFacetFamilyCarrier
    fiveFourMeridianBoundaryFacets).apply_symm_apply] at hnat
  exact hnat.trans fiveFourBoundaryCarrierBase_map_eq_centralBase

theorem fiveFourBoundaryRealizationLoop_map_central_cast :
    ((fiveFourBoundaryRealizationLoop.map
      (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom.continuous).cast
        fiveFourBoundaryRealizationBase_map_central_eq.symm
        fiveFourBoundaryRealizationBase_map_central_eq.symm) =
      fiveFourCentralRealizationLoop := by
  ext t
  change (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
      (fiveFourBoundaryRealizationLoop t) = fiveFourCentralRealizationLoop t
  apply (orderedRealizationHomeomorphFacetFamilyCarrier
    centralInterfaceFacets).injective
  have hnat := ConcreteCategory.congr_hom
    (orderedRealizationToFacetFamilyCarrier_naturality
      fiveFourMeridianBoundaryFacets_le_centralInterface)
    (fiveFourBoundaryRealizationLoop t)
  change (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets)
      ((SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
        (fiveFourBoundaryRealizationLoop t)) =
    facetFamilyCarrierMapOfFacetFamilyLE
      fiveFourMeridianBoundaryFacets_le_centralInterface
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        fiveFourMeridianBoundaryFacets) (fiveFourBoundaryRealizationLoop t)) at hnat
  rw [show (orderedRealizationHomeomorphFacetFamilyCarrier
      fiveFourMeridianBoundaryFacets) (fiveFourBoundaryRealizationLoop t) =
      fiveFourBoundaryCarrierLoop t by
    exact (orderedRealizationHomeomorphFacetFamilyCarrier
      fiveFourMeridianBoundaryFacets).apply_symm_apply _] at hnat
  have hcarrier := congrArg (fun p => p t)
    fiveFourBoundaryCarrierLoop_map_central_cast
  change facetFamilyCarrierMapOfFacetFamilyLE
      fiveFourMeridianBoundaryFacets_le_centralInterface
        (fiveFourBoundaryCarrierLoop t) = fiveFourCentralCarrierLoop t at hcarrier
  exact (hnat.trans hcarrier).trans (by
    exact ((orderedRealizationHomeomorphFacetFamilyCarrier
      centralInterfaceFacets).apply_symm_apply (fiveFourCentralCarrierLoop t)).symm)

theorem fiveFourBoundaryRealizationLoop_map_central_not_homotopic_refl :
    ¬ (fiveFourBoundaryRealizationLoop.map
      (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom.continuous).Homotopic
        (Path.refl
          ((SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
            ((orderedRealizationHomeomorphFacetFamilyCarrier
              fiveFourMeridianBoundaryFacets).symm
                (facetFamilyVertexOfIsFace
                  (facets := fiveFourMeridianBoundaryFacets) 7
                    (isFace_singleton_left_of_pair
                      fiveFourBoundaryEdge_seven_three))))) := by
  intro h
  have hcast := h.pathCast fiveFourBoundaryRealizationBase_map_central_eq.symm
    fiveFourBoundaryRealizationBase_map_central_eq.symm
  rw [fiveFourBoundaryRealizationLoop_map_central_cast] at hcast
  apply fiveFourCentralRealizationLoop_not_homotopic_refl
  convert hcast using 1
  ext t
  exact fiveFourBoundaryRealizationBase_map_central_eq.symm

/-! The four-zero boundary inclusion carries its explicit circle circuit to the essential
central meridian. -/

theorem fourZeroBoundaryEdge_three_one :
    IsFace fourZeroMeridianBoundaryFacets ({3, 1} : Finset TrisectionVertex) :=
  ⟨{3, 1}, by decide, Finset.Subset.rfl⟩

theorem fourZeroBoundaryEdge_one_twelve :
    IsFace fourZeroMeridianBoundaryFacets ({1, 12} : Finset TrisectionVertex) :=
  ⟨{1, 12}, by decide, Finset.Subset.rfl⟩

theorem fourZeroBoundaryEdge_twelve_three :
    IsFace fourZeroMeridianBoundaryFacets ({12, 3} : Finset TrisectionVertex) :=
  ⟨{12, 3}, by decide, Finset.Subset.rfl⟩

noncomputable def fourZeroBoundaryCarrierLoop :
    Path
      (facetFamilyVertexOfIsFace (facets := fourZeroMeridianBoundaryFacets) 3
        (isFace_singleton_left_of_pair fourZeroBoundaryEdge_three_one))
      (facetFamilyVertexOfIsFace (facets := fourZeroMeridianBoundaryFacets) 3
        (isFace_singleton_left_of_pair fourZeroBoundaryEdge_three_one)) :=
  ((facetFamilyEdgePathOfIsFace fourZeroBoundaryEdge_three_one).trans
    ((facetFamilyEdgePathOfIsFace fourZeroBoundaryEdge_one_twelve).trans
      (facetFamilyEdgePathOfIsFace fourZeroBoundaryEdge_twelve_three))).cast rfl rfl

theorem fourZeroBoundaryCarrierBase_map_eq_centralBase :
    facetFamilyCarrierMapOfFacetFamilyLE
        fourZeroMeridianBoundaryFacets_le_centralInterface
        (facetFamilyVertexOfIsFace (facets := fourZeroMeridianBoundaryFacets) 3
          (isFace_singleton_left_of_pair fourZeroBoundaryEdge_three_one)) =
      facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
        (isFace_singleton_left_of_pair centralEdge_three_one) := by
  rfl

theorem fourZeroBoundaryCarrierLoop_map_central_cast :
    ((fourZeroBoundaryCarrierLoop.map
      (continuous_facetFamilyCarrierMapOfFacetFamilyLE
        fourZeroMeridianBoundaryFacets_le_centralInterface)).cast
          fourZeroBoundaryCarrierBase_map_eq_centralBase.symm
          fourZeroBoundaryCarrierBase_map_eq_centralBase.symm) =
      fourZeroCentralCarrierLoop := by
  ext t
  simp only [fourZeroBoundaryCarrierLoop, fourZeroCentralCarrierLoop,
    facetFamilyEdgePathOfIsFace, facetFamilyEdgePath, Path.cast_coe,
    Path.map_coe, Function.comp_apply]
  simp only [Path.trans_apply]
  split_ifs <;> rfl

noncomputable def fourZeroBoundaryRealizationBase :
    SSet.toTop.obj (orderedSSet fourZeroMeridianBoundaryFacets) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
    fourZeroMeridianBoundaryFacets).symm
      (facetFamilyVertexOfIsFace (facets := fourZeroMeridianBoundaryFacets) 3
        (isFace_singleton_left_of_pair fourZeroBoundaryEdge_three_one))

noncomputable def fourZeroBoundaryRealizationLoop :
    Path
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        fourZeroMeridianBoundaryFacets).symm
          (facetFamilyVertexOfIsFace (facets := fourZeroMeridianBoundaryFacets) 3
            (isFace_singleton_left_of_pair fourZeroBoundaryEdge_three_one)))
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        fourZeroMeridianBoundaryFacets).symm
          (facetFamilyVertexOfIsFace (facets := fourZeroMeridianBoundaryFacets) 3
            (isFace_singleton_left_of_pair fourZeroBoundaryEdge_three_one))) :=
  fourZeroBoundaryCarrierLoop.map
    (orderedRealizationHomeomorphFacetFamilyCarrier
      fourZeroMeridianBoundaryFacets).symm.continuous

theorem fourZeroBoundaryRealizationBase_map_central_eq :
    (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
        ((orderedRealizationHomeomorphFacetFamilyCarrier
          fourZeroMeridianBoundaryFacets).symm
            (facetFamilyVertexOfIsFace (facets := fourZeroMeridianBoundaryFacets) 3
              (isFace_singleton_left_of_pair fourZeroBoundaryEdge_three_one))) =
      (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets).symm
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
          (isFace_singleton_left_of_pair centralEdge_three_one)) := by
  apply (orderedRealizationHomeomorphFacetFamilyCarrier
    centralInterfaceFacets).injective
  rw [(orderedRealizationHomeomorphFacetFamilyCarrier
    centralInterfaceFacets).apply_symm_apply]
  have hnat := ConcreteCategory.congr_hom
    (orderedRealizationToFacetFamilyCarrier_naturality
      fourZeroMeridianBoundaryFacets_le_centralInterface)
    ((orderedRealizationHomeomorphFacetFamilyCarrier
      fourZeroMeridianBoundaryFacets).symm
        (facetFamilyVertexOfIsFace (facets := fourZeroMeridianBoundaryFacets) 3
          (isFace_singleton_left_of_pair fourZeroBoundaryEdge_three_one)))
  change (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets)
      ((SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
        ((orderedRealizationHomeomorphFacetFamilyCarrier
          fourZeroMeridianBoundaryFacets).symm
            (facetFamilyVertexOfIsFace (facets := fourZeroMeridianBoundaryFacets) 3
              (isFace_singleton_left_of_pair fourZeroBoundaryEdge_three_one)))) =
    facetFamilyCarrierMapOfFacetFamilyLE
      fourZeroMeridianBoundaryFacets_le_centralInterface
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        fourZeroMeridianBoundaryFacets)
          ((orderedRealizationHomeomorphFacetFamilyCarrier
            fourZeroMeridianBoundaryFacets).symm
              (facetFamilyVertexOfIsFace (facets := fourZeroMeridianBoundaryFacets) 3
                (isFace_singleton_left_of_pair fourZeroBoundaryEdge_three_one)))) at hnat
  rw [(orderedRealizationHomeomorphFacetFamilyCarrier
    fourZeroMeridianBoundaryFacets).apply_symm_apply] at hnat
  exact hnat.trans fourZeroBoundaryCarrierBase_map_eq_centralBase

theorem fourZeroBoundaryRealizationLoop_map_central_cast :
    ((fourZeroBoundaryRealizationLoop.map
      (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom.continuous).cast
        fourZeroBoundaryRealizationBase_map_central_eq.symm
        fourZeroBoundaryRealizationBase_map_central_eq.symm) =
      fourZeroCentralRealizationLoop := by
  ext t
  change (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
      (fourZeroBoundaryRealizationLoop t) = fourZeroCentralRealizationLoop t
  apply (orderedRealizationHomeomorphFacetFamilyCarrier
    centralInterfaceFacets).injective
  have hnat := ConcreteCategory.congr_hom
    (orderedRealizationToFacetFamilyCarrier_naturality
      fourZeroMeridianBoundaryFacets_le_centralInterface)
    (fourZeroBoundaryRealizationLoop t)
  change (orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets)
      ((SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
        (fourZeroBoundaryRealizationLoop t)) =
    facetFamilyCarrierMapOfFacetFamilyLE
      fourZeroMeridianBoundaryFacets_le_centralInterface
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        fourZeroMeridianBoundaryFacets) (fourZeroBoundaryRealizationLoop t)) at hnat
  rw [show (orderedRealizationHomeomorphFacetFamilyCarrier
      fourZeroMeridianBoundaryFacets) (fourZeroBoundaryRealizationLoop t) =
      fourZeroBoundaryCarrierLoop t by
    exact (orderedRealizationHomeomorphFacetFamilyCarrier
      fourZeroMeridianBoundaryFacets).apply_symm_apply _] at hnat
  have hcarrier := congrArg (fun p => p t)
    fourZeroBoundaryCarrierLoop_map_central_cast
  change facetFamilyCarrierMapOfFacetFamilyLE
      fourZeroMeridianBoundaryFacets_le_centralInterface
        (fourZeroBoundaryCarrierLoop t) = fourZeroCentralCarrierLoop t at hcarrier
  exact (hnat.trans hcarrier).trans (by
    exact ((orderedRealizationHomeomorphFacetFamilyCarrier
      centralInterfaceFacets).apply_symm_apply (fourZeroCentralCarrierLoop t)).symm)

theorem fourZeroBoundaryRealizationLoop_map_central_not_homotopic_refl :
    ¬ (fourZeroBoundaryRealizationLoop.map
      (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom.continuous).Homotopic
        (Path.refl
          ((SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
            ((orderedRealizationHomeomorphFacetFamilyCarrier
              fourZeroMeridianBoundaryFacets).symm
                (facetFamilyVertexOfIsFace
                  (facets := fourZeroMeridianBoundaryFacets) 3
                    (isFace_singleton_left_of_pair
                      fourZeroBoundaryEdge_three_one))))) := by
  intro h
  have hcast := h.pathCast fourZeroBoundaryRealizationBase_map_central_eq.symm
    fourZeroBoundaryRealizationBase_map_central_eq.symm
  rw [fourZeroBoundaryRealizationLoop_map_central_cast] at hcast
  apply fourZeroCentralRealizationLoop_not_homotopic_refl
  convert hcast using 1
  ext t
  exact fourZeroBoundaryRealizationBase_map_central_eq.symm

noncomputable def fiveFourBoundaryRealizationFundamentalClass :
    FundamentalGroup
      (SSet.toTop.obj (orderedSSet fiveFourMeridianBoundaryFacets))
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        fiveFourMeridianBoundaryFacets).symm
          (facetFamilyVertexOfIsFace (facets := fiveFourMeridianBoundaryFacets) 7
            (isFace_singleton_left_of_pair fiveFourBoundaryEdge_seven_three))) :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk fiveFourBoundaryRealizationLoop)

theorem fiveFourBoundaryInclCentral_fundamentalGroup_map_ne_one :
    FundamentalGroup.mapOfEq
      (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
      fiveFourBoundaryRealizationBase_map_central_eq
      fiveFourBoundaryRealizationFundamentalClass ≠ 1 := by
  have hmap :
      FundamentalGroup.mapOfEq
        (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
        fiveFourBoundaryRealizationBase_map_central_eq
        fiveFourBoundaryRealizationFundamentalClass =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk fiveFourCentralRealizationLoop) := by
    rw [FundamentalGroup.mapOfEq_apply]
    change (Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk fiveFourBoundaryRealizationLoop)
        (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom).cast
          fiveFourBoundaryRealizationBase_map_central_eq.symm
          fiveFourBoundaryRealizationBase_map_central_eq.symm =
      Path.Homotopic.Quotient.mk fiveFourCentralRealizationLoop
    rw [← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast,
      fiveFourBoundaryRealizationLoop_map_central_cast]
  rw [hmap]
  exact fundamentalGroup_mk_ne_one_of_not_homotopic_refl
    fiveFourCentralRealizationLoop
    fiveFourCentralRealizationLoop_not_homotopic_refl

noncomputable def fiveFourBoundaryRealizationPiOneClass :=
  piOneClassOfPath fiveFourBoundaryRealizationLoop

theorem fiveFourBoundaryInclCentral_piOne_map_ne_one :
    HomotopyGroup.map
      (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
      fiveFourBoundaryRealizationBase_map_central_eq
      fiveFourBoundaryRealizationPiOneClass ≠ 1 := by
  intro h
  have hfund := congrArg
    (HomotopyGroup.pi1MulEquivFundamentalGroup
      (X := SSet.toTop.obj (orderedSSet centralInterfaceFacets))) h
  simp only [fiveFourBoundaryRealizationPiOneClass] at hfund
  rw [pi1MulEquivFundamentalGroup_map_piOneClassOfPath] at hfund
  apply fiveFourBoundaryInclCentral_fundamentalGroup_map_ne_one
  simpa [fiveFourBoundaryRealizationPiOneClass,
    fiveFourBoundaryRealizationFundamentalClass] using hfund

theorem fiveFourCentralRealizationBase_map_pairwise_eq :
    (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
        fiveFourCentralRealizationBase =
      (SSet.toTop.map
        (fiveFourMeridianBoundaryInclCentral ≫
          fiveFourCentralInterfaceInclPairwise)).hom
        fiveFourBoundaryRealizationBase := by
  rw [show fiveFourCentralRealizationBase =
      (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
        fiveFourBoundaryRealizationBase by
    exact fiveFourBoundaryRealizationBase_map_central_eq.symm]
  exact (ConcreteCategory.congr_hom
    (SSet.toTop.map_comp fiveFourMeridianBoundaryInclCentral
      fiveFourCentralInterfaceInclPairwise)
    fiveFourBoundaryRealizationBase).symm

/-- The five-four meridian is a nonzero kernel class for the central-to-pairwise map on `π₁`. -/
theorem fiveFourCentralInterfaceInclPairwise_piOne_map_not_injective :
    ¬ Function.Injective
      (HomotopyGroup.map (N := Fin 1)
        (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
        fiveFourCentralRealizationBase_map_pairwise_eq) := by
  intro hinjective
  apply fiveFourBoundaryInclCentral_piOne_map_ne_one
  apply hinjective
  have hcomp := HomotopyGroup.map_comp_apply (N := Fin 1)
    (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
    fiveFourCentralRealizationBase_map_pairwise_eq
    (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
    fiveFourBoundaryRealizationBase_map_central_eq
    fiveFourBoundaryRealizationPiOneClass
  have hcontinuous :
      (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom.comp
          (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom =
        (SSet.toTop.map
          (fiveFourMeridianBoundaryInclCentral ≫
            fiveFourCentralInterfaceInclPairwise)).hom := by
    apply ContinuousMap.ext
    intro z
    exact (ConcreteCategory.congr_hom
      (SSet.toTop.map_comp fiveFourMeridianBoundaryInclCentral
        fiveFourCentralInterfaceInclPairwise) z).symm
  have hcontinuousBase :
      ((SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom.comp
          (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom)
          fiveFourBoundaryRealizationBase =
        (SSet.toTop.map
          (fiveFourMeridianBoundaryInclCentral ≫
            fiveFourCentralInterfaceInclPairwise)).hom
          fiveFourBoundaryRealizationBase :=
    congrArg (fun k => k fiveFourBoundaryRealizationBase) hcontinuous
  have hcongr := HomotopyGroup.map_congr (N := Fin 1)
    hcontinuous hcontinuousBase rfl fiveFourBoundaryRealizationPiOneClass
  have htrivial := fiveFourMeridianViaCentralInclPairwise_piOne_trivial
    fiveFourBoundaryRealizationBase
    fiveFourBoundaryRealizationPiOneClass
  have hkill :
      HomotopyGroup.map
        (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
        fiveFourCentralRealizationBase_map_pairwise_eq
        (HomotopyGroup.map
          (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
          fiveFourBoundaryRealizationBase_map_central_eq
          fiveFourBoundaryRealizationPiOneClass) = 1 :=
    hcomp.trans (hcongr.trans htrivial)
  exact hkill.trans
    ((HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
      fiveFourCentralRealizationBase_map_pairwise_eq).map_one).symm

noncomputable def fourZeroBoundaryRealizationFundamentalClass :
    FundamentalGroup
      (SSet.toTop.obj (orderedSSet fourZeroMeridianBoundaryFacets))
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        fourZeroMeridianBoundaryFacets).symm
          (facetFamilyVertexOfIsFace (facets := fourZeroMeridianBoundaryFacets) 3
            (isFace_singleton_left_of_pair fourZeroBoundaryEdge_three_one))) :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk fourZeroBoundaryRealizationLoop)

theorem fourZeroBoundaryInclCentral_fundamentalGroup_map_ne_one :
    FundamentalGroup.mapOfEq
      (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
      fourZeroBoundaryRealizationBase_map_central_eq
      fourZeroBoundaryRealizationFundamentalClass ≠ 1 := by
  have hmap :
      FundamentalGroup.mapOfEq
        (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
        fourZeroBoundaryRealizationBase_map_central_eq
        fourZeroBoundaryRealizationFundamentalClass =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk fourZeroCentralRealizationLoop) := by
    rw [FundamentalGroup.mapOfEq_apply]
    change (Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk fourZeroBoundaryRealizationLoop)
        (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom).cast
          fourZeroBoundaryRealizationBase_map_central_eq.symm
          fourZeroBoundaryRealizationBase_map_central_eq.symm =
      Path.Homotopic.Quotient.mk fourZeroCentralRealizationLoop
    rw [← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast,
      fourZeroBoundaryRealizationLoop_map_central_cast]
  rw [hmap]
  exact fundamentalGroup_mk_ne_one_of_not_homotopic_refl
    fourZeroCentralRealizationLoop
    fourZeroCentralRealizationLoop_not_homotopic_refl

noncomputable def fourZeroBoundaryRealizationPiOneClass :=
  piOneClassOfPath fourZeroBoundaryRealizationLoop

theorem fourZeroBoundaryInclCentral_piOne_map_ne_one :
    HomotopyGroup.map
      (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
      fourZeroBoundaryRealizationBase_map_central_eq
      fourZeroBoundaryRealizationPiOneClass ≠ 1 := by
  intro h
  have hfund := congrArg
    (HomotopyGroup.pi1MulEquivFundamentalGroup
      (X := SSet.toTop.obj (orderedSSet centralInterfaceFacets))) h
  simp only [fourZeroBoundaryRealizationPiOneClass] at hfund
  rw [pi1MulEquivFundamentalGroup_map_piOneClassOfPath] at hfund
  apply fourZeroBoundaryInclCentral_fundamentalGroup_map_ne_one
  simpa [fourZeroBoundaryRealizationPiOneClass,
    fourZeroBoundaryRealizationFundamentalClass] using hfund

theorem fourZeroCentralRealizationBase_map_pairwise_eq :
    (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
        fourZeroCentralRealizationBase =
      (SSet.toTop.map
        (fourZeroMeridianBoundaryInclCentral ≫
          fourZeroCentralInterfaceInclPairwise)).hom
        fourZeroBoundaryRealizationBase := by
  rw [show fourZeroCentralRealizationBase =
      (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
        fourZeroBoundaryRealizationBase by
    exact fourZeroBoundaryRealizationBase_map_central_eq.symm]
  exact (ConcreteCategory.congr_hom
    (SSet.toTop.map_comp fourZeroMeridianBoundaryInclCentral
      fourZeroCentralInterfaceInclPairwise)
    fourZeroBoundaryRealizationBase).symm

/-- The four-zero meridian is a nonzero kernel class for the central-to-pairwise map on `π₁`. -/
theorem fourZeroCentralInterfaceInclPairwise_piOne_map_not_injective :
    ¬ Function.Injective
      (HomotopyGroup.map (N := Fin 1)
        (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
        fourZeroCentralRealizationBase_map_pairwise_eq) := by
  intro hinjective
  apply fourZeroBoundaryInclCentral_piOne_map_ne_one
  apply hinjective
  have hcomp := HomotopyGroup.map_comp_apply (N := Fin 1)
    (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
    fourZeroCentralRealizationBase_map_pairwise_eq
    (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
    fourZeroBoundaryRealizationBase_map_central_eq
    fourZeroBoundaryRealizationPiOneClass
  have hcontinuous :
      (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom.comp
          (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom =
        (SSet.toTop.map
          (fourZeroMeridianBoundaryInclCentral ≫
            fourZeroCentralInterfaceInclPairwise)).hom := by
    apply ContinuousMap.ext
    intro z
    exact (ConcreteCategory.congr_hom
      (SSet.toTop.map_comp fourZeroMeridianBoundaryInclCentral
        fourZeroCentralInterfaceInclPairwise) z).symm
  have hcontinuousBase :
      ((SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom.comp
          (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom)
          fourZeroBoundaryRealizationBase =
        (SSet.toTop.map
          (fourZeroMeridianBoundaryInclCentral ≫
            fourZeroCentralInterfaceInclPairwise)).hom
          fourZeroBoundaryRealizationBase :=
    congrArg (fun k => k fourZeroBoundaryRealizationBase) hcontinuous
  have hcongr := HomotopyGroup.map_congr (N := Fin 1)
    hcontinuous hcontinuousBase rfl fourZeroBoundaryRealizationPiOneClass
  have htrivial := fourZeroMeridianViaCentralInclPairwise_piOne_trivial
    fourZeroBoundaryRealizationBase
    fourZeroBoundaryRealizationPiOneClass
  have hkill :
      HomotopyGroup.map
        (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
        fourZeroCentralRealizationBase_map_pairwise_eq
        (HomotopyGroup.map
          (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
          fourZeroBoundaryRealizationBase_map_central_eq
          fourZeroBoundaryRealizationPiOneClass) = 1 :=
    hcomp.trans (hcongr.trans htrivial)
  exact hkill.trans
    ((HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
      fourZeroCentralRealizationBase_map_pairwise_eq).map_one).symm

end Submission.ComplexProjectivePlaneTriangulation
