/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneProjectiveLineConnectivity

/-!
# Exact connectivity of the embedded projective line

The mapping-cylinder model proves the correct relative statement for the projective-line map.
This file strengthens it to the literal subspace of geometric `CP²`: the range of the standard
closed embedding `CP¹ → CP²`.  The embedding identifies its source homeomorphically with that
range, so functoriality transfers the already-computed induced maps to the actual subspace
inclusion.  The long exact sequence then proves that the pair is three-connected.

Its relative fourth homotopy group surjects onto `π₃(CP¹) = ℤ`, because `π₃(CP²) = 0`.
Consequently the embedded pair is not four-connected.  The finite four-triangle comparison has
exactly the same range, so the identical literal subspace result applies to it as well.
-/

open CategoryTheory
open scoped Topology Topology.Homotopy TopCat

noncomputable section

namespace Submission

universe u

/-! ## Embedded ranges and the relative long exact sequence -/

/-- If an embedding induces a bijection on a homotopy group, then inclusion of its literal
range induces a bijection on the same group. -/
theorem homotopyGroup_iStar_range_bijective_of_map_bijective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y)) (hf : Topology.IsEmbedding f) (x : X)
    (hmap : Function.Bijective
      (HomotopyGroup.map (N := Fin n) (x := x) (y := f x) f rfl)) :
    Function.Bijective
      (RelHomotopyGroup.iStar n Y (Set.range f) (hf.toHomeomorph x)) := by
  let e : X ≃ₜ Set.range f := hf.toHomeomorph
  let eMap : C(X, Set.range f) := ⟨e, e.continuous⟩
  have he : Function.Bijective
      (HomotopyGroup.map (N := Fin n) (x := x) (y := e x) eMap rfl) :=
    (HomotopyGroup.homeomorphEquiv e x).bijective
  have hcomp :
      (RelHomotopyGroup.iStar n Y (Set.range f) (e x)) ∘
          (HomotopyGroup.map (N := Fin n) (x := x) (y := e x) eMap rfl) =
        HomotopyGroup.map (N := Fin n) (x := x) (y := f x) f rfl := by
    funext z
    change HomotopyGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.range f, Y)) rfl
          (HomotopyGroup.map eMap rfl z) =
      HomotopyGroup.map f rfl z
    rw [HomotopyGroup.map_comp_apply]
    rfl
  apply (Function.Bijective.of_comp_iff _ he).mp
  rw [hcomp]
  exact hmap

/-- If an embedding induces a surjection on a homotopy group, then inclusion of its literal
range induces a surjection on the same group. -/
theorem homotopyGroup_iStar_range_surjective_of_map_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y)) (hf : Topology.IsEmbedding f) (x : X)
    (hmap : Function.Surjective
      (HomotopyGroup.map (N := Fin n) (x := x) (y := f x) f rfl)) :
    Function.Surjective
      (RelHomotopyGroup.iStar n Y (Set.range f) (hf.toHomeomorph x)) := by
  let e : X ≃ₜ Set.range f := hf.toHomeomorph
  let eMap : C(X, Set.range f) := ⟨e, e.continuous⟩
  have hcomp :
      (RelHomotopyGroup.iStar n Y (Set.range f) (e x)) ∘
          (HomotopyGroup.map (N := Fin n) (x := x) (y := e x) eMap rfl) =
        HomotopyGroup.map (N := Fin n) (x := x) (y := f x) f rfl := by
    funext z
    change HomotopyGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.range f, Y)) rfl
          (HomotopyGroup.map eMap rfl z) =
      HomotopyGroup.map f rfl z
    rw [HomotopyGroup.map_comp_apply]
    rfl
  apply Function.Surjective.of_comp
  rw [hcomp]
  exact hmap

/-- A literal pair is three-connected when its inclusion is bijective in degrees zero, one,
and two and surjective in degree three. -/
theorem isThreeConnectedPair_of_bijective_iStar_low_of_surjective_three
    {Y : Type} [TopologicalSpace Y] (A : Set Y)
    (hzero : ∀ a : A, Function.Bijective
      (RelHomotopyGroup.iStar 0 Y A a))
    (hone : ∀ a : A, Function.Bijective
      (RelHomotopyGroup.iStar 1 Y A a))
    (htwo : ∀ a : A, Function.Bijective
      (RelHomotopyGroup.iStar 2 Y A a))
    (hthree : ∀ a : A, Function.Surjective
      (RelHomotopyGroup.iStar 3 Y A a)) :
    IsNConnectedPair 3 Y A where
  surjective_iStar_zero a := (hzero a).surjective
  unique_piRel k hk a := by
    have hk' : k ≤ 2 := by omega
    interval_cases k
    · exact RelHomotopyGroup.unique_of_surjective_iStar_succ_of_injective_iStar
        0 Y A a (hone a).surjective (hzero a).injective
    · exact RelHomotopyGroup.unique_of_surjective_iStar_succ_of_injective_iStar
        1 Y A a (htwo a).surjective (hone a).injective
    · exact RelHomotopyGroup.unique_of_surjective_iStar_succ_of_injective_iStar
        2 Y A a (hthree a) (htwo a).injective

/-- If `π₃(A)` is infinite and `π₃(Y)` is trivial at the same basepoint, then relative `π₄`
of `(Y, A)` is infinite. -/
theorem RelHomotopyGroup.piFour_infinite_of_subspace_piThree
    {Y : Type*} [TopologicalSpace Y] {A : Set Y} (a : A)
    (hsubspace : Infinite (π_ 3 A a))
    (hambient : Subsingleton (π_ 3 Y (a : Y))) :
    Infinite (RelHomotopyGroup 4 Y A a) := by
  letI : Infinite (π_ 3 A a) := hsubspace
  letI : Subsingleton (π_ 3 Y (a : Y)) := hambient
  apply Infinite.of_surjective (RelHomotopyGroup.bd 3 Y A a)
  intro z
  exact (RelHomotopyGroup.mulExact_bdHom_iStarHom 2 Y A a z).mp
    (Subsingleton.elim _ _)

/-! ## The literal bottom projective line in geometric `CP²` -/

/-- The maintained bottom-projective-line morphism is a topological embedding. -/
theorem complexProjectivePlaneBottomInclTopCat_isEmbedding :
    Topology.IsEmbedding complexProjectivePlaneBottomInclTopCat.hom :=
  complexProjectivePlaneBottomIncl_isClosedEmbedding.isEmbedding

/-- The standard bottom projective line as a literal subspace of geometric `CP²`. -/
def complexProjectivePlaneProjectiveLine : Set (ComplexProjectiveModel 2) :=
  Set.range complexProjectivePlaneBottomInclTopCat.hom

/-- The standard embedding identifies `CP¹` homeomorphically with its literal range in
`CP²`. -/
noncomputable def complexProjectivePlaneProjectiveLineHomeomorph :
    ComplexProjectiveModel 1 ≃ₜ complexProjectivePlaneProjectiveLine := by
  change ComplexProjectiveModel 1 ≃ₜ Set.range complexProjectivePlaneBottomIncl
  exact complexProjectivePlaneBottomInclTopCat_isEmbedding.toHomeomorph

/-- The maintained basepoint of the literal projective-line subspace. -/
noncomputable def complexProjectivePlaneProjectiveLineBasepoint :
    complexProjectivePlaneProjectiveLine :=
  complexProjectivePlaneProjectiveLineHomeomorph
    (complexProjectiveModelBasepoint 1)

/-- The literal projective-line basepoint is the maintained basepoint of geometric `CP²`. -/
@[simp]
theorem complexProjectivePlaneProjectiveLineBasepoint_coe :
    (complexProjectivePlaneProjectiveLineBasepoint : ComplexProjectiveModel 2) =
      complexProjectiveModelBasepoint 2 := by
  change complexProjectivePlaneBottomIncl (complexProjectiveModelBasepoint 1) =
    complexProjectiveModelBasepoint 2
  exact complexProjectivePlaneBottomIncl_basepoint

/-- Inclusion of the literal bottom projective line is bijective on path components at every
basepoint. -/
theorem complexProjectivePlaneProjectiveLine_iStar_piZero_bijective
    (a : complexProjectivePlaneProjectiveLine) :
    Function.Bijective
      (RelHomotopyGroup.iStar 0 (ComplexProjectiveModel 2)
        complexProjectivePlaneProjectiveLine a) := by
  obtain ⟨x, rfl⟩ :=
    complexProjectivePlaneProjectiveLineHomeomorph.surjective a
  change Function.Bijective
    (RelHomotopyGroup.iStar 0 (ComplexProjectiveModel 2)
      (Set.range complexProjectivePlaneBottomInclTopCat.hom)
      (complexProjectivePlaneBottomInclTopCat_isEmbedding.toHomeomorph x))
  exact homotopyGroup_iStar_range_bijective_of_map_bijective
    0 complexProjectivePlaneBottomInclTopCat.hom
    complexProjectivePlaneBottomInclTopCat_isEmbedding x
    (complexProjectivePlaneBottomIncl_piZero_bijective_at x)

/-- Inclusion of the literal bottom projective line is bijective on fundamental groups at
every basepoint. -/
theorem complexProjectivePlaneProjectiveLine_iStar_piOne_bijective
    (a : complexProjectivePlaneProjectiveLine) :
    Function.Bijective
      (RelHomotopyGroup.iStar 1 (ComplexProjectiveModel 2)
        complexProjectivePlaneProjectiveLine a) := by
  obtain ⟨x, rfl⟩ :=
    complexProjectivePlaneProjectiveLineHomeomorph.surjective a
  change Function.Bijective
    (RelHomotopyGroup.iStar 1 (ComplexProjectiveModel 2)
      (Set.range complexProjectivePlaneBottomInclTopCat.hom)
      (complexProjectivePlaneBottomInclTopCat_isEmbedding.toHomeomorph x))
  exact homotopyGroup_iStar_range_bijective_of_map_bijective
    1 complexProjectivePlaneBottomInclTopCat.hom
    complexProjectivePlaneBottomInclTopCat_isEmbedding x
    (complexProjectivePlaneBottomIncl_piOne_bijective_at x)

/-- Inclusion of the literal bottom projective line is bijective on second homotopy groups at
every basepoint. -/
theorem complexProjectivePlaneProjectiveLine_iStar_piTwo_bijective
    (a : complexProjectivePlaneProjectiveLine) :
    Function.Bijective
      (RelHomotopyGroup.iStar 2 (ComplexProjectiveModel 2)
        complexProjectivePlaneProjectiveLine a) := by
  obtain ⟨x, rfl⟩ :=
    complexProjectivePlaneProjectiveLineHomeomorph.surjective a
  change Function.Bijective
    (RelHomotopyGroup.iStar 2 (ComplexProjectiveModel 2)
      (Set.range complexProjectivePlaneBottomInclTopCat.hom)
      (complexProjectivePlaneBottomInclTopCat_isEmbedding.toHomeomorph x))
  exact homotopyGroup_iStar_range_bijective_of_map_bijective
    2 complexProjectivePlaneBottomInclTopCat.hom
    complexProjectivePlaneBottomInclTopCat_isEmbedding x
    (complexProjectivePlaneBottomIncl_piTwo_bijective_at x)

/-- Inclusion of the literal bottom projective line is surjective on third homotopy groups at
every basepoint. -/
theorem complexProjectivePlaneProjectiveLine_iStar_piThree_surjective
    (a : complexProjectivePlaneProjectiveLine) :
    Function.Surjective
      (RelHomotopyGroup.iStar 3 (ComplexProjectiveModel 2)
        complexProjectivePlaneProjectiveLine a) := by
  obtain ⟨x, rfl⟩ :=
    complexProjectivePlaneProjectiveLineHomeomorph.surjective a
  change Function.Surjective
    (RelHomotopyGroup.iStar 3 (ComplexProjectiveModel 2)
      (Set.range complexProjectivePlaneBottomInclTopCat.hom)
      (complexProjectivePlaneBottomInclTopCat_isEmbedding.toHomeomorph x))
  exact homotopyGroup_iStar_range_surjective_of_map_surjective
    3 complexProjectivePlaneBottomInclTopCat.hom
    complexProjectivePlaneBottomInclTopCat_isEmbedding x
    (complexProjectivePlaneBottomIncl_piThree_surjective_at x)

/-- The literal embedded pair `(CP², CP¹)` is three-connected. -/
theorem complexProjectivePlaneProjectiveLine_isThreeConnectedPair :
    IsNConnectedPair 3 (ComplexProjectiveModel 2)
      complexProjectivePlaneProjectiveLine :=
  isThreeConnectedPair_of_bijective_iStar_low_of_surjective_three
    complexProjectivePlaneProjectiveLine
    complexProjectivePlaneProjectiveLine_iStar_piZero_bijective
    complexProjectivePlaneProjectiveLine_iStar_piOne_bijective
    complexProjectivePlaneProjectiveLine_iStar_piTwo_bijective
    complexProjectivePlaneProjectiveLine_iStar_piThree_surjective

/-- Relative `π₁(CP², CP¹)` is trivial at every basepoint of the literal projective line. -/
theorem complexProjectivePlaneProjectiveLine_relative_piOne_unique
    (a : complexProjectivePlaneProjectiveLine) :
    Nonempty
      (Unique
        (RelHomotopyGroup 1 (ComplexProjectiveModel 2)
          complexProjectivePlaneProjectiveLine a)) :=
  complexProjectivePlaneProjectiveLine_isThreeConnectedPair.unique_piRel
    0 (by omega) a

/-- Relative `π₂(CP², CP¹)` is trivial at every basepoint of the literal projective line. -/
theorem complexProjectivePlaneProjectiveLine_relative_piTwo_unique
    (a : complexProjectivePlaneProjectiveLine) :
    Nonempty
      (Unique
        (RelHomotopyGroup 2 (ComplexProjectiveModel 2)
          complexProjectivePlaneProjectiveLine a)) :=
  complexProjectivePlaneProjectiveLine_isThreeConnectedPair.unique_piRel
    1 (by omega) a

/-- Relative `π₃(CP², CP¹)` is trivial at every basepoint of the literal projective line. -/
theorem complexProjectivePlaneProjectiveLine_relative_piThree_unique
    (a : complexProjectivePlaneProjectiveLine) :
    Nonempty
      (Unique
        (RelHomotopyGroup 3 (ComplexProjectiveModel 2)
          complexProjectivePlaneProjectiveLine a)) :=
  complexProjectivePlaneProjectiveLine_isThreeConnectedPair.unique_piRel
    2 (by omega) a

/-- The literal projective line has infinite cyclic third homotopy group at the maintained
basepoint. -/
noncomputable def complexProjectivePlaneProjectiveLinePiThreeMulEquivInt :
    π_ 3 complexProjectivePlaneProjectiveLine
        complexProjectivePlaneProjectiveLineBasepoint ≃* Multiplicative ℤ := by
  let rangeEquiv := HomotopyGroup.homeomorphMulEquivOfEq
    (N := Fin 3) (x := complexProjectiveModelBasepoint 1)
    (y := complexProjectivePlaneProjectiveLineBasepoint)
    complexProjectivePlaneProjectiveLineHomeomorph rfl
  exact rangeEquiv.symm.trans
    (Classical.choice piThree_complexProjectiveLine_mulEquiv_int)

/-- Relative `π₄(CP², CP¹)` of the literal embedded pair is infinite. -/
theorem complexProjectivePlaneProjectiveLine_relative_piFour_infinite :
    Infinite
      (RelHomotopyGroup 4 (ComplexProjectiveModel 2)
        complexProjectivePlaneProjectiveLine
        complexProjectivePlaneProjectiveLineBasepoint) := by
  let e := complexProjectivePlaneProjectiveLinePiThreeMulEquivInt
  letI : Infinite
      (π_ 3 complexProjectivePlaneProjectiveLine
        complexProjectivePlaneProjectiveLineBasepoint) :=
    Infinite.of_injective e.symm e.symm.injective
  exact RelHomotopyGroup.piFour_infinite_of_subspace_piThree
    complexProjectivePlaneProjectiveLineBasepoint inferInstance
    (piThree_complexProjectivePlane_subsingleton_at _)

/-- The literal embedded pair `(CP², CP¹)` is not four-connected. -/
theorem complexProjectivePlaneProjectiveLine_not_isFourConnectedPair :
    ¬ IsNConnectedPair 4 (ComplexProjectiveModel 2)
      complexProjectivePlaneProjectiveLine :=
  not_isFourConnectedPair_of_infinite_relative_piFour
    complexProjectivePlaneProjectiveLineBasepoint
    complexProjectivePlaneProjectiveLine_relative_piFour_infinite

/-- The literal embedded pair `(CP², CP¹)` has connectivity exactly three. -/
theorem complexProjectivePlaneProjectiveLine_connectivity_exactly_three :
    IsNConnectedPair 3 (ComplexProjectiveModel 2)
        complexProjectivePlaneProjectiveLine ∧
      ¬ IsNConnectedPair 4 (ComplexProjectiveModel 2)
        complexProjectivePlaneProjectiveLine :=
  ⟨complexProjectivePlaneProjectiveLine_isThreeConnectedPair,
    complexProjectivePlaneProjectiveLine_not_isFourConnectedPair⟩

/-! ## The same literal range from the finite comparison -/

namespace ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The literal range pair of the finite projective-line comparison is three-connected. -/
theorem projectiveLineRealizationToComplexProjectivePlane_range_isThreeConnectedPair :
    IsNConnectedPair 3 (ComplexProjectiveModel 2)
      (Set.range projectiveLineRealizationToComplexProjectivePlane) := by
  rw [projectiveLineRealizationToComplexProjectivePlane_range]
  exact complexProjectivePlaneProjectiveLine_isThreeConnectedPair

/-- The literal range pair of the finite projective-line comparison is not four-connected. -/
theorem projectiveLineRealizationToComplexProjectivePlane_range_not_isFourConnectedPair :
    ¬ IsNConnectedPair 4 (ComplexProjectiveModel 2)
      (Set.range projectiveLineRealizationToComplexProjectivePlane) := by
  rw [projectiveLineRealizationToComplexProjectivePlane_range]
  exact complexProjectivePlaneProjectiveLine_not_isFourConnectedPair

/-- The literal range pair of the finite projective-line comparison has connectivity exactly
three. -/
theorem projectiveLineRealizationToComplexProjectivePlane_range_connectivity_exactly_three :
    IsNConnectedPair 3 (ComplexProjectiveModel 2)
        (Set.range projectiveLineRealizationToComplexProjectivePlane) ∧
      ¬ IsNConnectedPair 4 (ComplexProjectiveModel 2)
        (Set.range projectiveLineRealizationToComplexProjectivePlane) :=
  ⟨projectiveLineRealizationToComplexProjectivePlane_range_isThreeConnectedPair,
    projectiveLineRealizationToComplexProjectivePlane_range_not_isFourConnectedPair⟩

end ComplexProjectivePlaneTriangulation

end Submission
