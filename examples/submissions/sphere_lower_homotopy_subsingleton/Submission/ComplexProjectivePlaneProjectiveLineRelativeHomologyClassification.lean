/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneHomology

/-!
# Complete relative homology of `(CP², CP¹)`

The three-connected literal pair already has zero relative homology through degree three and
infinite-cyclic relative homology in degree four.  Above degree four, the long exact sequence
combines vanishing of the absolute homology of `CP²` with vanishing of the projective line's
homology to kill every remaining relative group.  Thus

`H_k(CP², CP¹; ℤ) ≅ ℤ` for `k = 4`, and it is zero for every `k ≠ 4`.

The canonical four-triangle projective-line comparison has exactly the same literal range, so
the identical classification is also recorded directly for that finite-to-geometric pair.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped Topology TopCat

noncomputable section

namespace Submission

/-- The literal embedded projective line has zero integral homology in every degree at least
three. -/
theorem isZero_Hgrp_complexProjectivePlaneProjectiveLine_of_three_le
    (k : ℕ) (hk : 3 ≤ k) :
    IsZero (Hgrp k (TopCat.of complexProjectivePlaneProjectiveLine)) :=
  IsZero.of_iso
    (isZero_Hgrp_sphere k 2 (by omega) (by omega))
    (hgrpIsoOfIso k complexProjectivePlaneProjectiveLineIsoSphereTwo)

/-- Relative integral homology of the literal pair vanishes in every degree at least five. -/
theorem isZero_complexProjectivePlaneProjectiveLine_relativeHomology_of_five_le
    (k : ℕ) (hk : 5 ≤ k) :
    IsZero
      (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) k
        complexProjectivePlaneProjectiveLine) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 :=
    ⟨k - 1, by omega⟩
  let i := subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
    complexProjectivePlaneProjectiveLine
  exact isZero_Hrel_of_epi_of_mono i n
    ((isZero_Hgrp_complexProjectivePlane_of_five_le (n + 1)
      (by omega)).epi _)
    ((isZero_Hgrp_complexProjectivePlaneProjectiveLine_of_three_le n
      (by omega)).mono _)

/-- Relative integral homology of the literal pair vanishes in every degree other than
four. -/
theorem isZero_complexProjectivePlaneProjectiveLine_relativeHomology_of_ne_four
    (k : ℕ) (hk : k ≠ 4) :
    IsZero
      (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) k
        complexProjectivePlaneProjectiveLine) := by
  by_cases hlow : k ≤ 3
  · exact isZero_complexProjectivePlaneProjectiveLine_relativeHomology k hlow
  · exact
      isZero_complexProjectivePlaneProjectiveLine_relativeHomology_of_five_le
        k (by omega)

/-- Complete relative integral homology classification of the literal pair. -/
theorem complexProjectivePlaneProjectiveLine_relativeHomology_classification :
    (∀ k : ℕ, k ≠ 4 →
      IsZero
        (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) k
          complexProjectivePlaneProjectiveLine)) ∧
      Nonempty
        (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) 4
            complexProjectivePlaneProjectiveLine ≅
          AddCommGrpCat.of ℤ) :=
  ⟨isZero_complexProjectivePlaneProjectiveLine_relativeHomology_of_ne_four,
    ⟨complexProjectivePlaneProjectiveLineRelativeHomologyFourIsoInt⟩⟩

/-! ## The literal range of the finite projective-line comparison -/

namespace ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The finite projective-line comparison range has infinite-cyclic relative homology in
degree four. -/
noncomputable def
    projectiveLineRealizationToComplexProjectivePlaneRangeRelativeHomologyFourIsoInt :
    HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) 4
        (Set.range projectiveLineRealizationToComplexProjectivePlane) ≅
      AddCommGrpCat.of ℤ := by
  rw [projectiveLineRealizationToComplexProjectivePlane_range]
  exact complexProjectivePlaneProjectiveLineRelativeHomologyFourIsoInt

/-- The finite projective-line comparison range has zero relative homology outside degree
four. -/
theorem
    isZero_projectiveLineRealizationToComplexProjectivePlaneRange_relativeHomology_of_ne_four
    (k : ℕ) (hk : k ≠ 4) :
    IsZero
      (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) k
        (Set.range projectiveLineRealizationToComplexProjectivePlane)) := by
  rw [projectiveLineRealizationToComplexProjectivePlane_range]
  exact
    isZero_complexProjectivePlaneProjectiveLine_relativeHomology_of_ne_four k hk

/-- Complete relative integral homology classification of the finite comparison range. -/
theorem
    projectiveLineRealizationToComplexProjectivePlaneRange_relativeHomology_classification :
    (∀ k : ℕ, k ≠ 4 →
      IsZero
        (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) k
          (Set.range projectiveLineRealizationToComplexProjectivePlane))) ∧
      Nonempty
        (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) 4
            (Set.range projectiveLineRealizationToComplexProjectivePlane) ≅
          AddCommGrpCat.of ℤ) :=
  ⟨isZero_projectiveLineRealizationToComplexProjectivePlaneRange_relativeHomology_of_ne_four,
    ⟨projectiveLineRealizationToComplexProjectivePlaneRangeRelativeHomologyFourIsoInt⟩⟩

end ComplexProjectivePlaneTriangulation

end Submission
