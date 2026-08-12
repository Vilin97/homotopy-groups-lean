/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homotopy.Connected
import Submission.Hurewicz.VanishingSorries

/-!
# Homology vanishing for connected pairs

The coherent singular-simplex compression theorem consumes exactly the two fields of
`Submission.IsNConnectedPair`: surjectivity on path components and vanishing of the relative
homotopy groups in a bounded range.  This file packages its standard homological consequences
directly in terms of that connectivity structure.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped Topology

noncomputable section

namespace Submission

namespace IsNConnectedPair

variable {n : ℕ} {X : Type} [TopologicalSpace X] {A : Set X}

/-- An `n`-connected nonempty pair has zero relative singular homology in every degree at most
`n`. -/
theorem isZero_relativeHomology (h : IsNConnectedPair n X A) (hA : A.Nonempty)
    (k : ℕ) (hk : k ≤ n) :
    IsZero (HrelSet (Y := TopCat.of X) k A) :=
  isZero_HrelSet_of_unique_piRel_le n (TopCat.of X) A hA
    h.surjective_iStar_zero
    (fun j hj => h.unique_piRel j (by omega)) k hk

/-- For an `n`-connected nonempty pair, inclusion induces an isomorphism on singular homology
in every degree `k` with `k + 1 ≤ n`. -/
theorem isIso_homologyMap_subIncl (h : IsNConnectedPair n X A) (hA : A.Nonempty)
    (k : ℕ) (hk : k + 1 ≤ n) :
    IsIso (HgrpMap k (subIncl (Y := TopCat.of X) A)) :=
  isIso_relIota_of_unique_piRel_le n (TopCat.of X) A hA
    h.surjective_iStar_zero
    (fun j hj => h.unique_piRel j (by omega)) k hk

/-- For an `n`-connected nonempty pair, inclusion induces an epimorphism on singular homology
in every degree at most `n`. -/
theorem epi_homologyMap_subIncl (h : IsNConnectedPair n X A) (hA : A.Nonempty)
    (k : ℕ) (hk : k ≤ n) :
    Epi (HgrpMap k (subIncl (Y := TopCat.of X) A)) :=
  epi_relIota_of_unique_piRel_le n (TopCat.of X) A hA
    h.surjective_iStar_zero
    (fun j hj => h.unique_piRel j (by omega)) k hk

end IsNConnectedPair

end Submission
