/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.SphereCellCompressionSource
import Submission.Approximation.NorthPoleGeneralPosition

/-!
# Stable injectivity of spherical cap excision

The endpoint preparation, finite PL approximation, stable two-cell compression, and explicit
puncture bridge now compose to a homotopy in the source lower-cap/overlap pair.  Therefore two
source representatives whose inclusions are relatively homotopic in the target were already
relatively homotopic whenever `q + 3 ≤ 2d`.

Passing to quotient classes proves the injective half of stable spherical cap excision.  Together
with ordinary point-avoidance surjectivity, this also gives unconditional bijectivity in the
overlap of the two ranges.

## Main results

* `Submission.relGenLoop_homotopic_of_includedSourceHomotopy_stableRange`
* `Submission.sphereSuspensionExcisionHomAt_injective_of_stableRange`
* `Submission.sphereSuspensionExcisionHomAt_bijective_of_dimension`
-/

open Set
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {d q : ℕ}

/-- A target homotopy between included source representatives descends to a source-pair
homotopy in the stable two-cell range. -/
theorem relGenLoop_homotopic_of_includedSourceHomotopy_stableRange
    {p r : RelGenLoop (q + 2) (sphLowerCap d)
      (sphCapOverlapInLower d) (sphCapOverlapBase d)}
    (H₀ : ContinuousMap.HomotopyWith
      (RelGenLoop.map (sphCapInclusionPairMap d) p).val
      (RelGenLoop.map (sphCapInclusionPairMap d) r).val
      (fun f => f ∈ RelGenLoop (q + 2) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)))
    (hrange : q + 3 ≤ 2 * d) :
    RelGenLoop.Homotopic p r := by
  obtain ⟨H', hzero, hone, hheight, hjar, hend, A,
      x, y, hx, hy, g', K, hKx, hgy⟩ :=
    exists_includedSourceHomotopy_cellCompression_with_prepared_endpoints H₀ hrange
  have hprepareZero := relGenLoopHomotopic_endpointCapSqueezedSource p
  have hprepareOne := relGenLoopHomotopic_endpointCapSqueezedSource r
  have happroxZero := relativeSpherePLHomotopy_sourceZero_homotopic
    H' hheight hjar hend A (endpointCapSqueezedSourceRelGenLoop p) hzero
  have happroxOne := relativeSpherePLHomotopy_sourceOne_homotopic
    H' hheight hjar hend A (endpointCapSqueezedSourceRelGenLoop r) hone
  have hcompressed :=
    relativeSpherePLHomotopy_cellCompression_sourceEndpoints_homotopic
      H' hheight hjar hend A x y hx hy g' K hKx hgy
  exact hprepareZero.trans <| happroxZero.trans <|
    hcompressed.trans <| happroxOne.symm.trans hprepareOne.symm

/-- Homotopy of the included loops as relative loops is enough; choose its representing target
homotopy and apply the preceding theorem. -/
theorem relGenLoop_homotopic_of_map_homotopic_stableRange
    {p r : RelGenLoop (q + 2) (sphLowerCap d)
      (sphCapOverlapInLower d) (sphCapOverlapBase d)}
    (hpr : RelGenLoop.Homotopic
      (RelGenLoop.map (sphCapInclusionPairMap d) p)
      (RelGenLoop.map (sphCapInclusionPairMap d) r))
    (hrange : q + 3 ≤ 2 * d) :
    RelGenLoop.Homotopic p r :=
  relGenLoop_homotopic_of_includedSourceHomotopy_stableRange hpr.some hrange

/-- The cap-inclusion map on relative homotopy groups is injective throughout the stable
two-cell range. -/
theorem sphereSuspensionExcisionHomAt_injective_of_stableRange
    (d q : ℕ) (hrange : q + 3 ≤ 2 * d) :
    Function.Injective (sphereSuspensionExcisionHomAt d q) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ p =>
      induction b using Quotient.inductionOn with
      | _ r =>
          change (⟦RelGenLoop.map (sphCapInclusionPairMap d) p⟧ :
              π_rel (q + 2) (Sph (d + 1)) (sphUpperCap d)
                (sphUpperCapBase d)) =
            ⟦RelGenLoop.map (sphCapInclusionPairMap d) r⟧ at hab
          have hpr : RelGenLoop.Homotopic
              (RelGenLoop.map (sphCapInclusionPairMap d) p)
              (RelGenLoop.map (sphCapInclusionPairMap d) r) :=
            Quotient.exact hab
          exact Quotient.sound
            (relGenLoop_homotopic_of_map_homotopic_stableRange hpr hrange)

/-- In the ordinary point-avoidance range, the cap-excision map is now unconditionally
bijective: surjectivity comes from avoiding the north pole, while stable two-cell compression
supplies injectivity. -/
theorem sphereSuspensionExcisionHomAt_bijective_of_dimension
    (d q : ℕ) (hdim : q + 2 ≤ d) :
    Function.Bijective (sphereSuspensionExcisionHomAt d q) := by
  have hrange : q + 3 ≤ 2 * d := by omega
  exact ⟨sphereSuspensionExcisionHomAt_injective_of_stableRange d q hrange,
    sphereSuspensionExcisionHomAt_surjective_of_dimension d q hdim⟩

end Submission
