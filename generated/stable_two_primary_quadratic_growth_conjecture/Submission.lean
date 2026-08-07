import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped BigOperators Topology

namespace Submission

theorem stable_two_primary_quadratic_growth_conjecture :
    ∃ C : ℝ, C ≠ 0 ∧
      Filter.Tendsto
        (fun k : ℕ =>
          Real.logb 2 ((cumulativeTwoPrimaryStableOrder k : ℕ) : ℝ) /
            (k : ℝ) ^ 2)
        Filter.atTop (nhds C) := by
  sorry

end Submission
