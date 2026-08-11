/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.ProdSphereStep
import Submission.Homology.WangPathFibration

/-!
# The homology of `Ω S^{d+1}`, unconditionally

`Submission/Homology/WangPathFibration.lean` computes `H_*(Ω S^{d+1})` from the Wang sequence,
taking the product formula `H_{n+d}(F × Sᵈ) ≅ H_{n+d}(F) ⊞ Hₙ(F)` as the hypotheses
`ProdSphereSplitting` and `ProdSphereLowIso`. Both are now theorems for every space and every `d`
(`Submission/Homology/ProdSphereStep.lean`), so this file simply instantiates them.

## Main results

* `Submission.loopSphereHgrpPeriodicity` — `Hₙ(Ω S^{d+1}) ≅ H_{n+d}(Ω S^{d+1})`;
* `Submission.loopSphereHgrpMul` — `H_{j d}(Ω S^{d+1}) ≅ ℤ`;
* `Submission.isZero_loopSphereHgrp` — `H_k(Ω S^{d+1}) = 0` when `d ∤ k`.

Together: `H_k(Ω S^{d+1}; ℤ) = ℤ` if `d ∣ k` and `0` otherwise, for `d ≥ 1`.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

variable {d : ℕ} (x₀ : Sph (d + 1))

/-! ### `H_*(Ω S^{d+1})`, unconditionally

`Submission/Homology/ProdSphereStep.lean` proves `ProdSphereSplitting` and `ProdSphereLowIso` for
every space and every `d`, so the results above can be instantiated outright. -/

/-- The product formula for the fibre of the path fibration. -/
noncomputable def pathFibProdSplitting : ProdSphereSplitting (pathFib x₀) d :=
  prodSphereSplitting (pathFib x₀) d

/-- The low-degree half of the product formula for the fibre. -/
theorem pathFibProdLowIso : ProdSphereLowIso (pathFib x₀) d :=
  prodSphereLowIso (pathFib x₀) d

/-- **`H_*(Ω S^{d+1})` is `d`-periodic**, unconditionally. -/
noncomputable def loopSphereHgrpPeriodicity (hd : 0 < d) (n : ℕ) :
    Hgrp n (pathFib x₀) ≅ Hgrp (n + d) (pathFib x₀) :=
  pathFibPeriodicity x₀ (pathFibProdSplitting x₀) hd n

/-- **`H_{j d}(Ω S^{d+1}) ≅ ℤ`**, unconditionally. -/
noncomputable def loopSphereHgrpMul (hd : 0 < d) (j : ℕ) :
    Hgrp (j * d) (pathFib x₀) ≅ AddCommGrpCat.of ℤ :=
  hgrpPathFib_mul x₀ (pathFibProdSplitting x₀) hd j

/-- **`H_k(Ω S^{d+1}) = 0` when `d ∤ k`**, unconditionally. -/
theorem isZero_loopSphereHgrp (hd : 0 < d) (k : ℕ) (hk : ¬ d ∣ k) :
    IsZero (Hgrp k (pathFib x₀)) :=
  isZero_hgrpPathFib x₀ (pathFibProdSplitting x₀) (pathFibProdLowIso x₀) hd k hk

/-- **`H_k(Ω S^{d+1}) = 0` for `0 < k < d`**, unconditionally. -/
theorem isZero_loopSphereHgrp_of_lt (k : ℕ) (hk0 : 0 < k) (hk : k < d) :
    IsZero (Hgrp k (pathFib x₀)) :=
  isZero_pathFib_of_lt x₀ (pathFibProdLowIso x₀) k hk0 hk

end Submission
