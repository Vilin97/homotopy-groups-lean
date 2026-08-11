/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Lemmas about the simplex category

-/

@[expose] public section

namespace SimplexCategory

lemma δ_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    SimplexCategory.δ i j = Fin.succAbove i j := rfl

lemma σ_apply {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    SimplexCategory.σ i j = Fin.predAbove i j := rfl

end SimplexCategory
