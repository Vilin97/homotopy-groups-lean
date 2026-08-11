/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia

Vendored from https://github.com/jzxia/WhiteheadTheorem (Apache 2.0) via Vilin97/lean-pool.
-/

import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Sphere

/-!
# Submission.WhiteheadTheorem.Shapes.Disk

Imported Lean Pool material for `Submission.WhiteheadTheorem.Shapes.Disk`.

The definitions of `TopCat.disk`, `TopCat.diskBoundary`, `TopCat.sphere` and the notations
`𝔻 n`, `∂𝔻 n`, `𝕊 n` that this file originally introduced have since been upstreamed to
`Mathlib.Topology.Category.TopCat.Sphere`, so they are taken from Mathlib here.
-/

universe u


namespace TopCat

open scoped TopCat

/-- The inclusion `∂𝔻 n ⟶ 𝔻 n` of the boundary of the `n`-disk. -/
def diskBoundaryIncl (n : ℕ) : diskBoundary.{u} n ⟶ disk.{u} n :=
  ofHom
    { toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
        rw [isOpen_induced_iff, ← hst, ← hrs]
        tauto⟩ }

instance isEmpty_diskBoundary_zero : IsEmpty (diskBoundary.{u} 0) := by
  unfold diskBoundary
  simp_all only [isEmpty_ulift, Set.isEmpty_coe_sort]
  apply Set.subset_empty_iff.mp
  intro x hx
  have x0 : ‖x‖ = 0 := by rw [Subsingleton.elim x 0, norm_zero]
  simp_all

end TopCat
