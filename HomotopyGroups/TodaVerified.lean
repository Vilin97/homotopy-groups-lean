import HomotopyGroups.TodaTable

/-!
# Kernel-checked regions of the integral Toda table

The generated 20-by-20 table remains a single benchmark problem. This module records the two
regions already implied by maintained uniform computations: all 20 diagonal entries and all 19
positive-offset entries in the circle row.
-/

open scoped Topology

namespace HomotopyGroups

@[simp] theorem todaIntegralGroupCode_diagonal (nIndex : Fin 20) :
    todaIntegralGroupCode nIndex 0 = .infiniteCyclic := by
  fin_cases nIndex <;> rfl

/-- Embed the positive offsets 1 through 19 into the table's offset index. -/
def todaPositiveOffsetIndex (kIndex : Fin 19) : Fin 20 :=
  ⟨kIndex.val + 1, by omega⟩

@[simp] theorem todaIntegralGroupCode_circle_positive (kIndex : Fin 19) :
    todaIntegralGroupCode 0 (todaPositiveOffsetIndex kIndex) = .finiteCyclic 1 := by
  fin_cases kIndex <;> rfl

private def subsingletonMulEquiv
    (G H : Type*) [Group G] [Group H] [Subsingleton G] [Subsingleton H] :
    G ≃* H where
  toFun := fun _ => 1
  invFun := fun _ => 1
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := fun _ => Subsingleton.elim _ _
  map_mul' := fun _ _ => Subsingleton.elim _ _

private theorem circleHigherToda (j : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (j + 2) (SphereSpace 1) (sphereBasepoint 1) ≃*
        Multiplicative (ZMod 1)) := by
  letI := Submission.sph_one_higher_homotopy_subsingleton_at j (sphereBasepoint 1)
  exact ⟨subsingletonMulEquiv _ _⟩

/-- The 20 diagonal entries in the generated Toda table, proved by the uniform sphere-diagonal
calculation. -/
theorem toda_unstable_integral_diagonal (nIndex : Fin 20) :
    Nonempty
      (HomotopyGroup.Pi (nIndex.val + 1)
          (SphereSpace (nIndex.val + 1)) (sphereBasepoint (nIndex.val + 1)) ≃*
        todaIntegralGroup nIndex 0) := by
  rw [todaIntegralGroup, todaIntegralGroupCode_diagonal]
  exact sphere_diagonal_homotopy_mulEquiv_int nIndex.val

/-- The 19 positive-offset entries in the circle row of the generated Toda table, proved by
higher metric-circle vanishing. -/
theorem toda_unstable_integral_circle_positive (kIndex : Fin 19) :
    Nonempty
      (HomotopyGroup.Pi (kIndex.val + 2) (SphereSpace 1) (sphereBasepoint 1) ≃*
        todaIntegralGroup 0 (todaPositiveOffsetIndex kIndex)) := by
  rw [todaIntegralGroup, todaIntegralGroupCode_circle_positive]
  exact circleHigherToda kIndex.val

end HomotopyGroups
