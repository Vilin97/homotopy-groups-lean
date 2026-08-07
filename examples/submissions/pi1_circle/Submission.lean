import Mathlib
import Submission.Helpers

open scoped Topology

noncomputable section

namespace Submission

private def intAddEquivZMultiplesTwoPi :
    ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi) := by
  let f : ℤ →+ AddSubgroup.zmultiples (2 * Real.pi) :=
    { toFun := fun n =>
        ⟨n • (2 * Real.pi), AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := by intro m n; ext; simp [add_mul] }
  exact AddEquiv.ofBijective f ⟨by
    intro m n h
    apply smul_left_injective ℤ Real.two_pi_pos.ne'
    exact congrArg Subtype.val h
  , by
    rintro ⟨r, hr⟩
    rcases AddSubgroup.mem_zmultiples_iff.mp hr with ⟨n, rfl⟩
    exact ⟨n, rfl⟩⟩

theorem pi1_circle_mulEquiv_int :
    Nonempty
      (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃*
        Multiplicative ℤ) := by
  let e : Circle.exp ⁻¹' ({1} : Set Circle) := ⟨0, by simp⟩
  let coverEquiv := Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e
  exact ⟨HomotopyGroup.pi1MulEquivFundamentalGroup.trans <|
    coverEquiv.trans <| MulOpposite.opMulEquiv.symm.trans <|
      intAddEquivZMultiplesTwoPi.symm.toMultiplicative⟩

end Submission
