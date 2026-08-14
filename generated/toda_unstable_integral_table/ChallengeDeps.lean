import Mathlib

/-!
# Homotopy groups of standard spaces

`SphereSpace` is the unit metric sphere in `ℝ^(n+1)`.  The projective-space models
use mathlib's algebraic `Projectivization`, equipped with the quotient topology supplied
by `Mathlib.Topology.Constructions`.  These are concrete topological types, rather than
uninterpreted placeholders.
-/

open scoped Topology

namespace HomotopyGroups

/-- The standard unit `n`-sphere in Euclidean `(n+1)`-space. -/
abbrev SphereSpace (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The first coordinate vector, used as the basepoint of `SphereSpace n`. -/
noncomputable def sphereBasepoint (n : ℕ) : SphereSpace n :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]⟩

/-- Real projective `n`-space with its standard quotient topology. -/
abbrev RealProjectiveSpace (n : ℕ) :=
  Projectivization ℝ (Fin (n + 1) → ℝ)

/-- The quotient topology on real projective space. -/
noncomputable instance instTopologicalSpaceRealProjectiveSpace (n : ℕ) :
    TopologicalSpace (RealProjectiveSpace n) := by
  unfold RealProjectiveSpace Projectivization
  infer_instance

/-- The line spanned by the first coordinate vector. -/
noncomputable def realProjectiveBasepoint (n : ℕ) : RealProjectiveSpace n :=
  Projectivization.mk ℝ (Pi.single 0 1) (Pi.single_ne_zero_iff.mpr one_ne_zero)

/-- Complex projective `n`-space with its standard quotient topology. -/
abbrev ComplexProjectiveSpace (n : ℕ) :=
  Projectivization ℂ (Fin (n + 1) → ℂ)

/-- The quotient topology on complex projective space. -/
noncomputable instance instTopologicalSpaceComplexProjectiveSpace (n : ℕ) :
    TopologicalSpace (ComplexProjectiveSpace n) := by
  unfold ComplexProjectiveSpace Projectivization
  infer_instance

/-- The complex line spanned by the first coordinate vector. -/
noncomputable def complexProjectiveBasepoint (n : ℕ) : ComplexProjectiveSpace n :=
  Projectivization.mk ℂ (Pi.single 0 1) (Pi.single_ne_zero_iff.mpr one_ne_zero)
theorem pi1_circle_mulEquiv_int :
    Nonempty
      (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃*
        Multiplicative ℤ) := by
  sorry
theorem sphere_lower_homotopy_subsingleton
    (n k : ℕ) (hk : k < n) :
    Subsingleton
      (HomotopyGroup.Pi k (SphereSpace n) (sphereBasepoint n)) := by
  sorry
theorem sphere_diagonal_homotopy_mulEquiv_int (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (SphereSpace (n + 1))
          (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) := by
  sorry
theorem pi3_sphere_two_mulEquiv_int :
    Nonempty
      (HomotopyGroup.Pi 3 (SphereSpace 2) (sphereBasepoint 2) ≃*
        Multiplicative ℤ) := by
  sorry
theorem sphere_first_stable_homotopy_mulEquiv_zmod_two
    (n : ℕ) (hn : 3 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (SphereSpace n) (sphereBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  sorry
theorem pi1_realProjectiveSpace_mulEquiv_zmod_two
    (n : ℕ) (hn : 2 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi 1 (RealProjectiveSpace n)
          (realProjectiveBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  sorry
theorem realProjectiveSpace_higher_homotopy_mulEquiv_sphere
    (n k : ℕ) (_hn : 2 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (k + 2) (RealProjectiveSpace n)
          (realProjectiveBasepoint n) ≃*
        HomotopyGroup.Pi (k + 2) (SphereSpace n)
          (sphereBasepoint n)) := by
  sorry
theorem pi1_complexProjectiveSpace_subsingleton
    (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton
      (HomotopyGroup.Pi 1 (ComplexProjectiveSpace n)
        (complexProjectiveBasepoint n)) := by
  sorry
theorem pi2_complexProjectiveSpace_mulEquiv_int
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi 2 (ComplexProjectiveSpace n)
          (complexProjectiveBasepoint n) ≃*
        Multiplicative ℤ) := by
  sorry
theorem complexProjectiveSpace_higher_homotopy_mulEquiv_sphere
    (n k : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (k + 3) (ComplexProjectiveSpace n)
          (complexProjectiveBasepoint n) ≃*
        HomotopyGroup.Pi (k + 3) (SphereSpace (2 * n + 1))
          (sphereBasepoint (2 * n + 1))) := by
  sorry

end HomotopyGroups
open scoped Topology

namespace HomotopyGroups

/-- A concrete syntax for the finitely generated abelian groups in Toda's table. -/
inductive TodaIntegralGroupCode where
  | infiniteCyclic
  | finiteCyclic (order : ℕ)
  | product (left right : TodaIntegralGroupCode)

namespace TodaIntegralGroupCode

/-- Interpret a table code as an actual bundled multiplicative group. -/
noncomputable def asGrp : TodaIntegralGroupCode → GrpCat
  | .infiniteCyclic => GrpCat.of (Multiplicative ℤ)
  | .finiteCyclic order => GrpCat.of (Multiplicative (ZMod order))
  | .product left right => GrpCat.of (left.asGrp × right.asGrp)

end TodaIntegralGroupCode

/--
The additive group in Appendix B at zero-based sphere index `nIndex` and stem
`k`. Thus `nIndex = 0` denotes `S^1`; both indices range from 0 through 19.
-/
def todaIntegralGroupCode (nIndex k : Fin 20) : TodaIntegralGroupCode :=
  match k.val, nIndex.val with
  | 0, 0 => (.infiniteCyclic)
  | 0, 1 => (.infiniteCyclic)
  | 0, 2 => (.infiniteCyclic)
  | 0, 3 => (.infiniteCyclic)
  | 0, 4 => (.infiniteCyclic)
  | 0, 5 => (.infiniteCyclic)
  | 0, 6 => (.infiniteCyclic)
  | 0, 7 => (.infiniteCyclic)
  | 0, 8 => (.infiniteCyclic)
  | 0, 9 => (.infiniteCyclic)
  | 0, 10 => (.infiniteCyclic)
  | 0, 11 => (.infiniteCyclic)
  | 0, 12 => (.infiniteCyclic)
  | 0, 13 => (.infiniteCyclic)
  | 0, 14 => (.infiniteCyclic)
  | 0, 15 => (.infiniteCyclic)
  | 0, 16 => (.infiniteCyclic)
  | 0, 17 => (.infiniteCyclic)
  | 0, 18 => (.infiniteCyclic)
  | 0, 19 => (.infiniteCyclic)
  | 1, 0 => (.finiteCyclic 1)
  | 1, 1 => (.infiniteCyclic)
  | 1, 2 => (.finiteCyclic 2)
  | 1, 3 => (.finiteCyclic 2)
  | 1, 4 => (.finiteCyclic 2)
  | 1, 5 => (.finiteCyclic 2)
  | 1, 6 => (.finiteCyclic 2)
  | 1, 7 => (.finiteCyclic 2)
  | 1, 8 => (.finiteCyclic 2)
  | 1, 9 => (.finiteCyclic 2)
  | 1, 10 => (.finiteCyclic 2)
  | 1, 11 => (.finiteCyclic 2)
  | 1, 12 => (.finiteCyclic 2)
  | 1, 13 => (.finiteCyclic 2)
  | 1, 14 => (.finiteCyclic 2)
  | 1, 15 => (.finiteCyclic 2)
  | 1, 16 => (.finiteCyclic 2)
  | 1, 17 => (.finiteCyclic 2)
  | 1, 18 => (.finiteCyclic 2)
  | 1, 19 => (.finiteCyclic 2)
  | 2, 0 => (.finiteCyclic 1)
  | 2, 1 => (.finiteCyclic 2)
  | 2, 2 => (.finiteCyclic 2)
  | 2, 3 => (.finiteCyclic 2)
  | 2, 4 => (.finiteCyclic 2)
  | 2, 5 => (.finiteCyclic 2)
  | 2, 6 => (.finiteCyclic 2)
  | 2, 7 => (.finiteCyclic 2)
  | 2, 8 => (.finiteCyclic 2)
  | 2, 9 => (.finiteCyclic 2)
  | 2, 10 => (.finiteCyclic 2)
  | 2, 11 => (.finiteCyclic 2)
  | 2, 12 => (.finiteCyclic 2)
  | 2, 13 => (.finiteCyclic 2)
  | 2, 14 => (.finiteCyclic 2)
  | 2, 15 => (.finiteCyclic 2)
  | 2, 16 => (.finiteCyclic 2)
  | 2, 17 => (.finiteCyclic 2)
  | 2, 18 => (.finiteCyclic 2)
  | 2, 19 => (.finiteCyclic 2)
  | 3, 0 => (.finiteCyclic 1)
  | 3, 1 => (.finiteCyclic 2)
  | 3, 2 => .product (.finiteCyclic 4) ((.finiteCyclic 3))
  | 3, 3 => .product (.infiniteCyclic) (.product (.finiteCyclic 4) ((.finiteCyclic 3)))
  | 3, 4 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 5 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 6 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 7 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 8 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 9 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 10 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 11 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 12 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 13 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 14 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 15 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 16 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 17 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 18 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 3, 19 => .product (.finiteCyclic 8) ((.finiteCyclic 3))
  | 4, 0 => (.finiteCyclic 1)
  | 4, 1 => .product (.finiteCyclic 4) ((.finiteCyclic 3))
  | 4, 2 => (.finiteCyclic 2)
  | 4, 3 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 4, 4 => (.finiteCyclic 2)
  | 4, 5 => (.finiteCyclic 1)
  | 4, 6 => (.finiteCyclic 1)
  | 4, 7 => (.finiteCyclic 1)
  | 4, 8 => (.finiteCyclic 1)
  | 4, 9 => (.finiteCyclic 1)
  | 4, 10 => (.finiteCyclic 1)
  | 4, 11 => (.finiteCyclic 1)
  | 4, 12 => (.finiteCyclic 1)
  | 4, 13 => (.finiteCyclic 1)
  | 4, 14 => (.finiteCyclic 1)
  | 4, 15 => (.finiteCyclic 1)
  | 4, 16 => (.finiteCyclic 1)
  | 4, 17 => (.finiteCyclic 1)
  | 4, 18 => (.finiteCyclic 1)
  | 4, 19 => (.finiteCyclic 1)
  | 5, 0 => (.finiteCyclic 1)
  | 5, 1 => (.finiteCyclic 2)
  | 5, 2 => (.finiteCyclic 2)
  | 5, 3 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 5, 4 => (.finiteCyclic 2)
  | 5, 5 => (.infiniteCyclic)
  | 5, 6 => (.finiteCyclic 1)
  | 5, 7 => (.finiteCyclic 1)
  | 5, 8 => (.finiteCyclic 1)
  | 5, 9 => (.finiteCyclic 1)
  | 5, 10 => (.finiteCyclic 1)
  | 5, 11 => (.finiteCyclic 1)
  | 5, 12 => (.finiteCyclic 1)
  | 5, 13 => (.finiteCyclic 1)
  | 5, 14 => (.finiteCyclic 1)
  | 5, 15 => (.finiteCyclic 1)
  | 5, 16 => (.finiteCyclic 1)
  | 5, 17 => (.finiteCyclic 1)
  | 5, 18 => (.finiteCyclic 1)
  | 5, 19 => (.finiteCyclic 1)
  | 6, 0 => (.finiteCyclic 1)
  | 6, 1 => (.finiteCyclic 2)
  | 6, 2 => (.finiteCyclic 3)
  | 6, 3 => .product (.finiteCyclic 8) (.product (.finiteCyclic 3) ((.finiteCyclic 3)))
  | 6, 4 => (.finiteCyclic 2)
  | 6, 5 => (.finiteCyclic 2)
  | 6, 6 => (.finiteCyclic 2)
  | 6, 7 => (.finiteCyclic 2)
  | 6, 8 => (.finiteCyclic 2)
  | 6, 9 => (.finiteCyclic 2)
  | 6, 10 => (.finiteCyclic 2)
  | 6, 11 => (.finiteCyclic 2)
  | 6, 12 => (.finiteCyclic 2)
  | 6, 13 => (.finiteCyclic 2)
  | 6, 14 => (.finiteCyclic 2)
  | 6, 15 => (.finiteCyclic 2)
  | 6, 16 => (.finiteCyclic 2)
  | 6, 17 => (.finiteCyclic 2)
  | 6, 18 => (.finiteCyclic 2)
  | 6, 19 => (.finiteCyclic 2)
  | 7, 0 => (.finiteCyclic 1)
  | 7, 1 => (.finiteCyclic 3)
  | 7, 2 => .product (.finiteCyclic 3) ((.finiteCyclic 5))
  | 7, 3 => .product (.finiteCyclic 3) ((.finiteCyclic 5))
  | 7, 4 => .product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 5 => .product (.finiteCyclic 4) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 6 => .product (.finiteCyclic 8) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 7 => .product (.infiniteCyclic) (.product (.finiteCyclic 8) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))
  | 7, 8 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 9 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 10 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 11 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 12 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 13 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 14 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 15 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 16 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 17 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 18 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 7, 19 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 8, 0 => (.finiteCyclic 1)
  | 8, 1 => .product (.finiteCyclic 3) ((.finiteCyclic 5))
  | 8, 2 => (.finiteCyclic 2)
  | 8, 3 => (.finiteCyclic 2)
  | 8, 4 => (.finiteCyclic 2)
  | 8, 5 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 8, 6 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 8, 7 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 8, 8 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 8, 9 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 8, 10 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 8, 11 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 8, 12 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 8, 13 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 8, 14 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 8, 15 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 8, 16 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 8, 17 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 8, 18 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 8, 19 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 9, 0 => (.finiteCyclic 1)
  | 9, 1 => (.finiteCyclic 2)
  | 9, 2 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 9, 3 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 9, 4 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 9, 5 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 9, 6 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 9, 7 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))))
  | 9, 8 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 9, 9 => .product (.infiniteCyclic) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 9, 10 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 9, 11 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 9, 12 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 9, 13 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 9, 14 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 9, 15 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 9, 16 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 9, 17 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 9, 18 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 9, 19 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 10, 0 => (.finiteCyclic 1)
  | 10, 1 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 10, 2 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 10, 3 => .product (.finiteCyclic 8) (.product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))))
  | 10, 4 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) ((.finiteCyclic 9)))
  | 10, 5 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) ((.finiteCyclic 9)))
  | 10, 6 => .product (.finiteCyclic 8) (.product (.finiteCyclic 3) ((.finiteCyclic 2)))
  | 10, 7 => .product (.finiteCyclic 8) (.product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 3)))))
  | 10, 8 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 10, 9 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 10, 10 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 10, 11 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 10, 12 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 10, 13 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 10, 14 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 10, 15 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 10, 16 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 10, 17 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 10, 18 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 10, 19 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 11, 0 => (.finiteCyclic 1)
  | 11, 1 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 11, 2 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 7)))))
  | 11, 3 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 7))))))))
  | 11, 4 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 9) ((.finiteCyclic 7)))))
  | 11, 5 => .product (.finiteCyclic 8) (.product (.finiteCyclic 4) (.product (.finiteCyclic 9) ((.finiteCyclic 7))))
  | 11, 6 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 9) ((.finiteCyclic 7))))
  | 11, 7 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 9) ((.finiteCyclic 7))))
  | 11, 8 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 9) ((.finiteCyclic 7))))
  | 11, 9 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 9) ((.finiteCyclic 7))))
  | 11, 10 => .product (.finiteCyclic 8) (.product (.finiteCyclic 9) ((.finiteCyclic 7)))
  | 11, 11 => .product (.infiniteCyclic) (.product (.finiteCyclic 8) (.product (.finiteCyclic 9) ((.finiteCyclic 7))))
  | 11, 12 => .product (.finiteCyclic 8) (.product (.finiteCyclic 9) ((.finiteCyclic 7)))
  | 11, 13 => .product (.finiteCyclic 8) (.product (.finiteCyclic 9) ((.finiteCyclic 7)))
  | 11, 14 => .product (.finiteCyclic 8) (.product (.finiteCyclic 9) ((.finiteCyclic 7)))
  | 11, 15 => .product (.finiteCyclic 8) (.product (.finiteCyclic 9) ((.finiteCyclic 7)))
  | 11, 16 => .product (.finiteCyclic 8) (.product (.finiteCyclic 9) ((.finiteCyclic 7)))
  | 11, 17 => .product (.finiteCyclic 8) (.product (.finiteCyclic 9) ((.finiteCyclic 7)))
  | 11, 18 => .product (.finiteCyclic 8) (.product (.finiteCyclic 9) ((.finiteCyclic 7)))
  | 11, 19 => .product (.finiteCyclic 8) (.product (.finiteCyclic 9) ((.finiteCyclic 7)))
  | 12, 0 => (.finiteCyclic 1)
  | 12, 1 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 7)))))
  | 12, 2 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 12, 3 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))))
  | 12, 4 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 12, 5 => .product (.finiteCyclic 16) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 12, 6 => (.finiteCyclic 1)
  | 12, 7 => (.finiteCyclic 1)
  | 12, 8 => (.finiteCyclic 1)
  | 12, 9 => .product (.finiteCyclic 4) ((.finiteCyclic 3))
  | 12, 10 => (.finiteCyclic 2)
  | 12, 11 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 12, 12 => (.finiteCyclic 2)
  | 12, 13 => (.finiteCyclic 1)
  | 12, 14 => (.finiteCyclic 1)
  | 12, 15 => (.finiteCyclic 1)
  | 12, 16 => (.finiteCyclic 1)
  | 12, 17 => (.finiteCyclic 1)
  | 12, 18 => (.finiteCyclic 1)
  | 12, 19 => (.finiteCyclic 1)
  | 13, 0 => (.finiteCyclic 1)
  | 13, 1 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 13, 2 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 13, 3 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 3)))))
  | 13, 4 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 13, 5 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 13, 6 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 13, 7 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 13, 8 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 13, 9 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 13, 10 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 13, 11 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 13, 12 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 13, 13 => .product (.infiniteCyclic) ((.finiteCyclic 3))
  | 13, 14 => (.finiteCyclic 3)
  | 13, 15 => (.finiteCyclic 3)
  | 13, 16 => (.finiteCyclic 3)
  | 13, 17 => (.finiteCyclic 3)
  | 13, 18 => (.finiteCyclic 3)
  | 13, 19 => (.finiteCyclic 3)
  | 14, 0 => (.finiteCyclic 1)
  | 14, 1 => .product (.finiteCyclic 2) ((.finiteCyclic 3))
  | 14, 2 => .product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 14, 3 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 9) (.product (.finiteCyclic 3) (.product (.finiteCyclic 5) ((.finiteCyclic 7)))))))
  | 14, 4 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 14, 5 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 14, 6 => .product (.finiteCyclic 8) (.product (.finiteCyclic 4) ((.finiteCyclic 3)))
  | 14, 7 => .product (.finiteCyclic 16) (.product (.finiteCyclic 8) (.product (.finiteCyclic 4) (.product (.finiteCyclic 3) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))))
  | 14, 8 => .product (.finiteCyclic 16) ((.finiteCyclic 4))
  | 14, 9 => .product (.finiteCyclic 16) ((.finiteCyclic 2))
  | 14, 10 => .product (.finiteCyclic 16) ((.finiteCyclic 2))
  | 14, 11 => .product (.finiteCyclic 16) (.product (.finiteCyclic 4) (.product (.finiteCyclic 2) ((.finiteCyclic 3))))
  | 14, 12 => .product (.finiteCyclic 16) ((.finiteCyclic 2))
  | 14, 13 => .product (.finiteCyclic 8) ((.finiteCyclic 2))
  | 14, 14 => .product (.finiteCyclic 4) ((.finiteCyclic 2))
  | 14, 15 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 14, 16 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 14, 17 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 14, 18 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 14, 19 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 15, 0 => (.finiteCyclic 1)
  | 15, 1 => .product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 15, 2 => .product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 15, 3 => .product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 15, 4 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))
  | 15, 5 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))))
  | 15, 6 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))))
  | 15, 7 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))))))
  | 15, 8 => .product (.finiteCyclic 16) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))))
  | 15, 9 => .product (.finiteCyclic 16) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))))
  | 15, 10 => .product (.finiteCyclic 16) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))
  | 15, 11 => .product (.finiteCyclic 16) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))
  | 15, 12 => .product (.finiteCyclic 32) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))
  | 15, 13 => .product (.finiteCyclic 32) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))
  | 15, 14 => .product (.finiteCyclic 32) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))
  | 15, 15 => .product (.infiniteCyclic) (.product (.finiteCyclic 32) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))))
  | 15, 16 => .product (.finiteCyclic 32) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))
  | 15, 17 => .product (.finiteCyclic 32) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))
  | 15, 18 => .product (.finiteCyclic 32) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))
  | 15, 19 => .product (.finiteCyclic 32) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))
  | 16, 0 => (.finiteCyclic 1)
  | 16, 1 => .product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5)))
  | 16, 2 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 16, 3 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 3)))))
  | 16, 4 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 16, 5 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 9) ((.finiteCyclic 7)))))
  | 16, 6 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 16, 7 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))))))
  | 16, 8 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 16, 9 => .product (.finiteCyclic 16) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))
  | 16, 10 => (.finiteCyclic 2)
  | 16, 11 => (.finiteCyclic 2)
  | 16, 12 => (.finiteCyclic 2)
  | 16, 13 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 16, 14 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 16, 15 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 16, 16 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 16, 17 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 16, 18 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 16, 19 => .product (.finiteCyclic 2) ((.finiteCyclic 2))
  | 17, 0 => (.finiteCyclic 1)
  | 17, 1 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 17, 2 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3))))
  | 17, 3 => .product (.finiteCyclic 8) (.product (.finiteCyclic 4) (.product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 3)))))))
  | 17, 4 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 17, 5 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 17, 6 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 17, 7 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3))))))
  | 17, 8 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 17, 9 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 17, 10 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 17, 11 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 17, 12 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 17, 13 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 17, 14 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))))
  | 17, 15 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))))
  | 17, 16 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))))
  | 17, 17 => .product (.infiniteCyclic) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))))
  | 17, 18 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 17, 19 => .product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 2))))
  | 18, 0 => (.finiteCyclic 1)
  | 18, 1 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3))))
  | 18, 2 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3))))
  | 18, 3 => .product (.finiteCyclic 8) (.product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))))))))
  | 18, 4 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3))))
  | 18, 5 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 3)))))
  | 18, 6 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3))))
  | 18, 7 => .product (.finiteCyclic 8) (.product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 9) (.product (.finiteCyclic 3) ((.finiteCyclic 7))))))
  | 18, 8 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))
  | 18, 9 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3))))
  | 18, 10 => .product (.finiteCyclic 8) (.product (.finiteCyclic 4) ((.finiteCyclic 2)))
  | 18, 11 => .product (.finiteCyclic 32) (.product (.finiteCyclic 4) (.product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 5))))))
  | 18, 12 => .product (.finiteCyclic 8) (.product (.finiteCyclic 8) ((.finiteCyclic 2)))
  | 18, 13 => .product (.finiteCyclic 8) (.product (.finiteCyclic 8) ((.finiteCyclic 2)))
  | 18, 14 => .product (.finiteCyclic 8) (.product (.finiteCyclic 8) ((.finiteCyclic 2)))
  | 18, 15 => .product (.finiteCyclic 8) (.product (.finiteCyclic 8) (.product (.finiteCyclic 8) (.product (.finiteCyclic 2) ((.finiteCyclic 3)))))
  | 18, 16 => .product (.finiteCyclic 8) (.product (.finiteCyclic 8) ((.finiteCyclic 2)))
  | 18, 17 => .product (.finiteCyclic 8) (.product (.finiteCyclic 4) ((.finiteCyclic 2)))
  | 18, 18 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) ((.finiteCyclic 2)))
  | 18, 19 => .product (.finiteCyclic 8) ((.finiteCyclic 2))
  | 19, 0 => (.finiteCyclic 1)
  | 19, 1 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) ((.finiteCyclic 3))))
  | 19, 2 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11))))
  | 19, 3 => .product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11))))))))
  | 19, 4 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11))))
  | 19, 5 => .product (.finiteCyclic 32) (.product (.finiteCyclic 8) (.product (.finiteCyclic 3) ((.finiteCyclic 11))))
  | 19, 6 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11))))
  | 19, 7 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11))))
  | 19, 8 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11))))
  | 19, 9 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) (.product (.finiteCyclic 3) ((.finiteCyclic 11)))))
  | 19, 10 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11))))))
  | 19, 11 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11))))))))
  | 19, 12 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11))))))
  | 19, 13 => .product (.finiteCyclic 8) (.product (.finiteCyclic 4) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11)))))
  | 19, 14 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11)))))
  | 19, 15 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11)))))
  | 19, 16 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11)))))
  | 19, 17 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11))))
  | 19, 18 => .product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11))))
  | 19, 19 => .product (.infiniteCyclic) (.product (.finiteCyclic 8) (.product (.finiteCyclic 2) (.product (.finiteCyclic 3) ((.finiteCyclic 11)))))
  | _, _ => .finiteCyclic 1

/-- The actual group represented by `todaIntegralGroupCode`. -/
noncomputable def todaIntegralGroup (nIndex k : Fin 20) : GrpCat :=
  (todaIntegralGroupCode nIndex k).asGrp



end HomotopyGroups
