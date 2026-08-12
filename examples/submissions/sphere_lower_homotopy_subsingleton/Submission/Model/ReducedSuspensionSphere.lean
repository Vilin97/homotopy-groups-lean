/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import ChallengeDeps
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Submission.Model.ReducedSuspension
import Submission.Model.Sphere

/-!
# The reduced suspension of a metric sphere

The complement of the distinguished point in reduced suspension is the product of the open
interval with the complement of the source basepoint.  We identify those factors with `ℝ` and
Euclidean space using an affine tangent chart and stereographic projection.  One-point
compactification then gives a homeomorphism from the reduced suspension of a pointed metric
`n`-sphere to the maintained metric model of the `(n+1)`-sphere.

The homeomorphism sends the collapsed suspension point exactly to the standard sphere basepoint.
-/

open scoped Topology unitInterval

noncomputable section

namespace Submission

open unitInterval
open HomotopyGroups

namespace ReducedSusp

/-- The interior of the unit interval, expressed as a subtype of `I`. -/
abbrev InteriorI :=
  {t : I // t ≠ 0 ∧ t ≠ 1}

/-- Forgetting the nested subtype identifies the interior of `I` with the real interval `(0,1)`. -/
def interiorIHomeomorphIoo : InteriorI ≃ₜ Set.Ioo (0 : ℝ) 1 where
  toFun t := ⟨t.1, by
    constructor
    · exact lt_of_le_of_ne t.1.2.1 fun h =>
        t.2.1 (Subtype.ext h.symm)
    · exact lt_of_le_of_ne t.1.2.2 fun h =>
        t.2.2 (Subtype.ext h)⟩
  invFun t := ⟨⟨t.1, t.2.1.le, t.2.2.le⟩, by
    constructor
    · intro h
      exact t.2.1.ne' (congrArg Subtype.val h)
    · intro h
      exact t.2.2.ne (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The open interval `(0,1)` is homeomorphic to the real line. -/
noncomputable def iooZeroOneHomeomorphReal : Set.Ioo (0 : ℝ) 1 ≃ₜ ℝ := by
  let e : ℝ ≃ₜ ℝ := affineHomeomorph Real.pi (-(Real.pi / 2)) Real.pi_ne_zero
  have he : e '' Set.Ioo (0 : ℝ) 1 = Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [e]
    convert affineHomeomorph_image_Ioo Real.pi (-(Real.pi / 2)) 0 1 Real.pi_pos using 1
    all_goals ring_nf
  exact ((Homeomorph.image e (Set.Ioo (0 : ℝ) 1)).trans
    (Homeomorph.setCongr he)).trans Real.tanOrderIso.toHomeomorph

/-- The interior of the unit interval is a copy of the real line. -/
noncomputable def interiorIHomeomorphReal : InteriorI ≃ₜ ℝ :=
  interiorIHomeomorphIoo.trans iooZeroOneHomeomorphReal

/-- Removing one point from `Sⁿ` gives Euclidean `n`-space. -/
noncomputable def sphereComplHomeomorphEuclidean (n : ℕ) (x₀ : Sph n) :
    {x : Sph n // x ≠ x₀} ≃ₜ EuclideanSpace ℝ (Fin n) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  let e := stereographic' n x₀
  have hs : {x : Sph n | x ≠ x₀} = e.source := by
    rw [stereographic'_source]
    ext x
    simp
  have ht : e.target = (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
    exact stereographic'_target x₀
  exact (((Homeomorph.setCongr hs).trans e.toHomeomorphSourceTarget).trans
    (Homeomorph.setCongr ht)).trans (Homeomorph.Set.univ _)

/-- The non-basepoint locus of the reduced suspension of `Sⁿ` is Euclidean `(n+1)`-space,
presented as `ℝ × ℝⁿ`. -/
noncomputable def puncturedSphereHomeomorphProd (n : ℕ) (x₀ : Sph n) :
    Punctured x₀ ≃ₜ ℝ × EuclideanSpace ℝ (Fin n) := by
  have hset :
      {p : I × Sph n | ¬ReducedSuspCollapsed x₀ p} =
        {t : I | t ≠ 0 ∧ t ≠ 1} ×ˢ {x : Sph n | x ≠ x₀} := by
    ext p
    simp only [ReducedSuspCollapsed, Set.mem_setOf_eq, Set.mem_prod, not_or]
    tauto
  exact ((Homeomorph.setCongr hset).trans
    (Homeomorph.Set.prod {t : I | t ≠ 0 ∧ t ≠ 1} {x : Sph n | x ≠ x₀})).trans
      (interiorIHomeomorphReal.prodCongr (sphereComplHomeomorphEuclidean n x₀))

/-- The one-point compactification of `ℝ × ℝⁿ` is the metric `(n+1)`-sphere, with infinity sent
to the standard sphere basepoint. -/
noncomputable def onePointProdHomeomorphSphere (n : ℕ) :
    OnePoint (ℝ × EuclideanSpace ℝ (Fin n)) ≃ₜ Sph (n + 1) := by
  let E := EuclideanSpace ℝ (Fin (n + 2))
  let v : E := EuclideanSpace.single (0 : Fin (n + 2)) 1
  have hv : ‖v‖ = 1 := by rw [PiLp.norm_single, norm_one]
  have hv₀ : v ≠ 0 := fun h => by simp [h] at hv
  letI : Fact (Module.finrank ℝ E = (1 + n) + 1) := ⟨by simp [E]; omega⟩
  have hdim : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (ℝ ∙ v)ᗮ := by
    rw [Submodule.finrank_orthogonal_span_singleton (n := 1 + n) hv₀]
    simp [Module.finrank_prod]
  let e : (ℝ × EuclideanSpace ℝ (Fin n)) ≃ₜ (ℝ ∙ v)ᗮ :=
    (Classical.choice
      (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hdim)).toHomeomorph
  exact e.onePointCongr.trans (onePointHyperplaneHomeoUnitSphere hv)

@[simp]
theorem onePointCongr_infty {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) : e.onePointCongr (OnePoint.infty : OnePoint A) = OnePoint.infty := by
  rw [Homeomorph.onePointCongr_apply, OnePoint.map_infty]

@[simp]
theorem onePointProdHomeomorphSphere_infty (n : ℕ) :
    onePointProdHomeomorphSphere n OnePoint.infty = sphereBasepoint (n + 1) := by
  unfold onePointProdHomeomorphSphere
  rw [Homeomorph.trans_apply, onePointCongr_infty]
  unfold onePointHyperplaneHomeoUnitSphere
  rw [OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty]
  rfl

/-- **The reduced suspension of a pointed metric `n`-sphere is the metric `(n+1)`-sphere.** -/
noncomputable def sphereHomeomorph (n : ℕ) (x₀ : Sph n) :
    ReducedSusp (Sph n) x₀ ≃ₜ Sph (n + 1) :=
  (onePointHomeomorph x₀).symm |>.trans
    ((puncturedSphereHomeomorphProd n x₀).onePointCongr.trans
      (onePointProdHomeomorphSphere n))

@[simp]
theorem sphereHomeomorph_base (n : ℕ) (x₀ : Sph n) :
    sphereHomeomorph n x₀ (base x₀) = sphereBasepoint (n + 1) := by
  rw [sphereHomeomorph, Homeomorph.trans_apply, onePointHomeomorph_symm_base,
    Homeomorph.trans_apply, Homeomorph.onePointCongr_apply, OnePoint.map_infty,
    onePointProdHomeomorphSphere_infty]

end ReducedSusp

end Submission
