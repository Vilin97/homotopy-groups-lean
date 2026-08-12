/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SimplexGlue
import Submission.WhiteheadTheorem

/-!
# The simplex pair has the homotopy extension property, and can be compressed

The vendored `Submission.WhiteheadTheorem` library provides the homotopy extension property and
the compression lemma for the pair `(𝔻 j, ∂𝔻 j)`.  The compression recursion of
`Submission/Hurewicz/Vanishing.lean` needs both for the pair `(|Δ^j|, |∂Δ^j|)`.  This file
transports them along the homeomorphism `Submission.simplexHomeoBall`.

## Main results

* `Submission.simplex_hasHEP` — the pair `(|Δ^j|, |∂Δ^j|)` has the homotopy extension property;
* `Submission.exists_boundary_extension` — the pointwise form of it that the recursion uses;
* `Submission.exists_compression` — a map `|Δ^{j+1}| → X` taking `|∂Δ^{j+1}|` into `A` is
  homotopic rel `|∂Δ^{j+1}|` to a map into `A`, provided `π_rel (j+1) (X, A) = 0`.
-/

open Metric Set
open scoped Topology unitInterval TopCat

noncomputable section

namespace Submission

variable {j : ℕ}

/-! ### Transport of the homotopy extension property along homeomorphisms -/

/-- The homotopy extension property transports along a homeomorphism of pairs. -/
theorem hasHEP_of_homeomorph {A X A' X' Y : Type}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace A'] [TopologicalSpace X']
    [TopologicalSpace Y] {i : C(A, X)} {i' : C(A', X')} (eA : A ≃ₜ A') (eX : X ≃ₜ X')
    (hcomm : ∀ a, i' (eA a) = eX (i a)) (H : HasHomotopyExtensionProperty i' Y) :
    HasHomotopyExtensionProperty i Y := by
  intro f g hfg
  have key : ∀ a : A, f (i a) = g (a, 0) := fun a => congrFun hfg a
  have hsymm : ∀ a' : A', eX.symm (i' a') = i (eA.symm a') := by
    intro a'
    rw [← eA.apply_symm_apply a', hcomm, eX.symm_apply_apply, eA.symm_apply_apply]
  obtain ⟨G, hG₀, hGw⟩ := H ⟨fun x' => f (eX.symm x'), f.continuous.comp eX.symm.continuous⟩
      ⟨fun p => g (eA.symm p.1, p.2),
        g.continuous.comp ((eA.symm.continuous.comp continuous_fst).prodMk continuous_snd)⟩ (by
        funext a'
        show f (eX.symm (i' a')) = g (eA.symm a', 0)
        rw [hsymm]
        exact key _)
  refine ⟨⟨fun p => G (eX p.1, p.2),
    G.continuous.comp ((eX.continuous.comp continuous_fst).prodMk continuous_snd)⟩, ?_, ?_⟩
  · funext x
    have h := congrFun hG₀ (eX x)
    simp only [ContinuousMap.coe_mk, Function.comp_apply, Homeomorph.symm_apply_apply] at h
    exact h
  · funext p
    obtain ⟨a, t⟩ := p
    have h := congrFun hGw (eA a, t)
    simp only [ContinuousMap.coe_mk, Function.comp_apply, Prod.map_apply, id_eq,
      Homeomorph.symm_apply_apply] at h
    show g (a, t) = G (eX (i a), t)
    rw [h, hcomm]

/-! ### The simplex as the disk, without the `ULift` -/

/-- The standard `j`-simplex is homeomorphic to the disk `𝔻 j`. -/
def simplexHomeoDisk' (j : ℕ) : stdSimplex ℝ (Fin (j + 1)) ≃ₜ (𝔻 j : TopCat.{0}) :=
  (simplexHomeoBall j).trans Homeomorph.ulift.symm

@[simp]
theorem simplexHomeoDisk'_down (x : stdSimplex ℝ (Fin (j + 1))) :
    (simplexHomeoDisk' j x).down = simplexHomeoBall j x := rfl

/-- Points of the closed ball lying on the unit sphere form the boundary `∂𝔻 j`. -/
def sphereSubtypeHomeo (j : ℕ) :
    {y : closedBall (0 : EuclideanSpace ℝ (Fin j)) 1 // (y : EuclideanSpace ℝ (Fin j)) ∈ sphere 0 1}
      ≃ₜ (∂𝔻 j : TopCat.{0}) where
  toFun y := ⟨⟨(y : closedBall (0 : EuclideanSpace ℝ (Fin j)) 1), y.2⟩⟩
  invFun p := ⟨⟨(p.down : EuclideanSpace ℝ (Fin j)), sphere_subset_closedBall p.down.2⟩, p.down.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    continuous_uliftUp.comp
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
  continuous_invFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_uliftDown) _) _

/-- The boundary of the standard `j`-simplex is homeomorphic to `∂𝔻 j`. -/
def bdryHomeoDiskBoundary (j : ℕ) : bdry j ≃ₜ (∂𝔻 j : TopCat.{0}) :=
  ((simplexHomeoBall j).subtype fun x =>
      mem_bdry.trans ((norm_simplexHomeoBall_eq_one_iff x).symm.trans
        mem_sphere_zero_iff_norm.symm)).trans (sphereSubtypeHomeo j)

/-- The inclusion of the boundary of the standard simplex, as a continuous map. -/
def bdryIncl (j : ℕ) : C(bdry j, stdSimplex ℝ (Fin (j + 1))) :=
  ⟨fun b => (b : stdSimplex ℝ (Fin (j + 1))), continuous_subtype_val⟩

@[simp]
theorem bdryIncl_apply (b : bdry j) : bdryIncl j b = (b : stdSimplex ℝ (Fin (j + 1))) := rfl

theorem diskBoundaryIncl_bdryHomeo (b : bdry j) :
    (TopCat.diskBoundaryIncl.{0} j).hom (bdryHomeoDiskBoundary j b) =
      simplexHomeoDisk' j (bdryIncl j b) := rfl

/-- The image of the boundary inclusion of the disk is the set of unit vectors. -/
theorem range_diskBoundaryIncl (j : ℕ) :
    Set.range (TopCat.diskBoundaryIncl.{0} j).hom =
      {y : (𝔻 j : TopCat.{0}) | ‖((y.down : EuclideanSpace ℝ (Fin j)))‖ = 1} := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact mem_sphere_zero_iff_norm.1 p.down.2
  · intro hy
    exact ⟨⟨⟨(y.down : EuclideanSpace ℝ (Fin j)), mem_sphere_zero_iff_norm.2 hy⟩⟩, rfl⟩

/-- **The pair `(|Δ^j|, |∂Δ^j|)` has the homotopy extension property.** -/
theorem simplex_hasHEP (j : ℕ) (Y : Type) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty (bdryIncl j) Y :=
  hasHEP_of_homeomorph (bdryHomeoDiskBoundary j) (simplexHomeoDisk' j)
    diskBoundaryIncl_bdryHomeo (TopCat.diskBoundaryIncl_hasHEP.{0} j Y)

/-- The homotopy extension property of the simplex pair, in the pointwise form used by the
compression recursion: a map `f` on `|Δ^j|` together with a homotopy of its restriction to the
boundary extends to a homotopy of `f`. -/
theorem exists_boundary_extension {Y : Type} [TopologicalSpace Y]
    (f : C(stdSimplex ℝ (Fin (j + 1)), Y)) (g : C(bdry j × I, Y))
    (hg : ∀ b : bdry j, g (b, 0) = f (b : stdSimplex ℝ (Fin (j + 1)))) :
    ∃ G : C(stdSimplex ℝ (Fin (j + 1)) × I, Y),
      (∀ x, G (x, 0) = f x) ∧
        ∀ (b : bdry j) (t : I), G ((b : stdSimplex ℝ (Fin (j + 1))), t) = g (b, t) := by
  obtain ⟨G, hG₀, hGw⟩ := simplex_hasHEP j Y f g (funext fun b => (hg b).symm)
  exact ⟨G, fun x => (congrFun hG₀ x).symm, fun b t => (congrFun hGw (b, t)).symm⟩

/-! ### Compression of simplices -/

variable {Y : Type} [TopologicalSpace Y] {A : Set Y}

/-- Under the identification of the simplex with the disk, the boundary of the simplex
corresponds to the image of the boundary inclusion of the disk. -/
theorem mem_bdry_iff_mem_range (x : stdSimplex ℝ (Fin (j + 1))) :
    x ∈ bdry j ↔
      simplexHomeoDisk' j x ∈ Set.range (TopCat.diskBoundaryIncl.{0} j).hom := by
  rw [range_diskBoundaryIncl, Set.mem_setOf_eq, simplexHomeoDisk'_down]
  exact mem_bdry.trans (norm_simplexHomeoBall_eq_one_iff x).symm

/-- **Compression of a simplex into `A` rel its boundary.**  If all the relative homotopy groups
`π_rel (j + 1) (Y, A)` vanish, then a map `|Δ^{j+1}| → Y` taking the boundary into `A` is
homotopic, by a homotopy fixing the boundary pointwise, to a map with image in `A`. -/
theorem exists_compression (j : ℕ)
    (hpi : ∀ a : A, Nonempty (Unique (π_rel (j + 1) Y A a)))
    (u : C(stdSimplex ℝ (Fin (j + 2)), Y)) (hu : ∀ x ∈ bdry (j + 1), u x ∈ A) :
    ∃ K : C(stdSimplex ℝ (Fin (j + 2)) × I, Y),
      (∀ x, K (x, 0) = u x) ∧ (∀ x, K (x, 1) ∈ A) ∧
        ∀ x ∈ bdry (j + 1), ∀ t : I, K (x, t) = u x := by
  set e := simplexHomeoDisk' (j + 1) with he
  set f : C((𝔻 (j + 1) : TopCat.{0}), Y) :=
    ⟨fun y => u (e.symm y), u.continuous.comp e.symm.continuous⟩ with hf
  have hfe : ∀ x, f (e x) = u x := fun x => by
    show u (e.symm (e x)) = u x
    rw [e.symm_apply_apply]
  have hfp : TopCat.disk.IsMapOfPairs Y A f := by
    intro y
    have hmem : e.symm ((TopCat.diskBoundaryIncl.{0} (j + 1)).hom y) ∈ bdry (j + 1) := by
      rw [mem_bdry_iff_mem_range, ← he, e.apply_symm_apply]
      exact ⟨y, rfl⟩
    exact hu _ hmem
  obtain ⟨l, hlA, ⟨H⟩⟩ := TopCat.disk.homotopicRel_boundary_of_unique_pi Y A f hfp hpi
  refine ⟨⟨fun p => H (p.2, e p.1),
    (map_continuous H).comp (continuous_snd.prodMk (e.continuous.comp continuous_fst))⟩,
    ?_, ?_, ?_⟩
  · intro x
    show H (0, e x) = u x
    rw [H.apply_zero, hfe]
  · intro x
    exact hlA ⟨e x, (H.apply_one (e x)).symm⟩
  · intro x hx t
    show H (t, e x) = u x
    rw [H.eq_fst t ((mem_bdry_iff_mem_range x).1 hx), hfe]

end Submission
