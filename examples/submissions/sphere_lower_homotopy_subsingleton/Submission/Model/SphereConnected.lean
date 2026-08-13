/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Submission.Approximation.Simplex
import Submission.SphereHomotopy

/-!
# `Sⁿ` is `(n-1)`-connected

We prove that `π_k(Sⁿ)` is trivial for `k < n`.

The argument does not use charts.  A generalized loop `f : I^k → Sⁿ` is regarded as a map into
`ℝ^{n+1}` of constant norm `1`; it is replaced by its piecewise-affine interpolation `G` on a
grid fine enough that `‖G - f‖ ≤ 1/2`, and then projected radially back to the sphere.  Three
things make this work.

* `G` never vanishes, so the radial projection is defined, and so is the radial projection of the
  whole straight-line homotopy from `f` to `G`;  this gives a homotopy from `f` to
  `radialProj ∘ G` inside `Sⁿ`.
* `f` is constant equal to the basepoint on the boundary of the cube, and the grid vertices which
  contribute to the value of `G` at a boundary point again lie on the boundary, so `G` — and hence
  the whole homotopy — is constant equal to the basepoint there.  The homotopy is therefore
  relative to the cube boundary, as homotopy groups require.
* The value `G y` lies in the affine span of at most `k + 1` of the values of `f` at grid vertices
  (`Submission.cubeGridAffineApprox_mem_convexHull`), so every ray through a value of `G` lies in
  the affine span of the origin together with those `k + 1` points — a subspace of dimension at
  most `k + 1 ≤ n < n + 1`.  A finite union of such subspaces is Haar-null, so some unit vector
  avoids all of them and `radialProj ∘ G` is not surjective.

Half A (`Submission/Model/SphereCompl.lean`) then finishes the proof.

## Main definitions

* `Submission.gridConeSpan` — the finite union of subspaces containing every ray through a value
  of the piecewise-affine approximation.

## Main results

* `Submission.cubeGridAffineApprox_eq_of_mem_boundary` — the piecewise-affine approximation of a
  map which is constant on the cube boundary is constant there with the same value;
* `Submission.exists_radialProj_ne` — in dimension `k + 2 ≤ finrank`, the radial projection of a
  piecewise-affine approximation misses a unit vector;
* `Submission.subsingleton_homotopyGroup_sphere_of_lt` — `π_k(Sⁿ)` is trivial for `k < n`.
* `Submission.simplyConnectedSpace_sph_of_two_le` — every metric sphere of dimension at least two
  is simply connected.
-/

open scoped unitInterval Topology Topology.Homotopy

open MeasureTheory Module

namespace Submission

/-! ### The cone over a piecewise-affine image -/

section ConeSpan

variable {n N : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The points spanning the cone attached to a set `S` of grid vertices: the origin together with
the values of `g` at the vertices of `S`. -/
noncomputable def gridConePoints (N : ℕ) (g : C(I^ Fin n, V)) (S : Finset (Fin n → ℕ)) :
    Option {v // v ∈ S} → V
  | none => 0
  | some v => g (gridVertex N (v : Fin n → ℕ))

/-- The union, over the simplices of the `N`-fold grid, of the affine span of the origin together
with the values of `g` at the vertices of that simplex.  Each piece is a linear subspace of
dimension at most `n + 1`, and the union contains every ray through a value of the
piecewise-affine approximation of `g`. -/
noncomputable def gridConeSpan (n N : ℕ) (g : C(I^ Fin n, V)) : Set V :=
  ⋃ S ∈ gridSimplices n N, (affineSpan ℝ (Set.range (gridConePoints N g S)) : Set V)

omit [NormedSpace ℝ V] in
theorem zero_mem_gridConePoints_range (g : C(I^ Fin n, V)) (S : Finset (Fin n → ℕ)) :
    (0 : V) ∈ Set.range (gridConePoints N g S) :=
  ⟨none, rfl⟩

/-- The origin belongs to the cone: the empty set of vertices is one of the grid simplices. -/
theorem zero_mem_gridConeSpan (g : C(I^ Fin n, V)) : (0 : V) ∈ gridConeSpan n N g :=
  Set.mem_iUnion₂.mpr
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩,
      subset_affineSpan ℝ _ (zero_mem_gridConePoints_range g ∅)⟩

/-- The cone is stable under scalar multiplication: each of its pieces is an affine subspace
containing the origin, hence a linear subspace. -/
theorem smul_mem_gridConeSpan {g : C(I^ Fin n, V)} {z : V} (hz : z ∈ gridConeSpan n N g) (c : ℝ) :
    c • z ∈ gridConeSpan n N g := by
  obtain ⟨S, hS, hzS⟩ := Set.mem_iUnion₂.mp hz
  refine Set.mem_iUnion₂.mpr ⟨S, hS, ?_⟩
  have h0 : (0 : V) ∈ affineSpan ℝ (Set.range (gridConePoints N g S)) :=
    subset_affineSpan ℝ _ (zero_mem_gridConePoints_range g S)
  simpa using
    AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ (Set.range (gridConePoints N g S))) c hzS h0 h0

/-- Every value of the piecewise-affine approximation lies in the cone. -/
theorem cubeGridAffineApprox_mem_gridConeSpan (hN : 1 ≤ N) (g : C(I^ Fin n, V)) (y : I^ Fin n) :
    cubeGridAffineApprox n N g y ∈ gridConeSpan n N g := by
  refine Set.mem_iUnion₂.mpr ⟨activeVerts N y, activeVerts_mem_gridSimplices hN y, ?_⟩
  have hsub : ((fun v => g (gridVertex N v)) '' (activeVerts N y : Set (Fin n → ℕ)))
      ⊆ Set.range (gridConePoints N g (activeVerts N y)) := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨some ⟨v, hv⟩, rfl⟩
  exact affineSpan_mono ℝ hsub
    (convexHull_subset_affineSpan _ (cubeGridAffineApprox_mem_convexHull hN g y))

/-- Every ray through a value of the piecewise-affine approximation lies in the cone. -/
theorem radialProj_cubeGridAffineApprox_mem_gridConeSpan (hN : 1 ≤ N) (g : C(I^ Fin n, V))
    (y : I^ Fin n) : radialProj (cubeGridAffineApprox n N g y) ∈ gridConeSpan n N g :=
  smul_mem_gridConeSpan (cubeGridAffineApprox_mem_gridConeSpan hN g y) _

end ConeSpan

section ConeSpanMeasure

variable {n N : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure]

include μ in
/-- The cone over a piecewise-affine image is Haar-null as soon as `n + 2 ≤ finrank ℝ V`: each
piece is the affine span of at most `n + 2` points. -/
theorem addHaar_gridConeSpan (hdim : n + 2 ≤ finrank ℝ V) (g : C(I^ Fin n, V)) :
    μ (gridConeSpan n N g) = 0 := by
  have hsum : ∑ S ∈ gridSimplices n N,
      μ (affineSpan ℝ (Set.range (gridConePoints N g S)) : Set V) = 0 := by
    refine Finset.sum_eq_zero fun S hS => ?_
    refine addHaar_of_card_le μ (p := gridConePoints N g S) Set.Subset.rfl ?_
    rw [Fintype.card_option, Fintype.card_coe]
    have := card_le_of_mem_gridSimplices hS
    omega
  show μ (⋃ S ∈ gridSimplices n N, (affineSpan ℝ (Set.range (gridConePoints N g S)) : Set V)) = 0
  exact nonpos_iff_eq_zero.mp (hsum ▸ measure_biUnion_finset_le _ _)

include μ in
/-- Some unit vector avoids the cone over a piecewise-affine image. -/
theorem exists_norm_eq_one_notMem_gridConeSpan (hdim : n + 2 ≤ finrank ℝ V)
    (g : C(I^ Fin n, V)) : ∃ q : V, ‖q‖ = 1 ∧ q ∉ gridConeSpan n N g := by
  obtain ⟨p, -, hp⟩ := exists_notMem_of_measure_zero μ ({()} : Finset Unit)
    (fun _ => gridConeSpan n N g) (fun _ _ => addHaar_gridConeSpan μ hdim g) isOpen_univ
    Set.univ_nonempty
  have hp' : p ∉ gridConeSpan n N g := hp () (Finset.mem_singleton_self ())
  have hp0 : p ≠ 0 := fun h => hp' (h ▸ zero_mem_gridConeSpan (N := N) g)
  refine ⟨radialProj p, norm_radialProj hp0, fun hc => hp' ?_⟩
  have hmem := smul_mem_gridConeSpan hc ‖p‖
  rwa [smul_norm_radialProj hp0] at hmem

include μ in
/-- **General position.**  If the cube has dimension `n` and `n + 2 ≤ finrank ℝ V`, then the
radial projection of the piecewise-affine approximation misses a unit vector. -/
theorem exists_radialProj_ne (hN : 1 ≤ N) (hdim : n + 2 ≤ finrank ℝ V) (g : C(I^ Fin n, V)) :
    ∃ q : V, ‖q‖ = 1 ∧ ∀ y, radialProj (cubeGridAffineApprox n N g y) ≠ q := by
  obtain ⟨q, hq1, hq2⟩ := exists_norm_eq_one_notMem_gridConeSpan (N := N) μ hdim g
  exact ⟨q, hq1, fun y hc =>
    hq2 (hc ▸ radialProj_cubeGridAffineApprox_mem_gridConeSpan hN g y)⟩

end ConeSpanMeasure

/-! ### The approximation is constant on the cube boundary -/

section Boundary

variable {n N : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A grid vertex contributing at a boundary point of the cube is itself a boundary point. -/
theorem gridVertex_mem_boundary_of_gridCoeff_pos (hN : 1 ≤ N) {v : Fin n → ℕ} {y : I^ Fin n}
    {j : Fin n} (hj : y j = 0 ∨ y j = 1) (hv : v ∈ activeVerts N y) :
    gridVertex N v ∈ Cube.boundary (Fin n) := by
  obtain ⟨hvmem, hvpos⟩ := mem_activeVerts.mp hv
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have habs := abs_lt.mp (abs_sub_lt_one_of_gridCoeff_pos hvpos j)
  have hcoe := coe_gridVertex hN hvmem j
  refine ⟨j, ?_⟩
  rcases hj with h0 | h1
  · left
    have hyj : ((y j : ℝ)) = 0 := congrArg Subtype.val h0
    rw [hyj, mul_zero] at habs
    have hlt : (v j : ℝ) < 1 := by linarith [habs.1]
    have : v j = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hlt)
    refine Subtype.ext ?_
    rw [hcoe, this]
    simp
  · right
    have hyj : ((y j : ℝ)) = 1 := congrArg Subtype.val h1
    rw [hyj, mul_one] at habs
    have hlt : (v j : ℝ) < (N : ℝ) + 1 := by linarith [habs.1]
    have hgt : (N : ℝ) - 1 < (v j : ℝ) := by linarith [habs.2]
    have h1' : v j < N + 1 := by exact_mod_cast hlt
    have h2' : N ≤ v j := by
      by_contra hc
      have : (v j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_le hc)
      linarith
    have hvN : v j = N := by omega
    refine Subtype.ext ?_
    rw [hcoe, hvN, div_self (ne_of_gt hN')]
    simp

/-- The piecewise-affine approximation of a map which is constant on the boundary of the cube is
constant on the boundary, with the same value.  This is what makes the approximation homotopy a
homotopy *relative to the cube boundary*. -/
theorem cubeGridAffineApprox_eq_of_mem_boundary (hN : 1 ≤ N) (g : C(I^ Fin n, V)) {b : V}
    (hg : ∀ z ∈ Cube.boundary (Fin n), g z = b) {y : I^ Fin n}
    (hy : y ∈ Cube.boundary (Fin n)) : cubeGridAffineApprox n N g y = b := by
  obtain ⟨j, hj⟩ := hy
  have hval : ∀ v ∈ activeVerts N y, g (gridVertex N v) = b := fun v hv =>
    hg _ (gridVertex_mem_boundary_of_gridCoeff_pos hN hj hv)
  rw [cubeGridAffineApprox_eq_sum_activeVerts,
    Finset.sum_congr rfl (fun v hv => by rw [hval v hv]), ← Finset.sum_smul,
    sum_gridCoeff_activeVerts hN, one_smul]

end Boundary

/-! ### `π_k(Sⁿ) = 0` for `k < n` -/

section Vanishing

variable {k n : ℕ}

/-- A generalized loop of dimension `k` in `Sⁿ`, read as a continuous map into `ℝ^{n+1}`. -/
noncomputable def genLoopToEuclidean {x : Sph n} (f : Ω^ (Fin k) (Sph n) x) :
    C(I^ Fin k, EuclideanSpace ℝ (Fin (n + 1))) :=
  ⟨fun y => ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))),
    continuous_subtype_val.comp f.1.continuous⟩

@[simp]
theorem genLoopToEuclidean_apply {x : Sph n} (f : Ω^ (Fin k) (Sph n) x) (y : I^ Fin k) :
    genLoopToEuclidean f y = ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) :=
  rfl

/-- **Every generalized loop of dimension `k < n` in `Sⁿ` is nullhomotopic.** -/
theorem homotopyGroup_eq_one_of_lt [Nonempty (Fin k)] (hkn : k < n) (x : Sph n)
    (f : Ω^ (Fin k) (Sph n) x) :
    (⟦f⟧ : HomotopyGroup (Fin k) (Sph n) x) = (1 : HomotopyGroup (Fin k) (Sph n) x) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  set F : C(I^ Fin k, EuclideanSpace ℝ (Fin (n + 1))) := genLoopToEuclidean f
  have hFnorm : ∀ y, ‖F y‖ = 1 := fun y => norm_coe_sph (f y)
  have hFbd : ∀ z ∈ Cube.boundary (Fin k),
      F z = ((x : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) :=
    fun z hz => congrArg Subtype.val (_root_.GenLoop.boundary f z hz)
  obtain ⟨N, hN, hdist⟩ := exists_cubeGridAffineApprox_dist_le k F hhalf
  -- the straight-line homotopy from `F` to its piecewise-affine approximation never vanishes
  have hHdist : ∀ (t : I) (y : I^ Fin k),
      dist (cubeGridAffineApproxHomotopy k N F (t, y)) (F y) ≤ 1 / 2 :=
    fun t y => cubeGridAffineApproxHomotopy_dist_le F hdist t y
  have hHne : ∀ p : I × I^ Fin k, cubeGridAffineApproxHomotopy k N F p ≠ 0 := by
    rintro ⟨t, y⟩ hc
    have h := hHdist t y
    rw [hc, dist_zero_left, hFnorm] at h
    linarith
  have hGne : ∀ y : I^ Fin k, cubeGridAffineApprox k N F y ≠ 0 := by
    intro y
    have h := hHne (1, y)
    rwa [cubeGridAffineApproxHomotopy_one] at h
  -- the approximation is still constant at the basepoint on the cube boundary
  have hxnorm : ‖((x : Sph n) : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := norm_coe_sph x
  have hGbd : ∀ z ∈ Cube.boundary (Fin k),
      cubeGridAffineApprox k N F z = ((x : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) :=
    fun z hz => cubeGridAffineApprox_eq_of_mem_boundary hN F hFbd hz
  have hHbd : ∀ (t : I) (z : I^ Fin k), z ∈ Cube.boundary (Fin k) →
      cubeGridAffineApproxHomotopy k N F (t, z) =
        ((x : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) := by
    intro t z hz
    rw [cubeGridAffineApproxHomotopy_apply, hFbd z hz, hGbd z hz, ← add_smul]
    norm_num
  -- the radial projection of the approximation, as a generalized loop
  obtain ⟨ghat, hghat⟩ : ∃ g : Ω^ (Fin k) (Sph n) x, ∀ y : I^ Fin k,
      ((g y : Sph n) : EuclideanSpace ℝ (Fin (n + 1)))
        = radialProj (cubeGridAffineApprox k N F y) :=
    ⟨⟨⟨fun y => ⟨radialProj (cubeGridAffineApprox k N F y),
          mem_sphere_zero_iff_norm.mpr (norm_radialProj (hGne y))⟩,
        Continuous.subtype_mk
          (continuous_radialProj (cubeGridAffineApprox k N F).continuous hGne) _⟩,
      fun z hz => Subtype.ext (by
        show radialProj (cubeGridAffineApprox k N F z)
          = ((x : Sph n) : EuclideanSpace ℝ (Fin (n + 1)))
        rw [hGbd z hz]
        exact radialProj_of_norm_eq_one hxnorm)⟩, fun _ => rfl⟩
  -- the radial projection of the straight-line homotopy is a homotopy rel the cube boundary
  have hhom : _root_.GenLoop.Homotopic f ghat := by
    apply genLoopHomotopic_of_radialHomotopy f ghat
      (cubeGridAffineApproxHomotopy k N F) hHne
    · intro y
      rw [cubeGridAffineApproxHomotopy_zero]
      exact radialProj_of_norm_eq_one (hFnorm y)
    · intro y
      rw [cubeGridAffineApproxHomotopy_one]
      exact (hghat y).symm
    · intro s t ht
      rw [hHbd s t ht, radialProj_of_norm_eq_one hxnorm]
  -- general position: the radial projection of the approximation misses a point of the sphere
  have hdim : k + 2 ≤ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [finrank_euclideanSpace_fin]
    omega
  obtain ⟨q, hq1, hq2⟩ :=
    exists_radialProj_ne (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) hN hdim F
  have hghat_ne : ∀ y : I^ Fin k, ghat y ≠ (⟨q, mem_sphere_zero_iff_norm.mpr hq1⟩ : Sph n) :=
    fun y hc => hq2 y ((hghat y).symm.trans (congrArg Subtype.val hc))
  have hqx : (⟨q, mem_sphere_zero_iff_norm.mpr hq1⟩ : Sph n) ≠ x := by
    intro hc
    obtain ⟨i⟩ := ‹Nonempty (Fin k)›
    have hy0 : (fun _ => (0 : I) : I^ Fin k) ∈ Cube.boundary (Fin k) := ⟨i, Or.inl rfl⟩
    exact hghat_ne _ ((_root_.GenLoop.boundary ghat _ hy0).trans hc.symm)
  rw [Quotient.sound hhom]
  exact homotopyGroup_eq_one_of_not_surjective n x ghat _ hqx hghat_ne

/-- **`π_k(Sⁿ) = 0` for `k < n`.**  In particular `Sⁿ` is `(n-1)`-connected: `S³` is
`2`-connected, and `π₁(Ω S^{m+1}) ≅ π₂(S^{m+1})` is trivial for `m ≥ 1`. -/
theorem subsingleton_homotopyGroup_sphere_of_lt (k n : ℕ) (hkn : k < n) (x : Sph n) :
    Subsingleton (HomotopyGroup.Pi k (Sph n) x) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · haveI := pathConnectedSpace_sph (n := n) (by omega)
    exact subsingleton_homotopyGroup_zero x
  · haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    refine ⟨fun a b => ?_⟩
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q => rw [homotopyGroup_eq_one_of_lt hkn x p, homotopyGroup_eq_one_of_lt hkn x q]

/-- A metric sphere of dimension at least two is simply connected. -/
theorem simplyConnectedSpace_sph_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    SimplyConnectedSpace (Sph n) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨pathConnectedSpace_sph (by omega), ?_⟩
  intro x γ
  letI : Subsingleton (HomotopyGroup.Pi 1 (Sph n) x) :=
    subsingleton_homotopyGroup_sphere_of_lt 1 n (by omega) x
  letI : Subsingleton (FundamentalGroup (Sph n) x) :=
    HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.symm.subsingleton
  have heq : (⟦γ⟧ : Path.Homotopic.Quotient x x) = ⟦Path.refl x⟧ :=
    Subsingleton.elim (FundamentalGroup.fromPath ⟦γ⟧)
      (FundamentalGroup.fromPath ⟦Path.refl x⟧)
  exact Quotient.exact heq

end Vanishing

end Submission
