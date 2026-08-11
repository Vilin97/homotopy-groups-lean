/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The covering-space argument below is adapted from TauCeti at commit
2b5d1fc89767051f490d5b4f00e76a4cdbd92876.  The final homeomorphism to the
benchmark's metric `SphereSpace 1` and the convenience lattice corollaries are new here.
-/
import ChallengeDeps

open HomotopyGroups
open scoped ContinuousMap Topology Topology.Homotopy unitInterval
open Topology.Homotopy

noncomputable section

namespace Submission

namespace CircleHigher

namespace GenLoop

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Postcomposition of a generalized loop by a based continuous map. -/
def map (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) : Ω^ N Y y :=
  ⟨f.comp p.1, fun t ht => by
    simpa [hf] using congrArg f (_root_.GenLoop.boundary p t ht)⟩

@[simp]
theorem map_apply (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) (t : I^N) :
    map f hf p t = f (p t) :=
  rfl

@[simp]
theorem map_const (f : C(X, Y)) (hf : f x = y) :
    map f hf (_root_.GenLoop.const : Ω^ N X x) =
      (_root_.GenLoop.const : Ω^ N Y y) := by
  apply _root_.GenLoop.ext
  intro t
  simp [hf]

/-- Postcomposition preserves homotopy relative to the cube boundary. -/
theorem map_homotopic {p q : Ω^ N X x} (h : _root_.GenLoop.Homotopic p q)
    (f : C(X, Y)) (hf : f x = y) :
    _root_.GenLoop.Homotopic (map f hf p) (map f hf q) :=
  ContinuousMap.HomotopicRel.comp_continuousMap h f

variable [DecidableEq N]

@[simp]
theorem map_transAt (f : C(X, Y)) (hf : f x = y) (i : N) (p q : Ω^ N X x) :
    map f hf (_root_.GenLoop.transAt i p q) =
      _root_.GenLoop.transAt i (map f hf p) (map f hf q) := by
  apply _root_.GenLoop.ext
  intro t
  simp only [map_apply, _root_.GenLoop.transAt, _root_.GenLoop.coe_copy]
  split_ifs <;> rfl

end GenLoop

namespace HomotopyGroup

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- The map on homotopy classes induced by a based continuous map. -/
def map (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (GenLoop.map f hf) fun _ _ h => GenLoop.map_homotopic h f hf

@[simp]
theorem map_mk (f : C(X, Y)) (hf : f x = y) (p : Ω^ N X x) :
    map f hf (⟦p⟧ : HomotopyGroup N X x) = ⟦GenLoop.map f hf p⟧ :=
  rfl

/-- In positive dimensions the induced map is a monoid homomorphism. -/
def mapHom [DecidableEq N] [Nonempty N] (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := map f hf
  map_one' := by
    rw [_root_.HomotopyGroup.one_def, map_mk, GenLoop.map_const]
    exact _root_.HomotopyGroup.one_def.symm
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    simp only [_root_.HomotopyGroup.mul_spec (i := Classical.arbitrary N), map_mk,
      GenLoop.map_transAt]

end HomotopyGroup

private theorem zero_mem_cubeBoundary {N : Type*} [Nonempty N] :
    (0 : I^N) ∈ Cube.boundary N :=
  ⟨Classical.arbitrary N, Or.inl rfl⟩

namespace GenLoop

variable {N X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
  {p : E → X} {e : E}

/-- A covering map reflects homotopy of generalized loops. -/
@[simp]
theorem map_homotopic_iff [Nonempty N] (hp : IsCoveringMap p) {F G : Ω^ N E e} :
    _root_.GenLoop.Homotopic
        (map ⟨p, hp.continuous⟩ rfl F) (map ⟨p, hp.continuous⟩ rfl G) ↔
      _root_.GenLoop.Homotopic F G :=
  (hp.homotopicRel_iff_comp (f₀ := (F : C(I^N, E))) (f₁ := (G : C(I^N, E)))
    ⟨0, zero_mem_cubeBoundary,
      (_root_.GenLoop.boundary F 0 zero_mem_cubeBoundary).trans
        (_root_.GenLoop.boundary G 0 zero_mem_cubeBoundary).symm⟩).symm

/-- In dimension at least two, every generalized loop in the base of a
covering map lifts to a generalized loop at a prescribed point of the fibre. -/
theorem map_surjective [Nontrivial N] (hp : IsCoveringMap p) (f : Ω^ N X (p e)) :
    ∃ F : Ω^ N E e, map ⟨p, hp.continuous⟩ rfl F = f := by
  classical
  let i := Classical.arbitrary N
  let : Nonempty { j // j ≠ i } :=
    ⟨⟨(exists_ne i).choose, (exists_ne i).choose_spec⟩⟩
  let q : C(I × I^{ j // j ≠ i }, X) := (f : C(I^N, X)).comp (Cube.insertAt i)
  let cX : C(I^{ j // j ≠ i }, X) := .const _ (p e)
  let cE : C(I^{ j // j ≠ i }, E) := .const _ e
  let qRel : cX.HomotopyRel cX (Cube.boundary { j // j ≠ i }) :=
    { toContinuousMap := q
      map_zero_left := fun _ =>
        _root_.GenLoop.boundary f _ (Cube.insertAt_boundary i (Or.inl (Or.inl rfl)))
      map_one_left := fun _ =>
        _root_.GenLoop.boundary f _ (Cube.insertAt_boundary i (Or.inl (Or.inr rfl)))
      prop' := fun _ _ ha =>
        _root_.GenLoop.boundary f _ (Cube.insertAt_boundary i (Or.inr ha)) }
  let QRel : cE.HomotopyRel cE (Cube.boundary { j // j ≠ i }) :=
    hp.liftHomotopyRel qRel ⟨0, zero_mem_cubeBoundary, rfl⟩
      (funext fun _ => rfl) (funext fun _ => rfl)
  let P : Ω (Ω^ { j // j ≠ i } E e) _root_.GenLoop.const :=
    { toContinuousMap :=
        ⟨fun t => ⟨QRel.toContinuousMap.curry t, fun y hy => QRel.prop t y hy⟩,
          QRel.toContinuousMap.curry.continuous.subtype_mk _⟩
      source' := by ext y; exact QRel.apply_zero y
      target' := by ext y; exact QRel.apply_one y }
  let F : Ω^ N E e := _root_.GenLoop.fromLoop i P
  have hQ : p ∘ QRel.toContinuousMap = q := by
    simp only [QRel, IsCoveringMap.liftHomotopyRel]
    exact hp.liftHomotopy_lifts _ _ _
  have hF_apply (y : I^N) : F y = QRel (Cube.splitAt i y) := by
    rw [_root_.GenLoop.fromLoop_apply]
    rfl
  have hpF : ∀ y, p (F y) = f y := fun y => by
    calc
      p (F y) = p (QRel (Cube.splitAt i y)) := congr_arg p (hF_apply y)
      _ = q (Cube.splitAt i y) := congrFun hQ (Cube.splitAt i y)
      _ = f y := congr_arg f (Homeomorph.symm_apply_apply (Cube.splitAt i) y)
  exact ⟨F, _root_.GenLoop.ext _ _ hpF⟩

end GenLoop

namespace HomotopyGroup

variable {N X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
  {p : E → X} {e : E}

theorem map_injective [Nonempty N] (hp : IsCoveringMap p) :
    Function.Injective
      (map (N := N) (x := e) (y := p e) (⟨p, hp.continuous⟩ : C(E, X)) rfl) := by
  intro a b
  refine Quotient.inductionOn₂ a b fun F G h => ?_
  exact Quotient.sound ((GenLoop.map_homotopic_iff hp).1 (Quotient.exact h))

theorem map_surjective [Nontrivial N] (hp : IsCoveringMap p) :
    Function.Surjective
      (map (N := N) (x := e) (y := p e) (⟨p, hp.continuous⟩ : C(E, X)) rfl) := by
  refine Quotient.ind fun f => ?_
  obtain ⟨F, hF⟩ := GenLoop.map_surjective hp f
  exact ⟨⟦F⟧, by rw [map_mk, hF]⟩

/-- A covering map induces an isomorphism on every homotopy group of
dimension at least two. -/
def coveringMulEquiv [DecidableEq N] [Nontrivial N]
    (hp : IsCoveringMap p) (e : E) :
    HomotopyGroup N E e ≃* HomotopyGroup N X (p e) := by
  classical
  exact MulEquiv.ofBijective (mapHom (⟨p, hp.continuous⟩ : C(E, X)) rfl)
    ⟨map_injective hp, map_surjective hp⟩

end HomotopyGroup

/-- Every homotopy group of a real topological vector space is trivial. -/
theorem subsingleton_topologicalVectorSpace
    {N E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (x : E) :
    Subsingleton (HomotopyGroup N E x) := by
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b fun f g => Quotient.sound ⟨?_⟩
  exact
    { toHomotopy := .affine f.1 g.1
      prop' := fun _ u hu => by
        simp [_root_.GenLoop.boundary f u hu, _root_.GenLoop.boundary g u hu] }

/-- All higher homotopy groups of a real additive circle vanish. -/
theorem subsingleton_addCircle {N : Type*} [Nontrivial N]
    (period : ℝ) (x : AddCircle period) :
    Subsingleton (HomotopyGroup N (AddCircle period) x) := by
  classical
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact ((HomotopyGroup.coveringMulEquiv
    (_root_.AddCircle.isCoveringMap_coe period) x).toEquiv.subsingleton_congr).mp
      (subsingleton_topologicalVectorSpace x)

/-- All higher homotopy groups of Mathlib's complex unit circle vanish. -/
theorem subsingleton_circle {N : Type*} [Nontrivial N] (x : Circle) :
    Subsingleton (HomotopyGroup N Circle x) := by
  classical
  let h : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (h.symm x)
  have htx : h (t : AddCircle (1 : ℝ)) = x := by
    rw [ht, h.apply_symm_apply]
  let hp : ℝ → Circle := h ∘ ((↑) : ℝ → AddCircle (1 : ℝ))
  have hcov : IsCoveringMap hp :=
    (_root_.AddCircle.isCoveringMap_coe (1 : ℝ)).homeomorph_comp h
  have hs : Subsingleton (HomotopyGroup N ℝ t) :=
    subsingleton_topologicalVectorSpace t
  rw [← htx]
  exact ((HomotopyGroup.coveringMulEquiv hcov t).toEquiv.subsingleton_congr).mp hs

/-- The standard complex circle is homeomorphic to the benchmark's unit sphere
in two-dimensional Euclidean space. -/
def circleHomeomorphSphereOne : Circle ≃ₜ SphereSpace 1 where
  toFun z := ⟨Complex.orthonormalBasisOneI.repr z, by
    rw [Metric.mem_sphere, dist_zero_right]
    rw [Complex.orthonormalBasisOneI.repr.norm_map]
    exact Circle.norm_coe z⟩
  invFun z := ⟨Complex.orthonormalBasisOneI.repr.symm z, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp z.property⟩
  left_inv z := Circle.ext (Complex.orthonormalBasisOneI.repr.symm_apply_apply z)
  right_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.apply_symm_apply z)
  continuous_toFun :=
    (Complex.orthonormalBasisOneI.repr.continuous.comp continuous_subtype_val).subtype_mk
      (fun z => by
        rw [Metric.mem_sphere, dist_zero_right]
        change ‖Complex.orthonormalBasisOneI.repr (z : ℂ)‖ = 1
        rw [Complex.orthonormalBasisOneI.repr.norm_map]
        exact Circle.norm_coe z)
  continuous_invFun :=
    (Complex.orthonormalBasisOneI.repr.symm.continuous.comp continuous_subtype_val).subtype_mk
      (fun z => by
        apply mem_sphere_zero_iff_norm.mpr
        change ‖Complex.orthonormalBasisOneI.repr.symm
          (z : EuclideanSpace ℝ (Fin 2))‖ = 1
        rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
        exact mem_sphere_zero_iff_norm.mp z.property)

end CircleHigher

/-- Every homotopy group of the benchmark's metric circle above degree one is trivial. -/
theorem sphere_one_higher_homotopy_subsingleton (k : ℕ) :
    Subsingleton
      (HomotopyGroup.Pi (k + 2) (SphereSpace 1) (sphereBasepoint 1)) := by
  classical
  let e := CircleHigher.circleHomeomorphSphereOne
  let x : Circle := e.symm (sphereBasepoint 1)
  have hx : e x = sphereBasepoint 1 := e.apply_symm_apply _
  -- A homeomorphism is used as a one-sheeted covering after the universal
  -- cover of the circle, so the chosen metric-sphere basepoint is handled
  -- without any hidden basepoint identification.
  let hcircle : AddCircle (1 : ℝ) ≃ₜ Circle :=
    AddCircle.homeomorphCircle one_ne_zero
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (hcircle.symm x)
  have htbase : e (hcircle (t : AddCircle (1 : ℝ))) = sphereBasepoint 1 := by
    rw [ht, hcircle.apply_symm_apply, hx]
  let p : ℝ → SphereSpace 1 :=
    e ∘ hcircle ∘ ((↑) : ℝ → AddCircle (1 : ℝ))
  have hp : IsCoveringMap p :=
    ((_root_.AddCircle.isCoveringMap_coe (1 : ℝ)).homeomorph_comp hcircle).homeomorph_comp e
  have hreal : Subsingleton (HomotopyGroup.Pi (k + 2) ℝ t) :=
    CircleHigher.subsingleton_topologicalVectorSpace t
  rw [← htbase]
  exact ((CircleHigher.HomotopyGroup.coveringMulEquiv hp t).toEquiv.subsingleton_congr).mp hreal

/-! Convenience names for ten displayed cells. They are not counted as distinct results. -/

theorem pi2_sphere_one_subsingleton :
    Subsingleton (HomotopyGroup.Pi 2 (SphereSpace 1) (sphereBasepoint 1)) := by
  simpa using sphere_one_higher_homotopy_subsingleton 0

theorem pi3_sphere_one_subsingleton :
    Subsingleton (HomotopyGroup.Pi 3 (SphereSpace 1) (sphereBasepoint 1)) := by
  simpa using sphere_one_higher_homotopy_subsingleton 1

theorem pi4_sphere_one_subsingleton :
    Subsingleton (HomotopyGroup.Pi 4 (SphereSpace 1) (sphereBasepoint 1)) := by
  simpa using sphere_one_higher_homotopy_subsingleton 2

theorem pi5_sphere_one_subsingleton :
    Subsingleton (HomotopyGroup.Pi 5 (SphereSpace 1) (sphereBasepoint 1)) := by
  simpa using sphere_one_higher_homotopy_subsingleton 3

theorem pi6_sphere_one_subsingleton :
    Subsingleton (HomotopyGroup.Pi 6 (SphereSpace 1) (sphereBasepoint 1)) := by
  simpa using sphere_one_higher_homotopy_subsingleton 4

theorem pi7_sphere_one_subsingleton :
    Subsingleton (HomotopyGroup.Pi 7 (SphereSpace 1) (sphereBasepoint 1)) := by
  simpa using sphere_one_higher_homotopy_subsingleton 5

theorem pi8_sphere_one_subsingleton :
    Subsingleton (HomotopyGroup.Pi 8 (SphereSpace 1) (sphereBasepoint 1)) := by
  simpa using sphere_one_higher_homotopy_subsingleton 6

theorem pi9_sphere_one_subsingleton :
    Subsingleton (HomotopyGroup.Pi 9 (SphereSpace 1) (sphereBasepoint 1)) := by
  simpa using sphere_one_higher_homotopy_subsingleton 7

theorem pi10_sphere_one_subsingleton :
    Subsingleton (HomotopyGroup.Pi 10 (SphereSpace 1) (sphereBasepoint 1)) := by
  simpa using sphere_one_higher_homotopy_subsingleton 8

theorem pi11_sphere_one_subsingleton :
    Subsingleton (HomotopyGroup.Pi 11 (SphereSpace 1) (sphereBasepoint 1)) := by
  simpa using sphere_one_higher_homotopy_subsingleton 9

end Submission
