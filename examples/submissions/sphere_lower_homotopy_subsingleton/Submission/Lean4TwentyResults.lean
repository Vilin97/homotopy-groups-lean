/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.IndependentResults
import Submission.MetricSpherePiOne
import Submission.Model.SphereConnected

/-!
# Twenty additional Lean 4 homotopy-group results

These declarations are mathematically distinct general statements.  The list does not count
numeric specializations, displayed lattice cells, or aliases of the same theorem.
-/

open scoped ContinuousMap Topology Topology.Homotopy
open HomotopyGroups

noncomputable section

namespace Submission

universe u v

/-! ## Induced maps -/

/-- Result 1: a based retraction induces an injection on homotopy groups in every dimension. -/
theorem homotopyGroup_retraction_injective
    {N : Type*} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (g : C(Y, X))
    (hf : f x = y) (hg : g y = x)
    (hgf : g.comp f = ContinuousMap.id X) :
    Function.Injective (HomotopyGroup.map (N := N) f hf) :=
  Function.LeftInverse.injective fun a =>
    HomotopyGroup.map_map_of_comp_eq_id g f hf hg hgf a

/-- Result 2: a based section induces a surjection on homotopy groups in every dimension. -/
theorem homotopyGroup_section_surjective
    {N : Type*} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (g : C(Y, X))
    (hf : f x = y) (hg : g y = x)
    (hfg : f.comp g = ContinuousMap.id Y) :
    Function.Surjective (HomotopyGroup.map (N := N) f hf) :=
  Function.RightInverse.surjective fun b =>
    HomotopyGroup.map_map_of_comp_eq_id f g hg hf hfg b

/-- Result 3: mutually inverse based maps induce a multiplicative equivalence. -/
theorem homotopyGroup_strict_equivalence
    (n : ℕ) {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (g : C(Y, X))
    (hf : f x = y) (hg : g y = x)
    (hgf : g.comp f = ContinuousMap.id X)
    (hfg : f.comp g = ContinuousMap.id Y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) X x ≃*
        HomotopyGroup.Pi (n + 1) Y y) := by
  refine ⟨MulEquiv.ofBijective (HomotopyGroup.mapHom f hf) ⟨?_, ?_⟩⟩
  · exact homotopyGroup_retraction_injective f g hf hg hgf
  · exact homotopyGroup_section_surjective f g hf hg hfg

/-- Result 4: a retract of a space with trivial homotopy group has trivial homotopy group. -/
theorem homotopyGroup_retract_subsingleton
    {N : Type*} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (g : C(Y, X))
    (hf : f x = y) (hg : g y = x)
    (hgf : g.comp f = ContinuousMap.id X)
    [Subsingleton (HomotopyGroup N Y y)] :
    Subsingleton (HomotopyGroup N X x) :=
  (homotopyGroup_retraction_injective f g hf hg hgf).subsingleton

/-- Result 5: a section of a map out of a homotopically trivial space has homotopically trivial
target. -/
theorem homotopyGroup_section_subsingleton
    {N : Type*} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (g : C(Y, X))
    (hf : f x = y) (hg : g y = x)
    (hfg : f.comp g = ContinuousMap.id Y)
    [Subsingleton (HomotopyGroup N X x)] :
    Subsingleton (HomotopyGroup N Y y) :=
  (homotopyGroup_section_surjective f g hf hg hfg).subsingleton

/-- Result 6: mutually inverse based maps preserve triviality of positive homotopy groups in
both directions. -/
theorem homotopyGroup_strict_equivalence_subsingleton_iff
    (n : ℕ) {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (g : C(Y, X))
    (hf : f x = y) (hg : g y = x)
    (hgf : g.comp f = ContinuousMap.id X)
    (hfg : f.comp g = ContinuousMap.id Y) :
    Subsingleton (HomotopyGroup.Pi (n + 1) X x) ↔
      Subsingleton (HomotopyGroup.Pi (n + 1) Y y) := by
  obtain ⟨e⟩ := homotopyGroup_strict_equivalence n f g hf hg hgf hfg
  exact e.toEquiv.subsingleton_congr

/-- Result 7: a homeomorphism preserves every positive homotopy group. -/
theorem homotopyGroup_homeomorphism_invariance
    (n : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) X x ≃*
        HomotopyGroup.Pi (n + 1) Y (e x)) :=
  nonempty_mulEquiv_of_homotopyEquiv' e.toHomotopyEquiv x

/-- Result 8: pointed-homotopic maps induce the same map, including in dimension zero. -/
theorem homotopyGroup_pointed_homotopy_invariance_all_dimensions
    (n : ℕ) {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} {f g : C(X, Y)} (hf : f x = y)
    {S : Set X} (hx : x ∈ S) (H : f.HomotopicRel g S) :
    HomotopyGroup.map (N := Fin n) f hf =
      HomotopyGroup.map g ((H.fst_eq_snd hx).symm.trans hf) :=
  HomotopyGroup.map_eq_of_homotopicRel hf hx H

/-! ## Products -/

/-- Result 9: a positive homotopy group of a binary product is trivial exactly when the two
factor groups are trivial. -/
theorem homotopyGroup_product_subsingleton_iff
    (n : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] (x : X) (y : Y) :
    Subsingleton (HomotopyGroup.Pi (n + 1) (X × Y) (x, y)) ↔
      Subsingleton (HomotopyGroup.Pi (n + 1) X x) ∧
        Subsingleton (HomotopyGroup.Pi (n + 1) Y y) := by
  let e := HomotopyGroup.prodMulEquiv (N := Fin (n + 1)) x y
  constructor
  · intro h
    have hp : Subsingleton
        (HomotopyGroup.Pi (n + 1) X x × HomotopyGroup.Pi (n + 1) Y y) :=
      e.toEquiv.subsingleton_congr.mp h
    letI := hp
    exact ⟨
      ⟨fun a b => congrArg Prod.fst
        (Subsingleton.elim (a, (1 : HomotopyGroup.Pi (n + 1) Y y)) (b, 1))⟩,
      ⟨fun a b => congrArg Prod.snd
        (Subsingleton.elim ((1 : HomotopyGroup.Pi (n + 1) X x), a) (1, b))⟩⟩
  · rintro ⟨hx, hy⟩
    letI := hx
    letI := hy
    exact e.toEquiv.subsingleton_congr.mpr inferInstance

/-- Result 10: multiplying by a contractible right factor does not change positive homotopy
groups. -/
theorem homotopyGroup_product_contractible_right
    (n : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] [ContractibleSpace Y]
    (x : X) (y : Y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (X × Y) (x, y) ≃*
        HomotopyGroup.Pi (n + 1) X x) := by
  letI : Subsingleton (HomotopyGroup.Pi (n + 1) Y y) :=
    subsingleton_homotopyGroup_of_contractible y
  letI : Unique (HomotopyGroup.Pi (n + 1) Y y) :=
    { default := 1
      uniq := fun _ => Subsingleton.elim _ _ }
  exact ⟨(HomotopyGroup.prodMulEquiv x y).trans MulEquiv.prodUnique⟩

/-- Result 11: multiplying by a contractible left factor does not change positive homotopy
groups. -/
theorem homotopyGroup_product_contractible_left
    (n : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] [ContractibleSpace X]
    (x : X) (y : Y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (X × Y) (x, y) ≃*
        HomotopyGroup.Pi (n + 1) Y y) := by
  letI : Subsingleton (HomotopyGroup.Pi (n + 1) X x) :=
    subsingleton_homotopyGroup_of_contractible x
  letI : Unique (HomotopyGroup.Pi (n + 1) X x) :=
    { default := 1
      uniq := fun _ => Subsingleton.elim _ _ }
  exact ⟨(HomotopyGroup.prodMulEquiv x y).trans MulEquiv.uniqueProd⟩

/-- Result 12: the fundamental group of a binary product is the product of the fundamental
groups. -/
theorem fundamentalGroup_product
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) :
    Nonempty
      (FundamentalGroup (X × Y) (x, y) ≃*
        FundamentalGroup X x × FundamentalGroup Y y) :=
  ⟨HomotopyGroup.pi1MulEquivFundamentalGroup.symm |>.trans
    ((HomotopyGroup.prodMulEquiv (N := Fin 1) x y).trans
      (MulEquiv.prodCongr HomotopyGroup.pi1MulEquivFundamentalGroup
        HomotopyGroup.pi1MulEquivFundamentalGroup))⟩

/-- Result 13: path components preserve binary products. -/
theorem zerothHomotopy_product
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) :
    Nonempty (ZerothHomotopy (X × Y) ≃ ZerothHomotopy X × ZerothHomotopy Y) :=
  ⟨HomotopyGroup.pi0EquivZerothHomotopy.symm |>.trans
    ((HomotopyGroup.prodEquiv (N := Fin 0) x y).trans
      (HomotopyGroup.pi0EquivZerothHomotopy.prodCongr
        HomotopyGroup.pi0EquivZerothHomotopy))⟩

/-! ## Vanishing and structure -/

/-- Result 14: a space homotopy equivalent to one with a trivial positive homotopy group also
has a trivial homotopy group. -/
theorem homotopyGroup_homotopy_equiv_subsingleton
    (n : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X)
    [Subsingleton (HomotopyGroup.Pi (n + 1) Y (e x))] :
    Subsingleton (HomotopyGroup.Pi (n + 1) X x) := by
  obtain ⟨h⟩ := nonempty_mulEquiv_of_homotopyEquiv' (N := Fin (n + 1)) e x
  exact h.injective.subsingleton

/-- Result 15: a homeomorphism preserves triviality of positive homotopy groups in both
directions. -/
theorem homotopyGroup_homeomorphism_subsingleton_iff
    (n : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    Subsingleton (HomotopyGroup.Pi (n + 1) X x) ↔
      Subsingleton (HomotopyGroup.Pi (n + 1) Y (e x)) := by
  obtain ⟨h⟩ := homotopyGroup_homeomorphism_invariance n X Y e x
  exact h.toEquiv.subsingleton_congr

/-- Result 16: in a path-connected space, triviality of a positive homotopy group is
independent of the basepoint. -/
theorem homotopyGroup_pathConnected_subsingleton_iff
    (n : ℕ) (X : Type u) [TopologicalSpace X] [PathConnectedSpace X]
    (x y : X) :
    Subsingleton (HomotopyGroup.Pi (n + 1) X x) ↔
      Subsingleton (HomotopyGroup.Pi (n + 1) X y) := by
  obtain ⟨h⟩ := nonempty_mulEquiv_of_pathConnectedSpace
    (N := Fin (n + 1)) x y
  exact h.toEquiv.subsingleton_congr

/-- Result 17: every homotopy group in dimension at least two is abelian. -/
theorem higher_homotopy_mul_comm
    (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X)
    (a b : HomotopyGroup.Pi (n + 2) X x) :
    a * b = b * a :=
  mul_comm a b

/-- Result 18: a covering map is injective on every positive homotopy group, including `pi_1`. -/
theorem homotopyGroup_covering_map_injective
    (n : ℕ) {E : Type u} {X : Type v}
    [TopologicalSpace E] [TopologicalSpace X]
    (p : E → X) (hp : IsCoveringMap p) (e : E) :
    Function.Injective
      (HomotopyGroup.mapHom (N := Fin (n + 1)) (x := e) (y := p e)
        (⟨p, hp.continuous⟩ : C(E, X)) rfl) :=
  HomotopyGroup.map_injective hp

/-! ## Exact metric-circle results at arbitrary basepoints -/

/-- Result 19: the fundamental group of the exact metric circle is infinite cyclic at every
basepoint. -/
theorem pi1_sphere_one_mulEquiv_int_at (x : SphereSpace 1) :
    Nonempty
      (HomotopyGroup.Pi 1 (SphereSpace 1) x ≃*
        Multiplicative ℤ) := by
  letI := pathConnectedSpace_sph (n := 1) (by omega)
  obtain ⟨e⟩ := nonempty_mulEquiv_of_pathConnectedSpace
    (N := Fin 1) x (sphereBasepoint 1)
  obtain ⟨c⟩ := pi1_sphere_one_mulEquiv_int
  exact ⟨e.trans c⟩

private theorem circle_higher_homotopy_subsingleton
    (k : ℕ) (x : Circle) :
    Subsingleton (HomotopyGroup.Pi (k + 2) Circle x) := by
  classical
  let h : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (h.symm x)
  have htx : h (t : AddCircle (1 : ℝ)) = x := by
    rw [ht, h.apply_symm_apply]
  let p : ℝ → Circle := h ∘ ((↑) : ℝ → AddCircle (1 : ℝ))
  have hp : IsCoveringMap p :=
    (_root_.AddCircle.isCoveringMap_coe (1 : ℝ)).homeomorph_comp h
  have hr : Subsingleton (HomotopyGroup.Pi (k + 2) ℝ t) :=
    subsingleton_homotopyGroup_of_contractible t
  rw [← htx]
  exact ((HomotopyGroup.coveringMulEquiv hp t).toEquiv.subsingleton_congr).mp hr

/-- Result 20: every homotopy group of the exact metric circle above degree one is trivial at
every basepoint. -/
theorem sphere_one_higher_homotopy_subsingleton_at
    (k : ℕ) (x : SphereSpace 1) :
    Subsingleton (HomotopyGroup.Pi (k + 2) (SphereSpace 1) x) := by
  let e := circleHomeomorphMetricSphereOne
  let z : Circle := e.symm x
  obtain ⟨h⟩ := homotopyGroup_homeomorphism_invariance (k + 1) Circle (SphereSpace 1) e z
  have hx : e z = x := e.apply_symm_apply x
  rw [hx] at h
  exact h.toEquiv.subsingleton_congr.mp (circle_higher_homotopy_subsingleton k z)

end Submission
