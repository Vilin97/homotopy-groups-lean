/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.WhiteheadTheorem.RelHomotopyGroup.LongExactSeq
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton
import Mathlib.Algebra.Exact.Basic

/-!
# The group structure on relative homotopy groups

The vendored `WhiteheadTheorem` library defines `π_rel n X A a = RelHomotopyGroup n X A a` as a
bare pointed set. This file equips it with its group structure and upgrades the long exact
sequence of a pair to a sequence of group homomorphisms.

## Strategy

In the conventions of `WhiteheadTheorem`, the distinguished ("relative") cube coordinate is the
*last* one: `⊔I^n` is the boundary of the cube with the interior of the face
`y (Fin.last _) = 1` removed. So every coordinate `i.castSucc` with `i : Fin n` is free, and
concatenating in such a direction preserves both defining conditions of `RelGenLoop`.

Splitting off the *first* cube coordinate identifies

`RelGenLoop (n + 2) X A a ≃ Path (const : RelGenLoop (n + 1) X A a) const`
  (`RelGenLoop.pathEquiv`)

compatibly with homotopies (`RelGenLoop.homotopic_iff_toPath`), hence

`π_rel (n + 2) X A a ≃ FundamentalGroup ↥(RelGenLoop (n + 1) X A a) const`
  (`RelHomotopyGroup.equivFundamentalGroup`),

and the group structure is transported along that equivalence. Conjugating by the cube-coordinate
swap `0 ↔ k.castSucc` (`RelGenLoop.reindex`) produces one such group structure `auxGroup k` per
free direction; they all agree by the Eckmann–Hilton argument
(`RelHomotopyGroup.auxGroup_indep`), which also yields commutativity from degree `3` on. This
mirrors `Mathlib/Topology/Homotopy/HomotopyGroup.lean`.

## Main definitions and results

* `RelGenLoop.transAt` / `RelGenLoop.symmAt` — concatenation and reversal in a free direction;
* `RelHomotopyGroup.group : Group (π_rel (n + 2) X A a)`;
* `RelHomotopyGroup.commGroup : CommGroup (π_rel (n + 3) X A a)`;
* `RelHomotopyGroup.one_def`, `mul_spec`, `inv_spec` — the unit, product and inverse on classes;
* `RelHomotopyGroup.iStarHom`, `jStarHom`, `bdHom` — the three maps of the long exact sequence
  of a pair, as `MonoidHom`s;
* `RelHomotopyGroup.mulExact_iStarHom_jStarHom`, `mulExact_jStarHom_bdHom`,
  `mulExact_bdHom_iStarHom` — exactness in the form of Mathlib's `Function.MulExact`, so that
  `Mathlib/Algebra/FiveLemma.lean` and the `Function.MulExact` API apply.
-/

open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Cube

variable {n : ℕ}

/-- Split off the *first* coordinate of a cube, `y ↦ (y 0, fun i ↦ y i.succ)`. -/
def splitAtFirst {n : ℕ} : (I^ Fin (n + 1)) ≃ₜ I × (I^ Fin n) where
  toFun y := (y 0, fun i ↦ y i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv y := by
    ext i
    refine Fin.cases ?_ ?_ i <;> simp
  right_inv p := by
    ext i <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by
    refine continuous_pi fun i ↦ ?_
    refine Fin.cases ?_ ?_ i
    · simpa using continuous_fst
    · intro j
      simpa using (continuous_apply j).comp' continuous_snd

lemma mem_boundary_iff_splitAtFirst {n : ℕ} {y : I^ Fin (n + 1)} :
    y ∈ (∂I^(n + 1)) ↔ (y 0 = 0 ∨ y 0 = 1) ∨ (fun i ↦ y i.succ) ∈ ∂I^n := by
  constructor
  · rintro ⟨i, hi⟩
    refine Fin.cases (motive := fun i ↦ (y i = 0 ∨ y i = 1) → _) ?_ ?_ i hi
    · exact fun h ↦ Or.inl h
    · exact fun j h ↦ Or.inr ⟨j, h⟩
  · rintro (h | ⟨j, hj⟩)
    · exact ⟨0, h⟩
    · exact ⟨j.succ, hj⟩

lemma succ_last_eq (n : ℕ) : (Fin.last n).succ = Fin.last (n + 1) := by
  ext; simp

lemma mem_boundaryJar_iff_splitAtFirst {n : ℕ} {y : I^ Fin (n + 2)} :
    y ∈ (⊔I^(n + 2)) ↔ (y 0 = 0 ∨ y 0 = 1) ∨ (fun i ↦ y i.succ) ∈ ⊔I^(n + 1) := by
  have hlast : y (Fin.last n).succ = y (Fin.last (n + 1)) := by rw [succ_last_eq]
  have hsucc : ∀ j : Fin (n + 1), j.succ < Fin.last (n + 1) ↔ j < Fin.last n := by
    intro j; simp [Fin.lt_def]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h0 : y 0 = 0 ∨ y 0 = 1
    · exact Or.inl h0
    refine Or.inr ⟨?_, ?_⟩
    · obtain ⟨i, hi⟩ := h1
      refine Fin.cases (motive := fun i ↦ (y i = 0 ∨ y i = 1) → _) (fun h ↦ absurd h h0)
        (fun j h ↦ ⟨j, h⟩) i hi
    · intro hy
      simp only [hlast] at hy
      obtain ⟨i, hilt, hi⟩ := h2 hy
      refine Fin.cases (motive := fun i ↦ i < Fin.last (n + 1) → (y i = 0 ∨ y i = 1) → _)
        (fun _ h ↦ absurd h h0) (fun j hjlt h ↦ ⟨j, (hsucc j).mp hjlt, h⟩) i hilt hi
  · rintro (h0 | ⟨h1, h2⟩)
    · exact ⟨⟨0, h0⟩, fun _ ↦ ⟨0, by simp [Fin.lt_def], h0⟩⟩
    · refine ⟨?_, ?_⟩
      · obtain ⟨j, hj⟩ := h1
        exact ⟨j.succ, hj⟩
      · intro hy
        simp only [← hlast] at hy
        obtain ⟨j, hjlt, hj⟩ := h2 hy
        exact ⟨j.succ, (hsucc j).mpr hjlt, hj⟩

lemma mem_boundary_cons {n : ℕ} (t : I) {z : I^ Fin n} (hz : z ∈ ∂I^n) :
    (Fin.cons t z : I^ Fin (n + 1)) ∈ ∂I^(n + 1) :=
  mem_boundary_iff_splitAtFirst.mpr <| Or.inr <| by simpa using hz

lemma mem_boundaryJar_cons {n : ℕ} (t : I) {z : I^ Fin (n + 1)} (hz : z ∈ ⊔I^(n + 1)) :
    (Fin.cons t z : I^ Fin (n + 2)) ∈ ⊔I^(n + 2) :=
  mem_boundaryJar_iff_splitAtFirst.mpr <| Or.inr <| by simpa using hz

lemma mem_boundaryJar_cons_zero {n : ℕ} (z : I^ Fin (n + 1)) :
    (Fin.cons 0 z : I^ Fin (n + 2)) ∈ ⊔I^(n + 2) :=
  mem_boundaryJar_iff_splitAtFirst.mpr <| Or.inl <| Or.inl <| by simp

lemma mem_boundaryJar_cons_one {n : ℕ} (z : I^ Fin (n + 1)) :
    (Fin.cons 1 z : I^ Fin (n + 2)) ∈ ⊔I^(n + 2) :=
  mem_boundaryJar_iff_splitAtFirst.mpr <| Or.inl <| Or.inr <| by simp

end Cube

namespace RelGenLoop

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}

/-- The inclusion of the relative generalized loops into all continuous maps on the cube,
as a continuous map. -/
def valCM (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    C(RelGenLoop n X A a, C(I^ Fin n, X)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
lemma valCM_apply (f : RelGenLoop n X A a) : valCM n X A a f = f.val := rfl

/-- A map on the `(n + 1)`-cube, viewed as a continuous family of maps on the `n`-cube
indexed by the *first* cube coordinate. -/
def curryFirst (f : C(I^ Fin (n + 1), X)) : C(I, C(I^ Fin n, X)) :=
  (f.comp (toContinuousMap Cube.splitAtFirst.symm)).curry

@[simp]
lemma curryFirst_apply (f : C(I^ Fin (n + 1), X)) (t : I) (z : I^ Fin n) :
    curryFirst f t z = f (Fin.cons t z) := rfl

/-- A continuous family of maps on the `n`-cube, viewed as a map on the `(n + 1)`-cube. -/
def uncurryFirst (F : C(I, C(I^ Fin n, X))) : C(I^ Fin (n + 1), X) :=
  F.uncurry.comp (toContinuousMap Cube.splitAtFirst)

@[simp]
lemma uncurryFirst_apply (F : C(I, C(I^ Fin n, X))) (y : I^ Fin (n + 1)) :
    uncurryFirst F y = F (y 0) (fun i ↦ y i.succ) := rfl

@[simp]
lemma curryFirst_uncurryFirst (F : C(I, C(I^ Fin n, X))) : curryFirst (uncurryFirst F) = F := by
  ext t z; simp

@[simp]
lemma uncurryFirst_curryFirst (f : C(I^ Fin (n + 1), X)) : uncurryFirst (curryFirst f) = f := by
  ext y
  show f (Fin.cons (y 0) fun i ↦ y i.succ) = f y
  exact congrArg _ (Fin.cons_self_tail y)

lemma curryFirst_mem {f : C(I^ Fin (n + 2), X)} (hf : f ∈ RelGenLoop (n + 2) X A a) (t : I) :
    curryFirst f t ∈ RelGenLoop (n + 1) X A a :=
  ⟨fun _ hz ↦ hf.1 _ (Cube.mem_boundary_cons t hz),
   fun _ hz ↦ hf.2 _ (Cube.mem_boundaryJar_cons t hz)⟩

/-- The membership criterion for `uncurryFirst`: a family of relative generalized loops which
is constant at both ends assembles into a relative generalized loop one dimension up. -/
lemma uncurryFirst_mem {F : C(I, C(I^ Fin (n + 1), X))}
    (hF : ∀ t, F t ∈ RelGenLoop (n + 1) X A a)
    (h0 : ∀ z, F 0 z = (a : X)) (h1 : ∀ z, F 1 z = (a : X)) :
    uncurryFirst F ∈ RelGenLoop (n + 2) X A a := by
  constructor
  · intro y hy
    rcases Cube.mem_boundary_iff_splitAtFirst.mp hy with (h | h) | hz
    · show F (y 0) _ ∈ A
      rw [h, h0]; exact a.property
    · show F (y 0) _ ∈ A
      rw [h, h1]; exact a.property
    · exact (hF (y 0)).1 _ hz
  · intro y hy
    rcases Cube.mem_boundaryJar_iff_splitAtFirst.mp hy with (h | h) | hz
    · show F (y 0) _ = _; rw [h]; exact h0 _
    · show F (y 0) _ = _; rw [h]; exact h1 _
    · exact (hF (y 0)).2 _ hz

/-- An `(n + 2)`-dimensional relative generalized loop, viewed as a loop, based at the constant
map, in the space of `(n + 1)`-dimensional relative generalized loops. -/
def toPath (f : RelGenLoop (n + 2) X A a) : Path (const : RelGenLoop (n + 1) X A a) const where
  toFun t := ⟨curryFirst f.val t, curryFirst_mem f.property t⟩
  continuous_toFun := Continuous.subtype_mk (map_continuous (curryFirst f.val)) _
  source' := Subtype.ext <| ContinuousMap.ext fun z ↦
    f.property.2 _ (Cube.mem_boundaryJar_cons_zero z)
  target' := Subtype.ext <| ContinuousMap.ext fun z ↦
    f.property.2 _ (Cube.mem_boundaryJar_cons_one z)

@[simp]
lemma toPath_apply_apply (f : RelGenLoop (n + 2) X A a) (t : I) (z : I^ Fin (n + 1)) :
    ((toPath f t : RelGenLoop (n + 1) X A a) : C(I^ Fin (n + 1), X)) z = f.val (Fin.cons t z) :=
  rfl

/-- A loop, based at the constant map, in the space of `(n + 1)`-dimensional relative generalized
loops, viewed as an `(n + 2)`-dimensional relative generalized loop. -/
def ofPath (p : Path (const : RelGenLoop (n + 1) X A a) const) : RelGenLoop (n + 2) X A a :=
  ⟨uncurryFirst ((valCM (n + 1) X A a).comp p.toContinuousMap),
    uncurryFirst_mem (fun t ↦ (p t).property)
      (fun z ↦ by simp only [ContinuousMap.comp_apply, Path.coe_toContinuousMap,
        Path.source, valCM_apply]; rfl)
      (fun z ↦ by simp only [ContinuousMap.comp_apply, Path.coe_toContinuousMap,
        Path.target, valCM_apply]; rfl)⟩

@[simp]
lemma ofPath_apply (p : Path (const : RelGenLoop (n + 1) X A a) const) (y : I^ Fin (n + 2)) :
    (ofPath p).val y = (p (y 0)).val (fun i ↦ y i.succ) := rfl

/-- Relative generalized loops of dimension `n + 2` are the same thing as loops based at the
constant map in the space of relative generalized loops of dimension `n + 1`. -/
def pathEquiv : RelGenLoop (n + 2) X A a ≃ Path (const : RelGenLoop (n + 1) X A a) const where
  toFun := toPath
  invFun := ofPath
  left_inv f := Subtype.ext <| ContinuousMap.ext fun y ↦ by
    show f.val (Fin.cons (y 0) fun i ↦ y i.succ) = f.val y
    exact congrArg _ (Fin.cons_self_tail y)
  right_inv p := by
    ext t z
    rfl

/-- The two-parameter analogue of `RelGenLoop.curryFirst`, used to translate homotopies. -/
def curryFirst₂ (H : C(I × I^ Fin (n + 1), X)) : C(I × I, C(I^ Fin n, X)) :=
  (H.comp ⟨fun p ↦ (p.1.1, Cube.splitAtFirst.symm (p.1.2, p.2)), by fun_prop⟩).curry

@[simp]
lemma curryFirst₂_apply (H : C(I × I^ Fin (n + 1), X)) (st : I × I) (z : I^ Fin n) :
    curryFirst₂ H st z = H (st.1, Fin.cons st.2 z) := rfl

/-- The two-parameter analogue of `RelGenLoop.uncurryFirst`, used to translate homotopies. -/
def uncurryFirst₂ (G : C(I × I, C(I^ Fin n, X))) : C(I × I^ Fin (n + 1), X) :=
  G.uncurry.comp ⟨fun p ↦ ((p.1, (Cube.splitAtFirst p.2).1), (Cube.splitAtFirst p.2).2),
    by fun_prop⟩

@[simp]
lemma uncurryFirst₂_apply (G : C(I × I, C(I^ Fin n, X))) (sy : I × I^ Fin (n + 1)) :
    uncurryFirst₂ G sy = G (sy.1, sy.2 0) (fun i ↦ sy.2 i.succ) := rfl

/-- Two `(n + 2)`-dimensional relative generalized loops are homotopic through relative
generalized loops exactly when the corresponding loops in the space of `(n + 1)`-dimensional
relative generalized loops are homotopic as paths. -/
theorem homotopic_iff_toPath (f g : RelGenLoop (n + 2) X A a) :
    Homotopic f g ↔ (toPath f).Homotopic (toPath g) := by
  constructor
  · rintro ⟨H⟩
    refine ⟨{ toFun := fun st ↦ ⟨curryFirst₂ H.toHomotopy.toContinuousMap st,
                curryFirst_mem (H.prop st.1) st.2⟩
              continuous_toFun := Continuous.subtype_mk
                (map_continuous (curryFirst₂ H.toHomotopy.toContinuousMap)) _
              map_zero_left := fun t ↦ Subtype.ext <| ContinuousMap.ext fun z ↦
                H.toHomotopy.apply_zero _
              map_one_left := fun t ↦ Subtype.ext <| ContinuousMap.ext fun z ↦
                H.toHomotopy.apply_one _
              prop' := fun s t ht ↦ Subtype.ext <| ContinuousMap.ext fun z ↦ ?_ }⟩
    rcases ht with rfl | rfl
    · exact ((H.prop s).2 _ (Cube.mem_boundaryJar_cons_zero z)).trans
        (f.property.2 _ (Cube.mem_boundaryJar_cons_zero z)).symm
    · exact ((H.prop s).2 _ (Cube.mem_boundaryJar_cons_one z)).trans
        (f.property.2 _ (Cube.mem_boundaryJar_cons_one z)).symm
  · rintro ⟨G⟩
    have hend : ∀ (s t : I), t ∈ ({0, 1} : Set I) →
        ∀ z, (G.toHomotopy.toContinuousMap (s, t)).val z = (a : X) := by
      intro s t ht z
      have h : (G.toHomotopy.toContinuousMap (s, t) : RelGenLoop (n + 1) X A a) = toPath f t :=
        G.prop s t ht
      rw [h]
      rcases ht with rfl | rfl
      · exact f.property.2 _ (Cube.mem_boundaryJar_cons_zero z)
      · exact f.property.2 _ (Cube.mem_boundaryJar_cons_one z)
    refine ⟨{ toFun := uncurryFirst₂ ((valCM (n + 1) X A a).comp G.toHomotopy.toContinuousMap)
              continuous_toFun := map_continuous _
              map_zero_left := fun y ↦ ?_
              map_one_left := fun y ↦ ?_
              prop' := fun s ↦ uncurryFirst_mem
                (F := (valCM (n + 1) X A a).comp (G.toHomotopy.toContinuousMap.curry s))
                (fun t ↦ (G.toHomotopy.toContinuousMap (s, t)).property)
                (hend s 0 (Or.inl rfl)) (hend s 1 (Or.inr rfl)) }⟩
    · refine (congrArg (fun u : RelGenLoop (n + 1) X A a ↦ u.val (fun i ↦ y i.succ))
        (G.toHomotopy.apply_zero (y 0))).trans ?_
      exact congrArg _ (Fin.cons_self_tail y)
    · refine (congrArg (fun u : RelGenLoop (n + 1) X A a ↦ u.val (fun i ↦ y i.succ))
        (G.toHomotopy.apply_one (y 0))).trans ?_
      exact congrArg _ (Fin.cons_self_tail y)

end RelGenLoop

namespace Cube

lemma update_mem_boundary {m : ℕ} {j : Fin m} {y : I^ Fin m} (hy : y ∈ ∂I^m)
    (hyj : ¬ (y j = 0 ∨ y j = 1)) (s : I) : Function.update y j s ∈ ∂I^m := by
  obtain ⟨k, hk⟩ := hy
  have hkj : k ≠ j := fun hc ↦ hyj (hc ▸ hk)
  exact ⟨k, by rwa [Function.update_of_ne hkj]⟩

lemma update_mem_boundaryJar {n : ℕ} {j : Fin (n + 1)} (hj : j ≠ Fin.last n)
    {y : I^ Fin (n + 1)} (hy : y ∈ ⊔I^(n + 1)) (hyj : ¬ (y j = 0 ∨ y j = 1)) (s : I) :
    Function.update y j s ∈ ⊔I^(n + 1) := by
  obtain ⟨h1, h2⟩ := hy
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ := h1
    have hkj : k ≠ j := fun hc ↦ hyj (hc ▸ hk)
    exact ⟨k, by rwa [Function.update_of_ne hkj]⟩
  · intro hlast
    rw [Function.update_of_ne (Ne.symm hj)] at hlast
    obtain ⟨k, hklt, hk⟩ := h2 hlast
    have hkj : k ≠ j := fun hc ↦ hyj (hc ▸ hk)
    exact ⟨k, hklt, by rwa [Function.update_of_ne hkj]⟩

lemma continuous_update {m : ℕ} (j : Fin m) {v : (I^ Fin m) → I} (hv : Continuous v) :
    Continuous fun y : I^ Fin m ↦ Function.update y j (v y) := by
  refine continuous_pi fun k ↦ ?_
  rcases eq_or_ne k j with rfl | hk
  · simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne hk] using continuous_apply k

end Cube

namespace RelGenLoop

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}

/-- The first-half reparametrisation `t ↦ 2t` of the unit interval, clamped to `I`. -/
def firstHalf (t : I) : I := Set.projIcc (0 : ℝ) 1 zero_le_one (2 * t)

/-- The second-half reparametrisation `t ↦ 2t - 1` of the unit interval, clamped to `I`. -/
def secondHalf (t : I) : I := Set.projIcc (0 : ℝ) 1 zero_le_one (2 * t - 1)

@[fun_prop]
lemma continuous_firstHalf : Continuous firstHalf :=
  continuous_projIcc.comp' (by fun_prop)

@[fun_prop]
lemma continuous_secondHalf : Continuous secondHalf :=
  continuous_projIcc.comp' (by fun_prop)

@[simp]
lemma firstHalf_zero : firstHalf 0 = 0 := by
  ext; simp [firstHalf, Set.projIcc]

@[simp]
lemma secondHalf_one : secondHalf 1 = 1 := by
  ext; norm_num [secondHalf, Set.projIcc]

lemma firstHalf_of_half {t : I} (h : (t : ℝ) = 1 / 2) : firstHalf t = 1 := by
  ext; simp [firstHalf, Set.projIcc, h]

lemma secondHalf_of_half {t : I} (h : (t : ℝ) = 1 / 2) : secondHalf t = 0 := by
  ext; simp [secondHalf, Set.projIcc, h]

/-- Concatenation of two continuous maps on the `m`-cube in the coordinate direction `j`,
assuming they agree along the wall where the two halves are glued. -/
def transCM (j : Fin m) (f g : C(I^ Fin m, X))
    (h : ∀ y : I^ Fin m, f (Function.update y j 1) = g (Function.update y j 0)) :
    C(I^ Fin m, X) where
  toFun y :=
    if (y j : ℝ) ≤ 1 / 2 then f (Function.update y j (firstHalf (y j)))
      else g (Function.update y j (secondHalf (y j)))
  continuous_toFun := by
    refine Continuous.if_le (f.continuous.comp' (Cube.continuous_update j (by fun_prop)))
      (g.continuous.comp' (Cube.continuous_update j (by fun_prop))) (by fun_prop)
      continuous_const fun y hy ↦ ?_
    rw [firstHalf_of_half hy, secondHalf_of_half hy]
    exact h y

lemma transCM_apply (j : Fin m) (f g : C(I^ Fin m, X)) (h) (y : I^ Fin m) :
    transCM j f g h y =
      if (y j : ℝ) ≤ 1 / 2 then f (Function.update y j (firstHalf (y j)))
        else g (Function.update y j (secondHalf (y j))) := rfl

lemma transCM_apply_of_eq_zero (j : Fin m) (f g : C(I^ Fin m, X)) (h) {y : I^ Fin m}
    (hy : y j = 0) : transCM j f g h y = f y := by
  have hu : Function.update y j (firstHalf (y j)) = y := by
    rw [hy, firstHalf_zero, ← hy, Function.update_eq_self]
  rw [transCM_apply, if_pos (by rw [hy]; simp), hu]

lemma transCM_apply_of_eq_one (j : Fin m) (f g : C(I^ Fin m, X)) (h) {y : I^ Fin m}
    (hy : y j = 1) : transCM j f g h y = g y := by
  have hu : Function.update y j (secondHalf (y j)) = y := by
    rw [hy, secondHalf_one, ← hy, Function.update_eq_self]
  rw [transCM_apply, if_neg (by rw [hy]; norm_num), hu]

end RelGenLoop

namespace Cube

lemma update_symm_mem_boundary {m : ℕ} (j : Fin m) {y : I^ Fin m} (hy : y ∈ ∂I^m) :
    Function.update y j (σ (y j)) ∈ ∂I^m := by
  obtain ⟨k, hk⟩ := hy
  rcases eq_or_ne k j with rfl | hkj
  · refine ⟨k, ?_⟩
    rw [Function.update_self]
    rcases hk with h | h
    · right; rw [h]; simp
    · left; rw [h]; simp
  · exact ⟨k, by rwa [Function.update_of_ne hkj]⟩

lemma update_symm_mem_boundaryJar {n : ℕ} {j : Fin (n + 1)} (hj : j ≠ Fin.last n)
    {y : I^ Fin (n + 1)} (hy : y ∈ ⊔I^(n + 1)) :
    Function.update y j (σ (y j)) ∈ ⊔I^(n + 1) := by
  obtain ⟨h1, h2⟩ := hy
  have key : ∀ k : Fin (n + 1), (y k = 0 ∨ y k = 1) →
      (Function.update y j (σ (y j)) k = 0 ∨ Function.update y j (σ (y j)) k = 1) := by
    intro k hk
    rcases eq_or_ne k j with rfl | hkj
    · rw [Function.update_self]
      rcases hk with h | h
      · right; rw [h]; simp
      · left; rw [h]; simp
    · rwa [Function.update_of_ne hkj]
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ := h1; exact ⟨k, key k hk⟩
  · intro hlast
    rw [Function.update_of_ne (Ne.symm hj)] at hlast
    obtain ⟨k, hklt, hk⟩ := h2 hlast
    exact ⟨k, hklt, key k hk⟩

end Cube

namespace RelGenLoop

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}

lemma update_castSucc_one_mem_boundaryJar (i : Fin n) (y : I^ Fin (n + 1)) :
    Function.update y i.castSucc 1 ∈ ⊔I^(n + 1) :=
  Cube.mem_boundaryJar_of_lt_last _
    ⟨i.castSucc, Fin.castSucc_lt_last i, Or.inr (Function.update_self _ _ _)⟩

lemma update_castSucc_zero_mem_boundaryJar (i : Fin n) (y : I^ Fin (n + 1)) :
    Function.update y i.castSucc 0 ∈ ⊔I^(n + 1) :=
  Cube.mem_boundaryJar_of_exists_eq_zero _ ⟨i.castSucc, Function.update_self _ _ _⟩

lemma transAt_wall (i : Fin n) (f g : RelGenLoop (n + 1) X A a) (y : I^ Fin (n + 1)) :
    f.val (Function.update y i.castSucc 1) = g.val (Function.update y i.castSucc 0) := by
  rw [f.property.2 _ (update_castSucc_one_mem_boundaryJar i y),
    g.property.2 _ (update_castSucc_zero_mem_boundaryJar i y)]

/-- Concatenation of two relative generalized loops in the free coordinate direction
`i.castSucc`; the last coordinate is the distinguished "relative" direction and is never used. -/
def transAt (i : Fin n) (f g : RelGenLoop (n + 1) X A a) : RelGenLoop (n + 1) X A a :=
  ⟨transCM i.castSucc f.val g.val (transAt_wall i f g), by
    intro y hy
    by_cases hyj : y i.castSucc = 0 ∨ y i.castSucc = 1
    · rcases hyj with h | h
      · rw [transCM_apply_of_eq_zero _ _ _ _ h]; exact f.property.1 y hy
      · rw [transCM_apply_of_eq_one _ _ _ _ h]; exact g.property.1 y hy
    · rw [transCM_apply]
      split_ifs
      · exact f.property.1 _ (Cube.update_mem_boundary hy hyj _)
      · exact g.property.1 _ (Cube.update_mem_boundary hy hyj _), by
    intro y hy
    by_cases hyj : y i.castSucc = 0 ∨ y i.castSucc = 1
    · rcases hyj with h | h
      · rw [transCM_apply_of_eq_zero _ _ _ _ h]; exact f.property.2 y hy
      · rw [transCM_apply_of_eq_one _ _ _ _ h]; exact g.property.2 y hy
    · rw [transCM_apply]
      split_ifs
      · exact f.property.2 _ (Cube.update_mem_boundaryJar (Fin.castSucc_ne_last i) hy hyj _)
      · exact g.property.2 _ (Cube.update_mem_boundaryJar (Fin.castSucc_ne_last i) hy hyj _)⟩

lemma transAt_apply (i : Fin n) (f g : RelGenLoop (n + 1) X A a) (y : I^ Fin (n + 1)) :
    (transAt i f g).val y =
      if (y i.castSucc : ℝ) ≤ 1 / 2
        then f.val (Function.update y i.castSucc (firstHalf (y i.castSucc)))
        else g.val (Function.update y i.castSucc (secondHalf (y i.castSucc))) := rfl

/-- Reversal of a relative generalized loop in the free coordinate direction `i.castSucc`. -/
def symmAt (i : Fin n) (f : RelGenLoop (n + 1) X A a) : RelGenLoop (n + 1) X A a :=
  ⟨f.val.comp ⟨fun y ↦ Function.update y i.castSucc (σ (y i.castSucc)),
      Cube.continuous_update _ (by fun_prop)⟩,
    fun _ hy ↦ f.property.1 _ (Cube.update_symm_mem_boundary _ hy),
    fun _ hy ↦ f.property.2 _
      (Cube.update_symm_mem_boundaryJar (Fin.castSucc_ne_last i) hy)⟩

lemma symmAt_apply (i : Fin n) (f : RelGenLoop (n + 1) X A a) (y : I^ Fin (n + 1)) :
    (symmAt i f).val y = f.val (Function.update y i.castSucc (σ (y i.castSucc))) := rfl

/-- Concatenation in two different free directions satisfies the interchange law. -/
theorem transAt_distrib {i j : Fin n} (h : i ≠ j) (f₁ f₂ f₃ f₄ : RelGenLoop (n + 1) X A a) :
    transAt i (transAt j f₁ f₂) (transAt j f₃ f₄) =
      transAt j (transAt i f₁ f₃) (transAt i f₂ f₄) := by
  have hne : i.castSucc ≠ j.castSucc := fun hc ↦ h (Fin.castSucc_injective n hc)
  refine Subtype.ext (ContinuousMap.ext fun y ↦ ?_)
  simp only [transAt_apply, Function.update_of_ne hne, Function.update_of_ne hne.symm]
  split_ifs <;> rw [Function.update_comm hne]

end RelGenLoop

namespace Cube

/-- Precomposition with a permutation of the cube coordinates. -/
def reindexCM {m : ℕ} (τ : Equiv.Perm (Fin m)) : C(I^ Fin m, I^ Fin m) :=
  ⟨fun y i ↦ y (τ i), continuous_pi fun i ↦ continuous_apply (τ i)⟩

@[simp]
lemma reindexCM_apply {m : ℕ} (τ : Equiv.Perm (Fin m)) (y : I^ Fin m) (i : Fin m) :
    reindexCM τ y i = y (τ i) := rfl

lemma perm_mem_boundary {m : ℕ} (τ : Equiv.Perm (Fin m)) {y : I^ Fin m} (hy : y ∈ ∂I^m) :
    reindexCM τ y ∈ ∂I^m := by
  obtain ⟨k, hk⟩ := hy
  exact ⟨τ.symm k, by simpa using hk⟩

lemma perm_mem_boundaryJar {n : ℕ} (τ : Equiv.Perm (Fin (n + 1)))
    (hτ : τ (Fin.last n) = Fin.last n) {y : I^ Fin (n + 1)} (hy : y ∈ ⊔I^(n + 1)) :
    reindexCM τ y ∈ ⊔I^(n + 1) := by
  obtain ⟨h1, h2⟩ := hy
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ := h1
    exact ⟨τ.symm k, by simpa using hk⟩
  · intro hlast
    rw [reindexCM_apply, hτ] at hlast
    obtain ⟨k, hklt, hk⟩ := h2 hlast
    refine ⟨τ.symm k, ?_, by simpa using hk⟩
    rw [Fin.lt_last_iff_ne_last] at hklt ⊢
    intro hc
    exact hklt (by rw [← Equiv.apply_symm_apply τ k, hc, hτ])

lemma update_reindexCM {m : ℕ} (τ : Equiv.Perm (Fin m)) (y : I^ Fin m) (u : Fin m) (v : I) :
    Function.update (reindexCM τ y) u v = reindexCM τ (Function.update y (τ u) v) := by
  funext k
  rcases eq_or_ne k u with rfl | hk
  · simp
  · rw [Function.update_of_ne hk, reindexCM_apply, reindexCM_apply,
      Function.update_of_ne fun hc ↦ hk (τ.injective hc)]

end Cube

namespace RelGenLoop

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}

/-- Precomposition of a relative generalized loop with a permutation of the cube coordinates
that fixes the distinguished last coordinate. -/
def reindex (τ : Equiv.Perm (Fin (n + 1))) (hτ : τ (Fin.last n) = Fin.last n)
    (f : RelGenLoop (n + 1) X A a) : RelGenLoop (n + 1) X A a :=
  ⟨f.val.comp (Cube.reindexCM τ),
    fun _ hy ↦ f.property.1 _ (Cube.perm_mem_boundary τ hy),
    fun _ hy ↦ f.property.2 _ (Cube.perm_mem_boundaryJar τ hτ hy)⟩

@[simp]
lemma reindex_apply (τ : Equiv.Perm (Fin (n + 1))) (hτ : τ (Fin.last n) = Fin.last n)
    (f : RelGenLoop (n + 1) X A a) (y : I^ Fin (n + 1)) :
    (reindex τ hτ f).val y = f.val (Cube.reindexCM τ y) := rfl

@[simp]
lemma reindex_const (τ : Equiv.Perm (Fin (n + 1))) (hτ : τ (Fin.last n) = Fin.last n) :
    reindex τ hτ (const : RelGenLoop (n + 1) X A a) = const := rfl

lemma reindex_reindex (τ : Equiv.Perm (Fin (n + 1))) (hτ : τ (Fin.last n) = Fin.last n)
    (hinv : ∀ i, τ (τ i) = i) (f : RelGenLoop (n + 1) X A a) :
    reindex τ hτ (reindex τ hτ f) = f := by
  refine Subtype.ext (ContinuousMap.ext fun y ↦ ?_)
  show f.val (Cube.reindexCM τ (Cube.reindexCM τ y)) = f.val y
  exact congrArg _ (funext fun i ↦ by simp [hinv])

lemma Homotopic.reindex {τ : Equiv.Perm (Fin (n + 1))} {hτ : τ (Fin.last n) = Fin.last n}
    {f g : RelGenLoop (n + 1) X A a} (H : Homotopic f g) :
    Homotopic (RelGenLoop.reindex τ hτ f) (RelGenLoop.reindex τ hτ g) :=
  ⟨{ toFun := fun sy ↦ H.some (sy.1, Cube.reindexCM τ sy.2)
     continuous_toFun := (map_continuous H.some).comp' (by fun_prop)
     map_zero_left := fun y ↦ H.some.toHomotopy.apply_zero _
     map_one_left := fun y ↦ H.some.toHomotopy.apply_one _
     prop' := fun s ↦ ⟨fun _ hy ↦ (H.some.prop s).1 _ (Cube.perm_mem_boundary τ hy),
       fun _ hy ↦ (H.some.prop s).2 _ (Cube.perm_mem_boundaryJar τ hτ hy)⟩ }⟩

lemma reindex_transAt {τ : Equiv.Perm (Fin (n + 1))} {hτ : τ (Fin.last n) = Fin.last n}
    {i j : Fin n} (hij : τ i.castSucc = j.castSucc) (f g : RelGenLoop (n + 1) X A a) :
    reindex τ hτ (transAt i f g) = transAt j (reindex τ hτ f) (reindex τ hτ g) := by
  refine Subtype.ext (ContinuousMap.ext fun y ↦ ?_)
  simp only [reindex_apply, transAt_apply, Cube.reindexCM_apply, hij, Cube.update_reindexCM]

lemma reindex_symmAt {τ : Equiv.Perm (Fin (n + 1))} {hτ : τ (Fin.last n) = Fin.last n}
    {i j : Fin n} (hij : τ i.castSucc = j.castSucc) (f : RelGenLoop (n + 1) X A a) :
    reindex τ hτ (symmAt i f) = symmAt j (reindex τ hτ f) := by
  refine Subtype.ext (ContinuousMap.ext fun y ↦ ?_)
  simp only [reindex_apply, symmAt_apply, Cube.reindexCM_apply, hij, Cube.update_reindexCM]

end RelGenLoop

namespace RelGenLoop

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}

lemma cons_eq_update (s : I) (y : I^ Fin (n + 1)) :
    (Fin.cons s (fun i ↦ y i.succ) : I^ Fin (n + 1)) = Function.update y 0 s := by
  funext k
  refine Fin.cases ?_ ?_ k
  · simp
  · intro j; simp [Fin.succ_ne_zero]

lemma trans_toPath_apply (f g : RelGenLoop (n + 2) X A a) (t : I) :
    ((toPath f).trans (toPath g)) t =
      if (t : ℝ) ≤ 1 / 2 then toPath f (firstHalf t) else toPath g (secondHalf t) := rfl

lemma symm_toPath_apply (f : RelGenLoop (n + 2) X A a) (t : I) :
    (toPath f).symm t = toPath f (σ t) := rfl

/-- Concatenating the corresponding loops corresponds to concatenating in the first direction. -/
lemma ofPath_trans (f g : RelGenLoop (n + 2) X A a) :
    ofPath ((toPath f).trans (toPath g)) = transAt 0 f g := by
  refine Subtype.ext (ContinuousMap.ext fun y ↦ ?_)
  rw [transAt_apply, Fin.castSucc_zero, ofPath_apply, trans_toPath_apply]
  split_ifs
  · exact congrArg _ (cons_eq_update _ y)
  · exact congrArg _ (cons_eq_update _ y)

/-- Reversing the corresponding loop corresponds to reversing in the first direction. -/
lemma ofPath_symm (f : RelGenLoop (n + 2) X A a) :
    ofPath (toPath f).symm = symmAt 0 f := by
  refine Subtype.ext (ContinuousMap.ext fun y ↦ ?_)
  rw [symmAt_apply, Fin.castSucc_zero, ofPath_apply, symm_toPath_apply]
  exact congrArg _ (cons_eq_update _ y)

/-- The constant loop corresponds to the constant relative generalized loop. -/
lemma ofPath_refl :
    ofPath (Path.refl (const : RelGenLoop (n + 1) X A a)) = (const : RelGenLoop (n + 2) X A a) :=
  rfl

/-- The permutation of the cube coordinates swapping the first coordinate with the `k`-th one;
it fixes the distinguished last coordinate. -/
def swapPerm (k : Fin (n + 1)) : Equiv.Perm (Fin (n + 2)) := Equiv.swap 0 k.castSucc

lemma swapPerm_last (k : Fin (n + 1)) : swapPerm k (Fin.last (n + 1)) = Fin.last (n + 1) :=
  Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (Ne.symm (Fin.castSucc_ne_last k))

lemma swapPerm_involutive (k : Fin (n + 1)) (i : Fin (n + 2)) :
    swapPerm k (swapPerm k i) = i := Equiv.swap_apply_self _ _ _

lemma swapPerm_zero (k : Fin (n + 1)) : swapPerm k (0 : Fin (n + 1)).castSucc = k.castSucc := by
  rw [Fin.castSucc_zero]; exact Equiv.swap_apply_left _ _

/-- Reindexing along `swapPerm k`. -/
abbrev swap (k : Fin (n + 1)) (f : RelGenLoop (n + 2) X A a) : RelGenLoop (n + 2) X A a :=
  reindex (swapPerm k) (swapPerm_last k) f

lemma swap_swap (k : Fin (n + 1)) (f : RelGenLoop (n + 2) X A a) : swap k (swap k f) = f :=
  reindex_reindex _ _ (swapPerm_involutive k) f

lemma swap_transAt (k : Fin (n + 1)) (f g : RelGenLoop (n + 2) X A a) :
    swap k (transAt 0 f g) = transAt k (swap k f) (swap k g) :=
  reindex_transAt (swapPerm_zero k) f g

lemma swap_symmAt (k : Fin (n + 1)) (f : RelGenLoop (n + 2) X A a) :
    swap k (symmAt 0 f) = symmAt k (swap k f) :=
  reindex_symmAt (swapPerm_zero k) f

end RelGenLoop

namespace RelHomotopyGroup

open RelGenLoop

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}

/-- The relative homotopy group `π_rel (n + 2) X A a` is the fundamental group of the space of
`(n + 1)`-dimensional relative generalized loops, based at the constant loop. -/
def equivFundamentalGroup (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    π_rel (n + 2) X A a ≃ FundamentalGroup (RelGenLoop (n + 1) X A a) RelGenLoop.const :=
  Quotient.congr RelGenLoop.pathEquiv fun _ _ ↦ RelGenLoop.homotopic_iff_toPath _ _

/-- Reindexing by the swap of the first and the `k`-th cube coordinate, on relative homotopy
groups. -/
def swapEquiv (k : Fin (n + 1)) : π_rel (n + 2) X A a ≃ π_rel (n + 2) X A a where
  toFun := Quotient.map (RelGenLoop.swap k) fun _ _ H ↦ H.reindex
  invFun := Quotient.map (RelGenLoop.swap k) fun _ _ H ↦ H.reindex
  left_inv := by rintro ⟨f⟩; exact congrArg _ (RelGenLoop.swap_swap k f)
  right_inv := by rintro ⟨f⟩; exact congrArg _ (RelGenLoop.swap_swap k f)

/-- The group structure on `π_rel (n + 2) X A a` obtained by concatenating relative generalized
loops in the free coordinate direction `k`. -/
abbrev auxGroup (k : Fin (n + 1)) : Group (π_rel (n + 2) X A a) :=
  ((swapEquiv k).trans (equivFundamentalGroup n X A a)).group

lemma auxGroup_mul (k : Fin (n + 1)) (p q : RelGenLoop (n + 2) X A a) :
    (auxGroup k).mul ⟦p⟧ ⟦q⟧ = (⟦transAt k q p⟧ : π_rel (n + 2) X A a) := by
  have key : RelGenLoop.swap k
      (RelGenLoop.ofPath ((toPath (RelGenLoop.swap k q)).trans (toPath (RelGenLoop.swap k p))))
      = transAt k q p := by
    rw [RelGenLoop.ofPath_trans, RelGenLoop.swap_transAt, RelGenLoop.swap_swap,
      RelGenLoop.swap_swap]
  rw [← key]
  rfl

lemma auxGroup_one (k : Fin (n + 1)) :
    (auxGroup k).one = (⟦RelGenLoop.const⟧ : π_rel (n + 2) X A a) := rfl

lemma auxGroup_inv (k : Fin (n + 1)) (p : RelGenLoop (n + 2) X A a) :
    (auxGroup k).inv ⟦p⟧ = (⟦symmAt k p⟧ : π_rel (n + 2) X A a) := by
  have key : RelGenLoop.swap k (RelGenLoop.ofPath (toPath (RelGenLoop.swap k p)).symm)
      = symmAt k p := by
    rw [RelGenLoop.ofPath_symm, RelGenLoop.swap_symmAt, RelGenLoop.swap_swap]
  rw [← key]
  rfl

end RelHomotopyGroup

namespace RelHomotopyGroup

open RelGenLoop

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}

/-- The class of the constant relative loop is a two-sided unit for `auxGroup k`. -/
theorem isUnital_auxGroup (k : Fin (n + 1)) :
    EckmannHilton.IsUnital (auxGroup k).mul (⟦RelGenLoop.const⟧ : π_rel (n + 2) X A a) where
  left_id := (auxGroup k).one_mul
  right_id := (auxGroup k).mul_one

/-- The group structures obtained from two different free directions coincide;
this is the Eckmann–Hilton argument. -/
theorem auxGroup_indep (k l : Fin (n + 1)) :
    (auxGroup k : Group (π_rel (n + 2) X A a)) = auxGroup l := by
  by_cases h : k = l
  · rw [h]
  refine Group.ext (EckmannHilton.mul (isUnital_auxGroup k) (isUnital_auxGroup l) ?_)
  intro x y z w
  obtain ⟨α, rfl⟩ := Quotient.exists_rep x
  obtain ⟨β, rfl⟩ := Quotient.exists_rep y
  obtain ⟨γ, rfl⟩ := Quotient.exists_rep z
  obtain ⟨δ, rfl⟩ := Quotient.exists_rep w
  show (auxGroup k).mul ((auxGroup l).mul ⟦α⟧ ⟦β⟧) ((auxGroup l).mul ⟦γ⟧ ⟦δ⟧) =
    (auxGroup l).mul ((auxGroup k).mul ⟦α⟧ ⟦γ⟧) ((auxGroup k).mul ⟦β⟧ ⟦δ⟧)
  rw [auxGroup_mul l α β, auxGroup_mul l γ δ, auxGroup_mul k α γ, auxGroup_mul k β δ,
    auxGroup_mul k (transAt l β α) (transAt l δ γ),
    auxGroup_mul l (transAt k γ α) (transAt k δ β)]
  exact congrArg _ (RelGenLoop.transAt_distrib h δ γ β α)

/-- The class of a concatenation does not depend on the chosen free direction. -/
theorem transAt_indep {k : Fin (n + 1)} (l : Fin (n + 1)) (f g : RelGenLoop (n + 2) X A a) :
    (⟦transAt k f g⟧ : π_rel (n + 2) X A a) = ⟦transAt l f g⟧ := by
  rw [← auxGroup_mul k g f, ← auxGroup_mul l g f]
  let m := fun (G : Type _) (_ : Group G) ↦ ((· * ·) : G → G → G)
  exact congr_fun₂ (congr_arg (m (π_rel (n + 2) X A a)) (auxGroup_indep k l)) ⟦g⟧ ⟦f⟧

/-- The class of a reversal does not depend on the chosen free direction. -/
theorem symmAt_indep {k : Fin (n + 1)} (l : Fin (n + 1)) (f : RelGenLoop (n + 2) X A a) :
    (⟦symmAt k f⟧ : π_rel (n + 2) X A a) = ⟦symmAt l f⟧ := by
  rw [← auxGroup_inv k f, ← auxGroup_inv l f]
  let inv := fun (G : Type _) (_ : Group G) ↦ ((·⁻¹) : G → G)
  exact congr_fun (congr_arg (inv (π_rel (n + 2) X A a)) (auxGroup_indep k l)) ⟦f⟧

/-- The group structure on the relative homotopy group `π_rel (n + 2) X A a`. -/
instance group : Group (π_rel (n + 2) X A a) := auxGroup 0

/-- Characterization of the multiplicative identity. -/
theorem one_def : (1 : π_rel (n + 2) X A a) = ⟦RelGenLoop.const⟧ := rfl

/-- Characterization of multiplication: it is concatenation in any free direction. -/
theorem mul_spec {k : Fin (n + 1)} {p q : RelGenLoop (n + 2) X A a} :
    ((· * ·) : _ → _ → π_rel (n + 2) X A a) ⟦p⟧ ⟦q⟧ = ⟦transAt k q p⟧ := by
  rw [transAt_indep (k := k) 0 q p]
  exact auxGroup_mul 0 p q

/-- Multiplication of classes of relative generalized loops, in beta-reduced form. -/
theorem mul_mk (k : Fin (n + 1)) (p q : RelGenLoop (n + 2) X A a) :
    @HMul.hMul (π_rel (n + 2) X A a) (π_rel (n + 2) X A a) (π_rel (n + 2) X A a) _ ⟦p⟧ ⟦q⟧ =
      ⟦transAt k q p⟧ := mul_spec

/-- Characterization of the multiplicative inverse: it is reversal in any free direction. -/
theorem inv_spec {k : Fin (n + 1)} {p : RelGenLoop (n + 2) X A a} :
    ((⟦p⟧)⁻¹ : π_rel (n + 2) X A a) = ⟦symmAt k p⟧ := by
  rw [symmAt_indep (k := k) 0 p]
  exact auxGroup_inv 0 p

/-- Relative homotopy groups are abelian from degree `3` on. -/
instance commGroup : CommGroup (π_rel (n + 3) X A a) :=
  have hne : (1 : Fin (n + 2)) ≠ 0 := by simp
  @EckmannHilton.commGroup _ (auxGroup (1 : Fin (n + 2))).mul 1 (isUnital_auxGroup 1) group
    (by
      intro x y z w
      obtain ⟨α, rfl⟩ := Quotient.exists_rep x
      obtain ⟨β, rfl⟩ := Quotient.exists_rep y
      obtain ⟨γ, rfl⟩ := Quotient.exists_rep z
      obtain ⟨δ, rfl⟩ := Quotient.exists_rep w
      show (auxGroup (1 : Fin (n + 2))).mul ((auxGroup 0).mul ⟦α⟧ ⟦β⟧) ((auxGroup 0).mul ⟦γ⟧ ⟦δ⟧) =
        (auxGroup 0).mul ((auxGroup 1).mul ⟦α⟧ ⟦γ⟧) ((auxGroup 1).mul ⟦β⟧ ⟦δ⟧)
      rw [auxGroup_mul 0 α β, auxGroup_mul 0 γ δ, auxGroup_mul 1 α γ, auxGroup_mul 1 β δ,
        auxGroup_mul 1 (transAt 0 β α) (transAt 0 δ γ),
        auxGroup_mul 0 (transAt 1 γ α) (transAt 1 δ β)]
      exact congrArg _ (RelGenLoop.transAt_distrib hne δ γ β α))

end RelHomotopyGroup

namespace GenLoop

/-- The explicit formula for concatenation of absolute generalized loops. -/
lemma transAt_apply {N : Type*} [DecidableEq N] {X : Type*} [TopologicalSpace X] {x : X}
    (i : N) (f g : Ω^ N X x) (t : I^N) :
    GenLoop.transAt i f g t =
      if (t i : ℝ) ≤ 1 / 2
        then f (Function.update t i (Set.projIcc 0 1 zero_le_one (2 * t i)))
        else g (Function.update t i (Set.projIcc 0 1 zero_le_one (2 * t i - 1))) := rfl

end GenLoop

namespace HomotopyGroup

/-- Multiplication of classes of generalized loops, in beta-reduced form. -/
lemma mul_mk {N : Type*} [DecidableEq N] [Nonempty N] {X : Type*} [TopologicalSpace X] {x : X}
    (i : N) (p q : Ω^ N X x) :
    @HMul.hMul (HomotopyGroup N X x) (HomotopyGroup N X x) (HomotopyGroup N X x) _ ⟦p⟧ ⟦q⟧ =
      ⟦GenLoop.transAt i q p⟧ :=
  HomotopyGroup.mul_spec

end HomotopyGroup

namespace Cube

lemma inclToTop_apply_last {n : ℕ} (z : I^ Fin n) : (Cube.inclToTop z) (Fin.last n) = 1 :=
  Cube.splitAtLast_symm_apply_last 1 z

lemma inclToTop_apply_castSucc {n : ℕ} (z : I^ Fin n) (i : Fin n) :
    (Cube.inclToTop z) i.castSucc = z i := by
  have := Cube.splitAtLast_symm_apply_eq_of_neq_last 1 z i.castSucc (Fin.castSucc_ne_last i)
  simpa [Cube.inclToTop] using this

lemma update_inclToTop {n : ℕ} (z : I^ Fin n) (i : Fin n) (v : I) :
    Function.update (Cube.inclToTop z) i.castSucc v = Cube.inclToTop (Function.update z i v) := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · rw [Function.update_of_ne (Ne.symm (Fin.castSucc_ne_last i)), inclToTop_apply_last,
      inclToTop_apply_last]
  · intro j
    rw [inclToTop_apply_castSucc]
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne fun hc ↦ hj (Fin.castSucc_injective _ hc),
        inclToTop_apply_castSucc, Function.update_of_ne hj]

end Cube

namespace RelHomotopyGroup

open RelGenLoop

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}

/-- A generalized loop in `A`, viewed as a generalized loop in `X`; this is the map on
representatives underlying `RelHomotopyGroup.iStar`. -/
def iStarGen (f : Ω^ (Fin n) A a) : Ω^ (Fin n) X (a : X) :=
  ⟨⟨Subtype.val ∘ f.val, f.val.continuous_toFun.subtype_val⟩,
    by intro y hy; simp only [ContinuousMap.coe_mk, Function.comp_apply, f.property y hy]⟩

@[simp]
lemma iStarGen_apply (f : Ω^ (Fin n) A a) (y : I^ Fin n) : iStarGen f y = (f y : X) := rfl

lemma iStar_mk (f : Ω^ (Fin n) A a) :
    iStar n X A a ⟦f⟧ = (⟦iStarGen f⟧ : π_ n X (a : X)) := rfl

lemma iStarGen_transAt (i : Fin n) (f g : Ω^ (Fin n) A a) :
    iStarGen (GenLoop.transAt i f g) =
      GenLoop.transAt i (iStarGen (a := a) (X := X) f) (iStarGen g) := by
  refine GenLoop.ext _ _ fun y ↦ ?_
  rw [iStarGen_apply, GenLoop.transAt_apply, GenLoop.transAt_apply]
  split_ifs <;> rfl

/-- A generalized loop in `X` based at `a`, viewed as a relative generalized loop; this is the
map on representatives underlying `RelHomotopyGroup.jStar`. -/
def jStarGen (f : Ω^ (Fin n) X (a : X)) : RelGenLoop n X A a :=
  ⟨f, fun y hy ↦ Set.mem_of_eq_of_mem (f.property y hy) (Subtype.coe_prop a),
    fun y hy ↦ f.property y ((Cube.boundaryJar_subset_boundary n) hy)⟩

@[simp]
lemma jStarGen_apply (f : Ω^ (Fin n) X (a : X)) (y : I^ Fin n) :
    (jStarGen (A := A) f).val y = f y := rfl

lemma jStar_mk (f : Ω^ (Fin n) X (a : X)) :
    jStar n X A a ⟦f⟧ = (⟦jStarGen f⟧ : π_rel n X A a) := rfl

lemma jStarGen_transAt (i : Fin n) (f g : Ω^ (Fin (n + 1)) X (a : X)) :
    jStarGen (A := A) (GenLoop.transAt i.castSucc f g) =
      RelGenLoop.transAt i (jStarGen f) (jStarGen g) :=
  Subtype.ext <| ContinuousMap.ext fun y ↦ by
    rw [jStarGen_apply, GenLoop.transAt_apply, RelGenLoop.transAt_apply]
    split_ifs <;> rfl

/-- The restriction of a relative generalized loop to the top face of the cube; this is the map
on representatives underlying `RelHomotopyGroup.bd`. -/
def bdGen (f : RelGenLoop (n + 1) X A a) : Ω^ (Fin n) A a :=
  ⟨⟨fun y ↦ ⟨f.val (Cube.inclToTop y), f.property.left _ (Cube.inclToTop.mem_boundary y)⟩,
      Continuous.subtype_mk (f.val.continuous_toFun.comp Cube.inclToTop.continuous) _⟩,
    fun _ hy ↦ Subtype.ext <| f.property.right _ (Cube.inclToTop.mem_boundaryJar_of hy)⟩

@[simp]
lemma bdGen_apply (f : RelGenLoop (n + 1) X A a) (z : I^ Fin n) :
    ((bdGen f z : A) : X) = f.val (Cube.inclToTop z) := rfl

lemma bd_mk (f : RelGenLoop (n + 1) X A a) :
    bd n X A a ⟦f⟧ = (⟦bdGen f⟧ : π_ n A a) := rfl

lemma bdGen_transAt (i : Fin n) (f g : RelGenLoop (n + 1) X A a) :
    bdGen (RelGenLoop.transAt i f g) = GenLoop.transAt i (bdGen f) (bdGen g) := by
  refine GenLoop.ext _ _ fun z ↦ Subtype.ext ?_
  rw [bdGen_apply, RelGenLoop.transAt_apply, GenLoop.transAt_apply,
    Cube.inclToTop_apply_castSucc]
  split_ifs
  · rw [Cube.update_inclToTop]; rfl
  · rw [Cube.update_inclToTop]; rfl

end RelHomotopyGroup

namespace RelHomotopyGroup

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}

/-- The map `i_*` of the long exact sequence of a pair, as a group homomorphism. -/
def iStarHom (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    π_ (n + 1) A a →* π_ (n + 1) X (a : X) where
  toFun := iStar (n + 1) X A a
  map_one' := (iStar_isPointedMap (n + 1) X A a).map_default
  map_mul' x y := by
    obtain ⟨p, rfl⟩ := Quotient.exists_rep x
    obtain ⟨q, rfl⟩ := Quotient.exists_rep y
    rw [HomotopyGroup.mul_mk (0 : Fin (n + 1)) p q, iStar_mk, iStar_mk, iStar_mk,
      iStarGen_transAt, ← HomotopyGroup.mul_mk (0 : Fin (n + 1))]

@[simp]
lemma coe_iStarHom (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    ⇑(iStarHom n X A a) = iStar (n + 1) X A a := rfl

/-- The map `j_*` of the long exact sequence of a pair, as a group homomorphism. -/
def jStarHom (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    π_ (n + 2) X (a : X) →* π_rel (n + 2) X A a where
  toFun := jStar (n + 2) X A a
  map_one' := (jStar_isPointedMap (n + 2) X A a).map_default
  map_mul' x y := by
    obtain ⟨p, rfl⟩ := Quotient.exists_rep x
    obtain ⟨q, rfl⟩ := Quotient.exists_rep y
    rw [HomotopyGroup.mul_mk (0 : Fin (n + 1)).castSucc p q, jStar_mk, jStar_mk, jStar_mk,
      jStarGen_transAt, ← mul_mk (0 : Fin (n + 1))]

@[simp]
lemma coe_jStarHom (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    ⇑(jStarHom n X A a) = jStar (n + 2) X A a := rfl

/-- The boundary map `∂` of the long exact sequence of a pair, as a group homomorphism. -/
def bdHom (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    π_rel (n + 2) X A a →* π_ (n + 1) A a where
  toFun := bd (n + 1) X A a
  map_one' := (bd_isPointedMap (n + 1) X A a).map_default
  map_mul' x y := by
    obtain ⟨p, rfl⟩ := Quotient.exists_rep x
    obtain ⟨q, rfl⟩ := Quotient.exists_rep y
    rw [mul_mk (0 : Fin (n + 1)) p q, bd_mk, bd_mk, bd_mk, bdGen_transAt,
      ← HomotopyGroup.mul_mk (0 : Fin (n + 1))]

@[simp]
lemma coe_bdHom (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    ⇑(bdHom n X A a) = bd (n + 1) X A a := rfl

/-- The library's `ExactSeq.IsExactAt` for pointed sets upgrades to Mathlib's
`Function.MulExact` as soon as the distinguished point is the group unit. -/
lemma mulExact_of_isExactAt {G H K : Type*} [Inhabited K] [One K] (hK : (default : K) = 1)
    {f : G → H} {g : H → K} (h : ExactSeq.IsExactAt f g) : Function.MulExact f g := by
  intro y
  rw [← hK, ← Set.mem_singleton_iff, ← Set.mem_preimage, h]

/-- Exactness of the long exact sequence of a pair at `π_ (n + 2) X a`. -/
theorem mulExact_iStarHom_jStarHom (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    Function.MulExact (iStarHom (n + 1) X A a) (jStarHom n X A a) :=
  mulExact_of_isExactAt rfl (isExactAt_iStar_jStar (n + 1) X A a)

/-- Exactness of the long exact sequence of a pair at `π_rel (n + 2) X A a`. -/
theorem mulExact_jStarHom_bdHom (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    Function.MulExact (jStarHom n X A a) (bdHom n X A a) :=
  mulExact_of_isExactAt rfl (isExactAt_jStar_bd (n + 1) X A a)

/-- Exactness of the long exact sequence of a pair at `π_ (n + 1) A a`. -/
theorem mulExact_bdHom_iStarHom (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    Function.MulExact (bdHom n X A a) (iStarHom n X A a) :=
  mulExact_of_isExactAt rfl (isExactAt_bd_iStar (n + 1) X A a)

end RelHomotopyGroup
