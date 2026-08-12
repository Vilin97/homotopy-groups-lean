/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SimplicialRelation

/-!
# Moving simplicial multiplication relations between face indices

The homotopy-addition induction needs to move a relation supported on three consecutive faces
through the ordered list of faces.  This file develops the required index-shift operation for
Mathlib's `PtSimplex.MulStruct` at the pinned dependency revision.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace SSet.PtSimplex

universe u

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}

/-! ### Reversing pointed simplices -/

lemma reverse_opObjEquiv_yonedaEquiv_const {m : SimplexCategory}
    (y : X.op _⦋0⦌) :
    SSet.opObjEquiv (n := op m) (SSet.yonedaEquiv (SSet.const y)) =
      SSet.yonedaEquiv (SSet.const (SSet.opObjEquiv y)) :=
  rfl

lemma reverse_opObjEquiv_symm_yonedaEquiv_const {m : SimplexCategory}
    (y : X _⦋0⦌) :
    (SSet.opObjEquiv (n := op m)).symm (SSet.yonedaEquiv (SSet.const y)) =
      SSet.yonedaEquiv (SSet.const (SSet.opObjEquiv.symm y)) :=
  rfl

lemma reverse_δ_opObjEquiv (Y : SSet.{u}) {m : ℕ} (i : Fin (m + 2))
    (y : Y.op _⦋m + 1⦌) :
    Y.δ i (SSet.opObjEquiv y) = SSet.opObjEquiv (Y.op.δ i.rev y) := by
  simp [SSet.op_δ]

/-- Reverse all indices in a simplex map, without requiring its boundary to be constant. -/
def reverseSimplexMap {m : ℕ} (f : Δ[m] ⟶ X) : Δ[m] ⟶ X.op :=
  SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (SSet.yonedaEquiv f))

@[simp]
lemma yonedaEquiv_reverseSimplexMap {m : ℕ} (f : Δ[m] ⟶ X) :
    SSet.yonedaEquiv (reverseSimplexMap f) =
      SSet.opObjEquiv.symm (SSet.yonedaEquiv f) :=
  SSet.yonedaEquiv.apply_symm_apply _

/-- Reversal sends face `i` to face `i.rev`. -/
@[reassoc]
lemma δ_reverseSimplexMap {m : ℕ} (f : Δ[m + 1] ⟶ X) (i : Fin (m + 2)) :
    SSet.stdSimplex.δ i ≫ reverseSimplexMap f =
      reverseSimplexMap (SSet.stdSimplex.δ i.rev ≫ f) := by
  apply SSet.yonedaEquiv.injective
  calc
    SSet.yonedaEquiv (SSet.stdSimplex.δ i ≫ reverseSimplexMap f) =
        X.op.δ i (SSet.yonedaEquiv (reverseSimplexMap f)) := by
      symm
      simpa [CosimplicialObject.δ, SimplicialObject.δ] using
        (SSet.yonedaEquiv_naturality (SimplexCategory.δ i) (reverseSimplexMap f))
    _ = SSet.opObjEquiv.symm (X.δ i.rev (SSet.yonedaEquiv f)) := by
      rw [yonedaEquiv_reverseSimplexMap, SSet.op_δ, Equiv.apply_symm_apply]
    _ = SSet.opObjEquiv.symm
        (SSet.yonedaEquiv (SSet.stdSimplex.δ i.rev ≫ f)) := by
      congr 1
      simpa [CosimplicialObject.δ, SimplicialObject.δ] using
        (SSet.yonedaEquiv_naturality (SimplexCategory.δ i.rev) f)
    _ = SSet.yonedaEquiv
        (reverseSimplexMap (SSet.stdSimplex.δ i.rev ≫ f)) := by
      rw [yonedaEquiv_reverseSimplexMap]

@[simp]
lemma reverseSimplexMap_const {m : ℕ} (y : X _⦋0⦌) :
    reverseSimplexMap (SSet.const y : Δ[m] ⟶ X) =
      SSet.const (SSet.opObjEquiv.symm y) := by
  apply SSet.yonedaEquiv.injective
  rw [yonedaEquiv_reverseSimplexMap]
  exact reverse_opObjEquiv_symm_yonedaEquiv_const y

/-- Undo index reversal on a simplex map. -/
def unreverseSimplexMap {m : ℕ} (f : Δ[m] ⟶ X.op) : Δ[m] ⟶ X :=
  SSet.yonedaEquiv.symm (SSet.opObjEquiv (SSet.yonedaEquiv f))

@[simp]
lemma yonedaEquiv_unreverseSimplexMap {m : ℕ} (f : Δ[m] ⟶ X.op) :
    SSet.yonedaEquiv (unreverseSimplexMap f) =
      SSet.opObjEquiv (SSet.yonedaEquiv f) :=
  SSet.yonedaEquiv.apply_symm_apply _

/-- Undoing reversal also sends face `i` to face `i.rev`. -/
@[reassoc]
lemma δ_unreverseSimplexMap {m : ℕ} (f : Δ[m + 1] ⟶ X.op) (i : Fin (m + 2)) :
    SSet.stdSimplex.δ i ≫ unreverseSimplexMap f =
      unreverseSimplexMap (SSet.stdSimplex.δ i.rev ≫ f) := by
  apply SSet.yonedaEquiv.injective
  calc
    SSet.yonedaEquiv (SSet.stdSimplex.δ i ≫ unreverseSimplexMap f) =
        X.δ i (SSet.yonedaEquiv (unreverseSimplexMap f)) := by
      symm
      simpa [CosimplicialObject.δ, SimplicialObject.δ] using
        (SSet.yonedaEquiv_naturality (SimplexCategory.δ i) (unreverseSimplexMap f))
    _ = SSet.opObjEquiv (X.op.δ i.rev (SSet.yonedaEquiv f)) := by
      rw [yonedaEquiv_unreverseSimplexMap, reverse_δ_opObjEquiv]
    _ = SSet.opObjEquiv
        (SSet.yonedaEquiv (SSet.stdSimplex.δ i.rev ≫ f)) := by
      congr 1
      simpa [CosimplicialObject.δ, SimplicialObject.δ] using
        (SSet.yonedaEquiv_naturality (SimplexCategory.δ i.rev) f)
    _ = SSet.yonedaEquiv
        (unreverseSimplexMap (SSet.stdSimplex.δ i.rev ≫ f)) := by
      rw [yonedaEquiv_unreverseSimplexMap]

@[simp]
lemma unreverseSimplexMap_const {m : ℕ} (y : X.op _⦋0⦌) :
    unreverseSimplexMap (SSet.const y : Δ[m] ⟶ X.op) =
      SSet.const (SSet.opObjEquiv y) := by
  apply SSet.yonedaEquiv.injective
  rw [yonedaEquiv_unreverseSimplexMap]
  exact reverse_opObjEquiv_yonedaEquiv_const y

@[simp]
lemma reverseSimplexMap_unreverseSimplexMap {m : ℕ} (f : Δ[m] ⟶ X.op) :
    reverseSimplexMap (unreverseSimplexMap f) = f := by
  apply SSet.yonedaEquiv.injective
  simp

@[simp]
lemma unreverseSimplexMap_reverseSimplexMap {m : ℕ} (f : Δ[m] ⟶ X) :
    unreverseSimplexMap (reverseSimplexMap f) = f := by
  apply SSet.yonedaEquiv.injective
  simp

/-! ### Reversing horns -/

/-- Reverse every face index in a horn with values in the opposite simplicial set. -/
def unreverseHornFace {r : ℕ} {i : Fin (r + 2)}
    (F : ∀ (j : Fin (r + 2)) (_hj : j ≠ i), Δ[r] ⟶ X.op)
    (j : Fin (r + 2)) (hj : j ≠ i.rev) : Δ[r] ⟶ X :=
  unreverseSimplexMap (F j.rev (Fin.rev_ne_iff.mpr hj))

/-- Reversing all face indices preserves horn compatibility. -/
theorem unreverseHornFace_compatible {r : ℕ} {i : Fin (r + 2)}
    {F : ∀ (j : Fin (r + 2)) (_hj : j ≠ i), Δ[r] ⟶ X.op}
    (hF : SSet.horn.IsCompatible F) :
    SSet.horn.IsCompatible (unreverseHornFace F) := by
  obtain _ | r := r
  · simp
  · rw [SSet.horn.isCompatible_iff]
    intro j k hj hk hjk
    simp only [unreverseHornFace]
    rw [δ_unreverseSimplexMap, δ_unreverseSimplexMap]
    apply congrArg unreverseSimplexMap
    have hrev : k.rev < j.rev := by grind
    have hkindex :
        (k.pred (Fin.ne_zero_of_lt hjk)).rev =
          k.rev.castPred (Fin.ne_last_of_lt hrev) := by
      ext
      simp
      omega
    have hjindex :
        (j.castPred (Fin.ne_last_of_lt hjk)).rev =
          j.rev.pred (Fin.ne_zero_of_lt hrev) := by
      ext
      simp
      omega
    rw [hkindex, hjindex]
    exact (hF.δ_pred_comp k.rev j.rev (hjk := hrev)).symm

/-- The opposite of a Kan complex is Kan. -/
theorem kanComplex_op [KanComplex X] : KanComplex X.op := by
  apply SSet.KanComplex.iff.mpr
  intro r i F hF
  let F' := unreverseHornFace F
  have hF' : SSet.horn.IsCompatible F' := unreverseHornFace_compatible hF
  obtain ⟨φ, hφ⟩ := hF'.exists_lift_of_kanComplex
  refine ⟨reverseSimplexMap φ, ?_⟩
  intro j hj
  rw [δ_reverseSimplexMap, hφ j.rev (by simpa using hj)]
  simp [F', unreverseHornFace]

/-- Pointed simplices of the opposite simplicial set correspond to pointed simplices of the
original simplicial set by reversing all simplex indices. -/
def reverseEquiv : X.op.PtSimplex n (SSet.opObjEquiv.symm x) ≃ X.PtSimplex n x where
  toFun f :=
    { map := SSet.yonedaEquiv.symm (SSet.opObjEquiv (SSet.yonedaEquiv f.map))
      comm := by
        obtain _ | n := n
        · ext
        · apply SSet.boundary.hom_ext
          intro i
          rw [← Category.assoc, SSet.boundary.ι_ι, CosimplicialObject.δ,
            SSet.yonedaEquiv_symm_naturality_left]
          apply SSet.yonedaEquiv.injective
          rw [SSet.yonedaEquiv.apply_symm_apply]
          have hf' :
              X.op.δ i.rev (SSet.yonedaEquiv f.map) =
                SSet.yonedaEquiv
                  (SSet.const (SSet.opObjEquiv.symm x) : Δ[n] ⟶ X.op) := by
            calc
              _ = SSet.yonedaEquiv (SSet.stdSimplex.δ i.rev ≫ f.map) := by
                simpa [CosimplicialObject.δ, SimplicialObject.δ] using
                  (SSet.yonedaEquiv_naturality (SimplexCategory.δ i.rev) f.map)
              _ = _ := congrArg SSet.yonedaEquiv (f.δ_map i.rev)
          have hf'' := congrArg SSet.opObjEquiv hf'
          change X.δ i (SSet.opObjEquiv (SSet.yonedaEquiv f.map)) =
            SSet.yonedaEquiv (SSet.const x)
          rw [reverse_δ_opObjEquiv]
          simpa [reverse_opObjEquiv_yonedaEquiv_const] using hf'' }
  invFun g :=
    { map := SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (SSet.yonedaEquiv g.map))
      comm := by
        obtain _ | n := n
        · ext
        · apply SSet.boundary.hom_ext
          intro i
          rw [← Category.assoc, SSet.boundary.ι_ι, CosimplicialObject.δ,
            SSet.yonedaEquiv_symm_naturality_left]
          apply SSet.yonedaEquiv.injective
          rw [SSet.yonedaEquiv.apply_symm_apply]
          have hg' :
              X.δ i.rev (SSet.yonedaEquiv g.map) =
                SSet.yonedaEquiv (SSet.const x : Δ[n] ⟶ X) := by
            calc
              _ = SSet.yonedaEquiv (SSet.stdSimplex.δ i.rev ≫ g.map) := by
                simpa [CosimplicialObject.δ, SimplicialObject.δ] using
                  (SSet.yonedaEquiv_naturality (SimplexCategory.δ i.rev) g.map)
              _ = _ := congrArg SSet.yonedaEquiv (g.δ_map i.rev)
          have hg'' := congrArg SSet.opObjEquiv.symm hg'
          change X.op.δ i (SSet.opObjEquiv.symm (SSet.yonedaEquiv g.map)) =
            SSet.yonedaEquiv (SSet.const (SSet.opObjEquiv.symm x))
          rw [SSet.op_δ]
          simpa [reverse_opObjEquiv_symm_yonedaEquiv_const] using hg'' }
  left_inv f := by
    ext
    simp
  right_inv g := by
    ext
    simp

/-- Reverse a pointed simplex into the opposite simplicial set. -/
abbrev reverse (f : X.PtSimplex n x) :
    X.op.PtSimplex n (SSet.opObjEquiv.symm x) :=
  reverseEquiv.symm f

/-- Undo reversal of a pointed simplex. -/
abbrev unreverse (f : X.op.PtSimplex n (SSet.opObjEquiv.symm x)) : X.PtSimplex n x :=
  reverseEquiv f

@[simp]
lemma unreverse_reverse (f : X.PtSimplex n x) : f.reverse.unreverse = f :=
  reverseEquiv.apply_symm_apply f

@[simp]
lemma reverse_unreverse
    (f : X.op.PtSimplex n (SSet.opObjEquiv.symm x)) : f.unreverse.reverse = f :=
  reverseEquiv.symm_apply_apply f

@[simp]
lemma reverse_map (f : X.PtSimplex n x) :
    f.reverse.map = reverseSimplexMap f.map :=
  rfl

@[simp]
lemma unreverse_map (f : X.op.PtSimplex n (SSet.opObjEquiv.symm x)) :
    f.unreverse.map =
      SSet.yonedaEquiv.symm (SSet.opObjEquiv (SSet.yonedaEquiv f.map)) :=
  rfl

/-! ### Reversing multiplication structures -/

namespace MulStruct

/-! #### Moving a three-face relation one index to the left -/

/-- All faces of a degenerate pointed simplex are constant except the two faces which recover
the original simplex. -/
theorem δ_σ_ptSimplex {r : ℕ} (p : X.PtSimplex (r + 1) x)
    (i : Fin (r + 2)) (j : Fin (r + 3)) :
    SSet.stdSimplex.δ j ≫ SSet.stdSimplex.σ i ≫ p.map =
      if j = i.castSucc then p.map else if j = i.succ then p.map else SSet.const x := by
  split
  next hj =>
    subst j
    rw [SSet.stdSimplex.δ_comp_σ_self_assoc]
  next hj0 =>
    split
    next hj =>
      subst j
      rw [SSet.stdSimplex.δ_comp_σ_succ_assoc]
    next hj1 =>
      rcases lt_or_gt_of_ne (show j ≠ i.castSucc from hj0) with hj | hj
      · have hi : i ≠ 0 := by
          intro hi
          subst i
          simp at hj
        obtain ⟨i, rfl⟩ := i.eq_succ_of_ne_zero hi
        obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (by grind)
        rw [SSet.stdSimplex.δ_comp_σ_of_le_assoc (by grind), p.δ_map, SSet.comp_const]
      · have hj' : i.succ < j := by grind
        obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (by grind)
        have hjzero : j ≠ 0 := by
          intro hjzero
          subst j
          simp at hj'
        obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero hjzero
        rw [SSet.stdSimplex.δ_comp_σ_of_gt_assoc (by grind), p.δ_map, SSet.comp_const]

/-- The complete face table of a multiplication structure. -/
theorem δ_mulStruct_map {r : ℕ} {f g fg : X.PtSimplex r x}
    {i : Fin r} (h : MulStruct f g fg i) (j : Fin (r + 2)) :
    SSet.stdSimplex.δ j ≫ h.map =
      if j = i.castSucc.castSucc then g.map
      else if j = i.castSucc.succ then fg.map
      else if j = i.succ.succ then f.map
      else SSet.const x := by
  split
  next hj =>
    subst j
    exact h.δ_castSucc_castSucc_map
  next hj0 =>
    split
    next hj =>
      subst j
      exact h.δ_succ_castSucc_map
    next hj1 =>
      split
      next hj =>
        subst j
        exact h.δ_succ_succ_map
      next hj2 =>
        rcases lt_or_gt_of_ne (show j ≠ i.castSucc.castSucc from hj0) with hj | hj
        · exact h.δ_map_of_lt j hj
        · exact h.δ_map_of_gt j (by grind)

/-- The horn used to move a multiplication structure at `q.succ` to `q.castSucc`.  Its four
nonconstant prescribed faces are the degeneracies occurring in the classical homotopy-addition
index-shift table; the face at `q + 3` is omitted. -/
def moveLeftHornFace {m : ℕ}
    {f g fg : X.PtSimplex (m + 1) x}
    (q : Fin m) (h : MulStruct f g fg q.succ)
    (j : Fin (m + 4)) (_hj : j ≠ q.succ.succ.succ.castSucc) : Δ[m + 2] ⟶ X :=
  if j = q.castSucc.castSucc.castSucc.castSucc then
    SSet.stdSimplex.σ q.succ.succ ≫ f.map
  else if j = q.succ.castSucc.castSucc.castSucc then h.map
  else if j = q.succ.succ.castSucc.castSucc then
    SSet.stdSimplex.σ q.succ.castSucc ≫ g.map
  else if j = q.succ.succ.succ.succ then
    SSet.stdSimplex.σ q.castSucc.castSucc ≫ f.map
  else SSet.const x

/-- The prescribed faces of the index-shift horn agree on all intersections. -/
theorem moveLeftHornFace_compatible {m : ℕ}
    {f g fg : X.PtSimplex (m + 1) x}
    (q : Fin m) (h : MulStruct f g fg q.succ) :
    SSet.horn.IsCompatible (moveLeftHornFace q h) := by
  rw [SSet.horn.isCompatible_iff]
  intro j k hj hk hjk
  simp only [moveLeftHornFace]
  split_ifs with hj0 hj1 hj2 hj4 hk0 hk1 hk2 hk4
  all_goals try grind
  all_goals subst_vars
  all_goals simp_all [δ_σ_ptSimplex, δ_mulStruct_map,
    Fin.castPred_eq_iff_eq_castSucc]
  all_goals grind

variable [KanComplex X]

/-- The Kan filler of the horn which shifts a multiplication relation one place left. -/
def moveLeftFiller {m : ℕ}
    {f g fg : X.PtSimplex (m + 1) x}
    (q : Fin m) (h : MulStruct f g fg q.succ) : Δ[m + 3] ⟶ X :=
  (moveLeftHornFace_compatible q h).liftOfKanComplex

/-- Every prescribed face of the left-shift horn is recovered by its Kan filler. -/
@[reassoc]
theorem δ_moveLeftFiller {m : ℕ}
    {f g fg : X.PtSimplex (m + 1) x}
    (q : Fin m) (h : MulStruct f g fg q.succ)
    (j : Fin (m + 4)) (hj : j ≠ q.succ.succ.succ.castSucc) :
    SSet.stdSimplex.δ j ≫ moveLeftFiller q h = moveLeftHornFace q h j hj :=
  (moveLeftHornFace_compatible q h).δ_liftOfKanComplex j hj

@[simp]
lemma pred_moveLeftMissing {m : ℕ} (q : Fin m)
    (hq : q.succ.succ.succ.castSucc ≠ 0) :
    q.succ.succ.succ.castSucc.pred hq = q.castSucc.succ.succ := by
  ext
  simp

/-- Move a multiplication relation one face index to the left.  The two outer factors are
interchanged, while the middle (product) face is unchanged. -/
def moveLeft {m : ℕ}
    {f g fg : X.PtSimplex (m + 1) x}
    (q : Fin m) (h : MulStruct f g fg q.succ) :
    MulStruct g f fg q.castSucc where
  map :=
    SSet.stdSimplex.δ q.succ.succ.succ.castSucc ≫ moveLeftFiller q h
  δ_castSucc_castSucc_map := by
    have hprescribed :
        q.castSucc.castSucc.castSucc.castSucc ≠
          q.succ.succ.succ.castSucc := by grind
    rw [← Category.assoc, SSet.stdSimplex.δ_comp_δ' (by grind), Category.assoc,
      δ_moveLeftFiller q h _ hprescribed]
    simp [moveLeftHornFace, δ_σ_ptSimplex]
  δ_succ_castSucc_map := by
    have hprescribed :
        q.castSucc.castSucc.succ.castSucc ≠
          q.succ.succ.succ.castSucc := by grind
    rw [← Category.assoc, SSet.stdSimplex.δ_comp_δ' (by grind), Category.assoc,
      δ_moveLeftFiller q h _ hprescribed]
    simp [moveLeftHornFace, δ_mulStruct_map, Fin.ext_iff]
  δ_succ_succ_map := by
    have hprescribed :
        q.castSucc.succ.succ.castSucc ≠
          q.succ.succ.succ.castSucc := by grind
    rw [← Category.assoc, SSet.stdSimplex.δ_comp_δ' (by grind), Category.assoc,
      δ_moveLeftFiller q h _ hprescribed]
    simp [moveLeftHornFace, Fin.ext_iff]
    split_ifs with hindex
    · omega
    · rw [SSet.stdSimplex.δ_comp_σ_succ_assoc]
  δ_map_of_lt j hj := by
    have hprescribed : j.castSucc ≠ q.succ.succ.succ.castSucc := by grind
    rw [← Category.assoc, SSet.stdSimplex.δ_comp_δ' (by grind), Category.assoc,
      δ_moveLeftFiller q h _ hprescribed]
    have hjfirst :
        j.castSucc < q.castSucc.castSucc.castSucc.castSucc :=
      Fin.castSucc_lt_castSucc_iff.mpr hj
    have hfirst :
        j.castSucc ≠ q.castSucc.castSucc.castSucc.castSucc := ne_of_lt hjfirst
    have hsecond :
        j.castSucc ≠ q.succ.castSucc.castSucc.castSucc := by grind
    have hthird :
        j.castSucc ≠ q.succ.succ.castSucc.castSucc := by grind
    have hfourth : j.castSucc ≠ q.succ.succ.succ.succ := by grind
    simp only [moveLeftHornFace, if_neg hfirst, if_neg hsecond, if_neg hthird,
      if_neg hfourth, SSet.comp_const]
  δ_map_of_gt j hj := by
    have hprescribed : j.succ ≠ q.succ.succ.succ.castSucc := by grind
    rw [← Category.assoc, ← SSet.stdSimplex.δ_comp_δ (by grind), Category.assoc,
      δ_moveLeftFiller q h _ hprescribed]
    have hfirst :
        j.succ ≠ q.castSucc.castSucc.castSucc.castSucc := by grind
    have hsecond :
        j.succ ≠ q.succ.castSucc.castSucc.castSucc := by grind
    have hthird :
        j.succ ≠ q.succ.succ.castSucc.castSucc := by grind
    simp only [moveLeftHornFace, if_neg hfirst, if_neg hsecond, if_neg hthird]
    split_ifs
    · have hδ0 :
          q.succ.succ.succ ≠ q.castSucc.castSucc.castSucc := by grind
      have hδ1 :
          q.succ.succ.succ ≠ q.castSucc.castSucc.succ := by grind
      simp [δ_σ_ptSimplex, hδ0, hδ1]
    · simp

/-- Reverse all face indices in a multiplication structure.  Reversal swaps the two outer
factors and sends the multiplication index `i` to `i.rev`. -/
def reverse {f g fg : X.PtSimplex n x} {i : Fin n}
    (h : MulStruct f g fg i) {j : Fin n} (hij : i.rev = j := by grind) :
    MulStruct g.reverse f.reverse fg.reverse j where
  map := reverseSimplexMap h.map
  δ_castSucc_castSucc_map := by
    rw [δ_reverseSimplexMap]
    have hk : j.castSucc.castSucc.rev = i.succ.succ := by
      subst j
      simp [Fin.rev_castSucc]
    rw [hk, h.δ_succ_succ_map, reverse_map]
  δ_succ_castSucc_map := by
    rw [δ_reverseSimplexMap]
    have hk : j.castSucc.succ.rev = i.castSucc.succ := by
      subst j
      simp [Fin.rev_castSucc, Fin.rev_succ, Fin.castSucc_succ]
    rw [hk, h.δ_succ_castSucc_map, reverse_map]
  δ_succ_succ_map := by
    rw [δ_reverseSimplexMap]
    have hk : j.succ.succ.rev = i.castSucc.castSucc := by
      subst j
      simp [Fin.rev_succ]
    rw [hk, h.δ_castSucc_castSucc_map, reverse_map]
  δ_map_of_lt k hk := by
    rw [δ_reverseSimplexMap, h.δ_map_of_gt k.rev (by grind), reverseSimplexMap_const]
  δ_map_of_gt k hk := by
    rw [δ_reverseSimplexMap, h.δ_map_of_lt k.rev (by grind), reverseSimplexMap_const]

/-- Undo reversal of all face indices in a multiplication structure. -/
def unreverse
    {f g fg : X.op.PtSimplex n (SSet.opObjEquiv.symm x)} {i : Fin n}
    (h : MulStruct f g fg i) {j : Fin n} (hij : i.rev = j := by grind) :
    MulStruct g.unreverse f.unreverse fg.unreverse j where
  map := unreverseSimplexMap h.map
  δ_castSucc_castSucc_map := by
    rw [δ_unreverseSimplexMap]
    have hk : j.castSucc.castSucc.rev = i.succ.succ := by
      subst j
      simp [Fin.rev_castSucc]
    rw [hk, h.δ_succ_succ_map, unreverse_map]
    rfl
  δ_succ_castSucc_map := by
    rw [δ_unreverseSimplexMap]
    have hk : j.castSucc.succ.rev = i.castSucc.succ := by
      subst j
      simp [Fin.rev_castSucc, Fin.rev_succ, Fin.castSucc_succ]
    rw [hk, h.δ_succ_castSucc_map, unreverse_map]
    rfl
  δ_succ_succ_map := by
    rw [δ_unreverseSimplexMap]
    have hk : j.succ.succ.rev = i.castSucc.castSucc := by
      subst j
      simp [Fin.rev_succ]
    rw [hk, h.δ_castSucc_castSucc_map, unreverse_map]
    rfl
  δ_map_of_lt k hk := by
    rw [δ_unreverseSimplexMap, h.δ_map_of_gt k.rev (by grind),
      unreverseSimplexMap_const]
    rw [Equiv.apply_symm_apply]
  δ_map_of_gt k hk := by
    rw [δ_unreverseSimplexMap, h.δ_map_of_lt k.rev (by grind),
      unreverseSimplexMap_const]
    rw [Equiv.apply_symm_apply]

/-- Move a multiplication relation one face index to the right.  This is obtained by reversing
all simplex indices, applying `moveLeft`, and reversing back. -/
def moveRight {m : ℕ}
    {f g fg : X.PtSimplex (m + 1) x}
    (q : Fin m) (h : MulStruct f g fg q.castSucc) :
    MulStruct g f fg q.succ := by
  letI : KanComplex X.op := kanComplex_op
  let hr : MulStruct g.reverse f.reverse fg.reverse q.rev.succ :=
    h.reverse (j := q.rev.succ) (by simp [Fin.rev_castSucc])
  let hl : MulStruct f.reverse g.reverse fg.reverse q.rev.castSucc :=
    moveLeft q.rev hr
  simpa [Fin.rev_castSucc] using
    (hl.unreverse (j := q.succ) (by simp [Fin.rev_castSucc]))

end MulStruct

end SSet.PtSimplex

namespace Submission

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

variable
  {f g fg : (Sng (TopCat.of X)).PtSimplex (n + 2)
    (TopCat.toSSetObj₀Equiv.symm x)}

/-- A simplicial multiplication structure realizes multiplication of the associated cubical
homotopy classes at every face index, not only at the final index used in the definition. -/
theorem stickHomotopyClass_ofPtSimplex_mul_at
    (i : Fin (n + 2)) (r : SSet.PtSimplex.MulStruct f g fg i) :
    (NormalizedSimplex.ofPtSimplex fg).stickHomotopyClass =
      (NormalizedSimplex.ofPtSimplex f).stickHomotopyClass *
        (NormalizedSimplex.ofPtSimplex g).stickHomotopyClass := by
  let rec go
      {f g fg : (Sng (TopCat.of X)).PtSimplex (n + 2)
        (TopCat.toSSetObj₀Equiv.symm x)}
      (i : Fin (n + 2)) (r : SSet.PtSimplex.MulStruct f g fg i) :
      (NormalizedSimplex.ofPtSimplex fg).stickHomotopyClass =
        (NormalizedSimplex.ofPtSimplex f).stickHomotopyClass *
          (NormalizedSimplex.ofPtSimplex g).stickHomotopyClass := by
    by_cases hi : i = Fin.last (n + 1)
    · subst i
      exact stickHomotopyClass_ofPtSimplex_mul' r
    · obtain ⟨q, rfl⟩ := i.eq_castSucc_of_ne_last hi
      have hnext := go q.succ (r.moveRight q)
      simpa [mul_comm] using hnext
  termination_by i.rev.val
  decreasing_by grind
  exact go i r

end Submission
