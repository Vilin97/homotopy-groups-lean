/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SimplicialIndexShift

/-!
# Telescoping horns for simplicial homotopy addition

For a normalized boundary, the horn at stage `q` keeps the original faces strictly after
`q + 1`, replaces the earlier faces by the constant simplex, and omits face `q + 1`.  Its
missing face is the auxiliary term which telescopes the alternating boundary relation.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

/-- The prescribed faces of the stage-`q` telescoping horn. -/
def telescopeHornFace (b : NormalizedSimplexBoundary n X x) (q : Fin (n + 2))
    (i : Fin (n + 4)) (_hi : i ≠ q.succ.castSucc) :
    Δ[n + 2] ⟶ Sng (TopCat.of X) :=
  if i < q.succ.castSucc then
    SSet.const (TopCat.toSSetObj₀Equiv.symm x)
  else (b.face i).toPtSimplex.map

/-- Every codimension-one face of every prescribed telescoping-horn face is constant. -/
theorem δ_telescopeHornFace (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) (i : Fin (n + 4)) (hi : i ≠ q.succ.castSucc)
    (a : Fin (n + 3)) :
    SSet.stdSimplex.δ a ≫ telescopeHornFace b q i hi =
      SSet.const (TopCat.toSSetObj₀Equiv.symm x) := by
  simp only [telescopeHornFace]
  split
  · simp
  · exact (b.face i).toPtSimplex.δ_map a

/-- The faces prescribed for a telescoping horn agree on every intersection. -/
theorem telescopeHornFace_compatible (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) :
    SSet.horn.IsCompatible (telescopeHornFace b q) := by
  rw [SSet.horn.isCompatible_iff]
  intro j k hj hk hjk
  rw [δ_telescopeHornFace, δ_telescopeHornFace]

/-- The Kan filler of the stage-`q` telescoping horn. -/
def telescopeFiller (b : NormalizedSimplexBoundary n X x) (q : Fin (n + 2)) :
    Δ[n + 3] ⟶ Sng (TopCat.of X) :=
  (telescopeHornFace_compatible b q).liftOfKanComplex

/-- The telescoping filler recovers each of its prescribed faces. -/
@[reassoc]
theorem δ_telescopeFiller (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) (i : Fin (n + 4)) (hi : i ≠ q.succ.castSucc) :
    SSet.stdSimplex.δ i ≫ telescopeFiller b q = telescopeHornFace b q i hi :=
  (telescopeHornFace_compatible b q).δ_liftOfKanComplex i hi

/-- Complete face table for a telescoping filler. -/
theorem δ_telescopeFiller_table (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) (i : Fin (n + 4)) (hi : i ≠ q.succ.castSucc) :
    SSet.stdSimplex.δ i ≫ telescopeFiller b q =
      if i < q.succ.castSucc then
        SSet.const (TopCat.toSSetObj₀Equiv.symm x)
      else (b.face i).toPtSimplex.map := by
  rw [δ_telescopeFiller b q i hi]
  rfl

theorem δ_telescopeFiller_before (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) (i : Fin (n + 4)) (hi : i < q.succ.castSucc) :
    SSet.stdSimplex.δ i ≫ telescopeFiller b q =
      SSet.const (TopCat.toSSetObj₀Equiv.symm x) := by
  rw [δ_telescopeFiller_table b q i (ne_of_lt hi), if_pos hi]

theorem δ_telescopeFiller_after (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) (i : Fin (n + 4)) (hi : q.succ.castSucc < i) :
    SSet.stdSimplex.δ i ≫ telescopeFiller b q = (b.face i).toPtSimplex.map := by
  rw [δ_telescopeFiller_table b q i (ne_of_gt hi), if_neg (not_lt_of_ge hi.le)]

/-- The omitted face of a telescoping horn, with its induced pointed-simplex structure. -/
def telescopeFace (b : NormalizedSimplexBoundary n X x) (q : Fin (n + 2)) :
    (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x) where
  map := SSet.stdSimplex.δ q.succ.castSucc ≫ telescopeFiller b q
  comm := by
    apply SSet.boundary.hom_ext
    intro a
    trans SSet.const (TopCat.toSSetObj₀Equiv.symm x)
    · rw [← Category.assoc, SSet.boundary.ι_ι]
      by_cases ha : a.castSucc < q.succ.castSucc
      · have hprescribed : a.castSucc ≠ q.succ.castSucc := ne_of_lt ha
        rw [← Category.assoc, SSet.stdSimplex.δ_comp_δ' ha, Category.assoc,
          δ_telescopeFiller b q a.castSucc hprescribed,
          δ_telescopeHornFace]
      · have hqa : q.succ ≤ a := by grind
        have hprescribed : a.succ ≠ q.succ.castSucc := by grind
        rw [← Category.assoc, ← SSet.stdSimplex.δ_comp_δ hqa, Category.assoc,
          δ_telescopeFiller b q a.succ hprescribed,
          δ_telescopeHornFace]
    · simp

@[simp]
theorem telescopeFace_map (b : NormalizedSimplexBoundary n X x) (q : Fin (n + 2)) :
    (telescopeFace b q).map =
      SSet.stdSimplex.δ q.succ.castSucc ≫ telescopeFiller b q :=
  rfl

/-- The pointed map of a normalized boundary face is the corresponding face of the higher
simplex map. -/
theorem face_toPtSimplex_map (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 4)) :
    SSet.stdSimplex.δ i ≫ SSet.yonedaEquiv.symm b.simplex =
      (b.face i).toPtSimplex.map := by
  apply SSet.yonedaEquiv.injective
  calc
    SSet.yonedaEquiv
          (SSet.stdSimplex.δ i ≫ SSet.yonedaEquiv.symm b.simplex) =
        (Sng (TopCat.of X)).δ i b.simplex := by
      simpa using (yonedaEquiv_comp_δ (X := X) (q := n + 2) i
        (SSet.yonedaEquiv.symm b.simplex)).symm
    _ = (b.face i).simplex := (b.face_simplex i).symm
    _ = SSet.yonedaEquiv (b.face i).toPtSimplex.map := by
      rw [NormalizedSimplex.toPtSimplex_map, SSet.yonedaEquiv.apply_symm_apply]

/-- Face table for a degeneracy of a normalized simplex. -/
theorem δ_σ_normalizedSimplex (s : NormalizedSimplex n X x)
    (i : Fin (n + 3)) (j : Fin (n + 4)) :
    SSet.stdSimplex.δ j ≫ SSet.stdSimplex.σ i ≫ s.toPtSimplex.map =
      if j = i.castSucc then s.toPtSimplex.map
      else if j = i.succ then s.toPtSimplex.map
      else SSet.const (TopCat.toSSetObj₀Equiv.symm x) :=
  SSet.PtSimplex.MulStruct.δ_σ_ptSimplex s.toPtSimplex i j

/-- Face table for a normalized-simplex degeneracy, stated on its explicit Yoneda map. -/
theorem δ_σ_normalizedSimplex_map (s : NormalizedSimplex n X x)
    (i : Fin (n + 3)) (j : Fin (n + 4)) :
    SSet.stdSimplex.δ j ≫ SSet.stdSimplex.σ i ≫
        SSet.yonedaEquiv.symm s.simplex =
      if j = i.castSucc then SSet.yonedaEquiv.symm s.simplex
      else if j = i.succ then SSet.yonedaEquiv.symm s.simplex
      else SSet.const (TopCat.toSSetObj₀Equiv.symm x) :=
  δ_σ_normalizedSimplex s i j

/-- A pointed face of the stage-`q` telescoping filler: constant before the omitted face,
the auxiliary face at the omitted index, and the corresponding original face afterwards. -/
def telescopeBoundaryPtFace (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) (i : Fin (n + 4)) :
    (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x) :=
  if i < q.succ.castSucc then .const
  else if i = q.succ.castSucc then telescopeFace b q
  else (b.face i).toPtSimplex

/-- The stage-`q` telescoping filler together with its complete normalized boundary. -/
def telescopeBoundary (b : NormalizedSimplexBoundary n X x) (q : Fin (n + 2)) :
    NormalizedSimplexBoundary n X x where
  simplex := SSet.yonedaEquiv (telescopeFiller b q)
  face i := NormalizedSimplex.ofPtSimplex (telescopeBoundaryPtFace b q i)
  face_simplex i := by
    rw [NormalizedSimplex.ofPtSimplex_simplex]
    by_cases hi : i = q.succ.castSucc
    · subst i
      simp only [telescopeBoundaryPtFace, lt_self_iff_false, if_false, if_pos,
        telescopeFace_map]
      exact (yonedaEquiv_comp_δ (X := X) (q := n + 2) _
        (telescopeFiller b q)).symm
    · rw [yonedaEquiv_comp_δ (X := X) (q := n + 2) i (telescopeFiller b q),
        δ_telescopeFiller b q i hi]
      by_cases hilow : i < q.succ.castSucc
      · have hilow' : i < q.castSucc.succ := by
          simpa [Fin.castSucc_succ] using hilow
        simp [telescopeBoundaryPtFace, telescopeHornFace, hilow']
      · have hilow' : ¬(i < q.castSucc.succ) := by
          simpa [Fin.castSucc_succ] using hilow
        have hi' : i ≠ q.castSucc.succ := by
          simpa [Fin.castSucc_succ] using hi
        simp [telescopeBoundaryPtFace, telescopeHornFace, hi', hilow']

@[simp]
theorem telescopeBoundary_face_before (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) (i : Fin (n + 4)) (hi : i < q.succ.castSucc) :
    (telescopeBoundary b q).face i = NormalizedSimplex.const n x := by
  have hi' : i < q.castSucc.succ := by simpa [Fin.castSucc_succ] using hi
  simp [telescopeBoundary, telescopeBoundaryPtFace, hi',
    NormalizedSimplex.ofPtSimplex_const]

@[simp]
theorem telescopeBoundary_face_omitted (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) :
    (telescopeBoundary b q).face q.succ.castSucc =
      NormalizedSimplex.ofPtSimplex (telescopeFace b q) := by
  simp [telescopeBoundary, telescopeBoundaryPtFace, Fin.castSucc_succ]

@[simp]
theorem telescopeBoundary_face_after (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) (i : Fin (n + 4)) (hi : q.succ.castSucc < i) :
    (telescopeBoundary b q).face i = b.face i := by
  have hi' : q.castSucc.succ < i := by simpa [Fin.castSucc_succ] using hi
  have hnotlt : ¬(i < q.castSucc.succ) := by grind
  have hne : i ≠ q.castSucc.succ := by grind
  simp [telescopeBoundary, telescopeBoundaryPtFace, hnotlt, hne,
    NormalizedSimplex.ofPtSimplex_toPtSimplex]

/-- The boundary compared with stage `q`: the original boundary for `q = 0`, and the preceding
telescoping boundary for a successor stage. -/
def telescopePreviousBoundary (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) : NormalizedSimplexBoundary n X x :=
  Fin.cases b (fun p ↦ telescopeBoundary b p.castSucc) q

@[simp]
theorem telescopePreviousBoundary_zero (b : NormalizedSimplexBoundary n X x) :
    telescopePreviousBoundary b 0 = b :=
  rfl

@[simp]
theorem telescopePreviousBoundary_succ (b : NormalizedSimplexBoundary n X x)
    (p : Fin (n + 1)) :
    telescopePreviousBoundary b p.succ = telescopeBoundary b p.castSucc :=
  rfl

/-- The face at index `q` of the comparison boundary is the first original face at stage zero,
and the preceding auxiliary face at every successor stage. -/
def telescopePreviousFace (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) :
    (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x) :=
  (telescopePreviousBoundary b q).face q.castSucc.castSucc |>
    NormalizedSimplex.toPtSimplex

/-- The face after `q` in the comparison boundary is the corresponding original face. -/
theorem telescopePreviousBoundary_face_succ (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) :
    (telescopePreviousBoundary b q).face q.castSucc.succ =
      b.face q.castSucc.succ := by
  induction q using Fin.cases with
  | zero => rfl
  | succ p =>
      apply telescopeBoundary_face_after
      grind

/-- Faces strictly before the distinguished comparison face are constant. -/
theorem telescopePreviousBoundary_face_before (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) (i : Fin (n + 4)) (hi : i < q.castSucc.castSucc) :
    (telescopePreviousBoundary b q).face i = NormalizedSimplex.const n x := by
  induction q using Fin.cases with
  | zero =>
      simp at hi
  | succ p =>
      apply telescopeBoundary_face_before
      simpa [Fin.castSucc_succ] using hi

/-- Faces strictly after the distinguished comparison face are the corresponding original
boundary faces. -/
theorem telescopePreviousBoundary_face_after (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) (i : Fin (n + 4)) (hi : q.castSucc.castSucc < i) :
    (telescopePreviousBoundary b q).face i = b.face i := by
  induction q using Fin.cases with
  | zero => rfl
  | succ p =>
      apply telescopeBoundary_face_after
      simpa [Fin.castSucc_succ] using hi

theorem telescopePreviousBoundary_face_map_before
    (b : NormalizedSimplexBoundary n X x) (q : Fin (n + 2))
    (i : Fin (n + 4)) (hi : i < q.castSucc.castSucc) :
    SSet.yonedaEquiv.symm ((telescopePreviousBoundary b q).face i).simplex =
      SSet.const (TopCat.toSSetObj₀Equiv.symm x) := by
  rw [telescopePreviousBoundary_face_before b q i hi]
  rfl

theorem telescopePreviousBoundary_face_map_after
    (b : NormalizedSimplexBoundary n X x) (q : Fin (n + 2))
    (i : Fin (n + 4)) (hi : q.castSucc.castSucc < i) :
    SSet.yonedaEquiv.symm ((telescopePreviousBoundary b q).face i).simplex =
      SSet.yonedaEquiv.symm (b.face i).simplex := by
  rw [telescopePreviousBoundary_face_after b q i hi]

/-- Away from its distinguished face, the preceding boundary is constant to the left and
agrees with the original boundary to the right. -/
theorem telescopePreviousBoundary_face_map_table
    (b : NormalizedSimplexBoundary n X x) (q : Fin (n + 2))
    (i : Fin (n + 4)) (hi : i ≠ q.castSucc.castSucc) :
    SSet.yonedaEquiv.symm ((telescopePreviousBoundary b q).face i).simplex =
      if i < q.castSucc.succ then SSet.const (TopCat.toSSetObj₀Equiv.symm x)
      else SSet.yonedaEquiv.symm (b.face i).simplex := by
  rcases lt_or_gt_of_ne hi with hilow | hihigh
  · rw [telescopePreviousBoundary_face_map_before b q i hilow, if_pos (by grind)]
  · rw [telescopePreviousBoundary_face_map_after b q i hihigh, if_neg (by grind)]

/-! ### The three-face comparison at each telescoping stage -/

/-- The horn which compares the boundary before stage `q` with its new auxiliary face.  Its
missing face will have consecutive faces `previous`, `original`, and `new auxiliary`. -/
def telescopeRelationHornFace (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) (i : Fin (n + 5))
    (_hi : i ≠ q.succ.castSucc.castSucc) :
    Δ[n + 3] ⟶ Sng (TopCat.of X) :=
  if hbefore : i < q.castSucc.castSucc.castSucc then
    SSet.stdSimplex.σ q.succ ≫
      ((telescopePreviousBoundary b q).face
        (i.castPred (by grind))).toPtSimplex.map
  else if hat : i = q.castSucc.castSucc.castSucc then
    SSet.stdSimplex.σ q.castSucc ≫ (telescopePreviousFace b q).map
  else if hx : i = q.succ.succ.castSucc then
    SSet.yonedaEquiv.symm (telescopePreviousBoundary b q).simplex
  else if hw : i = q.succ.succ.succ then
    telescopeFiller b q
  else
    SSet.stdSimplex.σ ⟨q.val + 2, by grind⟩ ≫
      ((telescopePreviousBoundary b q).face
        (i.pred (by
          intro hi
          subst i
          by_cases hq : q = 0
          · subst q
            apply hat
            ext
            simp
          · apply hbefore
            simpa [Fin.ext_iff] using (Fin.pos_iff_ne_zero.mpr hq)))).toPtSimplex.map

/-- The comparison-horn faces agree on every intersection. -/
theorem telescopeRelationHornFace_compatible
    (b : NormalizedSimplexBoundary n X x) (q : Fin (n + 2)) :
    SSet.horn.IsCompatible (telescopeRelationHornFace b q) := by
  rw [SSet.horn.isCompatible_iff]
  intro j k hj hk hjk
  simp only [telescopeRelationHornFace]
  split_ifs with hjb hja hjx hjw hkb hka hkx hkw
  all_goals try grind
  all_goals subst_vars
  all_goals simp_all [δ_σ_normalizedSimplex_map,
    SSet.PtSimplex.MulStruct.δ_σ_ptSimplex]
  all_goals try simp_all [face_toPtSimplex_map, δ_telescopeFiller_table,
    δ_telescopeFiller_before, telescopePreviousFace,
    Fin.castPred_eq_iff_eq_castSucc]
  all_goals try grind
  all_goals try
    exact telescopePreviousBoundary_face_map_table b q _ (by grind)
  all_goals try
    exact telescopePreviousBoundary_face_map_table b q _ (by
      intro hindex
      have hval := congrArg Fin.val hindex
      have hjval : j.val < q.val := by
        change j.val < q.val at hjb
        exact hjb
      simp at hval
      omega)
  rw [if_neg (by
    intro hindex
    have hval := congrArg Fin.val hindex
    simp at hval), if_pos (by
      apply Fin.ext
      simp)]
  have hk0 : k ≠ 0 := Fin.ne_zero_of_lt hjk
  have hjkval := hjk
  change q.val + 3 < k.val at hjkval
  have hafter : q.succ.castSucc < k.pred hk0 := by
    change q.val + 1 < (k.pred hk0).val
    rw [Fin.val_pred]
    omega
  rw [δ_telescopeFiller_after b q (k.pred hk0) hafter]
  change SSet.yonedaEquiv.symm (b.face (k.pred hk0)).simplex =
    SSet.yonedaEquiv.symm
      ((telescopePreviousBoundary b q).face (k.pred hk0)).simplex
  symm
  apply telescopePreviousBoundary_face_map_after
  change q.val < (k.pred hk0).val
  change q.val + 1 < (k.pred hk0).val at hafter
  omega

/-- The Kan filler of the three-face comparison horn at stage `q`. -/
def telescopeRelationFiller (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) : Δ[n + 4] ⟶ Sng (TopCat.of X) :=
  (telescopeRelationHornFace_compatible b q).liftOfKanComplex

/-- Every prescribed face of the comparison filler is recovered. -/
@[reassoc]
theorem δ_telescopeRelationFiller (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) (i : Fin (n + 5))
    (hi : i ≠ q.succ.castSucc.castSucc) :
    SSet.stdSimplex.δ i ≫ telescopeRelationFiller b q =
      telescopeRelationHornFace b q i hi :=
  (telescopeRelationHornFace_compatible b q).δ_liftOfKanComplex i hi

/-- The omitted comparison face packages the three consecutive faces `previous`, `original`,
and `new auxiliary` as a multiplication structure at the original index `q`. -/
def telescopeMulStruct (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) :
    SSet.PtSimplex.MulStruct
      (telescopeFace b q)
      (telescopePreviousFace b q)
      (b.face q.castSucc.succ).toPtSimplex q where
  map := SSet.stdSimplex.δ q.succ.castSucc.castSucc ≫
    telescopeRelationFiller b q
  δ_castSucc_castSucc_map := by
    rw [← Category.assoc]
    have hmissing : q.succ.castSucc.castSucc =
        q.castSucc.castSucc.succ := by ext; simp
    rw [hmissing, ← SSet.stdSimplex.δ_comp_δ_self, Category.assoc]
    have hprescribed : q.castSucc.castSucc.castSucc ≠
        q.succ.castSucc.castSucc := by grind
    rw [δ_telescopeRelationFiller b q _ hprescribed]
    simp [telescopeRelationHornFace,
      SSet.stdSimplex.δ_comp_σ_self_assoc]
  δ_succ_castSucc_map := by
    rw [← Category.assoc]
    have hmissing : q.succ.castSucc.castSucc =
        q.castSucc.succ.castSucc := by ext; simp
    rw [hmissing, SSet.stdSimplex.δ_comp_δ_self, Category.assoc]
    have hprescribed : q.castSucc.succ.succ ≠
        q.succ.castSucc.castSucc := by grind
    rw [δ_telescopeRelationFiller b q _ hprescribed]
    simp only [telescopeRelationHornFace]
    split_ifs with hbefore hat hx hw
    all_goals try grind
    rw [face_toPtSimplex_map,
      telescopePreviousBoundary_face_succ]
  δ_succ_succ_map := by
    rw [← Category.assoc,
      ← SSet.stdSimplex.δ_comp_δ (i := q.succ.castSucc)
        (j := q.succ.succ) (by grind), Category.assoc]
    have hprescribed : q.succ.succ.succ ≠
        q.succ.castSucc.castSucc := by grind
    rw [δ_telescopeRelationFiller b q _ hprescribed]
    simp only [telescopeRelationHornFace]
    split_ifs
    all_goals try grind
    rfl
  δ_map_of_lt j hj := by
    rw [← Category.assoc, SSet.stdSimplex.δ_comp_δ' (by grind),
      Category.assoc]
    have hprescribed : j.castSucc ≠ q.succ.castSucc.castSucc := by grind
    rw [δ_telescopeRelationFiller b q _ hprescribed]
    simp only [telescopeRelationHornFace]
    split_ifs
    all_goals try grind
    rw [SSet.PtSimplex.MulStruct.δ_σ_ptSimplex]
    split_ifs <;> grind
  δ_map_of_gt j hj := by
    rw [← Category.assoc,
      ← SSet.stdSimplex.δ_comp_δ (i := q.succ.castSucc) (j := j) (by grind),
      Category.assoc]
    have hprescribed : j.succ ≠ q.succ.castSucc.castSucc := by grind
    rw [δ_telescopeRelationFiller b q _ hprescribed]
    simp only [telescopeRelationHornFace]
    split_ifs
    all_goals try grind
    rw [SSet.PtSimplex.MulStruct.δ_σ_ptSimplex]
    split_ifs <;> grind

/-- At each stage, the original face after `q` is the product of the new auxiliary face and
the distinguished face of the preceding boundary. -/
theorem stickHomotopyClass_telescope_mul
    (b : NormalizedSimplexBoundary n X x) (q : Fin (n + 2)) :
    (b.face q.castSucc.succ).stickHomotopyClass =
      (NormalizedSimplex.ofPtSimplex (telescopeFace b q)).stickHomotopyClass *
        ((telescopePreviousBoundary b q).face
          q.castSucc.castSucc).stickHomotopyClass := by
  simpa [telescopePreviousFace] using
    stickHomotopyClass_ofPtSimplex_mul_at q (telescopeMulStruct b q)

/-- Additive form of the local telescope relation.  This is the three-term identity which
telescopes across the stages. -/
theorem additiveStickHomotopyClass_telescope_relation
    (b : NormalizedSimplexBoundary n X x) (q : Fin (n + 2)) :
    Additive.ofMul
          ((telescopePreviousBoundary b q).face
            q.castSucc.castSucc).stickHomotopyClass -
        Additive.ofMul (b.face q.castSucc.succ).stickHomotopyClass +
          Additive.ofMul
            (NormalizedSimplex.ofPtSimplex
              (telescopeFace b q)).stickHomotopyClass = 0 := by
  have h := congrArg Additive.ofMul (stickHomotopyClass_telescope_mul b q)
  change Additive.ofMul (b.face q.castSucc.succ).stickHomotopyClass =
      Additive.ofMul
          (NormalizedSimplex.ofPtSimplex
            (telescopeFace b q)).stickHomotopyClass +
        Additive.ofMul
          ((telescopePreviousBoundary b q).face
            q.castSucc.castSucc).stickHomotopyClass at h
  rw [h]
  abel

/-- The additive stick-breaking class of an original boundary face. -/
noncomputable def boundaryStickFaceClass (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 4)) : Additive (π_ (n + 2) X x) :=
  Additive.ofMul (b.face i).stickHomotopyClass

/-- The additive stick-breaking class of an auxiliary telescope face. -/
noncomputable def telescopeStickFaceClass (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) : Additive (π_ (n + 2) X x) :=
  Additive.ofMul
    (NormalizedSimplex.ofPtSimplex (telescopeFace b q)).stickHomotopyClass

/-- At a successor stage, the distinguished face of the preceding boundary is precisely the
auxiliary face constructed at the preceding stage. -/
@[simp]
theorem telescopePreviousBoundary_face_distinguished_succ
    (b : NormalizedSimplexBoundary n X x) (p : Fin (n + 1)) :
    (telescopePreviousBoundary b p.succ).face
        p.succ.castSucc.castSucc =
      NormalizedSimplex.ofPtSimplex (telescopeFace b p.castSucc) := by
  change (telescopeBoundary b p.castSucc).face
      p.succ.castSucc.castSucc = _
  rw [show p.succ.castSucc.castSucc =
      p.castSucc.succ.castSucc by ext; simp]
  exact telescopeBoundary_face_omitted b p.castSucc

@[simp]
theorem telescopeBoundary_face_previous_distinguished
    (b : NormalizedSimplexBoundary n X x) (p : Fin (n + 1)) :
    (telescopeBoundary b p.castSucc).face
        p.castSucc.castSucc.succ =
      NormalizedSimplex.ofPtSimplex (telescopeFace b p.castSucc) := by
  rw [show p.castSucc.castSucc.succ =
      p.castSucc.succ.castSucc by ext; simp]
  exact telescopeBoundary_face_omitted b p.castSucc

/-- The initial local relation starts with original face zero. -/
theorem telescopeStickFaceClass_zero_relation
    (b : NormalizedSimplexBoundary n X x) :
    boundaryStickFaceClass b 0 - boundaryStickFaceClass b 1 +
      telescopeStickFaceClass b 0 = 0 := by
  simpa [boundaryStickFaceClass, telescopeStickFaceClass] using
    additiveStickHomotopyClass_telescope_relation b (0 : Fin (n + 2))

/-- Every successor local relation starts with the preceding auxiliary face. -/
theorem telescopeStickFaceClass_succ_relation
    (b : NormalizedSimplexBoundary n X x) (p : Fin (n + 1)) :
    telescopeStickFaceClass b p.castSucc -
        boundaryStickFaceClass b p.succ.castSucc.succ +
      telescopeStickFaceClass b p.succ = 0 := by
  simpa [boundaryStickFaceClass, telescopeStickFaceClass] using
    additiveStickHomotopyClass_telescope_relation b p.succ

/-- The first auxiliary class is the difference of the first two original face classes. -/
theorem telescopeStickFaceClass_zero
    (b : NormalizedSimplexBoundary n X x) :
    telescopeStickFaceClass b 0 =
      boundaryStickFaceClass b 1 - boundaryStickFaceClass b 0 := by
  have h := telescopeStickFaceClass_zero_relation b
  rw [← sub_eq_zero]
  calc
    telescopeStickFaceClass b 0 -
        (boundaryStickFaceClass b 1 - boundaryStickFaceClass b 0) =
      boundaryStickFaceClass b 0 - boundaryStickFaceClass b 1 +
        telescopeStickFaceClass b 0 := by abel
    _ = 0 := h

/-- Each later auxiliary class is the next original class minus the preceding auxiliary
class. -/
theorem telescopeStickFaceClass_succ
    (b : NormalizedSimplexBoundary n X x) (p : Fin (n + 1)) :
    telescopeStickFaceClass b p.succ =
      boundaryStickFaceClass b p.succ.castSucc.succ -
        telescopeStickFaceClass b p.castSucc := by
  have h := telescopeStickFaceClass_succ_relation b p
  rw [← sub_eq_zero]
  calc
    telescopeStickFaceClass b p.succ -
        (boundaryStickFaceClass b p.succ.castSucc.succ -
          telescopeStickFaceClass b p.castSucc) =
      telescopeStickFaceClass b p.castSucc -
          boundaryStickFaceClass b p.succ.castSucc.succ +
        telescopeStickFaceClass b p.succ := by abel
    _ = 0 := h

/-- At the final stage, the last auxiliary face is related to the final original face. -/
def telescopeLastRelStruct (b : NormalizedSimplexBoundary n X x) :
    SSet.PtSimplex.RelStruct
      (telescopeFace b (Fin.last (n + 1)))
      (b.face (Fin.last (n + 3))).toPtSimplex
      (Fin.last (n + 2)) where
  map := telescopeFiller b (Fin.last (n + 1))
  δ_castSucc_map := by
    rw [show (Fin.last (n + 2)).castSucc =
        (Fin.last (n + 1)).succ.castSucc by ext; simp]
    rfl
  δ_succ_map := by
    have hprescribed :
        (Fin.last (n + 2)).succ ≠ (Fin.last (n + 1)).succ.castSucc := by grind
    rw [δ_telescopeFiller b (Fin.last (n + 1)) _ hprescribed]
    simp only [telescopeHornFace]
    split_ifs
    · grind
    · rfl
  δ_map_of_lt j hj := by
    have hprescribed : j ≠ (Fin.last (n + 1)).succ.castSucc := ne_of_lt hj
    rw [δ_telescopeFiller b (Fin.last (n + 1)) j hprescribed]
    simp [telescopeHornFace, hj]
  δ_map_of_gt j hj := by grind

/-- The final auxiliary face has the same maintained homotopy class as the last original
face. -/
theorem stickHomotopyClass_telescopeFace_last
    (b : NormalizedSimplexBoundary n X x) :
    (NormalizedSimplex.ofPtSimplex
        (telescopeFace b (Fin.last (n + 1)))).stickHomotopyClass =
      (b.face (Fin.last (n + 3))).stickHomotopyClass := by
  simpa using stickHomotopyClass_ofPtSimplex_rel (telescopeLastRelStruct b)

/-- The running telescope sequence starts at original face zero and then records the auxiliary
faces. -/
noncomputable def telescopeRunningClass (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) : Additive (π_ (n + 2) X x) :=
  Fin.cases (boundaryStickFaceClass b 0)
    (fun q ↦ telescopeStickFaceClass b q) i

@[simp]
theorem telescopeRunningClass_zero (b : NormalizedSimplexBoundary n X x) :
    telescopeRunningClass b 0 = boundaryStickFaceClass b 0 :=
  rfl

@[simp]
theorem telescopeRunningClass_succ (b : NormalizedSimplexBoundary n X x)
    (q : Fin (n + 2)) :
    telescopeRunningClass b q.succ = telescopeStickFaceClass b q :=
  rfl

/-- Every noninitial original face is the sum of the adjacent running telescope terms. -/
theorem boundaryStickFaceClass_mid_eq
    (b : NormalizedSimplexBoundary n X x) (q : Fin (n + 2)) :
    boundaryStickFaceClass b q.succ.castSucc =
      telescopeRunningClass b q.castSucc + telescopeRunningClass b q.succ := by
  induction q using Fin.cases with
  | zero =>
      simp only [Fin.castSucc_zero, telescopeRunningClass_zero,
        telescopeRunningClass_succ]
      rw [telescopeStickFaceClass_zero]
      abel
  | succ p =>
      rw [show p.succ.castSucc = p.castSucc.succ by ext; simp,
        telescopeRunningClass_succ, telescopeRunningClass_succ,
        telescopeStickFaceClass_succ]
      abel

/-- The last auxiliary class is the last original face class. -/
theorem telescopeStickFaceClass_last
    (b : NormalizedSimplexBoundary n X x) :
    telescopeStickFaceClass b (Fin.last (n + 1)) =
      boundaryStickFaceClass b (Fin.last (n + 3)) := by
  exact congrArg Additive.ofMul (stickHomotopyClass_telescopeFace_last b)

/-- Homotopy addition for a normalized simplicial boundary: the alternating sum of all
stick-breaking face classes vanishes. -/
theorem NormalizedSimplexBoundary.alternatingStickFaceClass_eq_zero
    (b : NormalizedSimplexBoundary n X x) :
    b.alternatingStickFaceClass = 0 := by
  rw [NormalizedSimplexBoundary.alternatingStickFaceClass]
  change (∑ i : Fin (n + 4),
    (-1 : ℤ) ^ i.val • boundaryStickFaceClass b i) = 0
  apply Fin.sum_neg_one_pow_eq_zero
    (d := boundaryStickFaceClass b) (r := telescopeRunningClass b)
  · rfl
  · exact boundaryStickFaceClass_mid_eq b
  · rw [show (Fin.last (n + 2) : Fin (n + 3)) =
        (Fin.last (n + 1)).succ by rfl,
      telescopeRunningClass_succ]
    exact (telescopeStickFaceClass_last b).symm

/-- Equivalent cubical-shell form of homotopy addition for a normalized simplex boundary. -/
theorem NormalizedSimplexBoundary.stickCubicalBoundaryClass_eq_zero
    (b : NormalizedSimplexBoundary n X x) :
    b.stickCubicalBoundaryClass = 0 := by
  rw [b.stickCubicalBoundaryClass_eq_alternatingStickFaceClass,
    b.alternatingStickFaceClass_eq_zero]

end Submission
