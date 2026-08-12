/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SimplexHEP
import Submission.Hurewicz.Prism

/-!
# The tower of compressing homotopies

Let `A` be a subspace of `X` such that every point of `X` can be joined to `A` by a path and all
the relative homotopy groups `π_rel (n+1) (X, A)` vanish.  This file builds, by recursion on the
dimension `j`, a homotopy `H f : |Δ^j| × I → X` for *every* continuous `f : |Δ^j| → X`, starting
at `f`, ending in `A`, compatible with the face inclusions, and constant on the maps that already
take their values in `A`.

The recursion is scheduled: the homotopy attached to a `j`-simplex has come to rest by the time
`cutoff j = 1 - 2 ^ (-(j+1))`.  Given the data in dimension `j`, the faces of a `(j+1)`-simplex
`f` glue to a homotopy on `|∂Δ^{j+1}| × I` (`Submission.glueFacesHomotopy`), which extends over
`|Δ^{j+1}| × I` by the homotopy extension property (`Submission.exists_boundary_extension`).  At
time `cutoff j` the extension already maps the boundary into `A`, so it can be compressed into `A`
rel the boundary (`Submission.exists_compression`); that compression is run on
`[cutoff j, cutoff (j+1)]`.  Because it fixes the boundary, and because the face homotopies are
already at rest after `cutoff j`, compatibility with the faces survives.

## Main definitions and results

* `Submission.cutoff` — the schedule;
* `Submission.Step A j` — the compressing homotopies in dimension `j`, with their invariants;
* `Submission.IsNext` — face compatibility between consecutive dimensions;
* `Submission.exists_base`, `Submission.exists_next` — the two steps of the recursion;
* `Submission.tower`, `Submission.tower_isNext` — the resulting tower.
-/

open scoped Topology unitInterval

noncomputable section

namespace Submission

variable {X : Type} [TopologicalSpace X]

/-! ### Paths into the subspace -/

/-- Surjectivity of `π₀(A) → π₀(X)` produces, for every point of `X`, a path joining it to `A`. -/
theorem exists_path_to_target {A : Set X} (a : A)
    (h₀ : Function.Surjective (RelHomotopyGroup.iStar 0 X A a)) (x : X) :
    ∃ γ : C(I, X), γ 0 = x ∧ γ 1 ∈ A := by
  obtain ⟨v, hv⟩ := h₀ (Quotient.mk _ ⟨ContinuousMap.const _ x,
    fun _ hy => by obtain ⟨i, -⟩ := hy; exact i.elim0⟩)
  induction v using Quotient.inductionOn with
  | _ w =>
    obtain ⟨F⟩ := Quotient.exact hv
    refine ⟨⟨fun t => F (unitInterval.symm t, fun i => i.elim0),
      (map_continuous F).comp (unitInterval.continuous_symm.prodMk continuous_const)⟩, ?_, ?_⟩
    · show F (unitInterval.symm 0, _) = x
      rw [unitInterval.symm_zero]
      exact F.apply_one _
    · show F (unitInterval.symm 1, _) ∈ A
      rw [unitInterval.symm_one, F.apply_zero]
      exact (w.1 _).2

/-! ### The schedule -/

/-- The instant by which the compressing homotopies of `j`-simplices have come to rest. -/
def cutoff (j : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ (j + 1)

theorem cutoff_nonneg (j : ℕ) : 0 ≤ cutoff j := by
  have h : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  simp only [cutoff]
  linarith

theorem cutoff_lt_one (j : ℕ) : cutoff j < 1 := by
  have h : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := by positivity
  simp only [cutoff]
  linarith

theorem cutoff_zero : cutoff 0 = 1 / 2 := by norm_num [cutoff]

theorem cutoff_lt_cutoff_succ (j : ℕ) : cutoff j < cutoff (j + 1) := by
  have h : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := by positivity
  have e : (1 / 2 : ℝ) ^ (j + 1 + 1) = 1 / 2 * (1 / 2 : ℝ) ^ (j + 1) := by ring
  simp only [cutoff, e]
  linarith

/-- The schedule, as a point of the unit interval. -/
def cutoffI (j : ℕ) : I := ⟨cutoff j, cutoff_nonneg j, (cutoff_lt_one j).le⟩

@[simp]
theorem coe_cutoffI (j : ℕ) : ((cutoffI j : I) : ℝ) = cutoff j := rfl

/-- The affine reparametrisation carrying `[cutoff j, cutoff (j+1)]` onto `I`, constant outside. -/
def ramp (j : ℕ) (t : I) : I :=
  ⟨max 0 (min 1 (((t : ℝ) - cutoff j) / (cutoff (j + 1) - cutoff j))),
    le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem continuous_ramp (j : ℕ) : Continuous (ramp j) := by
  refine Continuous.subtype_mk (continuous_const.max (continuous_const.min ?_)) _
  exact (continuous_subtype_val.sub continuous_const).div_const _

theorem ramp_eq_zero {j : ℕ} {t : I} (ht : (t : ℝ) ≤ cutoff j) : ramp j t = 0 := by
  have hd : 0 < cutoff (j + 1) - cutoff j := sub_pos.2 (cutoff_lt_cutoff_succ j)
  have hq : ((t : ℝ) - cutoff j) / (cutoff (j + 1) - cutoff j) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  refine Subtype.ext ?_
  show max 0 (min 1 _) = ((0 : I) : ℝ)
  rw [min_eq_right (hq.trans zero_le_one), max_eq_left hq, Set.Icc.coe_zero]

theorem ramp_eq_one {j : ℕ} {t : I} (ht : cutoff (j + 1) ≤ (t : ℝ)) : ramp j t = 1 := by
  have hd : 0 < cutoff (j + 1) - cutoff j := sub_pos.2 (cutoff_lt_cutoff_succ j)
  have hq : 1 ≤ ((t : ℝ) - cutoff j) / (cutoff (j + 1) - cutoff j) :=
    (one_le_div hd).2 (by linarith)
  refine Subtype.ext ?_
  show max 0 (min 1 _) = ((1 : I) : ℝ)
  rw [min_eq_left hq, max_eq_right zero_le_one, Set.Icc.coe_one]

/-! ### Boundary points as points of faces -/

/-- Every point of the boundary of a simplex lies on one of its faces. -/
theorem bdry_induction {j : ℕ} {P : stdSimplex ℝ (Fin (j + 2)) → Prop}
    (hP : ∀ (i : Fin (j + 2)) (y : stdSimplex ℝ (Fin (j + 1))), P (faceMap i y))
    {x : stdSimplex ℝ (Fin (j + 2))} (hx : x ∈ bdry (j + 1)) : P x := by
  obtain ⟨i, hi⟩ := hx
  exact faceMap_dropMap i hi ▸ hP i (dropMap i hi)

/-- Every point of the boundary of a simplex, as a subtype element, lies on one of its faces. -/
theorem bdry_exists {j : ℕ} (b : bdry (j + 1)) :
    ∃ (i : Fin (j + 2)) (y : stdSimplex ℝ (Fin (j + 1))),
      (⟨faceMap i y, faceMap_mem_bdry i y⟩ : bdry (j + 1)) = b :=
  ⟨bdryIdx b, dropMap _ (bdryIdx_spec b), Subtype.ext (faceMap_dropMap _ (bdryIdx_spec b))⟩

/-- If two distinct faces of a simplex meet at a point, that point lies on a codimension two
face, and the two arguments are the corresponding faces of a common simplex. -/
theorem exists_faceMap_factor {j : ℕ} {i k : Fin (j + 3)} (hik : i < k)
    {y z : stdSimplex ℝ (Fin (j + 2))} (h : faceMap i y = faceMap k z) :
    ∃ w : stdSimplex ℝ (Fin (j + 1)),
      y = faceMap (k.pred (Fin.ne_zero_of_lt hik)) w ∧
        z = faceMap (i.castPred (Fin.ne_last_of_lt hik)) w := by
  set j₀ := k.pred (Fin.ne_zero_of_lt hik) with hj₀
  set i₀ := i.castPred (Fin.ne_last_of_lt hik) with hi₀
  have hsucc : j₀.succ = k := Fin.succ_pred _ _
  have hcast : i₀.castSucc = i := Fin.castSucc_castPred _ _
  have hle : i₀ ≤ j₀ := by
    have h1 : (i₀ : ℕ) = (i : ℕ) := rfl
    have h2 : (j₀ : ℕ) = (k : ℕ) - 1 := rfl
    have h3 : (i : ℕ) < (k : ℕ) := hik
    rw [Fin.le_def, h1, h2]
    omega
  have hky : (y : stdSimplex ℝ (Fin (j + 2))).1 j₀ = 0 := by
    have hik' : i.succAbove j₀ = k := Fin.succAbove_pred_of_lt i k hik
    have e1 : (faceMap i y).1 (i.succAbove j₀) = y.1 j₀ := faceMap_coe_succAbove i y j₀
    rw [hik', h, faceMap_coe_same] at e1
    exact e1.symm
  refine ⟨dropMap j₀ hky, (faceMap_dropMap j₀ hky).symm, ?_⟩
  refine (faceMap_injective k ?_).symm
  calc faceMap k (faceMap i₀ (dropMap j₀ hky))
      = faceMap j₀.succ (faceMap i₀ (dropMap j₀ hky)) := by rw [hsucc]
    _ = faceMap i₀.castSucc (faceMap j₀ (dropMap j₀ hky)) := faceMap_faceMap hle _
    _ = faceMap i y := by rw [hcast, faceMap_dropMap]
    _ = faceMap k z := h

/-- Two distinct faces of the `1`-simplex are disjoint. -/
theorem faceMap_ne_faceMap_of_ne {i k : Fin 2} (hik : i ≠ k) (y z : stdSimplex ℝ (Fin 1)) :
    faceMap i y ≠ faceMap k z := by
  intro h
  have h1 : (faceMap i y).1 i = 0 := faceMap_coe_same i y
  have h2 : (faceMap i y).1 k = 0 := by rw [h]; exact faceMap_coe_same k z
  have hs : (faceMap i y).1 0 + (faceMap i y).1 1 = 1 := by
    have hsum := (faceMap i y).2.2
    rwa [Fin.sum_univ_two] at hsum
  clear h
  fin_cases i <;> fin_cases k <;> simp_all

/-! ### The recursion -/

variable (A : Set X)

/-- The compressing homotopies attached to the singular `j`-simplices of `X`, together with the
invariants that make the recursion on `j` go through. -/
structure Step (j : ℕ) where
  /-- The homotopy attached to a map `|Δ^j| → X`. -/
  H : C(stdSimplex ℝ (Fin (j + 1)), X) → C(stdSimplex ℝ (Fin (j + 1)) × I, X)
  /-- The homotopy starts at the given map. -/
  start (f : C(stdSimplex ℝ (Fin (j + 1)), X)) (y : stdSimplex ℝ (Fin (j + 1))) :
    H f (y, 0) = f y
  /-- The homotopy is at rest after `cutoff j`. -/
  stab (f : C(stdSimplex ℝ (Fin (j + 1)), X)) (y : stdSimplex ℝ (Fin (j + 1))) (t : I)
    (ht : cutoff j ≤ (t : ℝ)) : H f (y, t) = H f (y, 1)
  /-- The homotopy is constant on the maps that already take their values in `A`. -/
  fix {f : C(stdSimplex ℝ (Fin (j + 1)), X)} (hf : ∀ y, f y ∈ A)
    (y : stdSimplex ℝ (Fin (j + 1))) (t : I) : H f (y, t) = f y
  /-- The homotopies attached to the faces of a simplex agree wherever the faces meet. -/
  glue (f : C(stdSimplex ℝ (Fin (j + 2)), X)) (i k : Fin (j + 2))
    (y z : stdSimplex ℝ (Fin (j + 1))) (t : I) (h : faceMap i y = faceMap k z) :
    H (f.comp (faceCM i)) (y, t) = H (f.comp (faceCM k)) (z, t)

variable {A}

/-- The homotopies of a `Step` compress into `A`: the endpoint of every homotopy lies in `A`. -/
def Step.Compresses {j : ℕ} (s : Step A j) : Prop :=
  ∀ (f : C(stdSimplex ℝ (Fin (j + 1)), X)) (y : stdSimplex ℝ (Fin (j + 1))), s.H f (y, 1) ∈ A

/-- The homotopies in dimension `j + 1` restrict on each face to the homotopies in dimension
`j`. -/
def IsNext {j : ℕ} (s : Step A j) (s' : Step A (j + 1)) : Prop :=
  ∀ (f : C(stdSimplex ℝ (Fin (j + 2)), X)) (i : Fin (j + 2))
    (y : stdSimplex ℝ (Fin (j + 1))) (t : I),
    s'.H f (faceMap i y, t) = s.H (f.comp (faceCM i)) (y, t)

/-- Doubling, as a self-map of the unit interval: it reaches `1` at `cutoff 0 = 1 / 2`. -/
def dbl (t : I) : I :=
  ⟨min 1 (2 * (t : ℝ)),
    le_min zero_le_one (mul_nonneg (by norm_num) (unitInterval.nonneg t)), min_le_left _ _⟩

theorem continuous_dbl : Continuous dbl :=
  Continuous.subtype_mk (continuous_const.min (continuous_const.mul continuous_subtype_val)) _

theorem dbl_zero : dbl 0 = 0 := by
  refine Subtype.ext ?_
  show min 1 (2 * ((0 : I) : ℝ)) = ((0 : I) : ℝ)
  rw [Set.Icc.coe_zero]
  norm_num

theorem dbl_eq_one {t : I} (ht : cutoff 0 ≤ (t : ℝ)) : dbl t = 1 := by
  have h : (1 : ℝ) / 2 ≤ (t : ℝ) := cutoff_zero ▸ ht
  refine Subtype.ext ?_
  show min 1 (2 * (t : ℝ)) = ((1 : I) : ℝ)
  rw [Set.Icc.coe_one, min_eq_left (by linarith)]

theorem cutoff_zero_le_one : cutoff 0 ≤ ((1 : I) : ℝ) := by
  rw [cutoff_zero, Set.Icc.coe_one]
  norm_num

/-- **The base of the recursion.** -/
theorem exists_base (hA : A.Nonempty)
    (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a)) :
    ∃ s : Step A 0, s.Compresses := by
  classical
  have main : ∀ f : C(stdSimplex ℝ (Fin 1), X), ∃ Hf : C(stdSimplex ℝ (Fin 1) × I, X),
      (∀ y, Hf (y, 0) = f y) ∧ (∀ y, Hf (y, 1) ∈ A) ∧
        (∀ (y : stdSimplex ℝ (Fin 1)) (t : I), cutoff 0 ≤ (t : ℝ) → Hf (y, t) = Hf (y, 1)) ∧
        ((∀ y, f y ∈ A) → ∀ y t, Hf (y, t) = f y) ∧
        (∀ y z (t : I), Hf (y, t) = Hf (z, t)) := by
    intro f
    by_cases hfA : ∀ y, f y ∈ A
    · exact ⟨⟨fun p => f p.1, f.continuous.comp continuous_fst⟩, fun _ => rfl, fun y => hfA y,
        fun _ _ _ => rfl, fun _ _ _ => rfl,
        fun y z _ => congrArg f (Subsingleton.elim y z)⟩
    · obtain ⟨γ, hγ₀, hγ₁⟩ :=
        exists_path_to_target ⟨hA.choose, hA.choose_spec⟩ (h₀ _) (f default)
      refine ⟨⟨fun p => γ (dbl p.2), γ.continuous.comp (continuous_dbl.comp continuous_snd)⟩,
        ?_, ?_, ?_, fun h => absurd h hfA, fun _ _ _ => rfl⟩
      · intro y
        show γ (dbl 0) = f y
        rw [dbl_zero, hγ₀]
        exact congrArg f (Subsingleton.elim _ _)
      · intro y
        show γ (dbl 1) ∈ A
        rw [dbl_eq_one cutoff_zero_le_one]
        exact hγ₁
      · intro y t ht
        show γ (dbl t) = γ (dbl 1)
        rw [dbl_eq_one ht, dbl_eq_one cutoff_zero_le_one]
  choose Hf hstart hmem hstab hfix hpt using main
  refine ⟨⟨Hf, hstart, hstab, fun {f} hf y t => hfix f hf y t, ?_⟩, fun f y => hmem f y⟩
  intro f i k y z t h
  obtain rfl : i = k := by
    by_contra hik
    exact faceMap_ne_faceMap_of_ne hik y z h
  exact hpt _ y z t

/-! ### Extending the homotopies by one dimension -/

/-- The homotopies attached to the faces of a `(j+1)`-simplex glue over `|∂Δ^{j+1}| × I` and
extend, by the homotopy extension property, over `|Δ^{j+1}| × I`. -/
theorem exists_face_extension {j : ℕ} (s : Step A j) (f : C(stdSimplex ℝ (Fin (j + 2)), X)) :
    ∃ G : C(stdSimplex ℝ (Fin (j + 2)) × I, X), (∀ y, G (y, 0) = f y) ∧
      ∀ (i : Fin (j + 2)) (y : stdSimplex ℝ (Fin (j + 1))) (t : I),
        G (faceMap i y, t) = s.H (f.comp (faceCM i)) (y, t) := by
  set gb : C(bdry (j + 1) × I, X) :=
    glueFacesHomotopy (fun i => s.H (f.comp (faceCM i))) (s.glue f) with hgbdef
  have hgb : ∀ (i : Fin (j + 2)) (y : stdSimplex ℝ (Fin (j + 1))) (t : I),
      gb (⟨faceMap i y, faceMap_mem_bdry i y⟩, t) = s.H (f.comp (faceCM i)) (y, t) :=
    fun i y t => glueFacesHomotopy_faceMap _ (s.glue f) i y t
  have hgb0 : ∀ b : bdry (j + 1), gb (b, 0) = f (b : stdSimplex ℝ (Fin (j + 2))) := by
    intro b
    obtain ⟨i, y, rfl⟩ := bdry_exists b
    rw [hgb i y 0]
    exact s.start _ y
  obtain ⟨G, hG0, hGb⟩ := exists_boundary_extension f gb hgb0
  exact ⟨G, hG0, fun i y t => by rw [hGb ⟨faceMap i y, faceMap_mem_bdry i y⟩ t, hgb i y t]⟩

/-- Face compatibility with the previous dimension implies the gluing condition one dimension
up: this is the codimension two coherence of the tower. -/
theorem glue_of_face {j : ℕ} (s : Step A j)
    (Hf : C(stdSimplex ℝ (Fin (j + 2)), X) → C(stdSimplex ℝ (Fin (j + 2)) × I, X))
    (hface : ∀ (f : C(stdSimplex ℝ (Fin (j + 2)), X)) (i : Fin (j + 2))
      (y : stdSimplex ℝ (Fin (j + 1))) (t : I),
      Hf f (faceMap i y, t) = s.H (f.comp (faceCM i)) (y, t))
    (f : C(stdSimplex ℝ (Fin (j + 3)), X)) (i k : Fin (j + 3))
    (y z : stdSimplex ℝ (Fin (j + 2))) (t : I) (h : faceMap i y = faceMap k z) :
    Hf (f.comp (faceCM i)) (y, t) = Hf (f.comp (faceCM k)) (z, t) := by
  have key : ∀ (i k : Fin (j + 3)) (y z : stdSimplex ℝ (Fin (j + 2))), i < k →
      faceMap i y = faceMap k z →
      Hf (f.comp (faceCM i)) (y, t) = Hf (f.comp (faceCM k)) (z, t) := by
    intro i k y z hik h
    obtain ⟨w, hy, hz⟩ := exists_faceMap_factor hik h
    set j₀ := k.pred (Fin.ne_zero_of_lt hik) with hj₀
    set i₀ := i.castPred (Fin.ne_last_of_lt hik) with hi₀
    have hle : i₀ ≤ j₀ := by
      have h1 : (i₀ : ℕ) = (i : ℕ) := rfl
      have h2 : (j₀ : ℕ) = (k : ℕ) - 1 := rfl
      have h3 : (i : ℕ) < (k : ℕ) := hik
      rw [Fin.le_def, h1, h2]
      omega
    have hcomp : (f.comp (faceCM i)).comp (faceCM j₀) = (f.comp (faceCM k)).comp (faceCM i₀) := by
      refine ContinuousMap.ext fun v => ?_
      show f (faceMap i (faceMap j₀ v)) = f (faceMap k (faceMap i₀ v))
      rw [← Fin.castSucc_castPred i (Fin.ne_last_of_lt hik), ← faceMap_faceMap hle,
        Fin.succ_pred]
    rw [hy, hz, hface (f.comp (faceCM i)) j₀ w t, hface (f.comp (faceCM k)) i₀ w t, hcomp]
  rcases lt_trichotomy i k with hik | rfl | hik
  · exact key i k y z hik h
  · rw [faceMap_injective i h]
  · exact (key k i z y hik h.symm).symm

/-- **The recursion step.**  If `π_rel (j+1) (X, A)` vanishes, the compressing homotopies of
dimension `j` extend to dimension `j + 1`, still compressing into `A`. -/
theorem exists_next {j : ℕ} (s : Step A j) (hs : s.Compresses)
    (hpi : ∀ a : A, Nonempty (Unique (π_rel (j + 1) X A a))) :
    ∃ s' : Step A (j + 1), IsNext s s' ∧ s'.Compresses := by
  classical
  have main : ∀ f : C(stdSimplex ℝ (Fin (j + 2)), X),
      ∃ Hf : C(stdSimplex ℝ (Fin (j + 2)) × I, X),
        (∀ y, Hf (y, 0) = f y) ∧ (∀ y, Hf (y, 1) ∈ A) ∧
          (∀ y (t : I), cutoff (j + 1) ≤ (t : ℝ) → Hf (y, t) = Hf (y, 1)) ∧
          ((∀ y, f y ∈ A) → ∀ y t, Hf (y, t) = f y) ∧
          (∀ (i : Fin (j + 2)) (y : stdSimplex ℝ (Fin (j + 1))) (t : I),
            Hf (faceMap i y, t) = s.H (f.comp (faceCM i)) (y, t)) := by
    intro f
    by_cases hfA : ∀ y, f y ∈ A
    · refine ⟨⟨fun p => f p.1, f.continuous.comp continuous_fst⟩, fun _ => rfl, fun y => hfA y,
        fun _ _ _ => rfl, fun _ _ _ => rfl, ?_⟩
      intro i y t
      exact (s.fix (f := f.comp (faceCM i)) (fun _ => hfA _) y t).symm
    · obtain ⟨G, hG0, hGface⟩ := exists_face_extension s f
      set u : C(stdSimplex ℝ (Fin (j + 2)), X) :=
        ⟨fun x => G (x, cutoffI j), G.continuous.comp (continuous_id.prodMk continuous_const)⟩
        with hudef
      have huface : ∀ (i : Fin (j + 2)) (y : stdSimplex ℝ (Fin (j + 1))),
          u (faceMap i y) = s.H (f.comp (faceCM i)) (y, 1) := by
        intro i y
        show G (faceMap i y, cutoffI j) = _
        rw [hGface i y (cutoffI j)]
        exact s.stab _ y (cutoffI j) le_rfl
      have huA : ∀ x ∈ bdry (j + 1), u x ∈ A := by
        intro x hx
        refine bdry_induction (P := fun x => u x ∈ A) (fun i y => ?_) hx
        rw [huface i y]
        exact hs _ y
      obtain ⟨K, hK0, hK1, hKb⟩ := exists_compression j hpi u huA
      have hmatch : ∀ p : stdSimplex ℝ (Fin (j + 2)) × I, ((p.2 : I) : ℝ) = cutoff j →
          G p = K (p.1, ramp j p.2) := by
        rintro ⟨x, t⟩ ht
        have ht' : t = cutoffI j := Subtype.ext ht
        subst ht'
        rw [ramp_eq_zero le_rfl, hK0]
        rfl
      refine ⟨⟨fun p => if ((p.2 : I) : ℝ) ≤ cutoff j then G p else K (p.1, ramp j p.2),
        Continuous.if_le G.continuous
          (K.continuous.comp (continuous_fst.prodMk ((continuous_ramp j).comp continuous_snd)))
          (continuous_subtype_val.comp continuous_snd) continuous_const hmatch⟩,
        ?_, ?_, ?_, fun h => absurd h hfA, ?_⟩
      · intro y
        show (if (((0 : I) : I) : ℝ) ≤ cutoff j then _ else _) = f y
        rw [if_pos (by simpa using cutoff_nonneg j)]
        exact hG0 y
      · intro y
        show (if (((1 : I) : I) : ℝ) ≤ cutoff j then _ else _) ∈ A
        rw [if_neg (by simpa using (cutoff_lt_one j).not_ge),
          ramp_eq_one (by simpa using (cutoff_lt_one (j + 1)).le)]
        exact hK1 y
      · intro y t ht
        have h1 : ¬ ((t : ℝ) ≤ cutoff j) :=
          not_le.2 (lt_of_lt_of_le (cutoff_lt_cutoff_succ j) ht)
        show (if ((t : I) : ℝ) ≤ cutoff j then _ else _) =
          (if (((1 : I) : I) : ℝ) ≤ cutoff j then _ else _)
        rw [if_neg h1, if_neg (by simpa using (cutoff_lt_one j).not_ge), ramp_eq_one ht,
          ramp_eq_one (by simpa using (cutoff_lt_one (j + 1)).le)]
      · intro i y t
        show (if ((t : I) : ℝ) ≤ cutoff j then _ else _) = _
        by_cases ht : ((t : I) : ℝ) ≤ cutoff j
        · rw [if_pos ht]
          exact hGface i y t
        · rw [if_neg ht, hKb _ (faceMap_mem_bdry i y) _, huface i y]
          exact (s.stab _ y t (le_of_not_ge ht)).symm
  choose Hf hstart hmem hstab hfix hface using main
  exact ⟨⟨Hf, hstart, hstab, fun {f} hf y t => hfix f hf y t, glue_of_face s Hf hface⟩,
    hface, fun f y => hmem f y⟩

/-- **The free recursion step.**  Without any hypothesis on the relative homotopy groups the
homotopies of dimension `j` still extend to dimension `j + 1` — by simply freezing at time
`cutoff j` — but the extension no longer compresses into `A`. -/
theorem exists_freeze {j : ℕ} (s : Step A j) : ∃ s' : Step A (j + 1), IsNext s s' := by
  classical
  have main : ∀ f : C(stdSimplex ℝ (Fin (j + 2)), X),
      ∃ Hf : C(stdSimplex ℝ (Fin (j + 2)) × I, X),
        (∀ y, Hf (y, 0) = f y) ∧
          (∀ y (t : I), cutoff (j + 1) ≤ (t : ℝ) → Hf (y, t) = Hf (y, 1)) ∧
          ((∀ y, f y ∈ A) → ∀ y t, Hf (y, t) = f y) ∧
          (∀ (i : Fin (j + 2)) (y : stdSimplex ℝ (Fin (j + 1))) (t : I),
            Hf (faceMap i y, t) = s.H (f.comp (faceCM i)) (y, t)) := by
    intro f
    by_cases hfA : ∀ y, f y ∈ A
    · refine ⟨⟨fun p => f p.1, f.continuous.comp continuous_fst⟩, fun _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ => rfl, ?_⟩
      intro i y t
      exact (s.fix (f := f.comp (faceCM i)) (fun _ => hfA _) y t).symm
    · obtain ⟨G, hG0, hGface⟩ := exists_face_extension s f
      have hmatch : ∀ p : stdSimplex ℝ (Fin (j + 2)) × I, ((p.2 : I) : ℝ) = cutoff j →
          G p = G (p.1, cutoffI j) := by
        rintro ⟨x, t⟩ ht
        rw [show t = cutoffI j from Subtype.ext ht]
      refine ⟨⟨fun p => if ((p.2 : I) : ℝ) ≤ cutoff j then G p else G (p.1, cutoffI j),
        Continuous.if_le G.continuous
          (G.continuous.comp (continuous_fst.prodMk continuous_const))
          (continuous_subtype_val.comp continuous_snd) continuous_const hmatch⟩,
        ?_, ?_, fun h => absurd h hfA, ?_⟩
      · intro y
        show (if (((0 : I) : I) : ℝ) ≤ cutoff j then _ else _) = f y
        rw [if_pos (by simpa using cutoff_nonneg j)]
        exact hG0 y
      · intro y t ht
        have h1 : ¬ ((t : ℝ) ≤ cutoff j) :=
          not_le.2 (lt_of_lt_of_le (cutoff_lt_cutoff_succ j) ht)
        show (if ((t : I) : ℝ) ≤ cutoff j then _ else _) =
          (if (((1 : I) : I) : ℝ) ≤ cutoff j then _ else _)
        rw [if_neg h1, if_neg (by simpa using (cutoff_lt_one j).not_ge)]
      · intro i y t
        show (if ((t : I) : ℝ) ≤ cutoff j then _ else _) = _
        by_cases ht : ((t : I) : ℝ) ≤ cutoff j
        · rw [if_pos ht]
          exact hGface i y t
        · rw [if_neg ht, hGface i y (cutoffI j), s.stab _ y (cutoffI j) le_rfl]
          exact (s.stab _ y t (le_of_not_ge ht)).symm
  choose Hf hstart hstab hfix hface using main
  exact ⟨⟨Hf, hstart, hstab, fun {f} hf y t => hfix f hf y t, glue_of_face s Hf hface⟩, hface⟩

/-! ### The towers -/

/-- The tower of compressing homotopies. -/
def tower (hA : A.Nonempty) (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a))
    (hpi : ∀ (n : ℕ) (a : A), Nonempty (Unique (π_rel (n + 1) X A a))) :
    (j : ℕ) → {s : Step A j // s.Compresses}
  | 0 => ⟨(exists_base hA h₀).choose, (exists_base hA h₀).choose_spec⟩
  | j + 1 =>
    ⟨(exists_next (tower hA h₀ hpi j).1 (tower hA h₀ hpi j).2 (hpi j)).choose,
      (exists_next (tower hA h₀ hpi j).1 (tower hA h₀ hpi j).2 (hpi j)).choose_spec.2⟩

theorem tower_isNext (hA : A.Nonempty)
    (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a))
    (hpi : ∀ (n : ℕ) (a : A), Nonempty (Unique (π_rel (n + 1) X A a))) (j : ℕ) :
    IsNext (tower hA h₀ hpi j).1 (tower hA h₀ hpi (j + 1)).1 :=
  (exists_next (tower hA h₀ hpi j).1 (tower hA h₀ hpi j).2 (hpi j)).choose_spec.1

/-- Level `j` of the tower truncated at `M`: the homotopies of dimension `j`, compressing into
`A` as long as `j ≤ M`. -/
structure StepLE (A : Set X) (M j : ℕ) where
  /-- The homotopies in dimension `j`. -/
  step : Step A j
  /-- They compress into `A` as long as `j ≤ M`. -/
  compresses : j ≤ M → step.Compresses

/-- The recursion step of the truncated tower: compress while below the bound, freeze after. -/
theorem exists_next_le (M : ℕ)
    (hpi : ∀ n < M, ∀ a : A, Nonempty (Unique (π_rel (n + 1) X A a))) {j : ℕ}
    (s : StepLE A M j) : ∃ s' : StepLE A M (j + 1), IsNext s.step s'.step := by
  by_cases h : j < M
  · obtain ⟨t, ht, htc⟩ := exists_next s.step (s.compresses h.le) (hpi j h)
    exact ⟨⟨t, fun _ => htc⟩, ht⟩
  · obtain ⟨t, ht⟩ := exists_freeze s.step
    exact ⟨⟨t, fun hle => absurd (by omega : j < M) h⟩, ht⟩

/-- The tower of homotopies compressing the simplices of dimension at most `M` into `A`. -/
def towerLE (M : ℕ) (hA : A.Nonempty)
    (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a))
    (hpi : ∀ n < M, ∀ a : A, Nonempty (Unique (π_rel (n + 1) X A a))) : (j : ℕ) → StepLE A M j
  | 0 => ⟨(exists_base hA h₀).choose, fun _ => (exists_base hA h₀).choose_spec⟩
  | j + 1 => (exists_next_le M hpi (towerLE M hA h₀ hpi j)).choose

theorem towerLE_isNext (M : ℕ) (hA : A.Nonempty)
    (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a))
    (hpi : ∀ n < M, ∀ a : A, Nonempty (Unique (π_rel (n + 1) X A a))) (j : ℕ) :
    IsNext (towerLE M hA h₀ hpi j).step (towerLE M hA h₀ hpi (j + 1)).step :=
  (exists_next_le M hpi (towerLE M hA h₀ hpi j)).choose_spec

end Submission
