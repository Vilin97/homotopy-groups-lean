/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Topology.Homotopy.Equiv
import Submission.ForMathlib.HomotopyGroup.Homotopy

/-!
# Change of basepoint and homotopy invariance for higher homotopy groups

Mathlib's `HomotopyGroup N X x` depends on a basepoint, and nothing in Mathlib relates the
groups at two different basepoints, nor shows that a homotopy equivalence induces an
isomorphism. This file supplies both, for an arbitrary nonempty index type `N` (in particular
in every dimension `n ≥ 1`).

The engine is the classical *collar* construction. Write `cubeRadius` for the sup-distance of a
point of the cube `I^N` from the centre, normalized so that the boundary has radius `1`. Given a
path `γ : Path x y` and a generalized loop `p : Ω^ N X x`, `transportFun` squeezes `p` into the
subcube of radius `1 - s/2` at time `s`, letting the surrounding collar traverse `γ` up to time
`s`. At `s = 1` this produces `GenLoop.transport γ p : Ω^ N X y`, and the whole family is a
homotopy from `p` to `GenLoop.transport γ p` which drags the cube boundary along `γ`.

The relation "`p` and `q` are joined by a homotopy dragging the boundary along a path homotopic
to `γ`" is `GenLoop.HomotopicAlong`. It is reflexive, symmetric and transitive in the obvious
sense, it is compatible with concatenation of generalized loops
(`GenLoop.homotopicAlong'_transAt`), and — the only real theorem here — a homotopy dragging the
boundary along a *nullhomotopic* loop can be replaced by a homotopy *relative* to the boundary
(`GenLoop.homotopic_of_homotopicAlong_refl`). That last statement is again proved by a collar
argument, gluing the given homotopy to a nullhomotopy of its boundary loop. It immediately gives
uniqueness of transport, hence that transport is a well-defined group isomorphism.

## Main declarations

* `Submission.GenLoop.transport`: transport of a generalized loop along a path.
* `Submission.HomotopyGroup.transportMulEquiv`: the basepoint-change isomorphism
  `π_N(X, x) ≃* π_N(X, y)` attached to a path `γ : Path x y`.
* `Submission.nonempty_mulEquiv_of_joined`: its existential form.
* `Submission.nonempty_mulEquiv_of_pathConnectedSpace`: in a path-connected space all the
  homotopy groups in a fixed dimension are isomorphic.
* `Submission.nonempty_mulEquiv_of_homotopyEquiv`,
  `Submission.nonempty_mulEquiv_of_homotopyEquiv'`: a homotopy equivalence induces isomorphisms
  on all positive-dimensional homotopy groups, with no hypothesis on basepoints.

## Implementation notes

The collar construction needs `N` to be finite: for infinite `N` the set `Cube.boundary N` is
dense in `I^N`, so there is no continuous radial coordinate at all. That degenerate case is not
lost, though — density also forces every homotopy group to be trivial
(`Submission.subsingleton_homotopyGroup_of_infinite`), so the final statements need no
finiteness hypothesis.
-/

namespace Submission

open scoped unitInterval Topology Topology.Homotopy

/-! ### Rescaling a subcube onto the whole cube -/

section CubeScale

variable {N : Type*}

/-- Rescale the subcube `[s/4, 1 - s/4]^N` onto the whole cube `I^N`. Points outside the
subcube are clamped onto the boundary. -/
noncomputable def cubeScale (s : I) (t : I^N) : I^N := fun i =>
  Set.projIcc 0 1 zero_le_one (((t i : ℝ) - (s : ℝ) / 4) / (1 - (s : ℝ) / 2))

theorem continuous_cubeScale : Continuous fun st : I × I^N => cubeScale st.1 st.2 := by
  refine continuous_pi fun i => continuous_projIcc.comp (Continuous.div ?_ ?_ fun st => ?_)
  · fun_prop
  · fun_prop
  · have h1 := unitInterval.le_one st.1
    have h2 : (0 : ℝ) < 1 - (st.1 : ℝ) / 2 := by linarith
    exact h2.ne'

@[simp]
theorem cubeScale_zero (t : I^N) : cubeScale 0 t = t := by
  funext i
  have h : ((t i : ℝ) - ((0 : I) : ℝ) / 4) / (1 - ((0 : I) : ℝ) / 2) = (t i : ℝ) := by
    norm_num
  rw [cubeScale, h, Set.projIcc_val]

end CubeScale

/-! ### The radial coordinate of a cube -/

section CubeRadius

variable {N : Type*} [Fintype N] [Nonempty N]

/-- The scaled sup-distance of a point of the cube `I^N` from the centre: it is `0` at the
centre and `1` exactly on the boundary `Cube.boundary N`. -/
noncomputable def cubeRadius (t : I^N) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |2 * (t i : ℝ) - 1|

theorem continuous_cubeRadius : Continuous (cubeRadius (N := N)) :=
  Continuous.finset_sup'_apply _ fun i _ => by fun_prop

theorem abs_le_cubeRadius (t : I^N) (i : N) : |2 * (t i : ℝ) - 1| ≤ cubeRadius t :=
  Finset.le_sup' (fun i => |2 * (t i : ℝ) - 1|) (Finset.mem_univ i)

theorem cubeRadius_le_one (t : I^N) : cubeRadius t ≤ 1 :=
  Finset.sup'_le _ (fun i => |2 * (t i : ℝ) - 1|) fun i _ => by
    rw [abs_le]
    have h₀ := unitInterval.nonneg (t i)
    have h₁ := unitInterval.le_one (t i)
    constructor <;> linarith

theorem exists_abs_eq_cubeRadius (t : I^N) : ∃ i, |2 * (t i : ℝ) - 1| = cubeRadius t := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := N)) fun i => |2 * (t i : ℝ) - 1|
  exact ⟨i, hi.symm⟩

theorem cubeRadius_eq_one_of_mem_boundary {t : I^N} (ht : t ∈ Cube.boundary N) :
    cubeRadius t = 1 := by
  obtain ⟨i, hi⟩ := ht
  refine le_antisymm (cubeRadius_le_one t) ?_
  have h := abs_le_cubeRadius t i
  rcases hi with hi | hi <;> rw [hi] at h <;> norm_num at h <;> linarith

theorem cubeScale_mem_boundary {s : I} {t : I^N} (h : cubeRadius t = 1 - (s : ℝ) / 2) :
    cubeScale s t ∈ Cube.boundary N := by
  have hs1 := unitInterval.le_one s
  have hs0 := unitInterval.nonneg s
  have hden : (0 : ℝ) < 1 - (s : ℝ) / 2 := by linarith
  obtain ⟨i, hi⟩ := exists_abs_eq_cubeRadius t
  rw [h] at hi
  refine ⟨i, ?_⟩
  rcases (abs_eq hden.le).mp hi with h1 | h1
  · right
    have hq : ((t i : ℝ) - (s : ℝ) / 4) / (1 - (s : ℝ) / 2) = 1 := by
      rw [div_eq_one_iff_eq hden.ne']; linarith
    apply Subtype.ext
    simp [cubeScale, hq, Set.projIcc]
  · left
    have hq : ((t i : ℝ) - (s : ℝ) / 4) / (1 - (s : ℝ) / 2) = 0 := by
      rw [div_eq_zero_iff]; left; linarith
    apply Subtype.ext
    simp [cubeScale, hq, Set.projIcc]

end CubeRadius

/-! ### Transporting a generalized loop along a path -/

section Transport

variable {N : Type*} [Fintype N] [Nonempty N]
variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- The underlying map of the transport homotopy: at time `s` the generalized loop `p` is
squeezed into the subcube of radius `1 - s / 2`, and the surrounding collar traverses the
initial segment of the path `γ` up to time `s`. -/
noncomputable def transportFun (γ : Path x y) (p : Ω^ N X x) (st : I × I^N) : X :=
  if cubeRadius st.2 ≤ 1 - (st.1 : ℝ) / 2 then p (cubeScale st.1 st.2)
  else γ (Set.projIcc 0 1 zero_le_one (2 * cubeRadius st.2 - 2 + (st.1 : ℝ)))

theorem continuous_transportFun (γ : Path x y) (p : Ω^ N X x) :
    Continuous (transportFun γ p) := by
  have hr : Continuous fun st : I × I^N => cubeRadius st.2 :=
    continuous_cubeRadius.comp continuous_snd
  have hs : Continuous fun st : I × I^N => (st.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  refine Continuous.if_le ((p : C(I^N, X)).continuous.comp continuous_cubeScale)
    (γ.continuous.comp (continuous_projIcc.comp
      (((hr.const_mul 2).sub continuous_const).add hs))) hr ?_ ?_
  · exact continuous_const.sub (hs.div_const 2)
  · intro st h
    have hb : cubeScale st.1 st.2 ∈ Cube.boundary N := cubeScale_mem_boundary h
    have h0 : 2 * cubeRadius st.2 - 2 + (st.1 : ℝ) = 0 := by rw [h]; ring
    have h1 : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := Subtype.ext (by simp [Set.projIcc])
    rw [GenLoop.boundary p _ hb, h0, h1, γ.source]

theorem transportFun_zero (γ : Path x y) (p : Ω^ N X x) (t : I^N) :
    transportFun γ p (0, t) = p t := by
  have h : cubeRadius t ≤ 1 - ((0 : I) : ℝ) / 2 := by
    show cubeRadius t ≤ 1 - (0 : ℝ) / 2
    linarith [cubeRadius_le_one t]
  simp only [transportFun, if_pos h, cubeScale_zero]

theorem transportFun_boundary (γ : Path x y) (p : Ω^ N X x) (s : I) {t : I^N}
    (ht : t ∈ Cube.boundary N) : transportFun γ p (s, t) = γ s := by
  have hr : cubeRadius t = 1 := cubeRadius_eq_one_of_mem_boundary ht
  by_cases h : cubeRadius t ≤ 1 - (s : ℝ) / 2
  · rw [hr] at h
    have hs : s = 0 := by
      have h2 : (0 : ℝ) ≤ (s : ℝ) := unitInterval.nonneg s
      ext
      show (s : ℝ) = 0
      linarith
    subst hs
    rw [transportFun_zero, GenLoop.boundary p t ht, γ.source]
  · simp only [transportFun]
    rw [if_neg h, hr]
    have h2 : (2 : ℝ) * 1 - 2 + (s : ℝ) = (s : ℝ) := by ring
    rw [h2, Set.projIcc_val]

/-- The transport of a generalized loop based at `x` along a path `γ : Path x y`: a
generalized loop based at `y`. -/
noncomputable def GenLoop.transport (γ : Path x y) (p : Ω^ N X x) : Ω^ N X y :=
  ⟨⟨fun t => transportFun γ p (1, t),
      (continuous_transportFun γ p).comp (continuous_const.prodMk continuous_id)⟩,
    fun _ ht => (transportFun_boundary γ p 1 ht).trans γ.target⟩

@[simp]
theorem GenLoop.transport_apply (γ : Path x y) (p : Ω^ N X x) (t : I^N) :
    GenLoop.transport γ p t = transportFun γ p (1, t) :=
  rfl

/-- The homotopy from `p` to its transport along `γ`, which moves the cube boundary along
`γ`. -/
noncomputable def transportHomotopy (γ : Path x y) (p : Ω^ N X x) :
    ContinuousMap.Homotopy (p : C(I^N, X)) ((GenLoop.transport γ p : Ω^ N X y) : C(I^N, X)) where
  toFun := transportFun γ p
  continuous_toFun := continuous_transportFun γ p
  map_zero_left := transportFun_zero γ p
  map_one_left _ := rfl

end Transport

/-! ### Homotopy along a path -/

section Along

variable {N : Type*} {X : Type*} [TopologicalSpace X] {x y z : X}

/-- `HomotopicAlong' δ p q` says that there is a homotopy of maps `I^N → X` from `p` to `q`
whose restriction to the cube boundary is exactly the path `δ`. -/
def GenLoop.HomotopicAlong' (δ : Path x y) (p : Ω^ N X x) (q : Ω^ N X y) : Prop :=
  ∃ H : ContinuousMap.Homotopy (p : C(I^N, X)) (q : C(I^N, X)),
    ∀ (s : I) (t : I^N), t ∈ Cube.boundary N → H (s, t) = δ s

/-- `HomotopicAlong γ p q` says that `p` and `q` are joined by a homotopy which drags the cube
boundary along a path homotopic to `γ`. This is the higher-dimensional analogue of conjugating
a loop by a path. -/
def GenLoop.HomotopicAlong (γ : Path x y) (p : Ω^ N X x) (q : Ω^ N X y) : Prop :=
  ∃ δ : Path x y, δ.Homotopic γ ∧ GenLoop.HomotopicAlong' δ p q

namespace GenLoop

variable {p : Ω^ N X x} {q : Ω^ N X y} {r : Ω^ N X z}

theorem HomotopicAlong'.homotopicAlong {δ γ : Path x y} (h : HomotopicAlong' δ p q)
    (hδ : δ.Homotopic γ) : HomotopicAlong γ p q :=
  ⟨δ, hδ, h⟩

theorem HomotopicAlong.mono {γ γ' : Path x y} (h : HomotopicAlong γ p q)
    (hγ : γ.Homotopic γ') : HomotopicAlong γ' p q :=
  let ⟨δ, hδ, hH⟩ := h
  ⟨δ, hδ.trans hγ, hH⟩

theorem HomotopicAlong'.symm {δ : Path x y} (h : HomotopicAlong' δ p q) :
    HomotopicAlong' δ.symm q p := by
  obtain ⟨H, hH⟩ := h
  exact ⟨H.symm, fun s t ht => hH _ t ht⟩

theorem HomotopicAlong.symm {γ : Path x y} (h : HomotopicAlong γ p q) :
    HomotopicAlong γ.symm q p :=
  let ⟨δ, hδ, hH⟩ := h
  ⟨δ.symm, hδ.symm₂, hH.symm⟩

theorem HomotopicAlong'.trans {δ : Path x y} {δ' : Path y z} (h : HomotopicAlong' δ p q)
    (h' : HomotopicAlong' δ' q r) : HomotopicAlong' (δ.trans δ') p r := by
  obtain ⟨H, hH⟩ := h
  obtain ⟨H', hH'⟩ := h'
  refine ⟨H.trans H', fun s t ht => ?_⟩
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs with hs
  · exact hH _ t ht
  · exact hH' _ t ht

theorem HomotopicAlong.trans {γ : Path x y} {γ' : Path y z} (h : HomotopicAlong γ p q)
    (h' : HomotopicAlong γ' q r) : HomotopicAlong (γ.trans γ') p r :=
  let ⟨δ, hδ, hH⟩ := h
  let ⟨δ', hδ', hH'⟩ := h'
  ⟨δ.trans δ', Path.Homotopic.hcomp hδ hδ', hH.trans hH'⟩

theorem homotopicAlong'_refl_of_homotopic {p q : Ω^ N X x}
    (h : _root_.GenLoop.Homotopic p q) :
    HomotopicAlong' (Path.refl x) p q := by
  obtain ⟨H⟩ := h
  exact ⟨H.toHomotopy, fun s t ht => (H.eq_fst s ht).trans (GenLoop.boundary p t ht)⟩

theorem homotopic_of_homotopicAlong'_refl {p q : Ω^ N X x}
    (h : HomotopicAlong' (Path.refl x) p q) : _root_.GenLoop.Homotopic p q := by
  obtain ⟨H, hH⟩ := h
  exact ⟨{ toHomotopy := H
           prop' := fun s t ht => (hH s t ht).trans (GenLoop.boundary p t ht).symm }⟩

variable [Fintype N] [Nonempty N]

theorem homotopicAlong'_transport (γ : Path x y) (p : Ω^ N X x) :
    HomotopicAlong' γ p (transport γ p) :=
  ⟨transportHomotopy γ p, fun s _ ht => transportFun_boundary γ p s ht⟩

theorem homotopicAlong_transport (γ : Path x y) (p : Ω^ N X x) :
    HomotopicAlong γ p (transport γ p) :=
  (homotopicAlong'_transport γ p).homotopicAlong (Path.Homotopic.refl γ)

theorem homotopic_transport_refl (p : Ω^ N X x) :
    _root_.GenLoop.Homotopic p (transport (Path.refl x) p) :=
  homotopic_of_homotopicAlong'_refl (homotopicAlong'_transport (Path.refl x) p)

/-- **The filling lemma.** If a homotopy drags the cube boundary along a nullhomotopic loop,
then the two generalized loops are homotopic relative to the cube boundary.

The homotopy `H` is glued to a nullhomotopy `G` of its boundary loop along a collar of the
cube: on the inner subcube of radius `1/2` one runs `H` (suitably rescaled), on the outer
collar one runs `G` in the radial direction. The result is a homotopy relative to the boundary
between the two "shrunken" loops, which are in turn homotopic to the originals. -/
theorem homotopic_of_homotopicAlong_refl {p q : Ω^ N X x}
    (h : HomotopicAlong (Path.refl x) p q) : _root_.GenLoop.Homotopic p q := by
  obtain ⟨δ, hδ, H, hH⟩ := h
  obtain ⟨G⟩ := hδ
  have hone : ((1 : I) : ℝ) = 1 := rfl
  have hzero : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := Subtype.ext (by simp [Set.projIcc])
  have hoone : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := Subtype.ext (by simp [Set.projIcc])
  have hm0 : (0 : I) ∈ ({0, 1} : Set I) := Set.mem_insert _ _
  have hm1 : (1 : I) ∈ ({0, 1} : Set I) := Set.mem_insert_of_mem _ rfl
  have hr : Continuous fun st : I × I^N => cubeRadius st.2 :=
    continuous_cubeRadius.comp continuous_snd
  have key : _root_.GenLoop.Homotopic (transport (Path.refl x) p) (transport (Path.refl x) q) := by
    refine ⟨⟨⟨⟨fun st =>
        if cubeRadius st.2 ≤ 1 - ((1 : I) : ℝ) / 2 then H (st.1, cubeScale 1 st.2)
        else G (Set.projIcc 0 1 zero_le_one (2 * cubeRadius st.2 - 2 + ((1 : I) : ℝ)), st.1),
      ?_⟩, ?_, ?_⟩, ?_⟩⟩
    · refine Continuous.if_le (H.continuous.comp (continuous_fst.prodMk
        (continuous_cubeScale.comp (continuous_const.prodMk continuous_snd))))
        (G.continuous.comp ((continuous_projIcc.comp
          (((hr.const_mul 2).sub continuous_const).add continuous_const)).prodMk
          continuous_fst)) hr continuous_const fun st h => ?_
      have hb : cubeScale 1 st.2 ∈ Cube.boundary N := cubeScale_mem_boundary h
      have h0 : 2 * cubeRadius st.2 - 2 + ((1 : I) : ℝ) = 0 := by rw [h, hone]; ring
      rw [hH st.1 _ hb, h0, hzero, G.apply_zero]
      rfl
    · intro t
      show _ = transportFun (Path.refl x) p (1, t)
      simp only [transportFun]
      split_ifs with hcase
      · exact H.apply_zero _
      · rw [G.eq_fst _ hm0]
        exact δ.source
    · intro t
      show _ = transportFun (Path.refl x) q (1, t)
      simp only [transportFun]
      split_ifs with hcase
      · exact H.apply_one _
      · rw [G.eq_fst _ hm1]
        exact δ.target
    · intro s t ht
      have hrad : cubeRadius t = 1 := cubeRadius_eq_one_of_mem_boundary ht
      have hne : ¬ cubeRadius t ≤ 1 - ((1 : I) : ℝ) / 2 := by rw [hrad, hone]; norm_num
      have h1 : 2 * cubeRadius t - 2 + ((1 : I) : ℝ) = 1 := by rw [hrad, hone]; ring
      show (if cubeRadius t ≤ 1 - ((1 : I) : ℝ) / 2 then _ else _) = _
      rw [if_neg hne, h1, hoone, G.apply_one]
      exact (GenLoop.boundary (transport (Path.refl x) p) t ht).symm
  exact (homotopic_transport_refl p).trans (key.trans (homotopic_transport_refl q).symm)

/-- Transport along a path is unique up to homotopy relative to the cube boundary. -/
theorem HomotopicAlong.unique {γ : Path x y} {p : Ω^ N X x} {q q' : Ω^ N X y}
    (h : HomotopicAlong γ p q) (h' : HomotopicAlong γ p q') : _root_.GenLoop.Homotopic q q' :=
  homotopic_of_homotopicAlong_refl
    ((h.symm.trans h').mono (Path.Homotopic.symm_trans γ))

end GenLoop

namespace GenLoop

variable {p : Ω^ N X x} {q : Ω^ N X y}

/-- The constant generalized loops at the two endpoints of a path are homotopic along it. -/
theorem homotopicAlong'_const (γ : Path x y) :
    HomotopicAlong' γ (_root_.GenLoop.const : Ω^ N X x) (_root_.GenLoop.const : Ω^ N X y) :=
  ⟨⟨⟨fun st => γ st.1, γ.continuous.comp continuous_fst⟩, fun _ => γ.source,
    fun _ => γ.target⟩, fun _ _ _ => rfl⟩

variable [DecidableEq N]

theorem update_mem_boundary_of_le {t : I^N} (ht : t ∈ Cube.boundary N) {i : N}
    (h : (t i : ℝ) ≤ 1 / 2) :
    Function.update t i (Set.projIcc 0 1 zero_le_one (2 * (t i : ℝ))) ∈ Cube.boundary N := by
  obtain ⟨j, hj⟩ := ht
  by_cases hji : j = i
  · subst hji
    rcases hj with hj | hj
    · refine ⟨j, Or.inl ?_⟩
      rw [Function.update_self, hj]
      exact Subtype.ext (by norm_num [Set.projIcc])
    · exact absurd h (by rw [hj]; norm_num)
  · exact ⟨j, by rwa [Function.update_of_ne hji]⟩

theorem update_mem_boundary_of_not_le {t : I^N} (ht : t ∈ Cube.boundary N) {i : N}
    (h : ¬ (t i : ℝ) ≤ 1 / 2) :
    Function.update t i (Set.projIcc 0 1 zero_le_one (2 * (t i : ℝ) - 1)) ∈ Cube.boundary N := by
  obtain ⟨j, hj⟩ := ht
  by_cases hji : j = i
  · subst hji
    rcases hj with hj | hj
    · exact absurd (by rw [hj]; norm_num : ((t j : ℝ)) ≤ 1 / 2) h
    · refine ⟨j, Or.inr ?_⟩
      rw [Function.update_self, hj]
      exact Subtype.ext (by norm_num [Set.projIcc])
  · exact ⟨j, by rwa [Function.update_of_ne hji]⟩

/-- Homotopy along a path is compatible with concatenation of generalized loops. -/
theorem homotopicAlong'_transAt {δ : Path x y} (i : N) {p₁ p₂ : Ω^ N X x} {q₁ q₂ : Ω^ N X y}
    (h₁ : HomotopicAlong' δ p₁ q₁) (h₂ : HomotopicAlong' δ p₂ q₂) :
    HomotopicAlong' δ (_root_.GenLoop.transAt i p₁ p₂) (_root_.GenLoop.transAt i q₁ q₂) := by
  obtain ⟨H₁, hH₁⟩ := h₁
  obtain ⟨H₂, hH₂⟩ := h₂
  have hi : Continuous fun st : I × I^N => ((st.2 i : ℝ)) :=
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
  refine ⟨⟨⟨fun st => if ((st.2 i : ℝ)) ≤ 1 / 2
      then H₁ (st.1, Function.update st.2 i (Set.projIcc 0 1 zero_le_one (2 * (st.2 i : ℝ))))
      else H₂ (st.1, Function.update st.2 i (Set.projIcc 0 1 zero_le_one (2 * (st.2 i : ℝ) - 1))),
    ?_⟩, ?_, ?_⟩, ?_⟩
  · refine Continuous.if_le
      (H₁.continuous.comp (continuous_fst.prodMk
        (continuous_snd.update i (continuous_projIcc.comp (hi.const_mul 2)))))
      (H₂.continuous.comp (continuous_fst.prodMk
        (continuous_snd.update i (continuous_projIcc.comp ((hi.const_mul 2).sub
          continuous_const))))) hi continuous_const fun st h => ?_
    have e₁ : Function.update st.2 i (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (st.2 i : ℝ)))
        ∈ Cube.boundary N := ⟨i, Or.inr (by
      rw [Function.update_self, h]
      exact Subtype.ext (by norm_num [Set.projIcc]))⟩
    have e₂ : Function.update st.2 i (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (st.2 i : ℝ) - 1))
        ∈ Cube.boundary N := ⟨i, Or.inl (by
      rw [Function.update_self, h]
      exact Subtype.ext (by norm_num [Set.projIcc]))⟩
    rw [hH₁ st.1 _ e₁, hH₂ st.1 _ e₂]
  · intro t
    show _ = _root_.GenLoop.transAt i p₁ p₂ t
    simp only [_root_.GenLoop.transAt, _root_.GenLoop.coe_copy]
    split_ifs with hcase
    · exact H₁.apply_zero _
    · exact H₂.apply_zero _
  · intro t
    show _ = _root_.GenLoop.transAt i q₁ q₂ t
    simp only [_root_.GenLoop.transAt, _root_.GenLoop.coe_copy]
    split_ifs with hcase
    · exact H₁.apply_one _
    · exact H₂.apply_one _
  · intro s t ht
    show (if ((t i : ℝ)) ≤ 1 / 2 then _ else _) = _
    split_ifs with hcase
    · exact hH₁ s _ (update_mem_boundary_of_le ht hcase)
    · exact hH₂ s _ (update_mem_boundary_of_not_le ht hcase)

end GenLoop

end Along

/-! ### Change of basepoint -/

section BasepointChange

variable {N : Type*} [Fintype N] [Nonempty N] [DecidableEq N]
variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- Transport of homotopy classes along a path `γ : Path x y`. -/
noncomputable def HomotopyGroup.transport (γ : Path x y) :
    HomotopyGroup N X x → HomotopyGroup N X y :=
  Quotient.map (GenLoop.transport γ) fun p p' h =>
    (GenLoop.homotopicAlong_transport γ p).unique
      ((((GenLoop.homotopicAlong'_refl_of_homotopic h).homotopicAlong
          (Path.Homotopic.refl (Path.refl x))).trans
        (GenLoop.homotopicAlong_transport γ p')).mono (Path.Homotopic.refl_trans γ))

omit [DecidableEq N] in
@[simp]
theorem HomotopyGroup.transport_mk (γ : Path x y) (p : Ω^ N X x) :
    HomotopyGroup.transport γ (⟦p⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.transport γ p⟧ : HomotopyGroup N X y) :=
  rfl

/-- Transporting homotopy classes along a path is a group homomorphism. -/
noncomputable def HomotopyGroup.transportHom (γ : Path x y) :
    HomotopyGroup N X x →* HomotopyGroup N X y where
  toFun := HomotopyGroup.transport γ
  map_one' :=
    Quotient.sound ((GenLoop.homotopicAlong_transport γ _).unique
      ((GenLoop.homotopicAlong'_const γ).homotopicAlong (Path.Homotopic.refl γ)))
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    have key : _root_.GenLoop.Homotopic
        (GenLoop.transport γ (_root_.GenLoop.transAt (Classical.arbitrary N) q p))
        (_root_.GenLoop.transAt (Classical.arbitrary N) (GenLoop.transport γ q)
          (GenLoop.transport γ p)) :=
      (GenLoop.homotopicAlong_transport γ _).unique
        ((GenLoop.homotopicAlong'_transAt _ (GenLoop.homotopicAlong'_transport γ q)
          (GenLoop.homotopicAlong'_transport γ p)).homotopicAlong (Path.Homotopic.refl γ))
    simp only [HomotopyGroup.transport_mk,
      _root_.HomotopyGroup.mul_spec (i := Classical.arbitrary N)]
    exact Quotient.sound key

/-- **Change of basepoint.** A path `γ : Path x y` induces an isomorphism of homotopy groups
`π_N(X, x) ≃* π_N(X, y)`, in every positive dimension. -/
noncomputable def HomotopyGroup.transportMulEquiv (γ : Path x y) :
    HomotopyGroup N X x ≃* HomotopyGroup N X y where
  toFun := HomotopyGroup.transport γ
  invFun := HomotopyGroup.transport γ.symm
  map_mul' := (HomotopyGroup.transportHom γ).map_mul
  left_inv a := by
    refine Quotient.inductionOn a fun p => ?_
    exact Quotient.sound (GenLoop.homotopic_of_homotopicAlong_refl
      (((GenLoop.homotopicAlong_transport γ p).trans
        (GenLoop.homotopicAlong_transport γ.symm _)).mono
        (Path.Homotopic.trans_symm γ))).symm
  right_inv a := by
    refine Quotient.inductionOn a fun p => ?_
    exact Quotient.sound (GenLoop.homotopic_of_homotopicAlong_refl
      (((GenLoop.homotopicAlong_transport γ.symm p).trans
        (GenLoop.homotopicAlong_transport γ _)).mono
        (Path.Homotopic.symm_trans γ))).symm

@[simp]
theorem HomotopyGroup.transportMulEquiv_apply (γ : Path x y) (a : HomotopyGroup N X x) :
    HomotopyGroup.transportMulEquiv γ a = HomotopyGroup.transport γ a :=
  rfl

end BasepointChange

/-! ### The zero-dimensional homotopy group of a path-connected space -/

/-- In dimension zero the cube boundary is empty, so a generalized loop is just a point of `X` and
its class is its path component.  Hence `π₀` of a path-connected space is a subsingleton. -/
theorem subsingleton_homotopyGroup_zero {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (x : X) : Subsingleton (HomotopyGroup (Fin 0) X x) := by
  refine ⟨fun a b => Quotient.inductionOn₂ a b fun p q => Quotient.sound ?_⟩
  obtain ⟨γ⟩ := PathConnectedSpace.joined (p (fun _ => 0)) (q (fun _ => 0))
  refine ⟨⟨⟨⟨fun st => γ st.1, by fun_prop⟩, fun y => ?_, fun y => ?_⟩, fun s t ht => ?_⟩⟩
  · show γ 0 = p y
    rw [γ.source]
    exact congrArg p (funext fun i => i.elim0)
  · show γ 1 = q y
    rw [γ.target]
    exact congrArg q (funext fun i => i.elim0)
  · exact absurd ht (by simp [Cube.boundary])

/-! ### Infinite index types

For an infinite index type the cube boundary `Cube.boundary N` is *dense* in `I^N`, so a
generalized loop takes all its values in `closure {x}` and the homotopy group is trivial. This
degenerate case is recorded here so that the change-of-basepoint theorem can be stated without
a finiteness hypothesis. -/

section Infinite

variable {N : Type*} [Infinite N] {X : Type*} [TopologicalSpace X] {x : X}

/-- For an infinite index type the boundary of the cube is dense: any basic open set constrains
only finitely many coordinates, so one more coordinate can be pushed to `0`. -/
theorem dense_cubeBoundary : Dense (Cube.boundary N) := by
  classical
  rw [dense_iff_inter_open]
  rintro U hU ⟨t, htU⟩
  obtain ⟨s, u, hu, hsub⟩ := isOpen_pi_iff.mp hU t htU
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset s
  refine ⟨Function.update t j 0, hsub fun i hi => ?_, ⟨j, Or.inl (by simp)⟩⟩
  rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
  exact (hu i hi).2

theorem GenLoop.mem_closure_singleton (f : Ω^ N X x) (t : I^N) :
    f t ∈ closure ({x} : Set X) := by
  have himg : (fun z : I^N => f z) '' Cube.boundary N ⊆ ({x} : Set X) := by
    rintro _ ⟨t', ht', rfl⟩
    exact GenLoop.boundary f t' ht'
  refine closure_mono himg (image_closure_subset_closure_image
    (map_continuous (f : C(I^N, X))) ⟨t, dense_cubeBoundary t, rfl⟩)

theorem GenLoop.continuous_contract (f : Ω^ N X x) :
    Continuous fun st : I × I^N => if st.1 = 0 then f st.2 else x := by
  rw [continuous_def]
  intro U hU
  by_cases hxU : x ∈ U
  · have hset : (fun st : I × I^N => if st.1 = 0 then f st.2 else x) ⁻¹' U =
        (Set.univ ×ˢ ((fun t : I^N => f t) ⁻¹' U)) ∪ ((({0} : Set I)ᶜ) ×ˢ Set.univ) := by
      ext st
      by_cases hs : st.1 = 0 <;> simp [Set.mem_prod, hs, hxU]
    rw [hset]
    exact (isOpen_univ.prod (hU.preimage (map_continuous (f : C(I^N, X))))).union
      (isOpen_compl_singleton.prod isOpen_univ)
  · have hset : (fun st : I × I^N => if st.1 = 0 then f st.2 else x) ⁻¹' U = ∅ := by
      ext st
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      by_cases hs : st.1 = 0
      · rw [if_pos hs]
        intro hmem
        obtain ⟨w, hwU, hw⟩ :=
          mem_closure_iff.mp (GenLoop.mem_closure_singleton f st.2) U hU hmem
        exact hxU (Set.mem_singleton_iff.mp hw ▸ hwU)
      · rw [if_neg hs]
        exact hxU
    rw [hset]
    exact isOpen_empty

/-- Over an infinite index type every generalized loop is nullhomotopic relative to the cube
boundary. -/
theorem GenLoop.homotopic_const_of_infinite (f : Ω^ N X x) :
    _root_.GenLoop.Homotopic f (_root_.GenLoop.const : Ω^ N X x) := by
  have h1 : (1 : I) ≠ 0 := fun h => by simpa using congrArg Subtype.val h
  refine ⟨⟨⟨⟨fun st => if st.1 = 0 then f st.2 else x, GenLoop.continuous_contract f⟩,
    fun t => by simp, fun t => ?_⟩, fun s t ht => ?_⟩⟩
  · show (if (1 : I) = 0 then f t else x) = _
    rw [if_neg h1]
    exact _root_.GenLoop.const_apply.symm
  · show (if s = 0 then f t else x) = _
    have hb : f t = x := GenLoop.boundary f t ht
    split_ifs
    · rfl
    · exact hb.symm

/-- Over an infinite index type all homotopy groups are trivial. -/
theorem subsingleton_homotopyGroup_of_infinite : Subsingleton (HomotopyGroup N X x) := by
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b fun p q => ?_
  exact Quotient.sound ((GenLoop.homotopic_const_of_infinite p).trans
    (GenLoop.homotopic_const_of_infinite q).symm)

end Infinite

/-- **Change of basepoint, existential form.** If `x` and `y` are joined by a path in `X`, the
homotopy groups of `X` at `x` and at `y` are isomorphic, in every positive dimension. -/
theorem nonempty_mulEquiv_of_joined {N : Type*} [DecidableEq N] [Nonempty N]
    {X : Type*} [TopologicalSpace X] {x y : X} (h : Joined x y) :
    Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N X y) := by
  cases finite_or_infinite N with
  | inl _ =>
    have : Fintype N := Fintype.ofFinite N
    exact h.elim fun γ => ⟨HomotopyGroup.transportMulEquiv γ⟩
  | inr _ =>
    have hx : Subsingleton (HomotopyGroup N X x) := subsingleton_homotopyGroup_of_infinite
    have hy : Subsingleton (HomotopyGroup N X y) := subsingleton_homotopyGroup_of_infinite
    exact ⟨⟨⟨fun _ => 1, fun _ => 1, fun _ => hx.allEq _ _, fun _ => hy.allEq _ _⟩,
      fun _ _ => hy.allEq _ _⟩⟩

/-- In a path-connected space all the homotopy groups (in a fixed positive dimension) are
isomorphic, whatever the basepoint. -/
theorem nonempty_mulEquiv_of_pathConnectedSpace {N : Type*} [DecidableEq N] [Nonempty N]
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x y : X) :
    Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N X y) :=
  nonempty_mulEquiv_of_joined (PathConnectedSpace.joined x y)

/-! ### Homotopy invariance -/

section HomotopyInvariance

variable {N : Type*} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A free homotopy `G` from `u` to `v` makes the two postcompositions of a generalized loop
homotopic along the path traced out by the basepoint. -/
theorem GenLoop.homotopicAlong'_map {u v : C(X, Y)} (G : ContinuousMap.Homotopy u v) (x : X)
    (p : Ω^ N X x) :
    GenLoop.HomotopicAlong' (G.evalAt x) (GenLoop.map u rfl p) (GenLoop.map v rfl p) := by
  have hc : Continuous fun st : I × I^N => G (st.1, p st.2) := by
    refine G.continuous.comp (continuous_fst.prodMk ?_)
    exact (p : C(I^N, X)).continuous.comp continuous_snd
  refine ⟨⟨⟨fun st => G (st.1, p st.2), hc⟩, fun _ => G.apply_zero _, fun _ => G.apply_one _⟩,
    fun s t ht => ?_⟩
  show G (s, p t) = G (s, x)
  rw [GenLoop.boundary p t ht]

variable [Fintype N] [Nonempty N]

/-- Freely homotopic maps induce the same map on homotopy groups, up to transporting the
basepoint along the path traced out by the homotopy. -/
theorem HomotopyGroup.transport_map_homotopy {u v : C(X, Y)} (G : ContinuousMap.Homotopy u v)
    (x : X) (a : HomotopyGroup N X x) :
    HomotopyGroup.transport (G.evalAt x) (HomotopyGroup.map u rfl a) =
      HomotopyGroup.map v rfl a := by
  refine Quotient.inductionOn a fun p => ?_
  exact Quotient.sound ((GenLoop.homotopicAlong_transport (G.evalAt x) _).unique
    ((GenLoop.homotopicAlong'_map G x p).homotopicAlong (Path.Homotopic.refl _)))

end HomotopyInvariance

/-- Auxiliary form of `Submission.nonempty_mulEquiv_of_homotopyEquiv` for a finite index
type, where the collar construction is available. -/
private theorem nonempty_mulEquiv_of_homotopyEquiv_aux {N : Type*} [DecidableEq N] [Nonempty N]
    [Finite N] {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (g : C(Y, X))
    (hgf : (g.comp f).Homotopic (ContinuousMap.id X))
    (hfg : (f.comp g).Homotopic (ContinuousMap.id Y)) (x : X) :
    Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N Y (f x)) := by
  have : Fintype N := Fintype.ofFinite N
  obtain ⟨G⟩ := hgf
  obtain ⟨G'⟩ := hfg
  have key1 : ∀ a : HomotopyGroup N X x,
      HomotopyGroup.transport (G.evalAt x)
        (HomotopyGroup.map g rfl (HomotopyGroup.map f rfl a)) = a := by
    intro a
    have h := HomotopyGroup.transport_map_homotopy (N := N) G x a
    rw [HomotopyGroup.map_id_apply] at h
    rw [HomotopyGroup.map_comp_apply]
    exact h
  have key2 : ∀ b : HomotopyGroup N Y (f x),
      HomotopyGroup.transport (G'.evalAt (f x))
        (HomotopyGroup.map f rfl (HomotopyGroup.map g rfl b)) = b := by
    intro b
    have h := HomotopyGroup.transport_map_homotopy (N := N) G' (f x) b
    rw [HomotopyGroup.map_id_apply] at h
    rw [HomotopyGroup.map_comp_apply]
    exact h
  have hinj : Function.Injective
      (HomotopyGroup.map (N := N) g (rfl : g (f x) = g (f x))) :=
    Function.LeftInverse.injective (g := fun c =>
      HomotopyGroup.transport (G'.evalAt (f x)) (HomotopyGroup.map f rfl c)) key2
  have hsurj : Function.Surjective
      (HomotopyGroup.map (N := N) g (rfl : g (f x) = g (f x))) := by
    intro c
    refine ⟨HomotopyGroup.map f rfl (HomotopyGroup.transportMulEquiv (G.evalAt x) c), ?_⟩
    exact (HomotopyGroup.transportMulEquiv (G.evalAt x)).injective
      (key1 (HomotopyGroup.transportMulEquiv (G.evalAt x) c))
  exact ⟨((MulEquiv.ofBijective (HomotopyGroup.mapHom (N := N) g (rfl : g (f x) = g (f x)))
    ⟨hinj, hsurj⟩).trans (HomotopyGroup.transportMulEquiv (G.evalAt x))).symm⟩

/-- **Homotopy invariance of the higher homotopy groups.** If `f : C(X, Y)` and `g : C(Y, X)`
are mutually inverse up to free homotopy, then `f` induces an isomorphism on every
positive-dimensional homotopy group. No compatibility between the basepoints is required:
the basepoint of the target is `f x`. -/
theorem nonempty_mulEquiv_of_homotopyEquiv {N : Type*} [DecidableEq N] [Nonempty N]
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (g : C(Y, X))
    (hgf : (g.comp f).Homotopic (ContinuousMap.id X))
    (hfg : (f.comp g).Homotopic (ContinuousMap.id Y)) (x : X) :
    Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N Y (f x)) := by
  rcases finite_or_infinite N with _ | _
  · exact nonempty_mulEquiv_of_homotopyEquiv_aux f g hgf hfg x
  · have hx : Subsingleton (HomotopyGroup N X x) := subsingleton_homotopyGroup_of_infinite
    have hy : Subsingleton (HomotopyGroup N Y (f x)) := subsingleton_homotopyGroup_of_infinite
    exact ⟨⟨⟨fun _ => 1, fun _ => 1, fun _ => hx.allEq _ _, fun _ => hy.allEq _ _⟩,
      fun _ _ => hy.allEq _ _⟩⟩

/-- **Homotopy invariance**, in terms of Mathlib's bundled `ContinuousMap.HomotopyEquiv`. -/
theorem nonempty_mulEquiv_of_homotopyEquiv' {N : Type*} [DecidableEq N] [Nonempty N]
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y)
    (x : X) : Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N Y (e x)) :=
  nonempty_mulEquiv_of_homotopyEquiv e.toFun e.invFun e.left_inv e.right_inv x

/-- **Homotopy invariance with prescribed basepoints.** If moreover `f x = y`, the homotopy
groups at `x` and `y` correspond. -/
theorem nonempty_mulEquiv_of_homotopyEquiv_of_eq {N : Type*} [DecidableEq N] [Nonempty N]
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (g : C(Y, X))
    (hgf : (g.comp f).Homotopic (ContinuousMap.id X))
    (hfg : (f.comp g).Homotopic (ContinuousMap.id Y)) {x : X} {y : Y} (hf : f x = y) :
    Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N Y y) :=
  hf ▸ nonempty_mulEquiv_of_homotopyEquiv f g hgf hfg x

end Submission
