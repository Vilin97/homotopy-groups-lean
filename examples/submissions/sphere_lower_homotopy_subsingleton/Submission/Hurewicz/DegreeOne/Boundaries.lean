/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.DegreeOne.Affine
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# The singular `1`-chain of a path, modulo boundaries

Let `X` be a topological space.  Sending a path to the singular `1`-simplex it defines gives a map
`Path x y → C₁(X; ℤ)`, `p ↦ edge p`.  This file proves the four facts that make this map behave
like a homomorphism from the fundamental groupoid once one passes to `C₁ / B₁`:

* the edge of a constant path is a boundary;
* `edge (p.trans q) - edge p - edge q` is a boundary;
* homotopic paths have homologous edges;
* `edge p.symm + edge p` is a boundary.

All four are witnessed by explicit singular `2`-simplices built with `Submission.affI` and
`Submission.affSq`: for concatenation, the `2`-simplex `|Δ²| → I → X` affine on `0, ½, 1`; for
homotopy invariance, the two halves of the prism `|Δ¹| × I` mapped into `X` by the homotopy.

## Main definitions

* `Submission.bdyOne` — the subgroup of singular `1`-boundaries;
* `Submission.edge` — the singular `1`-chain of a path;
* `Submission.transSimplex`, `Submission.prismLower`, `Submission.prismUpper` — the explicit
  `2`-simplices.

## Main results

* `Submission.d_edge` — the boundary of `edge p` is the difference of its endpoints;
* `Submission.edge_refl_mem`;
* `Submission.edge_trans_sub_mem`;
* `Submission.edge_sub_mem_of_homotopic`;
* `Submission.edge_symm_add_mem`.
-/

open CategoryTheory Simplicial Opposite
open scoped unitInterval

noncomputable section

namespace Submission

variable {X : TopCat.{0}}

/-! ### Boundaries -/

/-- The subgroup of singular `1`-boundaries of `X`. -/
def bdyOne (X : TopCat.{0}) : AddSubgroup ((CsingSSet (Sng X)).X 1) :=
  AddMonoidHom.range ((CsingSSet (Sng X)).d 2 1).hom

theorem mem_bdyOne {a : (CsingSSet (Sng X)).X 1} (c : (CsingSSet (Sng X)).X 2)
    (h : (CsingSSet (Sng X)).d 2 1 c = a) : a ∈ bdyOne X := ⟨c, h⟩

/-- The singular `1`-chain determined by a path. -/
def edge {x y : X} (p : Path x y) : (CsingSSet (Sng X)).X 1 := gen (pathSimplex p)

/-- The boundary of the `1`-chain of a path is the difference of the classes of its endpoints. -/
theorem d_edge {x y : X} (p : Path x y) :
    (CsingSSet (Sng X)).d 1 0 (edge p) =
      gen (constSimplex 0 y) - gen (constSimplex 0 x) := by
  rw [edge, d_gen, Fin.sum_univ_two, face_pathSimplex_zero, face_pathSimplex_one]
  simp [sub_eq_add_neg]

/-- The `1`-chain of a loop is a cycle. -/
theorem d_edge_loop {x : X} (p : Path x x) : (CsingSSet (Sng X)).d 1 0 (edge p) = 0 := by
  rw [d_edge, sub_self]

/-- The boundary of the constant `2`-simplex is the constant `1`-simplex. -/
theorem gen_constSimplex_one_mem (x : X) : gen (constSimplex 1 x) ∈ bdyOne X := by
  refine mem_bdyOne (gen (constSimplex 2 x)) ?_
  rw [d_gen, Fin.sum_univ_three, face_constSimplex, face_constSimplex, face_constSimplex]
  simp

/-- The `1`-chain of a constant path is a boundary. -/
theorem edge_refl_mem (x : X) : edge (Path.refl x) ∈ bdyOne X := by
  rw [edge, pathSimplex_refl]
  exact gen_constSimplex_one_mem x

/-! ### Reparametrisation lemmas for `Path.trans` -/

theorem trans_apply' {x y z : X} (p : Path x y) (q : Path y z) (s : I) :
    (p.trans q) s = if (s : ℝ) ≤ 1 / 2 then p.extend (2 * s) else q.extend (2 * s - 1) := rfl

theorem trans_apply_left {x y z : X} (p : Path x y) (q : Path y z) (s t : I)
    (h : (s : ℝ) = (t : ℝ) / 2) : (p.trans q) s = p t := by
  rw [trans_apply', if_pos (by rw [h]; linarith [t.2.2])]
  rw [show (2 : ℝ) * s = (t : ℝ) by rw [h]; ring]
  exact Path.extend_extends' p t

theorem trans_apply_right {x y z : X} (p : Path x y) (q : Path y z) (s t : I)
    (h : (s : ℝ) = (1 + (t : ℝ)) / 2) : (p.trans q) s = q t := by
  rw [trans_apply']
  split_ifs with hc
  · have ht : (t : ℝ) = 0 := le_antisymm (by rw [h] at hc; linarith) t.2.1
    rw [show (2 : ℝ) * s = 1 by rw [h, ht]; ring, Path.extend_one,
      show t = 0 from Subtype.ext ht, q.source]
  · rw [show (2 : ℝ) * s - 1 = (t : ℝ) by rw [h]; ring]
    exact Path.extend_extends' q t

/-! ### Concatenation -/

/-- The midpoint of the unit interval. -/
def half : I := ⟨1 / 2, Set.mem_Icc.2 ⟨by norm_num, by norm_num⟩⟩

@[simp] theorem half_coe : (half : ℝ) = 1 / 2 := rfl

/-- The singular `2`-simplex witnessing that `p.trans q` is the composite of `p` and `q`: the
concatenated path precomposed with the affine map `|Δ²| → I` taking the vertices to `0`, `½`,
`1`. -/
def transSimplex {x y z : X} (p : Path x y) (q : Path y z) : Sng X _⦋2⦌ :=
  sng ((p.trans q).toContinuousMap.comp (affI ![0, half, 1]))

theorem face_transSimplex_zero {x y z : X} (p : Path x y) (q : Path y z) :
    SSet.face (Sng X) 0 (transSimplex p q) = pathSimplex q := by
  rw [transSimplex, face_sng, ContinuousMap.comp_assoc, affI_comp_faceCM, succAbove_two_zero]
  refine congrArg sng (ContinuousMap.ext fun z => ?_)
  refine trans_apply_right p q _ (edgeParam z) ?_
  rw [affI_two_coe]
  simp only [half_coe]
  push_cast
  ring

theorem face_transSimplex_one {x y z : X} (p : Path x y) (q : Path y z) :
    SSet.face (Sng X) 1 (transSimplex p q) = pathSimplex (p.trans q) := by
  rw [transSimplex, face_sng, ContinuousMap.comp_assoc, affI_comp_faceCM, succAbove_two_one]
  rfl

theorem face_transSimplex_two {x y z : X} (p : Path x y) (q : Path y z) :
    SSet.face (Sng X) 2 (transSimplex p q) = pathSimplex p := by
  rw [transSimplex, face_sng, ContinuousMap.comp_assoc, affI_comp_faceCM, succAbove_two_two]
  refine congrArg sng (ContinuousMap.ext fun z => ?_)
  refine trans_apply_left p q _ (edgeParam z) ?_
  rw [affI_two_coe]
  simp only [half_coe]
  push_cast
  ring

/-- **Concatenation adds edges, modulo boundaries.** -/
theorem edge_trans_sub_mem {x y z : X} (p : Path x y) (q : Path y z) :
    edge (p.trans q) - (edge p + edge q) ∈ bdyOne X := by
  refine mem_bdyOne (-gen (transSimplex p q)) ?_
  rw [map_neg, d_gen, Fin.sum_univ_three, face_transSimplex_zero, face_transSimplex_one,
    face_transSimplex_two]
  show -((-1 : ℤ) ^ (0 : ℕ) • edge q + (-1 : ℤ) ^ (1 : ℕ) • edge (p.trans q) +
    (-1 : ℤ) ^ (2 : ℕ) • edge p) = _
  simp only [pow_zero, pow_one, pow_two, neg_mul, neg_neg, one_mul, one_smul, neg_smul]
  abel

/-! ### Homotopy invariance -/

theorem affSq_fst (a b : I × I) (z : stdSimplex ℝ (Fin 2)) :
    (((affSq ![a, b] z).1 : I) : ℝ) =
      (1 - (edgeParam z : ℝ)) * (a.1 : ℝ) + (edgeParam z : ℝ) * (b.1 : ℝ) := by
  rw [affSq_apply, show (fun j => ((![a, b] : Fin 2 → I × I) j).1) = ![a.1, b.1] by
    funext k; fin_cases k <;> rfl, affI_two_coe]

theorem affSq_snd (a b : I × I) (z : stdSimplex ℝ (Fin 2)) :
    (((affSq ![a, b] z).2 : I) : ℝ) =
      (1 - (edgeParam z : ℝ)) * (a.2 : ℝ) + (edgeParam z : ℝ) * (b.2 : ℝ) := by
  rw [affSq_apply, show (fun j => ((![a, b] : Fin 2 → I × I) j).2) = ![a.2, b.2] by
    funext k; fin_cases k <;> rfl, affI_two_coe]

theorem affSq_eq (a b : I × I) (z : stdSimplex ℝ (Fin 2)) (c d : I)
    (h1 : (c : ℝ) = (1 - (edgeParam z : ℝ)) * (a.1 : ℝ) + (edgeParam z : ℝ) * (b.1 : ℝ))
    (h2 : (d : ℝ) = (1 - (edgeParam z : ℝ)) * (a.2 : ℝ) + (edgeParam z : ℝ) * (b.2 : ℝ)) :
    affSq ![a, b] z = (c, d) :=
  Prod.ext (Subtype.ext ((affSq_fst a b z).trans h1.symm))
    (Subtype.ext ((affSq_snd a b z).trans h2.symm))

variable {x y : X} {p q : Path x y}

/-- The lower half `(0,0), (0,1), (1,1)` of the prism, mapped into `X` by a path homotopy. -/
def prismLower (H : Path.Homotopy p q) : Sng X _⦋2⦌ :=
  sng (H.toContinuousMap.comp (affSq ![(0, 0), (0, 1), (1, 1)]))

/-- The upper half `(0,0), (1,0), (1,1)` of the prism, mapped into `X` by a path homotopy. -/
def prismUpper (H : Path.Homotopy p q) : Sng X _⦋2⦌ :=
  sng (H.toContinuousMap.comp (affSq ![(0, 0), (1, 0), (1, 1)]))

theorem face_prismLower_zero (H : Path.Homotopy p q) :
    SSet.face (Sng X) 0 (prismLower H) = constSimplex 1 y := by
  rw [prismLower, face_sng, ContinuousMap.comp_assoc, affSq_comp_faceCM, succAbove_two_zero]
  refine congrArg sng (ContinuousMap.ext fun z => ?_)
  show H (affSq ![((0 : I), (1 : I)), ((1 : I), (1 : I))] z) = y
  rw [show affSq ![((0 : I), (1 : I)), ((1 : I), (1 : I))] z = (edgeParam z, 1) from
    affSq_eq _ _ z _ _ (by push_cast; ring) (by push_cast; ring)]
  exact H.target _

theorem face_prismLower_two (H : Path.Homotopy p q) :
    SSet.face (Sng X) 2 (prismLower H) = pathSimplex p := by
  rw [prismLower, face_sng, ContinuousMap.comp_assoc, affSq_comp_faceCM, succAbove_two_two]
  refine congrArg sng (ContinuousMap.ext fun z => ?_)
  show H (affSq ![((0 : I), (0 : I)), ((0 : I), (1 : I))] z) = p (edgeParam z)
  rw [show affSq ![((0 : I), (0 : I)), ((0 : I), (1 : I))] z = (0, edgeParam z) from
    affSq_eq _ _ z _ _ (by push_cast; ring) (by push_cast; ring)]
  exact H.apply_zero _

theorem face_prismUpper_zero (H : Path.Homotopy p q) :
    SSet.face (Sng X) 0 (prismUpper H) = pathSimplex q := by
  rw [prismUpper, face_sng, ContinuousMap.comp_assoc, affSq_comp_faceCM, succAbove_two_zero]
  refine congrArg sng (ContinuousMap.ext fun z => ?_)
  show H (affSq ![((1 : I), (0 : I)), ((1 : I), (1 : I))] z) = q (edgeParam z)
  rw [show affSq ![((1 : I), (0 : I)), ((1 : I), (1 : I))] z = (1, edgeParam z) from
    affSq_eq _ _ z _ _ (by push_cast; ring) (by push_cast; ring)]
  exact H.apply_one _

theorem face_prismUpper_two (H : Path.Homotopy p q) :
    SSet.face (Sng X) 2 (prismUpper H) = constSimplex 1 x := by
  rw [prismUpper, face_sng, ContinuousMap.comp_assoc, affSq_comp_faceCM, succAbove_two_two]
  refine congrArg sng (ContinuousMap.ext fun z => ?_)
  show H (affSq ![((0 : I), (0 : I)), ((1 : I), (0 : I))] z) = x
  rw [show affSq ![((0 : I), (0 : I)), ((1 : I), (0 : I))] z = (edgeParam z, 0) from
    affSq_eq _ _ z _ _ (by push_cast; ring) (by push_cast; ring)]
  exact H.source _

/-- Both halves of the prism have the same middle face, the diagonal of the square. -/
theorem face_prism_one (H : Path.Homotopy p q) :
    SSet.face (Sng X) 1 (prismLower H) = SSet.face (Sng X) 1 (prismUpper H) := by
  rw [prismLower, prismUpper, face_sng, face_sng, ContinuousMap.comp_assoc,
    ContinuousMap.comp_assoc, affSq_comp_faceCM, affSq_comp_faceCM, succAbove_two_one,
    succAbove_two_one]

/-- **Homotopic paths have homologous edges.** -/
theorem edge_sub_mem_of_homotopic (h : p.Homotopic q) : edge p - edge q ∈ bdyOne X := by
  obtain ⟨H⟩ := h
  have key : edge p - edge q - (gen (constSimplex 1 x) - gen (constSimplex 1 y)) ∈ bdyOne X := by
    refine mem_bdyOne (gen (prismLower H) - gen (prismUpper H)) ?_
    rw [map_sub, d_gen, d_gen, Fin.sum_univ_three, Fin.sum_univ_three, face_prismLower_zero,
      face_prismLower_two, face_prismUpper_zero, face_prismUpper_two, face_prism_one]
    show ((-1 : ℤ) ^ (0 : ℕ) • gen (constSimplex 1 y) +
        (-1 : ℤ) ^ (1 : ℕ) • gen (SSet.face (Sng X) 1 (prismUpper H)) +
        (-1 : ℤ) ^ (2 : ℕ) • edge p) -
      ((-1 : ℤ) ^ (0 : ℕ) • edge q +
        (-1 : ℤ) ^ (1 : ℕ) • gen (SSet.face (Sng X) 1 (prismUpper H)) +
        (-1 : ℤ) ^ (2 : ℕ) • gen (constSimplex 1 x)) = _
    simp only [pow_zero, pow_one, pow_two, neg_mul, neg_neg, one_mul, one_smul, neg_smul]
    abel
  have h2 : gen (constSimplex 1 x) - gen (constSimplex 1 y) ∈ bdyOne X :=
    sub_mem (gen_constSimplex_one_mem x) (gen_constSimplex_one_mem y)
  simpa using add_mem key h2

/-- Homotopic paths have homologous edges, phrased with `Path.Homotopic.Quotient`. -/
theorem edge_sub_mem_of_quotient_eq
    (h : Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk q) :
    edge p - edge q ∈ bdyOne X :=
  edge_sub_mem_of_homotopic (Path.Homotopic.Quotient.exact h)

/-! ### Inverses -/

/-- **Reversing a path negates its edge, modulo boundaries.** -/
theorem edge_symm_add_mem {x y : X} (p : Path x y) : edge p.symm + edge p ∈ bdyOne X := by
  have h1 : edge (p.symm.trans p) - (edge p.symm + edge p) ∈ bdyOne X :=
    edge_trans_sub_mem p.symm p
  have h2 : edge (p.symm.trans p) - edge (Path.refl y) ∈ bdyOne X :=
    edge_sub_mem_of_homotopic (Path.Homotopic.symm_trans p)
  have h3 : edge (Path.refl y) ∈ bdyOne X := edge_refl_mem y
  have hmem := sub_mem (add_mem h3 h2) h1
  have heq : edge (Path.refl y) + (edge (p.symm.trans p) - edge (Path.refl y)) -
      (edge (p.symm.trans p) - (edge p.symm + edge p)) = edge p.symm + edge p := by abel
  rwa [heq] at hmem

end Submission
