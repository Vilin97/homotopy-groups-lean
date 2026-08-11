/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.DegreeOne.Boundaries
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

/-!
# Closing up a path to a loop at the basepoint

Fix a path-connected space `X` with basepoint `w`, and choose for every point `x` a path
`conn x : Path w x`.  Every path `p : Path x y` then determines a loop
`(conn x) ⬝ p ⬝ (conn y)⁻¹` at `w`, and hence an element `arcClass p` of the *abelianised*
fundamental group.  This assignment is the key ingredient of the inverse Hurewicz map: it is
additive under concatenation, and — this is the content of `Submission.arcClass_triangle` — the
three edges of a singular `2`-simplex satisfy the resulting cocycle relation, because the
standard `2`-simplex is simply connected.

## Main definitions

* `Submission.conn` — the chosen path from the basepoint to a given point;
* `Submission.arcClass` — the class of a path in the abelianised fundamental group;
* `Submission.triPath` — the `i`-th edge of `|Δ²|`, as a path.

## Main results

* `Submission.arcClass_eq` — the class only depends on the underlying function;
* `Submission.arcClass_trans` — additivity under concatenation;
* `Submission.arcClass_loop` — for a loop at `w`, the class is the image in the abelianisation;
* `Submission.arcClass_triangle` — the relation satisfied by the three edges of a `2`-simplex.
-/

open CategoryTheory Simplicial Opposite
open scoped unitInterval

noncomputable section

namespace Submission

/-! ### Coordinates of the face inclusions in low dimensions -/

theorem faceMap_zero_three (x : stdSimplex ℝ (Fin 2)) :
    (faceMap (0 : Fin 3) x).1 = ![0, x.1 0, x.1 1] := by
  funext k
  fin_cases k
  · exact faceMap_coe_same 0 x
  · exact faceMap_coe_succAbove 0 x 0
  · exact faceMap_coe_succAbove 0 x 1

theorem faceMap_one_three (x : stdSimplex ℝ (Fin 2)) :
    (faceMap (1 : Fin 3) x).1 = ![x.1 0, 0, x.1 1] := by
  funext k
  fin_cases k
  · exact faceMap_coe_succAbove 1 x 0
  · exact faceMap_coe_same 1 x
  · exact faceMap_coe_succAbove 1 x 1

theorem faceMap_two_three (x : stdSimplex ℝ (Fin 2)) :
    (faceMap (2 : Fin 3) x).1 = ![x.1 0, x.1 1, 0] := by
  funext k
  fin_cases k
  · exact faceMap_coe_succAbove 2 x 0
  · exact faceMap_coe_succAbove 2 x 1
  · exact faceMap_coe_same 2 x

theorem faceMap_zero_two (x : stdSimplex ℝ (Fin 1)) :
    (faceMap (0 : Fin 2) x).1 = ![0, x.1 0] := by
  funext k
  fin_cases k
  · exact faceMap_coe_same 0 x
  · exact faceMap_coe_succAbove 0 x 0

theorem faceMap_one_two (x : stdSimplex ℝ (Fin 1)) :
    (faceMap (1 : Fin 2) x).1 = ![x.1 0, 0] := by
  funext k
  fin_cases k
  · exact faceMap_coe_succAbove 1 x 0
  · exact faceMap_coe_same 1 x

theorem edgeInv_zero_val : (edgeInv 0).1 = ![1, 0] := by
  funext k; fin_cases k <;> norm_num

theorem edgeInv_one_val : (edgeInv 1).1 = ![0, 1] := by
  funext k; fin_cases k <;> norm_num

theorem default_val (x : stdSimplex ℝ (Fin 1)) : x.1 = ![1] := by
  funext k; fin_cases k; simpa using x.2.2

/-! ### The vertices of the standard `2`-simplex, reached along the three edges -/

theorem vertex_one_eq : faceMap (2 : Fin 3) (edgeInv 1) = faceMap (0 : Fin 3) (edgeInv 0) := by
  refine Subtype.ext ?_
  rw [faceMap_two_three, faceMap_zero_three, edgeInv_zero_val, edgeInv_one_val]
  funext k; fin_cases k <;> norm_num

theorem vertex_zero_eq : faceMap (1 : Fin 3) (edgeInv 0) = faceMap (2 : Fin 3) (edgeInv 0) := by
  refine Subtype.ext ?_
  rw [faceMap_one_three, faceMap_two_three, edgeInv_zero_val]
  funext k; fin_cases k <;> norm_num

theorem vertex_two_eq : faceMap (1 : Fin 3) (edgeInv 1) = faceMap (0 : Fin 3) (edgeInv 1) := by
  refine Subtype.ext ?_
  rw [faceMap_one_three, faceMap_zero_three, edgeInv_one_val]
  funext k; fin_cases k <;> norm_num

theorem faceMap_zero_default_two (x : stdSimplex ℝ (Fin 1)) :
    faceMap (0 : Fin 2) x = edgeInv 1 := by
  refine Subtype.ext ?_
  rw [faceMap_zero_two, edgeInv_one_val, default_val x]
  funext k; fin_cases k <;> norm_num

theorem faceMap_one_default_two (x : stdSimplex ℝ (Fin 1)) :
    faceMap (1 : Fin 2) x = edgeInv 0 := by
  refine Subtype.ext ?_
  rw [faceMap_one_two, edgeInv_zero_val, default_val x]
  funext k; fin_cases k <;> norm_num

/-! ### The faces of a singular `1`-simplex -/

variable {X : TopCat.{0}}

theorem face_zero_eq (s : Sng X _⦋1⦌) :
    SSet.face (Sng X) 0 s = constSimplex 0 (arc s 1) := by
  conv_lhs => rw [← sng_sngEquiv s]
  rw [face_sng, constSimplex]
  refine congrArg sng (ContinuousMap.ext fun z => ?_)
  show sngEquiv X 1 s (faceMap 0 z) = sngEquiv X 1 s (edgeInv 1)
  rw [faceMap_zero_default_two]

theorem face_one_eq (s : Sng X _⦋1⦌) :
    SSet.face (Sng X) 1 s = constSimplex 0 (arc s 0) := by
  conv_lhs => rw [← sng_sngEquiv s]
  rw [face_sng, constSimplex]
  refine congrArg sng (ContinuousMap.ext fun z => ?_)
  show sngEquiv X 1 s (faceMap 1 z) = sngEquiv X 1 s (edgeInv 0)
  rw [faceMap_one_default_two]

/-! ### The standard `2`-simplex is simply connected -/

instance simplyConnected_stdSimplex (m : ℕ) :
    SimplyConnectedSpace (stdSimplex ℝ (Fin (m + 1))) :=
  haveI : ContractibleSpace (stdSimplex ℝ (Fin (m + 1))) :=
    (convex_stdSimplex ℝ (Fin (m + 1))).contractibleSpace ⟨_, single_mem_stdSimplex ℝ 0⟩
  SimplyConnectedSpace.ofContractible _

/-- The path traversing the `i`-th edge of `|Δ²|`, i.e. the face opposite the vertex `i`. -/
def triPath (i : Fin 3) : Path (faceMap i (edgeInv 0)) (faceMap i (edgeInv 1)) :=
  toPath ((faceCM i).comp edgeInv)

@[simp]
theorem triPath_apply (i : Fin 3) (t : I) : triPath i t = faceMap i (edgeInv t) := rfl

/-- Cancelling a reversed path at the front of a composite. -/
theorem quotient_symm_trans_trans {x y z : X} (P : Path.Homotopic.Quotient x y)
    (Q : Path.Homotopic.Quotient y z) : P.symm.trans (P.trans Q) = Q := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

/-! ### Closing a path up to a loop at the basepoint -/

variable [PathConnectedSpace X] (w : X)

/-- The chosen path from the basepoint to a given point. -/
def conn (x : X) : Path w x := PathConnectedSpace.somePath w x

/-- The abelianised fundamental group of `X` at `w`, written additively. -/
abbrev AbPi (w : X) : Type := Additive (Abelianization (FundamentalGroup X w))

/-- The class in the abelianised fundamental group of a homotopy class of paths, closed up into a
loop at the basepoint using the chosen connecting paths. -/
def arcQ {x y : X} (P : Path.Homotopic.Quotient x y) : AbPi w :=
  Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
    (((Path.Homotopic.Quotient.mk (conn w x)).trans P).trans
      (Path.Homotopic.Quotient.mk (conn w y)).symm)))

/-- The class in the abelianised fundamental group of a path, closed up into a loop at the
basepoint using the chosen connecting paths. -/
def arcClass {x y : X} (p : Path x y) : AbPi w := arcQ w (Path.Homotopic.Quotient.mk p)

omit [PathConnectedSpace X] in
theorem of_mul_of (U V : Path.Homotopic.Quotient w w) :
    Abelianization.of (FundamentalGroup.fromPath U) *
        Abelianization.of (FundamentalGroup.fromPath V) =
      Abelianization.of (FundamentalGroup.fromPath (U.trans V)) := by
  rw [mul_comm, ← map_mul]
  rfl

/-- Two paths with the same underlying function have the same class. -/
theorem arcClass_eq {x y x' y' : X} (p : Path x y) (q : Path x' y') (h : ∀ t, p t = q t) :
    arcClass w p = arcClass w q := by
  have hx : x = x' := by rw [← p.source, ← q.source]; exact h 0
  have hy : y = y' := by rw [← p.target, ← q.target]; exact h 1
  subst hx; subst hy
  exact congrArg (arcClass w) (DFunLike.ext p q h)

theorem arcClass_cast {x y x' y' : X} (p : Path x y) (hx : x' = x) (hy : y' = y) :
    arcClass w (p.cast hx hy) = arcClass w p :=
  arcClass_eq w _ _ fun _ => rfl

/-- Homotopic paths have the same class. -/
theorem arcClass_homotopic {x y : X} {p q : Path x y} (h : p.Homotopic q) :
    arcClass w p = arcClass w q :=
  congrArg (arcQ w) (Path.Homotopic.Quotient.eq.2 h)

/-- Concatenation of paths corresponds to addition of classes. -/
theorem arcQ_trans {x y z : X} (P : Path.Homotopic.Quotient x y)
    (Q : Path.Homotopic.Quotient y z) : arcQ w (P.trans Q) = arcQ w P + arcQ w Q := by
  rw [arcQ, arcQ, arcQ, ← ofMul_mul, of_mul_of]
  refine congrArg (fun u => Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath u))) ?_
  simp [quotient_symm_trans_trans]

theorem arcClass_trans {x y z : X} (p : Path x y) (q : Path y z) :
    arcClass w (p.trans q) = arcClass w p + arcClass w q := by
  rw [arcClass, Path.Homotopic.Quotient.mk_trans, arcQ_trans, arcClass, arcClass]

/-- For a loop at the basepoint, the class is simply the image in the abelianisation. -/
theorem arcClass_loop (γ : Path w w) :
    arcClass w γ = Additive.ofMul (Abelianization.of
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) := by
  have hinv : Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (conn w w)).symm) =
      (Abelianization.of (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (conn w w))))⁻¹ :=
    map_inv Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (conn w w)))
  rw [arcClass, arcQ, ← of_mul_of, ← of_mul_of]
  refine congrArg Additive.ofMul ?_
  rw [hinv, mul_comm (Abelianization.of (FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (conn w w)))), mul_assoc, mul_inv_cancel, mul_one]

/-- Every element of the abelianised fundamental group is the class of a loop. -/
theorem exists_arcClass (u : AbPi w) : ∃ γ : Path w w, arcClass w γ = u := by
  obtain ⟨g, hg⟩ : ∃ g : FundamentalGroup X w, Abelianization.of g = Additive.toMul u :=
    QuotientGroup.induction_on (Additive.toMul u) fun z => ⟨z, rfl⟩
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  exact ⟨γ, by rw [arcClass_loop]; exact congrArg Additive.ofMul hg⟩

/-- The loop at the basepoint obtained by joining the endpoints of a path to the basepoint along
the chosen connecting paths. -/
def connLoop {x y : X} (p : Path x y) : Path w w :=
  ((conn w x).trans p).trans (conn w y).symm

theorem arcClass_eq_connLoop {x y : X} (p : Path x y) :
    arcClass w p = arcClass w (connLoop w p) := by
  rw [arcClass_loop, arcClass, arcQ, connLoop, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]

omit [PathConnectedSpace X] in
theorem edge_spath (s : Sng X _⦋1⦌) : edge (spath s) = gen s := by
  rw [edge, pathSimplex_spath]

/-! ### The triangle relation -/

/-- **The three edges of a singular `2`-simplex satisfy the cocycle relation.**  The edge from
vertex `0` to vertex `2` is, up to homotopy in the simply connected `|Δ²|`, the concatenation of
the edges `0 → 1` and `1 → 2`. -/
theorem arcClass_triangle (g : C(stdSimplex ℝ (Fin 3), X)) :
    arcClass w ((triPath 1).map g.continuous) =
      arcClass w ((triPath 2).map g.continuous) + arcClass w ((triPath 0).map g.continuous) := by
  have hhom : Path.Homotopic ((triPath 1).cast vertex_zero_eq.symm vertex_two_eq.symm)
      ((triPath 2).trans ((triPath 0).cast vertex_one_eq rfl)) :=
    SimplyConnectedSpace.paths_homotopic _ _
  have hmap := Path.Homotopic.map hhom g
  calc arcClass w ((triPath 1).map g.continuous)
      = arcClass w (((triPath 1).cast vertex_zero_eq.symm vertex_two_eq.symm).map g.continuous) :=
        arcClass_eq w _ _ fun _ => rfl
    _ = arcClass w
          (((triPath 2).trans ((triPath 0).cast vertex_one_eq rfl)).map g.continuous) :=
        arcClass_homotopic w hmap
    _ = arcClass w (((triPath 2).map g.continuous).trans
          (((triPath 0).cast vertex_one_eq rfl).map g.continuous)) := by
        rw [Path.map_trans]
    _ = arcClass w ((triPath 2).map g.continuous) +
          arcClass w (((triPath 0).cast vertex_one_eq rfl).map g.continuous) :=
        arcClass_trans w _ _
    _ = arcClass w ((triPath 2).map g.continuous) + arcClass w ((triPath 0).map g.continuous) := by
        rw [arcClass_eq w (((triPath 0).cast vertex_one_eq rfl).map g.continuous)
          ((triPath 0).map g.continuous) fun _ => rfl]

end Submission
