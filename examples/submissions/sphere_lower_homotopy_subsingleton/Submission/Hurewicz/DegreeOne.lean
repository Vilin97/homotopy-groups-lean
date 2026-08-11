/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.DegreeOne.ArcClass
import Submission.Homology.Basic
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# The Hurewicz theorem in degree one

For a path-connected space `X` with basepoint `w`, the Hurewicz map
`π₁(X, w) → H₁(X; ℤ)`, sending the class of a loop `γ` to the class of `γ` viewed as a singular
`1`-cycle, induces an isomorphism from the abelianisation of `π₁(X, w)` onto `H₁(X; ℤ)`.

## Outline of the proof

The map `Submission.hurewiczAdd` is built from the assignment `γ ↦ [γ]`, which is well defined on
homotopy classes and turns concatenation into addition by the explicit `2`-simplices of
`Submission/Hurewicz/DegreeOne/Boundaries.lean`; it therefore factors through the abelianisation.

Both injectivity and surjectivity come from one auxiliary homomorphism
`Submission.psiChain : C₁(X) → π₁(X, w)ᵃᵇ`, defined on a singular `1`-simplex `s` as the class of
the loop obtained by joining the endpoints of `s` to the basepoint along the chosen connecting
paths (`Submission.arcClass`).  It kills boundaries by `Submission.arcClass_triangle`.

* *Injectivity.*  If `[γ] = 0` then `γ` is a boundary, so `psiChain (edge γ) = 0`; but
  `psiChain (edge γ)` is the class of `γ` itself, since conjugation is trivial after
  abelianisation.
* *Surjectivity.*  The composite `hurewiczAdd ∘ psiChain : C₁(X) → H₁(X)` agrees, on generators
  and hence everywhere, with `a ↦ [a - ν(∂a)]`, where `ν` sends a `0`-simplex to the chosen path
  from the basepoint.  On a cycle `a` the correction term vanishes, so the composite hits `[a]`.

## Main results

* `Submission.hurewiczAdd` — the Hurewicz homomorphism `π₁(X, w)ᵃᵇ → H₁(X; ℤ)`;
* `Submission.hurewiczOneAddEquiv` —
  `Additive (Abelianization (FundamentalGroup X w)) ≃+ (Hgrp 1 X : Type)`;
* `Submission.hurewiczOneMulEquiv` —
  `Abelianization (FundamentalGroup X w) ≃* Multiplicative (Hgrp 1 X : Type)`;
* `Submission.hurewiczOnePi` — the same for the cube-based homotopy group `π_ 1 X w`.
-/

open CategoryTheory Simplicial Opposite
open scoped unitInterval Topology

noncomputable section

namespace Submission

variable {X : TopCat.{0}}

/-! ### Homology classes of singular `1`-cycles -/

theorem down_next_one : (ComplexShape.down ℕ).next 1 = 0 := by simp

theorem down_prev_one : (ComplexShape.down ℕ).prev 1 = 2 := by simp

/-- The homology class of a singular `1`-cycle. -/
def h1mk (a : (CsingSSet (Sng X)).X 1) (ha : (CsingSSet (Sng X)).d 1 0 a = 0) :
    (CsingSSet (Sng X)).homology 1 :=
  homologyMk a (by rw [down_next_one]; exact ha)

theorem h1mk_congr {a b : (CsingSSet (Sng X)).X 1} (ha : (CsingSSet (Sng X)).d 1 0 a = 0)
    (hb : (CsingSSet (Sng X)).d 1 0 b = 0) (h : a = b) : h1mk a ha = h1mk b hb := by
  subst h; rfl

theorem h1mk_add (a b : (CsingSSet (Sng X)).X 1) (ha : (CsingSSet (Sng X)).d 1 0 a = 0)
    (hb : (CsingSSet (Sng X)).d 1 0 b = 0)
    (hab : (CsingSSet (Sng X)).d 1 0 (a + b) = 0) :
    h1mk (a + b) hab = h1mk a ha + h1mk b hb :=
  homologyMk_add a b _ _

theorem h1mk_sub (a b : (CsingSSet (Sng X)).X 1) (ha : (CsingSSet (Sng X)).d 1 0 a = 0)
    (hb : (CsingSSet (Sng X)).d 1 0 b = 0)
    (hab : (CsingSSet (Sng X)).d 1 0 (a - b) = 0) :
    h1mk (a - b) hab = h1mk a ha - h1mk b hb :=
  homologyMk_sub a b _ _

theorem h1mk_eq_zero_iff (a : (CsingSSet (Sng X)).X 1) (ha : (CsingSSet (Sng X)).d 1 0 a = 0) :
    h1mk a ha = 0 ↔ a ∈ bdyOne X := by
  have h := homologyMk_eq_zero_iff (K := CsingSSet (Sng X)) (i := 1) a
    (by rw [down_next_one]; exact ha)
  rw [down_prev_one] at h
  exact h

theorem h1mk_eq_of_sub_mem {a b : (CsingSSet (Sng X)).X 1}
    (ha : (CsingSSet (Sng X)).d 1 0 a = 0) (hb : (CsingSSet (Sng X)).d 1 0 b = 0)
    (h : a - b ∈ bdyOne X) : h1mk a ha = h1mk b hb := by
  have hab : (CsingSSet (Sng X)).d 1 0 (a - b) = 0 := by rw [map_sub, ha, hb, sub_zero]
  rw [← sub_eq_zero, ← h1mk_sub a b ha hb hab]
  exact (h1mk_eq_zero_iff _ hab).2 h

theorem h1mk_surjective (z : (CsingSSet (Sng X)).homology 1) :
    ∃ (a : (CsingSSet (Sng X)).X 1) (ha : (CsingSSet (Sng X)).d 1 0 a = 0), h1mk a ha = z := by
  obtain ⟨a, ha, rfl⟩ := homologyMk_surjective z
  exact ⟨a, by rw [← down_next_one]; exact ha, rfl⟩

/-- The boundary of a singular `1`-simplex. -/
theorem d_gen_one (s : Sng X _⦋1⦌) :
    (CsingSSet (Sng X)).d 1 0 (gen s) =
      gen (SSet.face (Sng X) 0 s) - gen (SSet.face (Sng X) 1 s) := by
  rw [d_gen, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

/-! ### The Hurewicz homomorphism -/

variable (w : X)

/-- The homology class of a loop at the basepoint. -/
def loopH (γ : Path w w) : (CsingSSet (Sng X)).homology 1 := h1mk (edge γ) (d_edge_loop γ)

theorem loopH_congr {γ δ : Path w w} (h : γ.Homotopic δ) : loopH w γ = loopH w δ :=
  h1mk_eq_of_sub_mem _ _ (edge_sub_mem_of_homotopic h)

theorem loopH_refl : loopH w (Path.refl w) = 0 :=
  (h1mk_eq_zero_iff _ _).2 (edge_refl_mem w)

theorem loopH_trans (α β : Path w w) : loopH w (α.trans β) = loopH w α + loopH w β := by
  have hcyc : (CsingSSet (Sng X)).d 1 0 (edge α + edge β) = 0 := by
    rw [map_add, d_edge_loop, d_edge_loop, add_zero]
  rw [loopH, h1mk_eq_of_sub_mem (d_edge_loop (α.trans β)) hcyc (edge_trans_sub_mem α β),
    h1mk_add (edge α) (edge β) (d_edge_loop α) (d_edge_loop β) hcyc]
  rfl

/-- The Hurewicz map on homotopy classes of loops. -/
def loopHQ : FundamentalGroup X w → (CsingSSet (Sng X)).homology 1 :=
  Quotient.lift (loopH w) fun _ _ h => loopH_congr w h

@[simp]
theorem loopHQ_mk (γ : Path w w) : loopHQ w (Path.Homotopic.Quotient.mk γ) = loopH w γ := rfl

theorem loopHQ_one : loopHQ w (1 : FundamentalGroup X w) = 0 := by
  rw [FundamentalGroup.one_def, ← Path.Homotopic.Quotient.mk_refl, loopHQ_mk, loopH_refl]

theorem loopHQ_mul (P Q : FundamentalGroup X w) :
    loopHQ w (P * Q) = loopHQ w P + loopHQ w Q := by
  induction P using Path.Homotopic.Quotient.ind with
  | mk α =>
    induction Q using Path.Homotopic.Quotient.ind with
    | mk β =>
      rw [FundamentalGroup.mul_def, ← Path.Homotopic.Quotient.mk_trans, loopHQ_mk, loopHQ_mk,
        loopHQ_mk, loopH_trans, add_comm]

/-- The Hurewicz homomorphism `π₁(X, w) → H₁(X; ℤ)`. -/
def hurewiczMonoidHom :
    FundamentalGroup X w →* Multiplicative ((CsingSSet (Sng X)).homology 1) where
  toFun P := Multiplicative.ofAdd (loopHQ w P)
  map_one' := congrArg Multiplicative.ofAdd (loopHQ_one w)
  map_mul' P Q := congrArg Multiplicative.ofAdd (loopHQ_mul w P Q)

/-- The Hurewicz homomorphism out of the abelianised fundamental group. -/
def hurewiczAdd : AbPi w →+ (CsingSSet (Sng X)).homology 1 :=
  AddMonoidHom.mk' (fun u => Multiplicative.toAdd
      (Abelianization.lift (hurewiczMonoidHom w) (Additive.toMul u)))
    fun _ _ => congrArg Multiplicative.toAdd
      (map_mul (Abelianization.lift (hurewiczMonoidHom w)) _ _)

theorem hurewiczAdd_of (P : FundamentalGroup X w) :
    hurewiczAdd w (Additive.ofMul (Abelianization.of P)) = loopHQ w P :=
  congrArg Multiplicative.toAdd (Abelianization.lift_apply_of (hurewiczMonoidHom w) P)

/-! ### The inverse construction on chains -/

variable [PathConnectedSpace X]

@[simp]
theorem hurewiczAdd_arcClass (γ : Path w w) : hurewiczAdd w (arcClass w γ) = loopH w γ := by
  rw [arcClass_loop, hurewiczAdd_of, loopHQ_mk]

/-- The map on singular `1`-chains sending a `1`-simplex to the class, in the abelianised
fundamental group, of the loop obtained by joining its endpoints to the basepoint. -/
def psiChain : (CsingSSet (Sng X)).X 1 ⟶ AddCommGrpCat.of (AbPi w) :=
  ccDesc fun s => intHom (arcClass w (spath s))

@[simp]
theorem psiChain_gen (s : Sng X _⦋1⦌) : psiChain w (gen s) = arcClass w (spath s) := by
  rw [psiChain, ccDesc_gen, intHom_one]

theorem psiChain_edge (γ : Path w w) : psiChain w (edge γ) = arcClass w γ := by
  rw [edge, psiChain_gen]
  exact arcClass_eq w _ _ fun t => arc_pathSimplex γ t

theorem arcClass_spath_face (τ : Sng X _⦋2⦌) (i : Fin 3) :
    arcClass w (spath (SSet.face (Sng X) i τ)) =
      arcClass w ((triPath i).map (sngEquiv X 2 τ).continuous) := by
  refine arcClass_eq w _ _ fun t => ?_
  show sngEquiv X 1 (SSet.face (Sng X) i τ) (edgeInv t) = sngEquiv X 2 τ (faceMap i (edgeInv t))
  rw [show sngEquiv X 1 (SSet.face (Sng X) i τ) = (sngEquiv X 2 τ).comp (faceCM i) from
    sngEquiv_δ X i τ]
  rfl

/-- `psiChain` kills boundaries: this is the triangle relation for a singular `2`-simplex. -/
theorem psiChain_comp_d : (CsingSSet (Sng X)).d 2 1 ≫ psiChain w = 0 := by
  refine chainComplexX_hom_ext fun τ => ?_
  rw [ConcreteCategory.comp_apply, zero_hom_apply, d_gen, Fin.sum_univ_three]
  simp only [map_add, map_zsmul]
  show (-1 : ℤ) ^ (0 : ℕ) • psiChain w (gen (SSet.face (Sng X) 0 τ)) +
      (-1 : ℤ) ^ (1 : ℕ) • psiChain w (gen (SSet.face (Sng X) 1 τ)) +
      (-1 : ℤ) ^ (2 : ℕ) • psiChain w (gen (SSet.face (Sng X) 2 τ)) = 0
  rw [psiChain_gen, psiChain_gen, psiChain_gen, arcClass_spath_face, arcClass_spath_face,
    arcClass_spath_face, arcClass_triangle w (sngEquiv X 2 τ)]
  simp only [pow_zero, pow_one, pow_two, neg_mul, neg_neg, one_mul, one_smul, neg_smul]
  abel

theorem psiChain_boundary (a : (CsingSSet (Sng X)).X 1) (ha : a ∈ bdyOne X) :
    psiChain w a = 0 := by
  obtain ⟨c, rfl⟩ := ha
  rw [show ((CsingSSet (Sng X)).d 2 1).hom c = (CsingSSet (Sng X)).d 2 1 c from rfl,
    ← ConcreteCategory.comp_apply, psiChain_comp_d, zero_hom_apply]

/-! ### Injectivity -/

theorem hurewiczAdd_injective : Function.Injective (hurewiczAdd w) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨γ, rfl⟩ := exists_arcClass w u
  rw [hurewiczAdd_arcClass, loopH] at hu
  rw [← psiChain_edge w γ]
  exact psiChain_boundary w _ ((h1mk_eq_zero_iff _ _).1 hu)

/-! ### Surjectivity -/

/-- The map on singular `0`-chains sending a `0`-simplex to the chosen path joining the basepoint
to it. -/
def connChain : (CsingSSet (Sng X)).X 0 ⟶ (CsingSSet (Sng X)).X 1 :=
  ccDesc fun v => intHom (edge (conn w (pt0 v)))

@[simp]
theorem connChain_gen (v : Sng X _⦋0⦌) : connChain w (gen v) = edge (conn w (pt0 v)) := by
  rw [connChain, ccDesc_gen, intHom_one]

theorem d_connChain_gen (v : Sng X _⦋0⦌) :
    (CsingSSet (Sng X)).d 1 0 (connChain w (gen v)) = gen v - gen (constSimplex 0 w) := by
  rw [connChain_gen, d_edge, constSimplex_pt0]

/-- The correction operator `a ↦ a - ν(∂a)`, which lands in the cycles for every chain. -/
def corrHom : (CsingSSet (Sng X)).X 1 ⟶ (CsingSSet (Sng X)).X 1 :=
  𝟙 _ - (CsingSSet (Sng X)).d 1 0 ≫ connChain w

theorem corrHom_apply (a : (CsingSSet (Sng X)).X 1) :
    corrHom w a = a - connChain w ((CsingSSet (Sng X)).d 1 0 a) := rfl

theorem corrHom_eq_of_cycle (a : (CsingSSet (Sng X)).X 1)
    (ha : (CsingSSet (Sng X)).d 1 0 a = 0) : corrHom w a = a := by
  rw [corrHom_apply, ha, map_zero, sub_zero]

theorem d_corrHom : corrHom w ≫ (CsingSSet (Sng X)).d 1 0 = 0 := by
  refine chainComplexX_hom_ext fun s => ?_
  rw [ConcreteCategory.comp_apply, zero_hom_apply, corrHom_apply, d_gen_one]
  simp only [map_sub, d_gen_one, d_connChain_gen]
  abel

theorem d_corrHom_apply (a : (CsingSSet (Sng X)).X 1) :
    (CsingSSet (Sng X)).d 1 0 (corrHom w a) = 0 := by
  rw [← ConcreteCategory.comp_apply, d_corrHom, zero_hom_apply]

/-- The additive map `C₁(X) → H₁(X)` given by `a ↦ [a - ν(∂a)]`. -/
def corrCycleHom :
    ((CsingSSet (Sng X)).X 1 : Type) →+ ((CsingSSet (Sng X)).homology 1 : Type) where
  toFun a := h1mk (corrHom w a) (d_corrHom_apply w a)
  map_zero' := by
    have h0 : corrHom w (0 : (CsingSSet (Sng X)).X 1) = 0 := map_zero _
    rw [show h1mk (corrHom w 0) (d_corrHom_apply w 0) =
      h1mk (0 : (CsingSSet (Sng X)).X 1) (map_zero _) from h1mk_congr _ _ h0]
    exact homologyMk_zero
  map_add' a b := by
    have hab : corrHom w (a + b) = corrHom w a + corrHom w b := map_add _ a b
    have hs : (CsingSSet (Sng X)).d 1 0 (corrHom w a + corrHom w b) = 0 := by
      rw [map_add, d_corrHom_apply, d_corrHom_apply, add_zero]
    rw [show h1mk (corrHom w (a + b)) (d_corrHom_apply w (a + b)) =
      h1mk (corrHom w a + corrHom w b) hs from h1mk_congr _ _ hab,
      h1mk_add _ _ (d_corrHom_apply w a) (d_corrHom_apply w b)]

/-- The homomorphism `C₁(X) → H₁(X)` given by `a ↦ [a - ν(∂a)]`. -/
def lambdaPrime : (CsingSSet (Sng X)).X 1 ⟶ (CsingSSet (Sng X)).homology 1 :=
  AddCommGrpCat.ofHom (corrCycleHom w)

@[simp]
theorem lambdaPrime_apply (a : (CsingSSet (Sng X)).X 1) :
    lambdaPrime w a = h1mk (corrHom w a) (d_corrHom_apply w a) := rfl

theorem lambdaPrime_of_cycle (a : (CsingSSet (Sng X)).X 1)
    (ha : (CsingSSet (Sng X)).d 1 0 a = 0) : lambdaPrime w a = h1mk a ha := by
  rw [lambdaPrime_apply]
  exact h1mk_congr _ _ (corrHom_eq_of_cycle w a ha)

theorem corrHom_gen (s : Sng X _⦋1⦌) :
    corrHom w (gen s) =
      gen s - edge (conn w (arc s 1)) + edge (conn w (arc s 0)) := by
  rw [corrHom_apply, d_gen_one, map_sub, connChain_gen, connChain_gen, face_zero_eq, face_one_eq,
    pt0_constSimplex, pt0_constSimplex]
  abel

theorem edge_connLoop_sub_corrHom_mem (s : Sng X _⦋1⦌) :
    edge (connLoop w (spath s)) - corrHom w (gen s) ∈ bdyOne X := by
  have h1 := edge_trans_sub_mem ((conn w (arc s 0)).trans (spath s)) (conn w (arc s 1)).symm
  have h2 := edge_trans_sub_mem (conn w (arc s 0)) (spath s)
  have h3 := edge_symm_add_mem (conn w (arc s 1))
  have hkey : edge (connLoop w (spath s)) - corrHom w (gen s) =
      (edge (((conn w (arc s 0)).trans (spath s)).trans (conn w (arc s 1)).symm) -
          (edge ((conn w (arc s 0)).trans (spath s)) + edge (conn w (arc s 1)).symm)) +
        (edge ((conn w (arc s 0)).trans (spath s)) -
          (edge (conn w (arc s 0)) + edge (spath s))) +
        (edge (conn w (arc s 1)).symm + edge (conn w (arc s 1))) := by
    rw [corrHom_gen, connLoop, ← edge_spath s]
    abel
  rw [hkey]
  exact add_mem (add_mem h1 h2) h3

/-- The composite of `psiChain` with the Hurewicz map agrees with the correction operator
followed by the class map. -/
theorem psiChain_comp_hurewicz :
    psiChain w ≫ AddCommGrpCat.ofHom (hurewiczAdd w) = lambdaPrime w := by
  refine chainComplexX_hom_ext fun s => ?_
  rw [ConcreteCategory.comp_apply, lambdaPrime_apply]
  show hurewiczAdd w (psiChain w (gen s)) = _
  rw [psiChain_gen, arcClass_eq_connLoop w (spath s), hurewiczAdd_arcClass, loopH]
  exact h1mk_eq_of_sub_mem _ _ (edge_connLoop_sub_corrHom_mem w s)

theorem hurewiczAdd_surjective : Function.Surjective (hurewiczAdd w) := by
  intro z
  obtain ⟨a, ha, rfl⟩ := h1mk_surjective z
  refine ⟨psiChain w a, ?_⟩
  have h := congrArg (fun f : (CsingSSet (Sng X)).X 1 ⟶ (CsingSSet (Sng X)).homology 1 => f a)
    (psiChain_comp_hurewicz w)
  rw [ConcreteCategory.comp_apply, lambdaPrime_of_cycle w a ha] at h
  exact h

/-! ### The Hurewicz isomorphism -/

/-- **The Hurewicz theorem in degree one.**  For a path-connected space `X` with basepoint `w`,
the Hurewicz map induces an isomorphism from the abelianisation of the fundamental group onto the
first singular homology group. -/
def hurewiczOneAddEquiv : AbPi w ≃+ (CsingSSet (Sng X)).homology 1 :=
  AddEquiv.ofBijective (hurewiczAdd w) ⟨hurewiczAdd_injective w, hurewiczAdd_surjective w⟩

@[simp]
theorem hurewiczOneAddEquiv_apply (u : AbPi w) : hurewiczOneAddEquiv w u = hurewiczAdd w u := rfl

/-- **The Hurewicz theorem in degree one**, stated for `Hgrp 1 X`. -/
def hurewiczOne :
    Additive (Abelianization (FundamentalGroup X w)) ≃+ (Hgrp 1 X : Type) :=
  hurewiczOneAddEquiv w

/-- **The Hurewicz theorem in degree one**, multiplicative form. -/
def hurewiczOneMulEquiv :
    Abelianization (FundamentalGroup X w) ≃* Multiplicative (Hgrp 1 X : Type) :=
  AddEquiv.toMultiplicativeRight (hurewiczOne w)

/-- The Hurewicz map sends the class of a loop `γ` to the homology class of `γ` viewed as a
singular `1`-cycle.  This pins down `hurewiczOne`. -/
theorem hurewiczOne_apply (γ : Path w w) :
    hurewiczOne w (Additive.ofMul (Abelianization.of
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))) =
      h1mk (edge γ) (d_edge_loop γ) :=
  hurewiczAdd_of w (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))

/-- **The Hurewicz theorem in degree one**, for a path-connected topological space. -/
def hurewiczOneOfSpace (W : Type) [TopologicalSpace W] [PathConnectedSpace W] (v : W) :
    Additive (Abelianization (FundamentalGroup W v)) ≃+ (Hgrp 1 (TopCat.of W) : Type) :=
  hurewiczOne (X := TopCat.of W) v

/-- **The Hurewicz theorem in degree one**, for the cube-based first homotopy group `π_ 1`. -/
def hurewiczOnePi : Additive (Abelianization (π_ 1 X w)) ≃+ (Hgrp 1 X : Type) :=
  (MulEquiv.toAdditive
    (HomotopyGroup.pi1MulEquivFundamentalGroup.abelianizationCongr)).trans (hurewiczOne w)

/-- **The Hurewicz theorem in degree one** for `π_ 1`, for a path-connected space. -/
def hurewiczOnePiOfSpace (W : Type) [TopologicalSpace W] [PathConnectedSpace W] (v : W) :
    Additive (Abelianization (π_ 1 W v)) ≃+ (Hgrp 1 (TopCat.of W) : Type) :=
  hurewiczOnePi (X := TopCat.of W) v

end Submission
