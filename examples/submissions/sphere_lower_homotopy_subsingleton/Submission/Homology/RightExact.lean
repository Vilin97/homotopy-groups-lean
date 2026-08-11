/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.MayerVietorisIso
import Submission.Homology.HomologyZero

/-!
# Right exactness of `H₀`, and two degenerate homology computations

For a short exact sequence of chain complexes indexed by `ℕ` the induced sequence on `H₀` is right
exact: `H₀(X₂) ⟶ H₀(X₃) ⟶ 0`.  This is the piece of the homology sequence that the six-term
`composableArrows₅` does not see, because there is no degree `-1`.

The proof is the standard one: in degree `0` a chain complex over `ℕ` has
`homologyι 0 : H₀ ≅ opcycles 0` (Mathlib's `ChainComplex.isIso_homologyι₀`), and `opcycles` is
right exact (Mathlib's `HomologicalComplex.HomologySequence.opcycles_right_exact`, whose epimorphism
part is an instance).

## Main results

* `epi_homologyMap_zero` — right exactness of `H₀`;
* `epi_mvKappa_zero` — `H₀(A) ⊞ H₀(B) ⟶ H₀(X) ⟶ 0` in Mayer–Vietoris;
* `isZero_Hgrp_of_isEmpty` — the homology of the empty space vanishes;
* `isZero_Hred_zero_of_pathConnected` — `H̃₀(X) = 0` for path-connected `X`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

noncomputable section

namespace Submission

/-! ### Two trivialities about zero objects -/

theorem isZero_of_mono_of_isZero {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    {P Q : C} (f : P ⟶ Q) [Mono f] (h : IsZero Q) : IsZero P :=
  (IsZero.iff_id_eq_zero _).2 <| by
    refine (cancel_mono f).1 ?_
    rw [Category.id_comp, zero_comp]
    exact h.eq_zero_of_tgt f

theorem isZero_of_epi_of_isZero {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    {P Q : C} (f : P ⟶ Q) [Epi f] (h : IsZero P) : IsZero Q :=
  (IsZero.iff_id_eq_zero _).2 <| by
    refine (cancel_epi f).1 ?_
    rw [Category.comp_id, comp_zero]
    exact h.eq_zero_of_src f

/-! ### Right exactness of `H₀` -/

/-- **Right exactness of `H₀`.**  For a short exact sequence of chain complexes indexed by `ℕ`,
the map `H₀(X₂) ⟶ H₀(X₃)` is an epimorphism. -/
theorem epi_homologyMap_zero {S : ShortComplex (ChainComplex AddCommGrpCat.{0} ℕ)}
    (hS : S.ShortExact) : Epi (HomologicalComplex.homologyMap S.g 0) := by
  haveI : Epi (S.g.f 0) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS 0).epi_g
  haveI : Epi (HomologicalComplex.opcyclesMap S.g 0) := inferInstance
  have hnat : HomologicalComplex.homologyMap S.g 0 ≫ S.X₃.homologyι 0 =
      S.X₂.homologyι 0 ≫ HomologicalComplex.opcyclesMap S.g 0 :=
    HomologicalComplex.homologyι_naturality S.g 0
  haveI : Epi (HomologicalComplex.homologyMap S.g 0 ≫ S.X₃.homologyι 0) := by
    rw [hnat]; infer_instance
  have hfac : HomologicalComplex.homologyMap S.g 0 =
      (HomologicalComplex.homologyMap S.g 0 ≫ S.X₃.homologyι 0) ≫ inv (S.X₃.homologyι 0) := by
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hfac]
  infer_instance

/-- **Mayer–Vietoris is right exact at `H₀(X)`:** `H₀(A) ⊞ H₀(B) ⟶ H₀(X) ⟶ 0`. -/
theorem epi_mvKappa_zero {X : TopCat.{0}} (A B : Set X)
    (h : interior A ∪ interior B = Set.univ) : Epi (mvKappa A B 0) := by
  haveI hg : Epi (HomologicalComplex.homologyMap (mvSC A B).g 0) :=
    epi_homologyMap_zero (mvSC_shortExact A B)
  haveI : Epi ((mvSumIso A B 0).hom ≫ mvKappa A B 0) := by
    rw [homologyMap_mvSC_g A B h 0]; infer_instance
  exact epi_of_epi (mvSumIso A B 0).hom (mvKappa A B 0)

/-! ### The homology of the empty space -/

instance isEmpty_toSSet_obj (Y : TopCat.{0}) [IsEmpty Y] (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj Y) _⦋n⦌) := by
  refine ⟨fun s => ?_⟩
  exact IsEmpty.elim (inferInstanceAs (IsEmpty Y))
    (Y.toSSetObjEquiv (op ⦋n⦌) s (stdSimplex.vertex 0))

/-- The singular homology of the empty space vanishes. -/
theorem isZero_Hgrp_of_isEmpty (Y : TopCat.{0}) [IsEmpty Y] (n : ℕ) : IsZero (Hgrp n Y) := by
  have hK : IsZero (Csing Y) := by
    refine (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun i => ?_)
    have hXi : IsZero ((Csing Y).X i) :=
      (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ (fun j => isEmptyElim j))
    exact hXi.eq_of_src _ _
  exact (HomologicalComplex.homologyFunctor AddCommGrpCat.{0}
    (ComplexShape.down ℕ) n).map_isZero hK

/-! ### Reduced homology in degree zero -/

instance instPathConnectedSpacePUnit : PathConnectedSpace (TopCat.of PUnit.{1}) := by
  constructor
  · exact ⟨PUnit.unit⟩
  · intro x y
    exact ⟨(Path.refl x).cast rfl (Subsingleton.elim x y)⟩

/-- **`H̃₀(X) = 0` for a path-connected space.** -/
theorem isZero_Hred_zero_of_pathConnected {X : TopCat.{0}} [PathConnectedSpace X] (x : X) :
    IsZero (Hred 0 x) := by
  haveI hepi : Epi (relJ 0 (ptIncl x)) :=
    epi_homologyMap_zero (relShortComplex_shortExact (ptIncl x))
  haveI : IsIso (relIota 0 (ptIncl x)) := isIso_HgrpMap_zero (ptIncl x)
  have hz : relJ 0 (ptIncl x) = 0 := relJ_eq_zero_of_epi (ptIncl x) 0 inferInstance
  refine (IsZero.iff_id_eq_zero _).2 ((cancel_epi (relJ 0 (ptIncl x))).1 ?_)
  rw [Category.comp_id, comp_zero, hz]

/-! ### Additivity of `H₀` over a clopen partition -/

/-- **Additivity of `H₀`.**  If `A` and `B` are disjoint and their interiors cover `X`, the
Mayer–Vietoris map `H₀(A) ⊞ H₀(B) ⟶ H₀(X)` is an isomorphism.  (Monomorphism because the
intersection is empty, epimorphism by right exactness.) -/
theorem isIso_mvKappa_zero_of_isEmpty_inter {X : TopCat.{0}} (A B : Set X)
    (h : interior A ∪ interior B = Set.univ) [IsEmpty (A ∩ B : Set X)] :
    IsIso (mvKappa A B 0) := by
  haveI : Epi (mvKappa A B 0) := epi_mvKappa_zero A B h
  have hι : mvIota A B 0 = 0 :=
    (isZero_Hgrp_of_isEmpty (TopCat.of (A ∩ B : Set X)) 0).eq_zero_of_src _
  haveI : Mono (mvKappa A B 0) := (mayerVietoris_exact_iota_kappa A B h 0).mono_g hι
  exact isIso_of_mono_of_epi _

/-- `H₀(A) ⊞ H₀(B) ≅ H₀(X)` for a clopen partition `X = A ⊔ B`. -/
def mvKappaZeroIso {X : TopCat.{0}} (A B : Set X)
    (h : interior A ∪ interior B = Set.univ) [IsEmpty (A ∩ B : Set X)] :
    mvSum A B 0 ≅ Hgrp 0 X :=
  haveI := isIso_mvKappa_zero_of_isEmpty_inter A B h
  asIso (mvKappa A B 0)

end Submission
