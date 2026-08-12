/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SimplexCubeClass
import Submission.Hurewicz.CubeFundamentalClass
import Submission.Model.SphereConnected

/-!
# The orientation coefficient of the explicit cube simplex

The explicit simplex class of `Submission.Hurewicz.SimplexCubeClass` and the canonical oriented
fundamental class of `Submission.Hurewicz.CubeFundamentalClass` both lie in the infinite cyclic
group `H_{n+2}(I^{n+2}, ∂I^{n+2})`.  This file names the integer relating them and proves that it
is a unit.  The key point is that the coherent normalization deformation makes multiplication by
this integer surjective on the first nonvanishing relative homology of every sufficiently
connected space.  Applying that statement to a sphere forces the coefficient to be `1` or `-1`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

-- Upstream Mathlib marks these `@[implicit_reducible]`; our pinned revision does not.
attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.alternatingFaceMapComplex AlgebraicTopology.AlternatingFaceMapComplex.obj
  SSet.chainComplexFunctor AlgebraicTopology.singularChainComplexFunctor
  CategoryTheory.Functor.postcompose₂ CategoryTheory.SimplicialObject.whiskering
  CategoryTheory.Functor.whiskeringLeft CategoryTheory.Functor.comp

noncomputable section

namespace Submission

/-- The integer represented by the explicit simplex class under the chosen orientation of the
top relative homology of the cube pair. -/
noncomputable def cubeSimplexOrientationDegree (n : ℕ) : ℤ :=
  (cubePairTopHomologyIsoInt n).hom (cubeSimplexRelativeClass n)

/-- The explicit simplex class is the orientation coefficient times the canonical fundamental
class. -/
theorem cubeSimplexRelativeClass_eq_degree_smul (n : ℕ) :
    cubeSimplexRelativeClass n =
      cubeSimplexOrientationDegree n • cubePairFundamentalClass n := by
  apply (AddCommGrpCat.mono_iff_injective (cubePairTopHomologyIsoInt n).hom).1 inferInstance
  rw [map_zsmul, cubePairTopHomologyIsoInt_fundamentalClass]
  simp [cubeSimplexOrientationDegree]

/-- Consequently, the explicit-simplex evaluator is the orientation coefficient times the
canonical relative Hurewicz evaluator. -/
theorem simplexRelativeHurewicz_eq_degree_smul_relativeHurewicz (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (z : π_rel (n + 2) X A a) :
    simplexRelativeHurewicz n A a z =
      cubeSimplexOrientationDegree n • relativeHurewicz n A a z := by
  induction z using Quotient.inductionOn with
  | _ p =>
      rw [simplexRelativeHurewicz_mk, relativeHurewicz_mk,
        cubeSimplexRelativeClass_eq_degree_smul, map_zsmul]

/-- A normalized simplex class is the orientation coefficient times the canonical relative
Hurewicz class of its cubical reparametrisation. -/
theorem NormalizedSimplex.degree_smul_relativeHurewicz_toRelGenLoop
    {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (s : NormalizedSimplex n X x) :
    cubeSimplexOrientationDegree n •
        relativeHurewicz n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))
          (⟦s.toRelGenLoop⟧ : π_rel (n + 2) X ({x} : Set X) ⟨x, rfl⟩) =
      s.relativeClass := by
  rw [← simplexRelativeHurewicz_eq_degree_smul_relativeHurewicz]
  exact s.simplexRelativeHurewicz_toRelGenLoop

/-- The degreewise relative-chain projection is surjective. -/
theorem relProj_f_surjective {X : Type} [TopologicalSpace X]
    (A : Set (TopCat.of X)) (k : ℕ) :
    Function.Surjective ((relProj (subIncl A)).f k) := by
  letI : Epi (cokernel.π (CsingMap (subIncl A))) := coequalizer.π_epi
  exact (AddCommGrpCat.epi_iff_surjective _).1
    (inferInstance : Epi ((cokernel.π (CsingMap (subIncl A))).f k))

namespace IsNConnected

variable {n : ℕ} {X : Type} [TopologicalSpace X]

attribute [local implicit_reducible] relComplex Hrel

/-- In the degree immediately below the normalized simplices, the point deformation vanishes on
relative chains. -/
theorem pointDeformation_relativeSelfMap_f_prev_eq_zero
    (hX : IsNConnected (n + 1) X) (x : X) :
    (hX.pointDeformation x).relativeSelfMap.f (n + 1) = 0 := by
  ext r
  obtain ⟨a, rfl⟩ := relProj_f_surjective (X := X) ({x} : Set (TopCat.of X)) (n + 1) r
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    (hX.pointDeformation x).relProj_comp_relativeSelfMap,
    HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply,
    (hX.pointDeformation x).selfMap_comp_relProj (n + 1) (by omega), zero_hom_apply]
  rfl

/-- Applying the top-dimensional point deformation to any relative chain produces a cycle. -/
theorem pointDeformation_relativeTopCycle (hX : IsNConnected (n + 1) X) (x : X)
    (a : (CsingSSet (Sng (TopCat.of X))).X (n + 2)) :
    (relComplex (subIncl (Y := TopCat.of X) ({x} : Set X))).d (n + 2) (n + 1)
        ((hX.pointDeformation x).relativeSelfMap.f (n + 2)
          ((relProj (subIncl (Y := TopCat.of X) ({x} : Set X))).f (n + 2) a)) = 0 := by
  rw [← ConcreteCategory.comp_apply,
    (hX.pointDeformation x).relativeSelfMap.comm (n + 2) (n + 1),
    ConcreteCategory.comp_apply,
    hX.pointDeformation_relativeSelfMap_f_prev_eq_zero x, zero_hom_apply]

/-- The homology class of the top-dimensional point deformation, as an additive map on absolute
singular chains. -/
noncomputable def pointDeformationTopClassHom (hX : IsNConnected (n + 1) X) (x : X) :
    ((CsingSSet (Sng (TopCat.of X))).X (n + 2) : Type) →+
      (HrelSet (Y := TopCat.of X) (n + 2) ({x} : Set X) : Type) where
  toFun a := homologyMk
    ((hX.pointDeformation x).relativeSelfMap.f (n + 2)
      ((relProj (subIncl (Y := TopCat.of X) ({x} : Set X))).f (n + 2) a)) (by
        rw [ChainComplex.next_nat_succ]
        exact hX.pointDeformation_relativeTopCycle x a)
  map_zero' := by
    simp only [map_zero]
    change homologyMk 0 _ = 0
    exact homologyMk_zero
  map_add' a b := by
    simp only [map_add]
    change homologyMk (_ + _) _ = _
    exact homologyMk_add _ _ _ _

/-- The categorical morphism underlying `pointDeformationTopClassHom`. -/
noncomputable def pointDeformationTopClassChain (hX : IsNConnected (n + 1) X) (x : X) :
    (CsingSSet (Sng (TopCat.of X))).X (n + 2) ⟶
      HrelSet (Y := TopCat.of X) (n + 2) ({x} : Set X) :=
  AddCommGrpCat.ofHom (hX.pointDeformationTopClassHom x)

/-- On a singular generator, the top deformation class is the relative class of its normalized
simplex. -/
@[simp]
theorem pointDeformationTopClassChain_gen (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 2⦌) :
    hX.pointDeformationTopClassChain x (gen s) =
      (hX.normalizeTopSimplex x s).relativeClass := by
  unfold pointDeformationTopClassChain pointDeformationTopClassHom
  change homologyMk
      ((hX.pointDeformation x).relativeSelfMap.f (n + 2)
        (relativeSimplexChain (X := TopCat.of X) ({x} : Set X) s)) _ = _
  unfold NormalizedSimplex.relativeClass relativeSimplexClass
  exact homologyMk_congr _ _ (hX.pointDeformation_relativeSimplexChain x s)

/-- Send a top singular simplex to the canonical relative Hurewicz class of its normalized
cubical loop. -/
noncomputable def normalizedRelativeHurewiczChain (hX : IsNConnected (n + 1) X) (x : X) :
    (CsingSSet (Sng (TopCat.of X))).X (n + 2) ⟶
      HrelSet (Y := TopCat.of X) (n + 2) ({x} : Set X) :=
  ccDesc fun s ↦ intHom
    (relativeHurewicz n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))
      (⟦(hX.normalizeTopSimplex x s).toRelGenLoop⟧ :
        π_rel (n + 2) X ({x} : Set X) ⟨x, rfl⟩))

@[simp]
theorem normalizedRelativeHurewiczChain_gen (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 2⦌) :
    hX.normalizedRelativeHurewiczChain x (gen s) =
      relativeHurewicz n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))
        (⟦(hX.normalizeTopSimplex x s).toRelGenLoop⟧ :
          π_rel (n + 2) X ({x} : Set X) ⟨x, rfl⟩) := by
  rw [normalizedRelativeHurewiczChain, ccDesc_gen, intHom_one]

/-- On every top chain, the deformation class is the orientation coefficient times the chain of
canonical relative Hurewicz values. -/
theorem pointDeformationTopClassChain_eq_degree_smul
    (hX : IsNConnected (n + 1) X) (x : X) :
    hX.pointDeformationTopClassChain x =
      cubeSimplexOrientationDegree n • hX.normalizedRelativeHurewiczChain x := by
  refine chainComplexX_hom_ext fun s ↦ ?_
  rw [pointDeformationTopClassChain_gen, AddCommGrpCat.zsmul_apply,
    normalizedRelativeHurewiczChain_gen]
  exact (hX.normalizeTopSimplex x s).degree_smul_relativeHurewicz_toRelGenLoop.symm

/-- Every first-nonvanishing relative homology class is the orientation coefficient times a
finite linear combination of canonical relative Hurewicz values. -/
theorem exists_orientationDegree_smul_normalizedRelativeHurewiczChain
    (hX : IsNConnected (n + 1) X) (x : X)
    (z : HrelSet (Y := TopCat.of X) (n + 2) ({x} : Set X)) :
    ∃ a : (CsingSSet (Sng (TopCat.of X))).X (n + 2),
      cubeSimplexOrientationDegree n • hX.normalizedRelativeHurewiczChain x a = z := by
  obtain ⟨r, hr, hzr⟩ := homologyMk_surjective z
  obtain ⟨a, rfl⟩ := relProj_f_surjective (X := X) ({x} : Set (TopCat.of X)) (n + 2) r
  refine ⟨a, ?_⟩
  have hclass := ConcreteCategory.congr_hom
    (hX.pointDeformationTopClassChain_eq_degree_smul x) a
  rw [AddCommGrpCat.zsmul_apply] at hclass
  rw [← hclass]
  change homologyMk
      ((hX.pointDeformation x).relativeSelfMap.f (n + 2)
        ((relProj (subIncl (Y := TopCat.of X) ({x} : Set X))).f (n + 2) a)) _ = z
  rw [← hzr, ← homologyMap_homologyMk]
  rw [(hX.pointDeformation x).homologyMap_relativeSelfMap_eq_id,
    ConcreteCategory.id_apply]

/-- The linear combination map built from normalized relative Hurewicz values is surjective. -/
theorem surjective_normalizedRelativeHurewiczChain
    (hX : IsNConnected (n + 1) X) (x : X) :
    Function.Surjective (hX.normalizedRelativeHurewiczChain x) := by
  intro z
  obtain ⟨a, ha⟩ := hX.exists_orientationDegree_smul_normalizedRelativeHurewiczChain x z
  refine ⟨cubeSimplexOrientationDegree n • a, ?_⟩
  rw [map_zsmul]
  exact ha

/-- In every `(n+1)`-connected space, multiplication by the cube-simplex orientation coefficient
is surjective on the first potentially nonzero relative homology group of the point pair. -/
theorem surjective_orientationDegree_smul (hX : IsNConnected (n + 1) X) (x : X) :
    Function.Surjective (fun z :
      HrelSet (Y := TopCat.of X) (n + 2) ({x} : Set X) ↦
        cubeSimplexOrientationDegree n • z) := by
  intro z
  obtain ⟨a, ha⟩ := hX.exists_orientationDegree_smul_normalizedRelativeHurewiczChain x z
  exact ⟨hX.normalizedRelativeHurewiczChain x a, ha⟩

end IsNConnected

/-- The `(n+2)`-sphere is `(n+1)`-connected. -/
theorem isNConnected_sphere_succ_succ (n : ℕ) :
    IsNConnected (n + 1) (Sph (n + 2)) where
  nonempty := inferInstance
  pathConnected := pathConnectedSpace_sph (by omega)
  subsingleton_pi k hk x :=
    subsingleton_homotopyGroup_sphere_of_lt (k + 1) (n + 2) (by omega) x

/-- A fixed point of the sphere used only to turn its top homology into relative homology. -/
noncomputable def cubeOrientationSpherePoint (n : ℕ) : Sph (n + 2) :=
  Classical.choice (inferInstance : Nonempty (Sph (n + 2)))

/-- The top relative homology of a sphere modulo its chosen basepoint is infinite cyclic. -/
noncomputable def spherePointTopRelativeHomologyIsoInt (n : ℕ) :
    HrelSet (Y := TopCat.of (Sph (n + 2))) (n + 2)
        ({cubeOrientationSpherePoint n} : Set (Sph (n + 2))) ≅ AddCommGrpCat.of ℤ := by
  let i := subIncl (Y := TopCat.of (Sph (n + 2)))
    ({cubeOrientationSpherePoint n} : Set (Sph (n + 2)))
  letI : ContractibleSpace ({cubeOrientationSpherePoint n} : Set (Sph (n + 2))) := inferInstance
  have htop : IsZero (Hgrp (n + 2)
      (TopCat.of ({cubeOrientationSpherePoint n} : Set (Sph (n + 2))))) :=
    isZero_Hgrp_of_contractible (X :=
      TopCat.of ({cubeOrientationSpherePoint n} : Set (Sph (n + 2)))) (n + 1)
  have hprev : IsZero (Hgrp (n + 1)
      (TopCat.of ({cubeOrientationSpherePoint n} : Set (Sph (n + 2))))) :=
    isZero_Hgrp_of_contractible (X :=
      TopCat.of ({cubeOrientationSpherePoint n} : Set (Sph (n + 2)))) n
  letI : IsIso (relJ (n + 2) i) :=
    isIso_relJ i (n + 1) (htop.eq_zero_of_src _) (hprev.mono _)
  exact (asIso (relJ (n + 2) i)).symm ≪≫ hgrpSphereSelfIsoZ (n + 1)

/-- The explicit cube simplex has degree `1` or `-1` with respect to the canonical orientation. -/
theorem isUnit_cubeSimplexOrientationDegree (n : ℕ) :
    IsUnit (cubeSimplexOrientationDegree n) := by
  let x : Sph (n + 2) := cubeOrientationSpherePoint n
  let e := spherePointTopRelativeHomologyIsoInt n
  obtain ⟨z, hz⟩ :=
    (isNConnected_sphere_succ_succ n).surjective_orientationDegree_smul x (e.inv (1 : ℤ))
  have hz' := congrArg (fun q ↦ e.hom q) hz
  rw [map_zsmul] at hz'
  have hmul : cubeSimplexOrientationDegree n * e.hom z = 1 := by
    simpa only [smul_eq_mul, Iso.inv_hom_id_apply] using hz'
  exact isUnit_iff_exists_inv.mpr ⟨e.hom z, hmul⟩

/-- Arithmetic form of `isUnit_cubeSimplexOrientationDegree`. -/
theorem cubeSimplexOrientationDegree_eq_one_or_neg_one (n : ℕ) :
    cubeSimplexOrientationDegree n = 1 ∨ cubeSimplexOrientationDegree n = -1 :=
  Int.isUnit_iff.mp (isUnit_cubeSimplexOrientationDegree n)

/-- The explicit simplex class is the canonical cube-pair fundamental class, up to orientation. -/
theorem cubeSimplexRelativeClass_eq_fundamental_or_neg (n : ℕ) :
    cubeSimplexRelativeClass n = cubePairFundamentalClass n ∨
      cubeSimplexRelativeClass n = -cubePairFundamentalClass n := by
  rcases cubeSimplexOrientationDegree_eq_one_or_neg_one n with h | h
  · left
    rw [cubeSimplexRelativeClass_eq_degree_smul, h, one_zsmul]
  · right
    rw [cubeSimplexRelativeClass_eq_degree_smul, h, neg_one_zsmul]

/-- The orientation coefficient packaged as a unit of `ℤ`. -/
noncomputable def cubeSimplexOrientationUnit (n : ℕ) : ℤˣ :=
  (isUnit_cubeSimplexOrientationDegree n).unit

@[simp]
theorem cubeSimplexOrientationUnit_coe (n : ℕ) :
    (cubeSimplexOrientationUnit n : ℤ) = cubeSimplexOrientationDegree n :=
  (isUnit_cubeSimplexOrientationDegree n).unit_spec

/-- Canonical relative Hurewicz evaluation on a normalized simplex is its relative simplex class,
up to the inverse of the single global orientation sign. -/
theorem NormalizedSimplex.relativeHurewicz_toRelGenLoop
    {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (s : NormalizedSimplex n X x) :
    relativeHurewicz n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))
        (⟦s.toRelGenLoop⟧ : π_rel (n + 2) X ({x} : Set X) ⟨x, rfl⟩) =
      ((↑(cubeSimplexOrientationUnit n)⁻¹ : ℤ) • s.relativeClass) := by
  let u := cubeSimplexOrientationUnit n
  have h := s.degree_smul_relativeHurewicz_toRelGenLoop
  change (u : ℤ) •
      relativeHurewicz n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))
        (⟦s.toRelGenLoop⟧ : π_rel (n + 2) X ({x} : Set X) ⟨x, rfl⟩) =
    s.relativeClass at h
  calc
    relativeHurewicz n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))
        (⟦s.toRelGenLoop⟧ : π_rel (n + 2) X ({x} : Set X) ⟨x, rfl⟩) =
      (↑u⁻¹ : ℤ) • ((u : ℤ) •
        relativeHurewicz n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))
          (⟦s.toRelGenLoop⟧ : π_rel (n + 2) X ({x} : Set X) ⟨x, rfl⟩)) := by
            rw [← mul_smul]
            simp
    _ = (↑u⁻¹ : ℤ) • s.relativeClass := by rw [h]

end Submission
