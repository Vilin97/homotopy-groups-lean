/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Model.SuspSphere
import Submission.SphereDegreeClassification

/-!
# Suspension maps on diagonal sphere homotopy classes

This file turns the explicit suspension model `Submission.Susp` and the homeomorphism
`Susp (Sph n) ≃ₜ Sph (n + 1)` into concrete operations on sphere self-maps and diagonal
homotopy classes.  In particular, suspension respects based homotopies and carries the canonical
diagonal generator to the next canonical generator.

The construction does not assert the Freudenthal range theorem.  Its eventual injectivity and
surjectivity are the remaining geometric content needed to upgrade the map below to the
successive equivalences consumed by `Submission.sphere_diagonal_mulEquiv_int_of_suspension_steps`.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

namespace Susp

universe u v

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
  {f g : C(X, Y)}

/-- The function underlying the suspension of a homotopy.  It retains the suspension height and
applies the original homotopy in the equatorial variable. -/
def mapHomotopyToFun (H : ContinuousMap.Homotopy f g) (p : I × Susp X) : Susp Y :=
  Quotient.lift
    (fun q : I × X => Susp.mk (q.1, H (p.1, q.2)))
    (by
      intro a b hab
      rcases hab with h | ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact congrArg (fun q : I × X => Susp.mk (q.1, H (p.1, q.2))) h
      · exact Susp.mk_eq_mk_of_rel (Or.inr (Or.inl ⟨hs, ht⟩))
      · exact Susp.mk_eq_mk_of_rel (Or.inr (Or.inr ⟨hs, ht⟩)))
    p.2

@[simp]
theorem mapHomotopyToFun_mk (H : ContinuousMap.Homotopy f g) (t : I) (p : I × X) :
    mapHomotopyToFun H (t, Susp.mk p) = Susp.mk (p.1, H (t, p.2)) :=
  rfl

/-- The suspended homotopy is jointly continuous in time and in the suspension variable. -/
theorem continuous_mapHomotopyToFun (H : ContinuousMap.Homotopy f g) :
    Continuous (mapHomotopyToFun H) := by
  refine Susp.isQuotientMap_mk.continuous_lift_prod_right ?_
  change Continuous fun p : I × (I × X) => Susp.mk (p.2.1, H (p.1, p.2.2))
  fun_prop

/-- Suspension carries a homotopy `f ≃ g` to a homotopy `Susp.map f ≃ Susp.map g`. -/
def mapHomotopy (H : ContinuousMap.Homotopy f g) :
    ContinuousMap.Homotopy (Susp.map f) (Susp.map g) where
  toFun := mapHomotopyToFun H
  continuous_toFun := continuous_mapHomotopyToFun H
  map_zero_left q := by
    induction q using Susp.ind with
    | h p =>
        rw [mapHomotopyToFun_mk, Susp.map_mk]
        exact congrArg (fun y => Susp.mk (p.1, y)) (H.map_zero_left p.2)
  map_one_left q := by
    induction q using Susp.ind with
    | h p =>
        rw [mapHomotopyToFun_mk, Susp.map_mk]
        exact congrArg (fun y => Susp.mk (p.1, y)) (H.map_one_left p.2)

@[simp]
theorem mapHomotopy_mk (H : ContinuousMap.Homotopy f g) (t : I) (p : I × X) :
    mapHomotopy H (t, Susp.mk p) = Susp.mk (p.1, H (t, p.2)) :=
  rfl

/-- The midpoint of the unit interval, used for the preferred equatorial basepoint. -/
def midpoint : I := ⟨1 / 2, by constructor <;> norm_num⟩

@[simp]
theorem midpoint_coe : (midpoint : ℝ) = 1 / 2 := rfl

/-- If the original homotopy fixes a point, its suspension fixes the corresponding point on the
equator. -/
theorem mapHomotopy_equator (H : ContinuousMap.Homotopy f g) (x : X) (y : Y)
    (h : ∀ t : I, H (t, x) = y) (t : I) :
    mapHomotopy H (t, Susp.mk (midpoint, x)) = Susp.mk (midpoint, y) := by
  rw [mapHomotopy_mk, h]

end Susp

/-- At the midpoint of the suspension, the meridian coefficient is one. -/
@[simp]
theorem merCoeff_half : merCoeff (1 / 2) = 1 := by
  rw [merCoeff]
  norm_num

/-- Under `Susp(Sⁿ) ≅ Sⁿ⁺¹`, the suspension of the distinguished basepoint at the equator is the
distinguished basepoint of the next sphere. -/
theorem suspSphHomeo_equator_sphereBasepoint (n : ℕ) :
    suspSphHomeo n (Susp.mk (Susp.midpoint, sphereBasepoint n)) = sphereBasepoint (n + 1) := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  induction i using Fin.lastCases with
  | last =>
      simp [suspSphHomeo_apply, suspSphLift_mk, suspSphMap_apply, suspSphFun,
        sphereBasepoint, Susp.midpoint]
  | cast i =>
      simp [suspSphHomeo_apply, suspSphLift_mk, suspSphMap_apply, suspSphFun,
        sphereBasepoint, Susp.midpoint]
      split_ifs <;> norm_num [merCoeff]

/-- The inverse sphere-suspension homeomorphism sends the distinguished basepoint to the
equatorial distinguished basepoint. -/
theorem suspSphHomeo_symm_sphereBasepoint (n : ℕ) :
    (suspSphHomeo n).symm (sphereBasepoint (n + 1)) =
      Susp.mk (Susp.midpoint, sphereBasepoint n) := by
  apply (suspSphHomeo n).injective
  rw [Homeomorph.apply_symm_apply, suspSphHomeo_equator_sphereBasepoint]

/-- Suspend a self-map of `Sⁿ` and transport it across `Susp(Sⁿ) ≅ Sⁿ⁺¹`. -/
noncomputable def sphereSuspensionSelfMap (n : ℕ) (f : C(Sph n, Sph n)) :
    C(Sph (n + 1), Sph (n + 1)) :=
  (suspSphHomeo n : C(Susp (Sph n), Sph (n + 1))).comp
    ((Susp.map f).comp (suspSphHomeo n).symm)

/-- Evaluation of a suspended sphere self-map in suspension coordinates. -/
@[simp]
theorem sphereSuspensionSelfMap_apply_susp (n : ℕ) (f : C(Sph n, Sph n))
    (q : Susp (Sph n)) :
    sphereSuspensionSelfMap n f (suspSphHomeo n q) =
      suspSphHomeo n (Susp.map f q) := by
  unfold sphereSuspensionSelfMap
  simp only [ContinuousMap.comp_apply]
  change (suspSphHomeo n)
      (Susp.map f ((suspSphHomeo n).symm (suspSphHomeo n q))) =
    suspSphHomeo n (Susp.map f q)
  exact congrArg (fun r : Susp (Sph n) => suspSphHomeo n r)
    (congrArg (Susp.map f) ((suspSphHomeo n).symm_apply_apply q))

/-- Suspension preserves the distinguished sphere basepoint. -/
theorem sphereSuspensionSelfMap_basepoint (n : ℕ) (f : C(Sph n, Sph n))
    (hf : f (sphereBasepoint n) = sphereBasepoint n) :
    sphereSuspensionSelfMap n f (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1) := by
  rw [← suspSphHomeo_equator_sphereBasepoint n,
    sphereSuspensionSelfMap_apply_susp, Susp.map_mk, hf,
    suspSphHomeo_equator_sphereBasepoint]

/-- Suspending the identity sphere self-map gives the identity in the next dimension. -/
@[simp]
theorem sphereSuspensionSelfMap_id (n : ℕ) :
    sphereSuspensionSelfMap n (ContinuousMap.id (Sph n)) =
      ContinuousMap.id (Sph (n + 1)) := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨q, rfl⟩ := (suspSphHomeo n).surjective z
  rw [sphereSuspensionSelfMap_apply_susp, Susp.map_id]
  rfl

/-- Suspension respects composition of sphere self-maps. -/
theorem sphereSuspensionSelfMap_comp (n : ℕ) (f g : C(Sph n, Sph n)) :
    sphereSuspensionSelfMap n (g.comp f) =
      (sphereSuspensionSelfMap n g).comp (sphereSuspensionSelfMap n f) := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨q, rfl⟩ := (suspSphHomeo n).surjective z
  rw [ContinuousMap.comp_apply]
  rw [sphereSuspensionSelfMap_apply_susp n (g.comp f) q]
  rw [sphereSuspensionSelfMap_apply_susp n f q]
  rw [sphereSuspensionSelfMap_apply_susp n g (Susp.map f q)]
  rw [Susp.map_comp]
  rfl

/-- Suspending a homotopy of sphere self-maps and conjugating by `Susp(Sⁿ) ≅ Sⁿ⁺¹`. -/
noncomputable def sphereSuspensionSelfMapHomotopy (n : ℕ) {f g : C(Sph n, Sph n)}
    (H : ContinuousMap.Homotopy f g) :
    ContinuousMap.Homotopy (sphereSuspensionSelfMap n f) (sphereSuspensionSelfMap n g) :=
  (ContinuousMap.Homotopy.refl
    (suspSphHomeo n : C(Susp (Sph n), Sph (n + 1)))).comp
      ((Susp.mapHomotopy H).compContinuousMap
        ((suspSphHomeo n).symm : C(Sph (n + 1), Susp (Sph n))))

/-- A suspended based homotopy remains based. -/
theorem sphereSuspensionSelfMapHomotopy_basepoint (n : ℕ) {f g : C(Sph n, Sph n)}
    (H : ContinuousMap.Homotopy f g)
    (hbase : ∀ t : I, H (t, sphereBasepoint n) = sphereBasepoint n) (t : I) :
    sphereSuspensionSelfMapHomotopy n H (t, sphereBasepoint (n + 1)) =
      sphereBasepoint (n + 1) := by
  dsimp [sphereSuspensionSelfMapHomotopy, ContinuousMap.Homotopy.compContinuousMap,
    ContinuousMap.Homotopy.comp]
  change suspSphHomeo n
    (Susp.mapHomotopy H (t, (suspSphHomeo n).symm (sphereBasepoint (n + 1)))) = _
  rw [suspSphHomeo_symm_sphereBasepoint,
    Susp.mapHomotopy_equator H (sphereBasepoint n) (sphereBasepoint n) hbase,
    suspSphHomeo_equator_sphereBasepoint]

/-- The diagonal homotopy class represented by the suspension of a based sphere self-map. -/
noncomputable def sphereSuspensionSelfMapClass (n : ℕ) (f : C(Sph n, Sph n))
    (hf : f (sphereBasepoint n) = sphereBasepoint n) :
    HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) :=
  sphereSelfMapClass (n + 1) (sphereSuspensionSelfMap n f)
    (sphereSuspensionSelfMap_basepoint n f hf)

/-- Based-homotopic sphere self-maps have equal suspended diagonal classes. -/
theorem sphereSuspensionSelfMapClass_eq_of_homotopy (n : ℕ) {f g : C(Sph n, Sph n)}
    (hf : f (sphereBasepoint n) = sphereBasepoint n)
    (hg : g (sphereBasepoint n) = sphereBasepoint n)
    (H : ContinuousMap.Homotopy f g)
    (hbase : ∀ t : I, H (t, sphereBasepoint n) = sphereBasepoint n) :
    sphereSuspensionSelfMapClass n f hf = sphereSuspensionSelfMapClass n g hg := by
  exact sphereSelfMapClass_eq_of_homotopy (n + 1)
    (sphereSuspensionSelfMap_basepoint n f hf)
    (sphereSuspensionSelfMap_basepoint n g hg)
    (sphereSuspensionSelfMapHomotopy n H)
    (sphereSuspensionSelfMapHomotopy_basepoint n H hbase)

/-- Suspend a cubical representative of a positive-dimensional diagonal sphere class. -/
noncomputable def genLoopDiagonalSuspension (n : ℕ)
    (α : Ω^ (Fin (n + 1)) (Sph (n + 1)) (sphereBasepoint (n + 1))) :
    HomotopyGroup.Pi (n + 2) (Sph (n + 2)) (sphereBasepoint (n + 2)) :=
  sphereSuspensionSelfMapClass (n + 1) (genLoopSphereMap n α)
    (genLoopSphereMap_basepoint n α)

/-- Cubically homotopic representatives have equal suspended diagonal classes. -/
theorem genLoopDiagonalSuspension_homotopyInvariant (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) (Sph (n + 1)) (sphereBasepoint (n + 1))}
    (H : GenLoop.Homotopic α β) :
    genLoopDiagonalSuspension n α = genLoopDiagonalSuspension n β := by
  obtain ⟨H⟩ := H
  exact sphereSuspensionSelfMapClass_eq_of_homotopy (n + 1)
    (genLoopSphereMap_basepoint n α) (genLoopSphereMap_basepoint n β)
    (genLoopSphereMapHomotopy n H) (genLoopSphereMapHomotopy_basepoint n H)

/-- The geometric suspension map between successive positive-dimensional diagonal sphere
homotopy classes. -/
noncomputable def sphereDiagonalSuspension (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) →
      HomotopyGroup.Pi (n + 2) (Sph (n + 2)) (sphereBasepoint (n + 2)) :=
  Quotient.lift (genLoopDiagonalSuspension n)
    (fun _ _ H => genLoopDiagonalSuspension_homotopyInvariant n H)

/-- Evaluation of diagonal suspension on a represented cubical homotopy class. -/
@[simp]
theorem sphereDiagonalSuspension_mk (n : ℕ)
    (α : Ω^ (Fin (n + 1)) (Sph (n + 1)) (sphereBasepoint (n + 1))) :
    sphereDiagonalSuspension n ⟦α⟧ = genLoopDiagonalSuspension n α :=
  rfl

/-- On a class represented by a based sphere self-map, diagonal suspension is represented by
the suspended self-map. -/
theorem sphereDiagonalSuspension_sphereSelfMapClass (n : ℕ)
    (f : C(Sph (n + 1), Sph (n + 1)))
    (hf : f (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1)) :
    sphereDiagonalSuspension n (sphereSelfMapClass (n + 1) f hf) =
      sphereSuspensionSelfMapClass (n + 1) f hf := by
  change sphereSuspensionSelfMapClass (n + 1)
    (genLoopSphereMap n (sphereSelfMapGenLoop (n + 1) f hf))
      (genLoopSphereMap_basepoint n (sphereSelfMapGenLoop (n + 1) f hf)) =
    sphereSuspensionSelfMapClass (n + 1) f hf
  let A := genLoopSphereMap n (sphereSelfMapGenLoop (n + 1) f hf)
  have hA : A (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1) :=
    genLoopSphereMap_basepoint n _
  have hmap : A = f := genLoopSphereMap_sphereSelfMapGenLoop n f hf
  let H : ContinuousMap.Homotopy A f :=
    (ContinuousMap.Homotopy.refl A).cast rfl hmap
  have hbase : ∀ t : I, H (t, sphereBasepoint (n + 1)) = sphereBasepoint (n + 1) := by
    intro t
    change A (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1)
    exact hA
  exact sphereSuspensionSelfMapClass_eq_of_homotopy (n + 1) hA hf H hbase

/-- Diagonal suspension carries the canonical generator to the canonical generator in the next
dimension. -/
@[simp]
theorem sphereDiagonalSuspension_generator (n : ℕ) :
    sphereDiagonalSuspension n (sphereGeneratorClass (n + 1)) =
      sphereGeneratorClass (n + 2) := by
  change sphereSelfMapClass (n + 2)
    (sphereSuspensionSelfMap (n + 1)
      (genLoopSphereMap n (sphereGenerator (n + 1))))
      (sphereSuspensionSelfMap_basepoint (n + 1)
        (genLoopSphereMap n (sphereGenerator (n + 1)))
        (genLoopSphereMap_basepoint n (sphereGenerator (n + 1)))) =
    sphereGeneratorClass (n + 2)
  have hmap : sphereSuspensionSelfMap (n + 1)
      (genLoopSphereMap n (sphereGenerator (n + 1))) =
      ContinuousMap.id (Sph (n + 2)) := by
    rw [genLoopSphereMap_sphereGenerator, sphereSuspensionSelfMap_id]
  let A := sphereSuspensionSelfMap (n + 1)
    (genLoopSphereMap n (sphereGenerator (n + 1)))
  have hA : A (sphereBasepoint (n + 2)) = sphereBasepoint (n + 2) :=
    sphereSuspensionSelfMap_basepoint (n + 1) _
      (genLoopSphereMap_basepoint n (sphereGenerator (n + 1)))
  let H : ContinuousMap.Homotopy A (ContinuousMap.id (Sph (n + 2))) :=
    (ContinuousMap.Homotopy.refl A).cast rfl hmap
  have hbase : ∀ t : I, H (t, sphereBasepoint (n + 2)) = sphereBasepoint (n + 2) := by
    intro t
    change A (sphereBasepoint (n + 2)) = sphereBasepoint (n + 2)
    exact hA
  calc
    sphereSelfMapClass (n + 2) A hA =
        sphereSelfMapClass (n + 2) (ContinuousMap.id (Sph (n + 2))) rfl :=
      sphereSelfMapClass_eq_of_homotopy (n + 2) hA rfl H hbase
    _ = sphereGeneratorClass (n + 2) := sphereSelfMapClass_id (n + 2)

end Submission
