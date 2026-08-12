/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SimplexCubeClass
import Submission.Hurewicz.SphereLoopBridge
import Submission.Hurewicz.StickBoundary

/-!
# The sphere reparameterization induced by stick-breaking

Composing stick-breaking coordinates with the inverse of the chosen cube--simplex
homeomorphism gives a self-map of the cube.  It is not injective on the cubical boundary, but it
preserves the boundary exactly and is injective away from it.  It therefore induces a genuine
self-homeomorphism after the boundary is collapsed to a sphere.

This is the geometric change of coordinates between the cubical representative used by the
relative Hurewicz construction and the stick-breaking representative used by simplicial
homotopy addition.
-/

open scoped Topology Topology.Homotopy unitInterval
open HomotopyGroups

noncomputable section

namespace Submission

/-- Stick-breaking, expressed as a self-map of the chosen cubical coordinates. -/
noncomputable def stickCubeReparam (d : ℕ) : C(I^Fin d, I^Fin d) :=
  (⟨(cubeHomeoSimplex d).symm, (cubeHomeoSimplex d).continuous_symm⟩ :
      C(stdSimplex ℝ (Fin (d + 1)), I^Fin d)).comp (stickSimplex d)

@[simp]
theorem stickCubeReparam_apply (d : ℕ) (t : I^Fin d) :
    stickCubeReparam d t = (cubeHomeoSimplex d).symm (stickSimplex d t) :=
  rfl

/-- The cubical stick reparameterization preserves and reflects the boundary. -/
theorem stickCubeReparam_mem_boundary_iff (d : ℕ) (t : I^Fin d) :
    stickCubeReparam d t ∈ Cube.boundary (Fin d) ↔
      t ∈ Cube.boundary (Fin d) := by
  constructor
  · intro ht
    have hs : stickSimplex d t ∈ bdry d := by
      have := cubeHomeoSimplex_mem_bdry d (stickCubeReparam d t) ht
      simpa [stickCubeReparam] using this
    exact mem_cube_boundary_of_stickSimplex_mem_bdry d t hs
  · intro ht
    exact cubeHomeoSimplex_symm_mem_boundary d _ (stickSimplex_mem_bdry d t ht)

/-- The cubical stick reparameterization is surjective. -/
theorem stickCubeReparam_surjective (d : ℕ) :
    Function.Surjective (stickCubeReparam d) := by
  intro y
  obtain ⟨t, ht⟩ := stickSimplex_surjective d (cubeHomeoSimplex d y)
  refine ⟨t, ?_⟩
  apply (cubeHomeoSimplex d).injective
  simp [stickCubeReparam, ht]

/-- Stick reparameterization preserves exactly the fibres of the cubical sphere quotient. -/
theorem cubeToSphere_stickCubeReparam_eq_iff (d : ℕ) (u v : I^Fin d) :
    cubeToSphere d (stickCubeReparam d u) =
        cubeToSphere d (stickCubeReparam d v) ↔
      cubeToSphere d u = cubeToSphere d v := by
  rw [cubeToSphere_eq_iff, cubeToSphere_eq_iff]
  constructor
  · rintro (huv | ⟨hu, hv⟩)
    · by_cases hu' : u ∈ Cube.boundary (Fin d)
      · right
        refine ⟨hu', ?_⟩
        apply (stickCubeReparam_mem_boundary_iff d v).mp
        rw [← huv]
        exact (stickCubeReparam_mem_boundary_iff d u).mpr hu'
      · have hv' : v ∉ Cube.boundary (Fin d) := by
          intro hv'
          apply hu'
          apply (stickCubeReparam_mem_boundary_iff d u).mp
          rw [huv]
          exact (stickCubeReparam_mem_boundary_iff d v).mpr hv'
        left
        apply stickSimplex_injective_of_not_mem_boundary d u v hu' hv'
        have h := congrArg (cubeHomeoSimplex d) huv
        simpa [stickCubeReparam] using h
    · right
      exact ⟨(stickCubeReparam_mem_boundary_iff d u).mp hu,
        (stickCubeReparam_mem_boundary_iff d v).mp hv⟩
  · rintro (rfl | ⟨hu, hv⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨(stickCubeReparam_mem_boundary_iff d u).mpr hu,
        (stickCubeReparam_mem_boundary_iff d v).mpr hv⟩

/-- The sphere-valued stick reparameterization is constant on the fibres of the cubical sphere
quotient. -/
theorem cubeToSphere_stickCubeReparam_factorsThrough (n : ℕ) :
    Function.FactorsThrough
      ((cubeToSphere (n + 1)).comp (stickCubeReparam (n + 1)))
      (cubeToSphere (n + 1)) := by
  intro u v huv
  exact (cubeToSphere_stickCubeReparam_eq_iff (n + 1) u v).2 huv

/-- The self-map of the positive-dimensional sphere induced by stick-breaking coordinates. -/
noncomputable def stickSphereMap (n : ℕ) :
    C(SphereSpace (n + 1), SphereSpace (n + 1)) :=
  (isQuotientMap_cubeToSphere n).lift
    ((cubeToSphere (n + 1)).comp (stickCubeReparam (n + 1)))
    (cubeToSphere_stickCubeReparam_factorsThrough n)

/-- The defining quotient triangle for the stick sphere map. -/
@[simp]
theorem stickSphereMap_comp_cubeToSphere (n : ℕ) :
    (stickSphereMap n).comp (cubeToSphere (n + 1)) =
      (cubeToSphere (n + 1)).comp (stickCubeReparam (n + 1)) :=
  (isQuotientMap_cubeToSphere n).lift_comp _ _

@[simp]
theorem stickSphereMap_cubeToSphere (n : ℕ) (u : I^Fin (n + 1)) :
    stickSphereMap n (cubeToSphere (n + 1) u) =
      cubeToSphere (n + 1) (stickCubeReparam (n + 1) u) := by
  have h := congrArg (fun f : C(I^Fin (n + 1), SphereSpace (n + 1)) => f u)
    (stickSphereMap_comp_cubeToSphere n)
  exact h

/-- The induced sphere map preserves the benchmark basepoint. -/
@[simp]
theorem stickSphereMap_basepoint (n : ℕ) :
    stickSphereMap n (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1) := by
  let u : I^Fin (n + 1) := fun _ => 0
  have hu : u ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  calc
    stickSphereMap n (sphereBasepoint (n + 1)) =
        stickSphereMap n (cubeToSphere (n + 1) u) := by
          rw [cubeToSphere_boundary (n + 1) u hu]
    _ = cubeToSphere (n + 1) (stickCubeReparam (n + 1) u) :=
      stickSphereMap_cubeToSphere n u
    _ = sphereBasepoint (n + 1) := cubeToSphere_boundary _ _
      ((stickCubeReparam_mem_boundary_iff (n + 1) u).2 hu)

/-- The induced sphere map is injective. -/
theorem stickSphereMap_injective (n : ℕ) : Function.Injective (stickSphereMap n) := by
  intro z w hzw
  obtain ⟨u, rfl⟩ := cubeToSphere_surjective n z
  obtain ⟨v, rfl⟩ := cubeToSphere_surjective n w
  rw [stickSphereMap_cubeToSphere, stickSphereMap_cubeToSphere] at hzw
  exact (cubeToSphere_stickCubeReparam_eq_iff (n + 1) u v).1 hzw

/-- The induced sphere map is surjective. -/
theorem stickSphereMap_surjective (n : ℕ) : Function.Surjective (stickSphereMap n) := by
  intro z
  obtain ⟨y, rfl⟩ := cubeToSphere_surjective n z
  obtain ⟨u, rfl⟩ := stickCubeReparam_surjective (n + 1) y
  exact ⟨cubeToSphere (n + 1) u, stickSphereMap_cubeToSphere n u⟩

/-- The quotient-sphere stick reparameterization is a homeomorphism. -/
theorem isHomeomorph_stickSphereMap (n : ℕ) : IsHomeomorph (stickSphereMap n) := by
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨(stickSphereMap n).continuous,
    stickSphereMap_injective n, stickSphereMap_surjective n⟩

/-- Stick-breaking supplies a based self-homeomorphism of every positive-dimensional sphere. -/
noncomputable def stickSphereHomeomorph (n : ℕ) :
    SphereSpace (n + 1) ≃ₜ SphereSpace (n + 1) :=
  (isHomeomorph_stickSphereMap n).homeomorph (stickSphereMap n)

@[simp]
theorem stickSphereHomeomorph_apply (n : ℕ) (z : SphereSpace (n + 1)) :
    stickSphereHomeomorph n z = stickSphereMap n z :=
  rfl

@[simp]
theorem stickSphereHomeomorph_basepoint (n : ℕ) :
    stickSphereHomeomorph n (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1) :=
  stickSphereMap_basepoint n

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Reparameterize a positive-dimensional cubical loop by the stick sphere homeomorphism. -/
noncomputable def stickReparamGenLoop (n : ℕ) (α : Ω^ (Fin (n + 1)) X x) :
    Ω^ (Fin (n + 1)) X x :=
  sphereTargetMapGenLoop (n + 1)
    ((targetGenLoopSphereMap n α).comp (stickSphereMap n)) (by
      rw [ContinuousMap.comp_apply, stickSphereMap_basepoint,
        targetGenLoopSphereMap_basepoint])

/-- On cubical representatives, sphere-level stick reparameterization is exactly precomposition
by the cubical stick map. -/
@[simp]
theorem stickReparamGenLoop_apply (n : ℕ) (α : Ω^ (Fin (n + 1)) X x)
    (u : I^Fin (n + 1)) :
    stickReparamGenLoop n α u = α (stickCubeReparam (n + 1) u) := by
  change targetGenLoopSphereMap n α
      (stickSphereMap n (cubeToSphere (n + 1) u)) = _
  rw [stickSphereMap_cubeToSphere]
  have h := congrArg (fun f : C(I^Fin (n + 1), X) =>
      f (stickCubeReparam (n + 1) u))
    (targetGenLoopSphereMap_comp_cubeToSphere n α)
  exact h

/-- Stick reparameterization respects relative cubical homotopy. -/
theorem stickReparamGenLoop_homotopic (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) X x} (h : GenLoop.Homotopic α β) :
    GenLoop.Homotopic (stickReparamGenLoop n α) (stickReparamGenLoop n β) := by
  obtain ⟨H, hbase⟩ := (targetGenLoop_homotopic_iff n α β).1 h
  let f := (targetGenLoopSphereMap n α).comp (stickSphereMap n)
  let g := (targetGenLoopSphereMap n β).comp (stickSphereMap n)
  have hf : f (sphereBasepoint (n + 1)) = x := by
    change targetGenLoopSphereMap n α
      (stickSphereMap n (sphereBasepoint (n + 1))) = x
    rw [stickSphereMap_basepoint]
    exact targetGenLoopSphereMap_basepoint n α
  have hg : g (sphereBasepoint (n + 1)) = x := by
    change targetGenLoopSphereMap n β
      (stickSphereMap n (sphereBasepoint (n + 1))) = x
    rw [stickSphereMap_basepoint]
    exact targetGenLoopSphereMap_basepoint n β
  have hcomp : GenLoop.Homotopic
      (sphereTargetMapGenLoop (n + 1) f hf)
      (sphereTargetMapGenLoop (n + 1) g hg) :=
    sphereTargetMapGenLoopHomotopy (n + 1) hf hg
      (H.compContinuousMap (stickSphereMap n)) (by
        intro t
        change H (t, stickSphereMap n (sphereBasepoint (n + 1))) = x
        rw [stickSphereMap_basepoint]
        exact hbase t)
  simpa only [stickReparamGenLoop, f, g] using hcomp

/-- Stick reparameterization as a well-defined operation on positive-dimensional homotopy
classes. -/
noncomputable def stickReparamClass (n : ℕ) :
    π_ (n + 1) X x → π_ (n + 1) X x :=
  Quotient.lift (fun α => (⟦stickReparamGenLoop n α⟧ : π_ (n + 1) X x))
    (fun _ _ h => Quotient.sound (stickReparamGenLoop_homotopic n h))

@[simp]
theorem stickReparamClass_mk (n : ℕ) (α : Ω^ (Fin (n + 1)) X x) :
    stickReparamClass n (⟦α⟧ : π_ (n + 1) X x) = ⟦stickReparamGenLoop n α⟧ :=
  rfl

/-- Reparameterization by the stick sphere homeomorphism is injective on homotopy classes. -/
theorem stickReparamClass_injective (n : ℕ) :
    Function.Injective (stickReparamClass (X := X) (x := x) n) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ α =>
    induction b using Quotient.inductionOn with
    | _ β =>
      apply Quotient.sound
      have hreparam : GenLoop.Homotopic
          (stickReparamGenLoop n α) (stickReparamGenLoop n β) :=
        Quotient.exact hab
      obtain ⟨H, hbase⟩ :=
        (targetGenLoop_homotopic_iff n
          (stickReparamGenLoop n α) (stickReparamGenLoop n β)).1 hreparam
      let f := targetGenLoopSphereMap n α
      let g := targetGenLoopSphereMap n β
      have hf : f (sphereBasepoint (n + 1)) = x :=
        targetGenLoopSphereMap_basepoint n α
      have hg : g (sphereBasepoint (n + 1)) = x :=
        targetGenLoopSphereMap_basepoint n β
      have hα : targetGenLoopSphereMap n (stickReparamGenLoop n α) =
          f.comp (stickSphereMap n) := by
        exact targetGenLoopSphereMap_sphereTargetMapGenLoop n _ _
      have hβ : targetGenLoopSphereMap n (stickReparamGenLoop n β) =
          g.comp (stickSphereMap n) := by
        exact targetGenLoopSphereMap_sphereTargetMapGenLoop n _ _
      let H' : ContinuousMap.Homotopy
          (f.comp (stickSphereMap n)) (g.comp (stickSphereMap n)) :=
        H.cast hα hβ
      have hbase' : ∀ t : I, H' (t, sphereBasepoint (n + 1)) = x := by
        intro t
        exact hbase t
      let einv : C(SphereSpace (n + 1), SphereSpace (n + 1)) :=
        ⟨(stickSphereHomeomorph n).symm,
          (stickSphereHomeomorph n).continuous_symm⟩
      have heinv_base : einv (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1) := by
        apply (stickSphereHomeomorph n).injective
        simp [einv]
      have hfe : (f.comp (stickSphereMap n)).comp einv = f := by
        apply ContinuousMap.ext
        intro z
        change f (stickSphereMap n ((stickSphereHomeomorph n).symm z)) = f z
        rw [← stickSphereHomeomorph_apply]
        simp
      have hge : (g.comp (stickSphereMap n)).comp einv = g := by
        apply ContinuousMap.ext
        intro z
        change g (stickSphereMap n ((stickSphereHomeomorph n).symm z)) = g z
        rw [← stickSphereHomeomorph_apply]
        simp
      let K : ContinuousMap.Homotopy f g :=
        (H'.compContinuousMap einv).cast hfe hge
      apply (targetGenLoop_homotopic_iff n α β).2
      refine ⟨K, ?_⟩
      intro t
      change H' (t, einv (sphereBasepoint (n + 1))) = x
      rw [heinv_base]
      exact hbase' t

namespace NormalizedSimplex

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

/-- The stick map of a normalized simplex is its chosen cubical map precomposed with the
cubical stick reparameterization. -/
theorem stickMap_eq_cubeMap_comp_stickCubeReparam (s : NormalizedSimplex n X x) :
    s.stickMap = s.cubeMap.comp (stickCubeReparam (n + 2)) := by
  apply ContinuousMap.ext
  intro t
  simp [stickMap, cubeMap, stickCubeReparam]

/-- After descent to the quotient sphere, the stick representative is the cubical
representative precomposed with the stick sphere homeomorphism. -/
theorem targetGenLoopSphereMap_toStickGenLoop (s : NormalizedSimplex n X x) :
    targetGenLoopSphereMap (n + 1) s.toStickGenLoop =
      (targetGenLoopSphereMap (n + 1) s.toGenLoop).comp (stickSphereMap (n + 1)) := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨u, rfl⟩ := cubeToSphere_surjective (n + 1) z
  have hstick := congrArg (fun f : C(I^Fin (n + 2), X) => f u)
    (targetGenLoopSphereMap_comp_cubeToSphere (n + 1) s.toStickGenLoop)
  have hcube := congrArg (fun f : C(I^Fin (n + 2), X) =>
      f (stickCubeReparam (n + 2) u))
    (targetGenLoopSphereMap_comp_cubeToSphere (n + 1) s.toGenLoop)
  rw [ContinuousMap.comp_apply, stickSphereMap_cubeToSphere]
  calc
    targetGenLoopSphereMap (n + 1) s.toStickGenLoop (cubeToSphere (n + 2) u) =
        s.toStickGenLoop u := hstick
    _ = s.toGenLoop (stickCubeReparam (n + 2) u) := by
      have h := congrArg (fun f : C(I^Fin (n + 2), X) => f u)
        s.stickMap_eq_cubeMap_comp_stickCubeReparam
      exact h
    _ = targetGenLoopSphereMap (n + 1) s.toGenLoop
        (cubeToSphere (n + 2) (stickCubeReparam (n + 2) u)) := hcube.symm

/-- On normalized simplices, class-level stick reparameterization changes the chosen cubical
coordinates into stick-breaking coordinates. -/
@[simp]
theorem stickReparamClass_homotopyClass (s : NormalizedSimplex n X x) :
    stickReparamClass (n + 1) s.homotopyClass = s.stickHomotopyClass := by
  rw [homotopyClass, stickReparamClass_mk, stickHomotopyClass]
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro u
  rw [stickReparamGenLoop_apply]
  have h := congrArg (fun f : C(I^Fin (n + 2), X) => f u)
    s.stickMap_eq_cubeMap_comp_stickCubeReparam
  exact h.symm

end NormalizedSimplex

end Submission
