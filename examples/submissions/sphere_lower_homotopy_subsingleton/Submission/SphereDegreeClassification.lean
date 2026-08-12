/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.SphereGenerator
import Submission.SphereHomologicalDegree

/-!
# Homological degree on diagonal sphere homotopy classes

The cubical generator `Iⁿ/∂Iⁿ → Sⁿ` constructed in `Submission.SphereGenerator` is a quotient
map in positive dimensions.  Thus every cubical representative descends to a based sphere
self-map, and a relative cubical homotopy descends to a based homotopy.  This file combines that
bridge with top integral homology to define a well-defined integer degree on every class in
`πₙ(Sⁿ)`.
-/

open CategoryTheory
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- The homological degree of the sphere self-map descended from a cubical representative. -/
def genLoopHomologicalDegree (n : ℕ)
    (α : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))) : ℤ :=
  sphereHomologicalDegree n (TopCat.ofHom (genLoopSphereMap n α))

/-- Cubically homotopic representatives have equal descended homological degree. -/
theorem genLoopHomologicalDegree_homotopyInvariant (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))}
    (H : GenLoop.Homotopic α β) :
    genLoopHomologicalDegree n α = genLoopHomologicalDegree n β := by
  obtain ⟨H⟩ := H
  exact sphereHomologicalDegree_homotopyInvariant n (genLoopSphereMapHomotopy n H)

/-- Homological degree as a well-defined integer-valued invariant on `πₙ(Sⁿ)`, for `n ≥ 1`. -/
def homotopyGroupSphereDegree (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (SphereSpace (n + 1)) (sphereBasepoint (n + 1)) → ℤ :=
  Quotient.lift (genLoopHomologicalDegree n)
    (fun _ _ H => genLoopHomologicalDegree_homotopyInvariant n H)

/-- Evaluation of degree on a represented cubical homotopy class. -/
@[simp]
theorem homotopyGroupSphereDegree_mk (n : ℕ)
    (α : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))) :
    homotopyGroupSphereDegree n ⟦α⟧ = genLoopHomologicalDegree n α :=
  rfl

/-- Descending the cubical generator itself gives the identity sphere self-map. -/
theorem genLoopSphereMap_sphereGenerator (n : ℕ) :
    genLoopSphereMap n (sphereGenerator (n + 1)) =
      ContinuousMap.id (SphereSpace (n + 1)) := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨x, rfl⟩ := cubeToSphere_surjective n z
  have h := congrArg (fun f : C(I^ Fin (n + 1), SphereSpace (n + 1)) => f x)
    (genLoopSphereMap_comp_cubeToSphere n (sphereGenerator (n + 1)))
  exact h

/-- The canonical diagonal sphere generator has homological degree one. -/
@[simp]
theorem homotopyGroupSphereDegree_generator (n : ℕ) :
    homotopyGroupSphereDegree n (sphereGeneratorClass (n + 1)) = 1 := by
  change sphereHomologicalDegree n
    (TopCat.ofHom (genLoopSphereMap n (sphereGenerator (n + 1)))) = 1
  rw [genLoopSphereMap_sphereGenerator]
  exact sphereHomologicalDegree_id n

/-- Descending the cubical loop obtained from a based self-map recovers that self-map. -/
theorem genLoopSphereMap_sphereSelfMapGenLoop (n : ℕ)
    (f : C(SphereSpace (n + 1), SphereSpace (n + 1)))
    (hf : f (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1)) :
    genLoopSphereMap n (sphereSelfMapGenLoop (n + 1) f hf) = f := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨x, rfl⟩ := cubeToSphere_surjective n z
  have h := congrArg (fun g : C(I^ Fin (n + 1), SphereSpace (n + 1)) => g x)
    (genLoopSphereMap_comp_cubeToSphere n (sphereSelfMapGenLoop (n + 1) f hf))
  exact h

/-- Two based sphere self-maps represent the same diagonal homotopy-group class exactly when
they are homotopic through based maps. Thus the cubical quotient used by Mathlib agrees with
the usual based-homotopy classification of sphere self-maps. -/
theorem sphereSelfMapClass_eq_iff_basedHomotopic (n : ℕ)
    {f g : C(SphereSpace (n + 1), SphereSpace (n + 1))}
    (hf : f (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1))
    (hg : g (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1)) :
    sphereSelfMapClass (n + 1) f hf = sphereSelfMapClass (n + 1) g hg ↔
      ∃ H : ContinuousMap.Homotopy f g,
        ∀ t : I, H (t, sphereBasepoint (n + 1)) = sphereBasepoint (n + 1) := by
  constructor
  · intro h
    have hloop : GenLoop.Homotopic
        (sphereSelfMapGenLoop (n + 1) f hf) (sphereSelfMapGenLoop (n + 1) g hg) :=
      Quotient.exact h
    obtain ⟨H⟩ := hloop
    rw [← genLoopSphereMap_sphereSelfMapGenLoop n f hf,
      ← genLoopSphereMap_sphereSelfMapGenLoop n g hg]
    exact ⟨genLoopSphereMapHomotopy n H, genLoopSphereMapHomotopy_basepoint n H⟩
  · rintro ⟨H, hbase⟩
    exact sphereSelfMapClass_eq_of_homotopy (n + 1) hf hg H hbase

/-- The constant cubical loop descends to the constant sphere self-map. -/
theorem genLoopSphereMap_const (n : ℕ) :
    genLoopSphereMap n
        (GenLoop.const : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))) =
      ContinuousMap.const (SphereSpace (n + 1)) (sphereBasepoint (n + 1)) := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨x, rfl⟩ := cubeToSphere_surjective n z
  have h := congrArg (fun k : C(I^ Fin (n + 1), SphereSpace (n + 1)) => k x)
    (genLoopSphereMap_comp_cubeToSphere n
      (GenLoop.const : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))))
  exact h

/-- The identity element of `πₙ(Sⁿ)` is represented by a constant map and hence has degree
zero. -/
@[simp]
theorem homotopyGroupSphereDegree_one (n : ℕ) :
    homotopyGroupSphereDegree n 1 = 0 := by
  rw [HomotopyGroup.one_def]
  change sphereHomologicalDegree n
    (TopCat.ofHom (genLoopSphereMap n
      (GenLoop.const : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))))) = 0
  rw [genLoopSphereMap_const]
  rw [show TopCat.ofHom
      (ContinuousMap.const (SphereSpace (n + 1)) (sphereBasepoint (n + 1))) =
        sphereConst n (sphereBasepoint (n + 1)) by
    ext
    rfl]
  exact sphereHomologicalDegree_const n (sphereBasepoint (n + 1))

/-- The canonical diagonal sphere generator is not nullhomotopic. -/
theorem sphereGeneratorClass_ne_one (n : ℕ) :
    sphereGeneratorClass (n + 1) ≠
      (1 : HomotopyGroup.Pi (n + 1) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))) := by
  intro h
  have hdegree := congrArg (homotopyGroupSphereDegree n) h
  rw [homotopyGroupSphereDegree_generator, homotopyGroupSphereDegree_one] at hdegree
  exact one_ne_zero hdegree

/-- Every positive-dimensional diagonal sphere homotopy group is nontrivial. -/
theorem sphere_diagonal_nontrivial (n : ℕ) :
    Nontrivial
      (HomotopyGroup.Pi (n + 1) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))) := by
  refine ⟨sphereGeneratorClass (n + 1), 1, ?_⟩
  exact sphereGeneratorClass_ne_one n

/-- On a class represented by a based sphere self-map, the class degree is the ordinary
homological degree of that self-map. -/
theorem homotopyGroupSphereDegree_sphereSelfMapClass (n : ℕ)
    (f : C(SphereSpace (n + 1), SphereSpace (n + 1)))
    (hf : f (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1)) :
    homotopyGroupSphereDegree n (sphereSelfMapClass (n + 1) f hf) =
      sphereHomologicalDegree n (TopCat.ofHom f) := by
  change sphereHomologicalDegree n
    (TopCat.ofHom (genLoopSphereMap n (sphereSelfMapGenLoop (n + 1) f hf))) = _
  rw [genLoopSphereMap_sphereSelfMapGenLoop]

/-- Every diagonal homotopy class admits a based self-map representative whose homological degree
is exactly the class invariant. -/
theorem homotopyGroup_exists_sphereSelfMapRepresentative_with_degree (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))) :
    ∃ (f : C(SphereSpace (n + 1), SphereSpace (n + 1)))
        (hf : f (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1)),
      sphereSelfMapClass (n + 1) f hf = a ∧
        sphereHomologicalDegree n (TopCat.ofHom f) = homotopyGroupSphereDegree n a := by
  obtain ⟨f, hf, hfa⟩ := homotopyGroup_exists_sphereSelfMapRepresentative n a
  refine ⟨f, hf, hfa, ?_⟩
  rw [← homotopyGroupSphereDegree_sphereSelfMapClass n f hf, hfa]

end Submission
