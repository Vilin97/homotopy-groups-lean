/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.SphereGenerator
import Submission.ForMathlib.HomotopyGroup.Map

/-!
# Cubical loops as based maps out of a sphere

The cubical generator `Submission.cubeToSphere` is a quotient map in every positive dimension.
Consequently a generalized loop in an arbitrary pointed target descends uniquely to a based map
out of the corresponding metric sphere.  Homotopies relative to the cube boundary descend as
well, and based homotopies pull back along the quotient map.

`Submission.SphereGenerator` contained this construction for self-maps of a sphere.  The target
generality here is the form needed by the first-nonvanishing Hurewicz inverse: a normalized
singular simplex represents a map from a sphere into the ambient space, while the boundary of a
higher simplex supplies a based nullhomotopy of a sphere map.

## Main definitions and results

* `Submission.BasedSphereMap` — continuous maps `S^m ⟶ X` preserving the chosen basepoints;
* `Submission.targetGenLoopSphereMap` — descent of a positive-dimensional cubical loop;
* `Submission.genLoopEquivBasedSphereMap` — the resulting equivalence on representatives;
* `Submission.targetGenLoop_homotopic_iff` — cubical relative homotopy is exactly based sphere
  homotopy;
* `Submission.sphereTargetMapClass_eq_map_generator` — a based sphere map represents the image of
  the canonical sphere generator;
* `Submission.homotopyGroup_exists_sphereTargetMapRepresentative` — every positive-dimensional
  homotopy class has a based sphere-map representative.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

open HomotopyGroups

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y} {m : ℕ}

/-- A continuous map from the metric `m`-sphere to a pointed target, preserving basepoints. -/
def BasedSphereMap (m : ℕ) (X : Type) [TopologicalSpace X] (x : X) :=
  {f : C(SphereSpace m, X) // f (sphereBasepoint m) = x}

namespace BasedSphereMap

instance (m : ℕ) (X : Type) [TopologicalSpace X] (x : X) : CoeFun (BasedSphereMap m X x)
    fun _ ↦ SphereSpace m → X :=
  ⟨fun f ↦ f.1⟩

@[simp]
theorem coe_mk (m : ℕ) (f : C(SphereSpace m, X)) (hf : f (sphereBasepoint m) = x) :
    ((⟨f, hf⟩ : BasedSphereMap m X x) : SphereSpace m → X) = f :=
  rfl

/-- The underlying continuous map of a based sphere map. -/
def valCM (f : BasedSphereMap m X x) : C(SphereSpace m, X) := f.1

@[simp]
theorem valCM_apply (f : BasedSphereMap m X x) (z : SphereSpace m) : valCM f z = f z := rfl

@[ext]
theorem ext {f g : BasedSphereMap m X x} (h : ∀ z, f z = g z) : f = g := by
  apply Subtype.ext
  exact ContinuousMap.ext h

end BasedSphereMap

/-- A generalized loop in an arbitrary target is constant on every fibre of the cubical sphere
quotient. -/
theorem targetGenLoop_factorsThrough_cubeToSphere (n : ℕ)
    (α : Ω^ (Fin (n + 1)) X x) :
    Function.FactorsThrough (α : C(I^ Fin (n + 1), X)) (cubeToSphere (n + 1)) := by
  intro u v huv
  rcases (cubeToSphere_eq_iff (n + 1) u v).mp huv with rfl | ⟨hu, hv⟩
  · rfl
  · rw [α.property u hu, α.property v hv]

/-- Descend a positive-dimensional cubical generalized loop to a continuous map out of the
metric sphere. -/
noncomputable def targetGenLoopSphereMap (n : ℕ) (α : Ω^ (Fin (n + 1)) X x) :
    C(SphereSpace (n + 1), X) :=
  (isQuotientMap_cubeToSphere n).lift α.1
    (targetGenLoop_factorsThrough_cubeToSphere n α)

/-- Descending a loop and then precomposing with the cubical quotient recovers the loop. -/
@[simp]
theorem targetGenLoopSphereMap_comp_cubeToSphere (n : ℕ)
    (α : Ω^ (Fin (n + 1)) X x) :
    (targetGenLoopSphereMap n α).comp (cubeToSphere (n + 1)) = α.1 :=
  (isQuotientMap_cubeToSphere n).lift_comp _ _

/-- The descended sphere map preserves the chosen basepoint. -/
theorem targetGenLoopSphereMap_basepoint (n : ℕ) (α : Ω^ (Fin (n + 1)) X x) :
    targetGenLoopSphereMap n α (sphereBasepoint (n + 1)) = x := by
  let u : I^ Fin (n + 1) := fun _ ↦ 0
  have hu : u ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  calc
    targetGenLoopSphereMap n α (sphereBasepoint (n + 1)) =
        targetGenLoopSphereMap n α (cubeToSphere (n + 1) u) := by
          rw [cubeToSphere_boundary (n + 1) u hu]
    _ = α u := by
      have h := congrArg (fun f : C(I^ Fin (n + 1), X) ↦ f u)
        (targetGenLoopSphereMap_comp_cubeToSphere n α)
      exact h
    _ = x := α.property u hu

/-- The based sphere map obtained by descending a positive-dimensional generalized loop. -/
noncomputable def targetGenLoopBasedSphereMap (n : ℕ) (α : Ω^ (Fin (n + 1)) X x) :
    BasedSphereMap (n + 1) X x :=
  ⟨targetGenLoopSphereMap n α, targetGenLoopSphereMap_basepoint n α⟩

/-- Precomposition of a based sphere map with the cubical quotient gives a generalized loop. -/
noncomputable def sphereTargetMapGenLoop (m : ℕ) (f : C(SphereSpace m, X))
    (hf : f (sphereBasepoint m) = x) : Ω^ (Fin m) X x :=
  ⟨f.comp (cubeToSphere m), fun u hu ↦ by
    rw [ContinuousMap.comp_apply, cubeToSphere_boundary m u hu, hf]⟩

/-- The generalized loop underlying a based sphere map. -/
noncomputable def BasedSphereMap.toGenLoop (f : BasedSphereMap m X x) : Ω^ (Fin m) X x :=
  sphereTargetMapGenLoop m f.1 f.2

@[simp]
theorem sphereTargetMapGenLoop_apply (m : ℕ) (f : C(SphereSpace m, X))
    (hf : f (sphereBasepoint m) = x) (u : I^ Fin m) :
    sphereTargetMapGenLoop m f hf u = f (cubeToSphere m u) :=
  rfl

/-- Pullback after descent is the original positive-dimensional generalized loop. -/
@[simp]
theorem sphereTargetMapGenLoop_targetGenLoopSphereMap (n : ℕ)
    (α : Ω^ (Fin (n + 1)) X x) :
    sphereTargetMapGenLoop (n + 1) (targetGenLoopSphereMap n α)
      (targetGenLoopSphereMap_basepoint n α) = α := by
  apply GenLoop.ext
  intro u
  have h := congrArg (fun f : C(I^ Fin (n + 1), X) ↦ f u)
    (targetGenLoopSphereMap_comp_cubeToSphere n α)
  exact h

/-- Descent after pullback is the original positive-dimensional based sphere map. -/
@[simp]
theorem targetGenLoopSphereMap_sphereTargetMapGenLoop (n : ℕ)
    (f : C(SphereSpace (n + 1), X)) (hf : f (sphereBasepoint (n + 1)) = x) :
    targetGenLoopSphereMap n (sphereTargetMapGenLoop (n + 1) f hf) = f := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨u, rfl⟩ := cubeToSphere_surjective n z
  have h := congrArg (fun g : C(I^ Fin (n + 1), X) ↦ g u)
    (targetGenLoopSphereMap_comp_cubeToSphere n
      (sphereTargetMapGenLoop (n + 1) f hf))
  exact h

/-- In positive dimensions, generalized loops are equivalent to based maps out of the metric
sphere already at the level of representatives. -/
noncomputable def genLoopEquivBasedSphereMap (n : ℕ) :
    Ω^ (Fin (n + 1)) X x ≃ BasedSphereMap (n + 1) X x where
  toFun := targetGenLoopBasedSphereMap n
  invFun := BasedSphereMap.toGenLoop
  left_inv α := sphereTargetMapGenLoop_targetGenLoopSphereMap n α
  right_inv f := by
    apply BasedSphereMap.ext
    intro z
    exact ContinuousMap.congr_fun
      (targetGenLoopSphereMap_sphereTargetMapGenLoop n f.1 f.2) z

/-! ### Homotopies -/

/-- A cubical homotopy relative to the boundary, curried in the cube variable, is constant on
the fibres of the cubical sphere quotient. -/
theorem targetGenLoopHomotopyCurry_factorsThrough_cubeToSphere (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) X x}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1)))) :
    Function.FactorsThrough (H.toContinuousMap.comp ContinuousMap.prodSwap).curry
      (cubeToSphere (n + 1)) := by
  intro u v huv
  apply ContinuousMap.ext
  intro t
  change H (t, u) = H (t, v)
  rcases (cubeToSphere_eq_iff (n + 1) u v).mp huv with rfl | ⟨hu, hv⟩
  · rfl
  · rw [H.eq_fst t hu, H.eq_fst t hv, α.property u hu, α.property v hv]

/-- Descend a relative cubical homotopy to a continuous family of paths on the sphere. -/
noncomputable def targetGenLoopSphereHomotopyCurry (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) X x}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1)))) :
    C(SphereSpace (n + 1), C(I, X)) :=
  (isQuotientMap_cubeToSphere n).lift
    (H.toContinuousMap.comp ContinuousMap.prodSwap).curry
    (targetGenLoopHomotopyCurry_factorsThrough_cubeToSphere n H)

@[simp]
theorem targetGenLoopSphereHomotopyCurry_apply_cubeToSphere (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) X x}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1))))
    (u : I^ Fin (n + 1)) (t : I) :
    targetGenLoopSphereHomotopyCurry n H (cubeToSphere (n + 1) u) t = H (t, u) := by
  have h := congrArg
    (fun f : C(I^ Fin (n + 1), C(I, X)) ↦ f u t)
    ((isQuotientMap_cubeToSphere n).lift_comp
      (H.toContinuousMap.comp ContinuousMap.prodSwap).curry
      (targetGenLoopHomotopyCurry_factorsThrough_cubeToSphere n H))
  exact h

/-- A cubical homotopy relative to the boundary descends to a homotopy of sphere maps. -/
noncomputable def targetGenLoopSphereMapHomotopy (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) X x}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1)))) :
    ContinuousMap.Homotopy (targetGenLoopSphereMap n α) (targetGenLoopSphereMap n β) where
  toContinuousMap := (targetGenLoopSphereHomotopyCurry n H).uncurry.comp ContinuousMap.prodSwap
  map_zero_left z := by
    obtain ⟨u, rfl⟩ := cubeToSphere_surjective n z
    change targetGenLoopSphereHomotopyCurry n H (cubeToSphere (n + 1) u) 0 =
      targetGenLoopSphereMap n α (cubeToSphere (n + 1) u)
    rw [targetGenLoopSphereHomotopyCurry_apply_cubeToSphere]
    have h := congrArg (fun f : C(I^ Fin (n + 1), X) ↦ f u)
      (targetGenLoopSphereMap_comp_cubeToSphere n α)
    exact (H.map_zero_left u).trans h.symm
  map_one_left z := by
    obtain ⟨u, rfl⟩ := cubeToSphere_surjective n z
    change targetGenLoopSphereHomotopyCurry n H (cubeToSphere (n + 1) u) 1 =
      targetGenLoopSphereMap n β (cubeToSphere (n + 1) u)
    rw [targetGenLoopSphereHomotopyCurry_apply_cubeToSphere]
    have h := congrArg (fun f : C(I^ Fin (n + 1), X) ↦ f u)
      (targetGenLoopSphereMap_comp_cubeToSphere n β)
    exact (H.map_one_left u).trans h.symm

/-- The descended homotopy fixes the target basepoint at every time. -/
theorem targetGenLoopSphereMapHomotopy_basepoint (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) X x}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1)))) (t : I) :
    targetGenLoopSphereMapHomotopy n H (t, sphereBasepoint (n + 1)) = x := by
  let u : I^ Fin (n + 1) := fun _ ↦ 0
  have hu : u ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  have hbase : cubeToSphere (n + 1) u = sphereBasepoint (n + 1) :=
    cubeToSphere_boundary (n + 1) u hu
  conv_lhs => rw [← hbase]
  change targetGenLoopSphereHomotopyCurry n H (cubeToSphere (n + 1) u) t = _
  rw [targetGenLoopSphereHomotopyCurry_apply_cubeToSphere, H.eq_fst t hu, α.property u hu]

/-- A based homotopy of sphere maps pulls back to a homotopy relative to the cube boundary. -/
theorem sphereTargetMapGenLoopHomotopy (m : ℕ)
    {f g : C(SphereSpace m, X)}
    (hf : f (sphereBasepoint m) = x) (hg : g (sphereBasepoint m) = x)
    (H : ContinuousMap.Homotopy f g)
    (hbase : ∀ t : I, H (t, sphereBasepoint m) = x) :
    GenLoop.Homotopic (sphereTargetMapGenLoop m f hf) (sphereTargetMapGenLoop m g hg) := by
  refine ⟨H.compContinuousMap (cubeToSphere m), ?_⟩
  intro t u hu
  change H (t, cubeToSphere m u) = f (cubeToSphere m u)
  rw [cubeToSphere_boundary m u hu, hbase, hf]

/-- In positive dimensions, relative cubical homotopy is equivalent to based homotopy of the
descended sphere maps. -/
theorem targetGenLoop_homotopic_iff (n : ℕ) (α β : Ω^ (Fin (n + 1)) X x) :
    GenLoop.Homotopic α β ↔
      ∃ H : ContinuousMap.Homotopy (targetGenLoopSphereMap n α)
          (targetGenLoopSphereMap n β),
        ∀ t : I, H (t, sphereBasepoint (n + 1)) = x := by
  constructor
  · rintro ⟨H⟩
    exact ⟨targetGenLoopSphereMapHomotopy n H,
      targetGenLoopSphereMapHomotopy_basepoint n H⟩
  · rintro ⟨H, hbase⟩
    have h := sphereTargetMapGenLoopHomotopy (n + 1)
      (targetGenLoopSphereMap_basepoint n α)
      (targetGenLoopSphereMap_basepoint n β) H hbase
    simpa only [sphereTargetMapGenLoop_targetGenLoopSphereMap] using h

/-! ### Homotopy classes represented by sphere maps -/

/-- The cubical homotopy class represented by a based map from a metric sphere to an arbitrary
pointed target. -/
noncomputable def sphereTargetMapClass (m : ℕ) (f : C(SphereSpace m, X))
    (hf : f (sphereBasepoint m) = x) : π_ m X x :=
  ⟦sphereTargetMapGenLoop m f hf⟧

/-- Based-homotopic sphere maps determine the same cubical homotopy class. -/
theorem sphereTargetMapClass_eq_of_homotopy (m : ℕ)
    {f g : C(SphereSpace m, X)}
    (hf : f (sphereBasepoint m) = x) (hg : g (sphereBasepoint m) = x)
    (H : ContinuousMap.Homotopy f g)
    (hbase : ∀ t : I, H (t, sphereBasepoint m) = x) :
    sphereTargetMapClass m f hf = sphereTargetMapClass m g hg :=
  Quotient.sound (sphereTargetMapGenLoopHomotopy m hf hg H hbase)

/-- The constant based sphere map represents the identity in every positive dimension. -/
@[simp]
theorem sphereTargetMapClass_const (m : ℕ) [Nonempty (Fin m)] :
    sphereTargetMapClass (X := X) (x := x) m (ContinuousMap.const (SphereSpace m) x) rfl = 1 := by
  rw [sphereTargetMapClass, HomotopyGroup.one_def]
  have hloop : sphereTargetMapGenLoop m (ContinuousMap.const (SphereSpace m) x) rfl =
      (GenLoop.const : Ω^ (Fin m) X x) := by
    apply GenLoop.ext
    intro u
    rfl
  exact congrArg Quotient.mk' hloop

/-- A based sphere map which is based-nullhomotopic represents the identity homotopy class. -/
theorem sphereTargetMapClass_eq_one_of_nullhomotopic (m : ℕ) [Nonempty (Fin m)]
    (f : C(SphereSpace m, X)) (hf : f (sphereBasepoint m) = x)
    (H : ContinuousMap.Homotopy f (ContinuousMap.const (SphereSpace m) x))
    (hbase : ∀ t : I, H (t, sphereBasepoint m) = x) :
    sphereTargetMapClass m f hf = 1 := by
  rw [sphereTargetMapClass_eq_of_homotopy m hf rfl H hbase,
    sphereTargetMapClass_const]

/-- A based sphere map represents the image of the canonical sphere generator under its induced
map on homotopy groups. -/
theorem sphereTargetMapClass_eq_map_generator (m : ℕ) [Nonempty (Fin m)]
    (f : C(SphereSpace m, X)) (hf : f (sphereBasepoint m) = x) :
    sphereTargetMapClass m f hf =
      HomotopyGroup.map f hf (sphereGeneratorClass m) := by
  rw [sphereTargetMapClass, sphereGeneratorClass, HomotopyGroup.map_mk]
  rfl

/-- Descending a positive-dimensional loop and taking the represented sphere-map class recovers
the original cubical homotopy class. -/
@[simp]
theorem sphereTargetMapClass_targetGenLoopSphereMap (n : ℕ)
    (α : Ω^ (Fin (n + 1)) X x) :
    sphereTargetMapClass (n + 1) (targetGenLoopSphereMap n α)
      (targetGenLoopSphereMap_basepoint n α) =
      (⟦α⟧ : π_ (n + 1) X x) := by
  change (⟦sphereTargetMapGenLoop (n + 1) (targetGenLoopSphereMap n α)
    (targetGenLoopSphereMap_basepoint n α)⟧ : π_ (n + 1) X x) = ⟦α⟧
  rw [sphereTargetMapGenLoop_targetGenLoopSphereMap]

/-- Every positive-dimensional cubical homotopy class is represented by a based map out of the
corresponding metric sphere. -/
theorem homotopyGroup_exists_sphereTargetMapRepresentative (n : ℕ)
    (a : π_ (n + 1) X x) :
    ∃ (f : C(SphereSpace (n + 1), X))
        (hf : f (sphereBasepoint (n + 1)) = x),
      sphereTargetMapClass (n + 1) f hf = a := by
  induction a using Quotient.ind with
  | _ α =>
      exact ⟨targetGenLoopSphereMap n α, targetGenLoopSphereMap_basepoint n α,
        sphereTargetMapClass_targetGenLoopSphereMap n α⟩

/-- Postcomposition of a sphere representative agrees with the induced map on cubical homotopy
groups. -/
theorem sphereTargetMapClass_comp (m : ℕ) (f : C(SphereSpace m, X))
    (hf : f (sphereBasepoint m) = x) (g : C(X, Y)) (hg : g x = y) :
    sphereTargetMapClass m (g.comp f) (by simp [hf, hg]) =
      HomotopyGroup.map g hg (sphereTargetMapClass m f hf) := by
  rw [sphereTargetMapClass, sphereTargetMapClass, HomotopyGroup.map_mk]
  rfl

end Submission
