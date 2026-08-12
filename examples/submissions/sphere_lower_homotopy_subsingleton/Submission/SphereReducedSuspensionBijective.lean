/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Submission.Hurewicz.CubicalDegreeOne
import Submission.Hurewicz.SphereDiagonalGeneric
import Submission.SphereReducedSuspension

/-!
# Bijectivity of diagonal reduced suspension

The reduced-suspension operation on cubical homotopy groups is already a monoid homomorphism.
This file proves that its specialization to successive diagonal sphere groups is bijective.

The geometric point is that reducing the suspension of the canonical cubical quotient
`I^d / ∂I^d → S^d` gives another quotient whose only non-singleton fibre is the boundary of
`I^(d+1)`.  It therefore descends to a self-homeomorphism of `S^(d+1)`.  Consequently reduced
suspension carries the canonical generator to a generator.  The first-nonvanishing Hurewicz
calculation (and its degree-one counterpart) says that the canonical class generates every
positive-dimensional diagonal sphere group.  Elementary infinite-cyclic group theory then
upgrades the suspension homomorphism to an isomorphism.
-/

open CategoryTheory HomotopyGroups
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-! ## The suspended cubical quotient -/

/-- In positive dimension, the cubical sphere quotient hits the sphere basepoint exactly on the
cube boundary. -/
theorem cubeToSphere_eq_sphereBasepoint_iff (n : ℕ) (u : I^Fin (n + 1)) :
    cubeToSphere (n + 1) u = sphereBasepoint (n + 1) ↔
      u ∈ Cube.boundary (Fin (n + 1)) := by
  constructor
  · intro hu
    let v : I^Fin (n + 1) := fun _ => 0
    have hv : v ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
    have hvbase : cubeToSphere (n + 1) v = sphereBasepoint (n + 1) :=
      cubeToSphere_boundary (n + 1) v hv
    have huv : cubeToSphere (n + 1) u = cubeToSphere (n + 1) v := hu.trans hvbase.symm
    rcases (cubeToSphere_eq_iff (n + 1) u v).mp huv with huv | huv
    · rw [huv]
      exact hv
    · exact huv.1
  · exact cubeToSphere_boundary (n + 1) u

/-- Reindex the reduced suspension of the canonical `(n+1)`-sphere generator by the standard
coordinates of an `(n+2)`-cube. -/
noncomputable def reducedSuspensionSphereGeneratorLoop (n : ℕ) :
    Ω^ (Fin (n + 2))
      (ReducedSusp (Sph (n + 1)) (sphereBasepoint (n + 1)))
      (ReducedSusp.base (sphereBasepoint (n + 1))) :=
  GenLoop.congr (ReducedSusp.base (sphereBasepoint (n + 1)))
    (finSuccEquiv (n + 1)).symm
    (GenLoop.reducedSuspension (sphereGenerator (n + 1)))

@[simp]
theorem reducedSuspensionSphereGeneratorLoop_apply (n : ℕ) (u : I^Fin (n + 2)) :
    reducedSuspensionSphereGeneratorLoop n u =
      ReducedSusp.mk (sphereBasepoint (n + 1))
        (u 0, cubeToSphere (n + 1) (fun i => u i.succ)) := by
  rfl

/-- A point of the cylinder defining the suspended cubical generator is collapsed exactly when
the corresponding point of the larger cube lies on its boundary. -/
theorem reducedSuspensionSphereGenerator_collapsed_iff (n : ℕ) (u : I^Fin (n + 2)) :
    ReducedSuspCollapsed (sphereBasepoint (n + 1))
        (u 0, cubeToSphere (n + 1) (fun i => u i.succ)) ↔
      u ∈ Cube.boundary (Fin (n + 2)) := by
  constructor
  · rintro (hu | hu | hu)
    · exact ⟨0, Or.inl hu⟩
    · exact ⟨0, Or.inr hu⟩
    · obtain ⟨i, hi⟩ := (cubeToSphere_eq_sphereBasepoint_iff n _).mp hu
      exact ⟨i.succ, hi⟩
  · rintro ⟨i, hi⟩
    induction i using Fin.cases with
    | zero =>
        rcases hi with hi | hi
        · exact Or.inl hi
        · exact Or.inr (Or.inl hi)
    | succ j =>
        right
        right
        apply (cubeToSphere_eq_sphereBasepoint_iff n _).2
        exact ⟨j, hi⟩

/-- The reindexed suspended generator has exactly the fibres of the standard cubical sphere
quotient: points agree, or both lie on the collapsed boundary. -/
theorem reducedSuspensionSphereGeneratorLoop_eq_iff (n : ℕ) (u v : I^Fin (n + 2)) :
    reducedSuspensionSphereGeneratorLoop n u =
        reducedSuspensionSphereGeneratorLoop n v ↔
      u = v ∨
        (u ∈ Cube.boundary (Fin (n + 2)) ∧
          v ∈ Cube.boundary (Fin (n + 2))) := by
  rw [reducedSuspensionSphereGeneratorLoop_apply,
    reducedSuspensionSphereGeneratorLoop_apply, ReducedSusp.mk_eq_mk]
  constructor
  · rintro (huv | ⟨hu, hv⟩)
    · have hzero : u 0 = v 0 := congrArg Prod.fst huv
      have htail : cubeToSphere (n + 1) (fun i => u i.succ) =
          cubeToSphere (n + 1) (fun i => v i.succ) := congrArg Prod.snd huv
      rcases (cubeToSphere_eq_iff (n + 1) _ _).mp htail with htail | ⟨hu, hv⟩
      · left
        funext i
        exact Fin.cases hzero (fun j => congrFun htail j) i
      · right
        exact ⟨⟨hu.choose.succ, hu.choose_spec⟩, ⟨hv.choose.succ, hv.choose_spec⟩⟩
    · right
      exact ⟨(reducedSuspensionSphereGenerator_collapsed_iff n u).1 hu,
        (reducedSuspensionSphereGenerator_collapsed_iff n v).1 hv⟩
  · rintro (rfl | ⟨hu, hv⟩)
    · exact Or.inl rfl
    · exact Or.inr
        ⟨(reducedSuspensionSphereGenerator_collapsed_iff n u).2 hu,
          (reducedSuspensionSphereGenerator_collapsed_iff n v).2 hv⟩

/-- The suspended cubical sphere generator is onto the reduced suspension. -/
theorem reducedSuspensionSphereGeneratorLoop_surjective (n : ℕ) :
    Function.Surjective (reducedSuspensionSphereGeneratorLoop n) := by
  intro q
  obtain ⟨p, rfl⟩ := ReducedSusp.mk_surjective (sphereBasepoint (n + 1)) q
  obtain ⟨u, hu⟩ := cubeToSphere_surjective n p.2
  let v : I^Fin (n + 2) := Fin.cases p.1 u
  refine ⟨v, ?_⟩
  rw [reducedSuspensionSphereGeneratorLoop_apply]
  change ReducedSusp.mk (sphereBasepoint (n + 1))
      (p.1, cubeToSphere (n + 1) u) = ReducedSusp.mk (sphereBasepoint (n + 1)) p
  rw [hu]

/-! ## The self-homeomorphism represented by the suspended generator -/

/-- Apply the maintained reduced-suspension-to-sphere homeomorphism to the suspended cubical
generator.  This is the representative obtained by applying
`sphereDiagonalReducedSuspensionHom` to the canonical diagonal class. -/
noncomputable def sphereDiagonalReducedSuspensionGeneratorLoop (n : ℕ) :
    Ω^ (Fin (n + 2)) (Sph (n + 2)) (sphereBasepoint (n + 2)) :=
  GenLoop.congr (sphereBasepoint (n + 2)) (finSuccEquiv (n + 1)).symm
    (GenLoop.map
      ⟨ReducedSusp.sphereHomeomorph (n + 1) (sphereBasepoint (n + 1)),
        (ReducedSusp.sphereHomeomorph (n + 1)
          (sphereBasepoint (n + 1))).continuous⟩
      (ReducedSusp.sphereHomeomorph_base (n + 1) (sphereBasepoint (n + 1)))
      (GenLoop.reducedSuspension (sphereGenerator (n + 1))))

@[simp]
theorem sphereDiagonalReducedSuspensionGeneratorLoop_apply (n : ℕ)
    (u : I^Fin (n + 2)) :
    sphereDiagonalReducedSuspensionGeneratorLoop n u =
      ReducedSusp.sphereHomeomorph (n + 1) (sphereBasepoint (n + 1))
        (reducedSuspensionSphereGeneratorLoop n u) := by
  rfl

theorem sphereDiagonalReducedSuspensionGeneratorLoop_eq_iff (n : ℕ)
    (u v : I^Fin (n + 2)) :
    sphereDiagonalReducedSuspensionGeneratorLoop n u =
        sphereDiagonalReducedSuspensionGeneratorLoop n v ↔
      u = v ∨
        (u ∈ Cube.boundary (Fin (n + 2)) ∧
          v ∈ Cube.boundary (Fin (n + 2))) := by
  rw [sphereDiagonalReducedSuspensionGeneratorLoop_apply,
    sphereDiagonalReducedSuspensionGeneratorLoop_apply]
  exact (ReducedSusp.sphereHomeomorph (n + 1)
    (sphereBasepoint (n + 1))).injective.eq_iff.trans
      (reducedSuspensionSphereGeneratorLoop_eq_iff n u v)

theorem sphereDiagonalReducedSuspensionGeneratorLoop_surjective (n : ℕ) :
    Function.Surjective (sphereDiagonalReducedSuspensionGeneratorLoop n) :=
  (ReducedSusp.sphereHomeomorph (n + 1)
      (sphereBasepoint (n + 1))).surjective.comp
    (reducedSuspensionSphereGeneratorLoop_surjective n)

/-- Descend the suspended generator through the standard cubical quotient. -/
noncomputable def sphereDiagonalReducedSuspensionGeneratorMap (n : ℕ) :
    C(Sph (n + 2), Sph (n + 2)) :=
  targetGenLoopSphereMap (n + 1) (sphereDiagonalReducedSuspensionGeneratorLoop n)

@[simp]
theorem sphereDiagonalReducedSuspensionGeneratorMap_basepoint (n : ℕ) :
    sphereDiagonalReducedSuspensionGeneratorMap n (sphereBasepoint (n + 2)) =
      sphereBasepoint (n + 2) := by
  simpa only [sphereDiagonalReducedSuspensionGeneratorMap, Nat.add_assoc, Nat.reduceAdd] using
    targetGenLoopSphereMap_basepoint (n + 1)
      (sphereDiagonalReducedSuspensionGeneratorLoop n)

theorem sphereDiagonalReducedSuspensionGeneratorMap_bijective (n : ℕ) :
    Function.Bijective (sphereDiagonalReducedSuspensionGeneratorMap n) := by
  constructor
  · intro x y hxy
    obtain ⟨u, rfl⟩ := cubeToSphere_surjective (n + 1) x
    obtain ⟨v, rfl⟩ := cubeToSphere_surjective (n + 1) y
    have hu := congrArg
      (fun f : C(I^Fin (n + 2), Sph (n + 2)) => f u)
      (targetGenLoopSphereMap_comp_cubeToSphere (n + 1)
        (sphereDiagonalReducedSuspensionGeneratorLoop n))
    have hv := congrArg
      (fun f : C(I^Fin (n + 2), Sph (n + 2)) => f v)
      (targetGenLoopSphereMap_comp_cubeToSphere (n + 1)
        (sphereDiagonalReducedSuspensionGeneratorLoop n))
    have huv : sphereDiagonalReducedSuspensionGeneratorLoop n u =
        sphereDiagonalReducedSuspensionGeneratorLoop n v := hu.symm.trans (hxy.trans hv)
    exact (cubeToSphere_eq_iff (n + 2) u v).2
      ((sphereDiagonalReducedSuspensionGeneratorLoop_eq_iff n u v).1 huv)
  · intro y
    obtain ⟨u, hu⟩ := sphereDiagonalReducedSuspensionGeneratorLoop_surjective n y
    refine ⟨cubeToSphere (n + 2) u, ?_⟩
    have h := congrArg
      (fun f : C(I^Fin (n + 2), Sph (n + 2)) => f u)
      (targetGenLoopSphereMap_comp_cubeToSphere (n + 1)
        (sphereDiagonalReducedSuspensionGeneratorLoop n))
    exact h.trans hu

/-- The sphere self-map represented by the suspended canonical generator is a homeomorphism. -/
noncomputable def sphereDiagonalReducedSuspensionGeneratorHomeomorph (n : ℕ) :
    Sph (n + 2) ≃ₜ Sph (n + 2) :=
  ((isHomeomorph_iff_continuous_bijective).2
      ⟨(sphereDiagonalReducedSuspensionGeneratorMap n).continuous,
        sphereDiagonalReducedSuspensionGeneratorMap_bijective n⟩).homeomorph
    (sphereDiagonalReducedSuspensionGeneratorMap n)

@[simp]
theorem sphereDiagonalReducedSuspensionGeneratorHomeomorph_apply (n : ℕ)
    (x : Sph (n + 2)) :
    sphereDiagonalReducedSuspensionGeneratorHomeomorph n x =
      sphereDiagonalReducedSuspensionGeneratorMap n x :=
  rfl

/-! ## Infinite-cyclic generator algebra -/

/-- An equivalence carries an explicit group generator to an explicit group generator. -/
theorem forall_mem_zpowers_map_mulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) {g : G}
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    ∀ y : H, y ∈ Subgroup.zpowers (e g) := by
  intro y
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (e.symm y))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, ?_⟩
  rw [← map_zpow, hk, e.apply_symm_apply]

/-- Under an isomorphism with the integers, an element with coordinate `1` or `-1` generates
the whole group. -/
theorem forall_mem_zpowers_of_mulEquiv_int_unit
    {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ) (g : G)
    (hg : e g = Multiplicative.ofAdd 1 ∨ e g = Multiplicative.ofAdd (-1)) :
    ∀ x : G, x ∈ Subgroup.zpowers g := by
  intro x
  apply Subgroup.mem_zpowers_iff.mpr
  rcases hg with hg | hg
  · refine ⟨(e x).toAdd, ?_⟩
    apply e.injective
    rw [map_zpow, hg]
    apply Multiplicative.toAdd.injective
    simp
  · refine ⟨-(e x).toAdd, ?_⟩
    apply e.injective
    rw [map_zpow, hg]
    apply Multiplicative.toAdd.injective
    simp

/-- A homomorphism between infinite cyclic groups is bijective if it carries a specified
generator to a specified generator. -/
theorem MonoidHom.bijective_of_maps_infinite_cyclic_generators
    {G H : Type*} [Group G] [Group H] (f : G →* H) {g : G}
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hfg : ∀ y : H, y ∈ Subgroup.zpowers (f g))
    (eG : G ≃* Multiplicative ℤ) (eH : H ≃* Multiplicative ℤ) :
    Function.Bijective f := by
  letI : Infinite G := Infinite.of_injective eG.symm eG.symm.injective
  letI : Infinite H := Infinite.of_injective eH.symm eH.symm.injective
  have hgOrder : orderOf g = 0 :=
    Infinite.orderOf_eq_zero_of_forall_mem_zpowers hg
  have hfgOrder : orderOf (f g) = 0 :=
    Infinite.orderOf_eq_zero_of_forall_mem_zpowers hfg
  let E : G ≃* H := mulEquivOfOrderOfEq hg hfg (hgOrder.trans hfgOrder.symm)
  have hfE : f = E.toMonoidHom :=
    (MonoidHom.eq_iff_eq_on_generator hg f E.toMonoidHom).2 (by
      simp [E])
  rw [hfE]
  exact E.bijective

/-! ## The canonical sphere classes are generators -/

/-- Hurewicz and the oriented top homology of `S^(n+2)` give the coordinate equivalence used to
recognize its canonical cubical class as a generator. -/
noncomputable def sphereDiagonalHurewiczMulEquiv (n : ℕ) :
    π_ (n + 2) (Sph (n + 2)) (sphereBasepoint (n + 2)) ≃*
      Multiplicative ℤ :=
  (AddEquiv.toMultiplicativeRight
      ((isNConnected_sphere_succ_succ n).absoluteHurewiczAddEquiv
        (sphereBasepoint (n + 2)))).trans
    (AddEquiv.toMultiplicative
      (hgrpSphereSelfIsoZ (n + 1)).addCommGroupIsoToAddEquiv)

theorem sphereDiagonalHurewiczMulEquiv_generator (n : ℕ) :
    sphereDiagonalHurewiczMulEquiv n (sphereGeneratorClass (n + 2)) =
      Multiplicative.ofAdd (absoluteHurewiczSphereGeneratorCoordinate n) :=
  rfl

/-- The canonical class generates every diagonal sphere group in dimension at least two. -/
theorem sphereGeneratorClass_generates_succ (n : ℕ) :
    ∀ x : π_ (n + 2) (Sph (n + 2)) (sphereBasepoint (n + 2)),
      x ∈ Subgroup.zpowers (sphereGeneratorClass (n + 2)) := by
  apply forall_mem_zpowers_of_mulEquiv_int_unit
    (sphereDiagonalHurewiczMulEquiv n) (sphereGeneratorClass (n + 2))
  rw [sphereDiagonalHurewiczMulEquiv_generator]
  exact (absoluteHurewiczSphereGeneratorCoordinate_eq_one_or_neg_one n).imp
    (congrArg Multiplicative.ofAdd) (congrArg Multiplicative.ofAdd)

/-- Hurewicz in degree one gives the corresponding coordinate equivalence for the metric
circle. -/
noncomputable def sphereOneHurewiczMulEquiv :
    π_ 1 (Sph 1) (sphereBasepoint 1) ≃* Multiplicative ℤ := by
  letI : PathConnectedSpace (Sph 1) := pathConnectedSpace_sph (by omega)
  let circle := Classical.choice (pi1_sph_one_at_mulEquiv_int (sphereBasepoint 1))
  letI : CommGroup (π_ 1 (Sph 1) (sphereBasepoint 1)) :=
    { (inferInstance : Group (π_ 1 (Sph 1) (sphereBasepoint 1))) with
      mul_comm := fun x y => circle.injective (by
        rw [map_mul, map_mul]
        exact mul_comm _ _) }
  exact Abelianization.equivOfComm.trans
    ((AddEquiv.toMultiplicativeRight
      (hurewiczOnePiOfSpace (Sph 1) (sphereBasepoint 1))).trans
        (AddEquiv.toMultiplicative
          (hgrpSphereSelfIsoZ 0).addCommGroupIsoToAddEquiv))

theorem sphereOneHurewiczMulEquiv_generator :
    sphereOneHurewiczMulEquiv (sphereGeneratorClass 1) =
      Multiplicative.ofAdd hurewiczOneSphereGeneratorCoordinate := by
  letI : PathConnectedSpace (Sph 1) := pathConnectedSpace_sph (by omega)
  let circle := Classical.choice (pi1_sph_one_at_mulEquiv_int (sphereBasepoint 1))
  letI : CommGroup (π_ 1 (Sph 1) (sphereBasepoint 1)) :=
    { (inferInstance : Group (π_ 1 (Sph 1) (sphereBasepoint 1))) with
      mul_comm := fun x y => circle.injective (by
        rw [map_mul, map_mul]
        exact mul_comm _ _) }
  change Multiplicative.ofAdd
      ((hgrpSphereSelfIsoZ 0).hom
        (hurewiczOnePiOfSpace (Sph 1) (sphereBasepoint 1)
          (Additive.ofMul (Abelianization.of (sphereGeneratorClass 1))))) =
    Multiplicative.ofAdd hurewiczOneSphereGeneratorCoordinate
  rfl

/-- The canonical cubical class generates the fundamental group of the metric circle. -/
theorem sphereGeneratorClass_generates_one :
    ∀ x : π_ 1 (Sph 1) (sphereBasepoint 1),
      x ∈ Subgroup.zpowers (sphereGeneratorClass 1) := by
  apply forall_mem_zpowers_of_mulEquiv_int_unit sphereOneHurewiczMulEquiv
    (sphereGeneratorClass 1)
  rw [sphereOneHurewiczMulEquiv_generator]
  exact hurewiczOneSphereGeneratorCoordinate_eq_one_or_neg_one.imp
    (congrArg Multiplicative.ofAdd) (congrArg Multiplicative.ofAdd)

/-- Uniformly, the canonical cubical class generates every positive-dimensional diagonal
sphere homotopy group. -/
theorem sphereGeneratorClass_generates (n : ℕ) :
    ∀ x : π_ (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)),
      x ∈ Subgroup.zpowers (sphereGeneratorClass (n + 1)) := by
  cases n with
  | zero => exact sphereGeneratorClass_generates_one
  | succ n => simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] using
      sphereGeneratorClass_generates_succ n

/-! ## Bijectivity of concrete reduced suspension -/

/-- Applying diagonal reduced suspension to the canonical class gives the class represented by
the descended suspended-generator self-map. -/
theorem sphereDiagonalReducedSuspensionHom_generator (n : ℕ) :
    sphereDiagonalReducedSuspensionHom n (sphereGeneratorClass (n + 1)) =
      sphereTargetMapClass (n + 2)
        (sphereDiagonalReducedSuspensionGeneratorMap n)
        (sphereDiagonalReducedSuspensionGeneratorMap_basepoint n) := by
  change sphereDiagonalReducedSuspensionHom n (sphereGeneratorClass (n + 1)) =
    sphereTargetMapClass (n + 2)
      (targetGenLoopSphereMap (n + 1) (sphereDiagonalReducedSuspensionGeneratorLoop n)) _
  rw [sphereTargetMapClass_targetGenLoopSphereMap (n + 1)]
  rfl

/-- The image of the canonical class under reduced suspension generates the target diagonal
group. -/
theorem sphereDiagonalReducedSuspensionHom_generator_generates (n : ℕ) :
    ∀ x : π_ (n + 2) (Sph (n + 2)) (sphereBasepoint (n + 2)),
      x ∈ Subgroup.zpowers
        (sphereDiagonalReducedSuspensionHom n (sphereGeneratorClass (n + 1))) := by
  let e := HomotopyGroup.homeomorphMulEquivOfEq
    (N := Fin (n + 2)) (sphereDiagonalReducedSuspensionGeneratorHomeomorph n)
    (sphereDiagonalReducedSuspensionGeneratorMap_basepoint n)
  have heGenerator : e (sphereGeneratorClass (n + 2)) =
      sphereDiagonalReducedSuspensionHom n (sphereGeneratorClass (n + 1)) := by
    rw [HomotopyGroup.homeomorphMulEquivOfEq_apply]
    rw [sphereDiagonalReducedSuspensionHom_generator]
    exact (sphereTargetMapClass_eq_map_generator (n + 2)
      (sphereDiagonalReducedSuspensionGeneratorMap n)
      (sphereDiagonalReducedSuspensionGeneratorMap_basepoint n)).symm
  rw [← heGenerator]
  exact forall_mem_zpowers_map_mulEquiv e (sphereGeneratorClass_generates (n + 1))

/-- **Concrete diagonal suspension is bijective.**  The maintained reduced-suspension
homomorphism between successive metric-sphere diagonal homotopy groups is a bijection in every
dimension. -/
theorem sphereDiagonalReducedSuspensionHom_bijective (n : ℕ) :
    Function.Bijective (sphereDiagonalReducedSuspensionHom n) := by
  apply MonoidHom.bijective_of_maps_infinite_cyclic_generators
    (sphereDiagonalReducedSuspensionHom n)
    (sphereGeneratorClass_generates n)
    (sphereDiagonalReducedSuspensionHom_generator_generates n)
  · exact Classical.choice
      (sphere_diagonal_sph_at_mulEquiv_int n (sphereBasepoint (n + 1)))
  · exact Classical.choice
      (sphere_diagonal_sph_at_mulEquiv_int (n + 1) (sphereBasepoint (n + 2)))

/-- The actual reduced-suspension homomorphism is an unconditional multiplicative equivalence
between successive diagonal sphere groups. -/
noncomputable def sphereDiagonalReducedSuspensionEquiv (n : ℕ) :
    π_ (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
      π_ (n + 2) (Sph (n + 2)) (sphereBasepoint (n + 2)) :=
  sphereDiagonalReducedSuspensionMulEquiv n
    (sphereDiagonalReducedSuspensionHom_bijective n)

/-- A third unconditional proof of the integral sphere diagonal, now propagated by the concrete
reduced-suspension homomorphism itself. -/
theorem sphere_diagonal_mulEquiv_int_via_reducedSuspension (n : ℕ) :
    Nonempty
      (π_ (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) :=
  sphere_diagonal_mulEquiv_int_of_reduced_suspension_bijective
    sphereDiagonalReducedSuspensionHom_bijective n

end Submission
