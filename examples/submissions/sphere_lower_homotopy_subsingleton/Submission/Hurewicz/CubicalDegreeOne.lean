/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.CubicalCollapse
import Submission.Hurewicz.DegreeOne
import Submission.Hurewicz.RelativeSimplex

/-!
# The cubical boundary comparison in degree one

This file compares the homology class carried by the canonical extension of a cubical loop to
the degree-one Hurewicz equivalence through the abelianisation of the fundamental group.  It is
the low-dimensional counterpart of `Submission.cubicalBoundaryHurewicz_eq_sign_smul_absolute`.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- A continuous map carries the singular simplex associated to a path to the simplex associated
to the mapped path. -/
theorem pathSimplex_map (f : C(X, Y)) {x₀ x₁ : X} (γ : Path x₀ x₁) :
    (TopCat.toSSet.map (TopCat.ofHom f)).app _ (pathSimplex γ) =
      pathSimplex (γ.map f.continuous) := by
  apply (sngEquiv (TopCat.of Y) 1).injective
  rw [sngEquiv_map, pathSimplex, sngEquiv_sng, pathSimplex, sngEquiv_sng]
  rfl

/-- The singular-chain map carries the edge of a path to the edge of its image. -/
theorem CsingMap_edge (f : C(X, Y)) {x₀ x₁ : X} (γ : Path x₀ x₁) :
    (CsingMap (TopCat.ofHom f)).f 1 (edge γ) = edge (γ.map f.continuous) := by
  rw [edge, CsingMap_gen, edge, pathSimplex_map]

/-- The homology class of a loop is natural under postcomposition. -/
theorem HgrpMap_loopH (f : C(X, Y)) (x₀ : X) (γ : Path x₀ x₀) :
    HgrpMap 1 (TopCat.ofHom f) (loopH x₀ γ) =
      loopH (f x₀) (γ.map f.continuous) := by
  unfold loopH h1mk
  exact homologyMap_homologyMk_congr (CsingMap (TopCat.ofHom f)) _ _ _ _
    (CsingMap_edge f γ)

/-- The degree-one Hurewicz equivalence evaluates on a cubical representative as the singular
homology class of its associated ordinary path. -/
theorem hurewiczOnePi_of_genLoop [PathConnectedSpace X] (q : Ω^ (Fin 1) X x) :
    hurewiczOnePiOfSpace X x
        (Additive.ofMul (Abelianization.of (⟦q⟧ : π_ 1 X x))) =
      loopH x (genLoopEquivOfUnique (Fin 1) q) := by
  rfl

/-- Passing from a one-dimensional generalized loop to a path commutes with a based map. -/
theorem genLoopEquivOfUnique_map (f : C(X, Y)) (hf : f x = y)
    (q : Ω^ (Fin 1) X x) :
    genLoopEquivOfUnique (Fin 1) (GenLoop.map f hf q) =
      ((genLoopEquivOfUnique (Fin 1) q).map f.continuous).cast hf.symm hf.symm := by
  ext t
  rfl

/-- Naturality of the degree-one Hurewicz map on a represented cubical loop. -/
theorem hurewiczOnePi_of_genLoop_naturality
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) (hf : f x = y) (q : Ω^ (Fin 1) X x) :
    HgrpMap 1 (TopCat.ofHom f)
        (hurewiczOnePiOfSpace X x
          (Additive.ofMul (Abelianization.of (⟦q⟧ : π_ 1 X x)))) =
      hurewiczOnePiOfSpace Y y
        (Additive.ofMul (Abelianization.of
          (⟦GenLoop.map f hf q⟧ : π_ 1 Y y))) := by
  cases hf
  rw [hurewiczOnePi_of_genLoop, hurewiczOnePi_of_genLoop,
    HgrpMap_loopH, genLoopEquivOfUnique_map]
  rfl

/-- Integer coordinate of the cubical-boundary Hurewicz value of the canonical circle
generator. -/
noncomputable def cubicalBoundarySphereGeneratorOneCoordinate : ℤ :=
  (hgrpSphereSelfIsoZ 0).hom
    (GenLoop.cubicalBoundaryHurewicz 0 (sphereGenerator 1))

/-- The cubical-boundary Hurewicz value of the canonical circle generator has unit coordinate. -/
theorem cubicalBoundarySphereGeneratorOneCoordinate_eq_one_or_neg_one :
    cubicalBoundarySphereGeneratorOneCoordinate = 1 ∨
      cubicalBoundarySphereGeneratorOneCoordinate = -1 := by
  let e := hgrpIsoOfCMHomotopyEquiv
    (cubeBoundaryJarCollapseUnliftedHomotopyEquiv 0) 1
  let b := cubeBoundaryTopHomologyIsoInt 0
  let s := hgrpSphereSelfIsoZ 0
  have heBij : Function.Bijective e.hom :=
    (ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance
  obtain ⟨v, hv⟩ := heBij.surjective (s.inv (1 : ℤ))
  let k : ℤ := b.hom v
  have hvfund : v = k • cubeBoundaryFundamentalClass 0 := by
    apply ((ConcreteCategory.isIso_iff_bijective b.hom).mp inferInstance).injective
    rw [map_zsmul]
    change b.hom v = k • b.hom (cubeBoundaryFundamentalClass 0)
    rw [cubeBoundaryTopHomologyIsoInt_fundamentalClass]
    simp [k]
  have hcoord := congrArg s.hom hv
  rw [hvfund, map_zsmul, map_zsmul] at hcoord
  have hehom : e.hom =
      HgrpMap 1 (GenLoop.cubicalBoundaryExtension (sphereGenerator 1)) := by
    rfl
  rw [hehom] at hcoord
  have hmul : k * cubicalBoundarySphereGeneratorOneCoordinate = 1 := by
    simpa [e, s, cubicalBoundarySphereGeneratorOneCoordinate,
      GenLoop.cubicalBoundaryHurewicz, smul_eq_mul] using hcoord
  rw [mul_comm] at hmul
  exact Int.eq_one_or_neg_one_of_mul_eq_one hmul

/-- Every cubical loop is obtained by applying its descended based circle map to the canonical
circle generator. -/
theorem genLoop_map_sphereGenerator_targetGenLoopSphereMap_one
    (q : Ω^ (Fin 1) X x) :
    GenLoop.map (targetGenLoopSphereMap 0 q)
        (targetGenLoopSphereMap_basepoint 0 q) (sphereGenerator 1) = q := by
  apply GenLoop.ext
  intro u
  have h := congrArg (fun f : C(I^Fin 1, X) => f u)
    (targetGenLoopSphereMap_comp_cubeToSphere 0 q)
  exact h

/-- Integer coordinate of the degree-one Hurewicz value of the canonical circle generator. -/
noncomputable def hurewiczOneSphereGeneratorCoordinate : ℤ := by
  letI : PathConnectedSpace (Sph 1) := pathConnectedSpace_sph (by omega)
  exact (hgrpSphereSelfIsoZ 0).hom
    (hurewiczOnePiOfSpace (Sph 1) (sphereBasepoint 1)
      (Additive.ofMul (Abelianization.of (sphereGeneratorClass 1))))

/-- The degree-one Hurewicz value of the canonical circle generator has unit coordinate. -/
theorem hurewiczOneSphereGeneratorCoordinate_eq_one_or_neg_one :
    hurewiczOneSphereGeneratorCoordinate = 1 ∨
      hurewiczOneSphereGeneratorCoordinate = -1 := by
  letI : PathConnectedSpace (Sph 1) := pathConnectedSpace_sph (by omega)
  let s := hgrpSphereSelfIsoZ 0
  let h := hurewiczOnePiOfSpace (Sph 1) (sphereBasepoint 1)
  obtain ⟨u, hu⟩ := h.surjective (s.inv (1 : ℤ))
  obtain ⟨z, hz⟩ := Quotient.exists_rep u.toMul
  have huRep : u = Additive.ofMul (Abelianization.of z) := by
    apply Additive.toMul.injective
    exact hz.symm
  subst u
  obtain ⟨q, hq⟩ := Quotient.exists_rep z
  have hzRep : z = (⟦q⟧ : π_ 1 (Sph 1) (sphereBasepoint 1)) := hq.symm
  subst z
  let f := targetGenLoopSphereMap 0 q
  let hf := targetGenLoopSphereMap_basepoint 0 q
  have hqMap : GenLoop.map f hf (sphereGenerator 1) = q :=
    genLoop_map_sphereGenerator_targetGenLoopSphereMap_one q
  have hnat := hurewiczOnePi_of_genLoop_naturality
    f hf (sphereGenerator 1)
  rw [hqMap, hu] at hnat
  have hcoord := congrArg s.hom hnat
  have hend : sphereHomologyEnd 0 (TopCat.ofHom f)
      hurewiczOneSphereGeneratorCoordinate = 1 := by
    simpa [s, h, sphereHomologyEnd, hurewiczOneSphereGeneratorCoordinate,
      sphereGeneratorClass] using hcoord
  rw [sphereHomologyEnd_apply] at hend
  have hmul : hurewiczOneSphereGeneratorCoordinate *
      sphereHomologicalDegree 0 (TopCat.ofHom f) = 1 := hend
  exact Int.eq_one_or_neg_one_of_mul_eq_one hmul

/-- The global sign comparing the cubical-boundary and degree-one Hurewicz normalisations. -/
noncomputable def cubicalBoundaryHurewiczOneSign : ℤ :=
  cubicalBoundarySphereGeneratorOneCoordinate *
    hurewiczOneSphereGeneratorCoordinate

theorem cubicalBoundaryHurewiczOneSign_eq_one_or_neg_one :
    cubicalBoundaryHurewiczOneSign = 1 ∨
      cubicalBoundaryHurewiczOneSign = -1 := by
  rcases cubicalBoundarySphereGeneratorOneCoordinate_eq_one_or_neg_one with hc | hc <;>
    rcases hurewiczOneSphereGeneratorCoordinate_eq_one_or_neg_one with hh | hh <;>
    simp [cubicalBoundaryHurewiczOneSign, hc, hh]

/-- On the canonical circle generator, cubical-boundary Hurewicz differs from degree-one
Hurewicz by the global orientation sign. -/
theorem cubicalBoundaryHurewicz_sphereGenerator_one :
    GenLoop.cubicalBoundaryHurewicz 0 (sphereGenerator 1) =
      cubicalBoundaryHurewiczOneSign •
        hurewiczOnePiOfSpace (Sph 1) (sphereBasepoint 1)
          (Additive.ofMul (Abelianization.of (sphereGeneratorClass 1))) := by
  letI : PathConnectedSpace (Sph 1) := pathConnectedSpace_sph (by omega)
  let s := hgrpSphereSelfIsoZ 0
  apply ((ConcreteCategory.isIso_iff_bijective s.hom).mp inferInstance).injective
  rw [map_zsmul]
  change cubicalBoundarySphereGeneratorOneCoordinate =
    cubicalBoundaryHurewiczOneSign * hurewiczOneSphereGeneratorCoordinate
  rcases hurewiczOneSphereGeneratorCoordinate_eq_one_or_neg_one with hh | hh <;>
    simp [cubicalBoundaryHurewiczOneSign, hh]

/-- Universal cubical-boundary comparison in degree one.  The cubical class agrees up to one
global orientation sign with the standard degree-one Hurewicz equivalence through
abelianisation. -/
theorem cubicalBoundaryHurewicz_eq_sign_smul_hurewiczOne
    [PathConnectedSpace X] (q : Ω^ (Fin 1) X x) :
    GenLoop.cubicalBoundaryHurewicz 0 q =
      cubicalBoundaryHurewiczOneSign •
        hurewiczOnePiOfSpace X x
          (Additive.ofMul (Abelianization.of (⟦q⟧ : π_ 1 X x))) := by
  letI : PathConnectedSpace (Sph 1) := pathConnectedSpace_sph (by omega)
  let f := targetGenLoopSphereMap 0 q
  let hf := targetGenLoopSphereMap_basepoint 0 q
  have hq : GenLoop.map f hf (sphereGenerator 1) = q :=
    genLoop_map_sphereGenerator_targetGenLoopSphereMap_one q
  calc
    GenLoop.cubicalBoundaryHurewicz 0 q =
        GenLoop.cubicalBoundaryHurewicz 0
          (GenLoop.map f hf (sphereGenerator 1)) := by rw [hq]
    _ = HgrpMap 1 (TopCat.ofHom f)
        (GenLoop.cubicalBoundaryHurewicz 0 (sphereGenerator 1)) :=
      GenLoop.cubicalBoundaryHurewicz_map 0 f hf (sphereGenerator 1)
    _ = HgrpMap 1 (TopCat.ofHom f)
        (cubicalBoundaryHurewiczOneSign •
          hurewiczOnePiOfSpace (Sph 1) (sphereBasepoint 1)
            (Additive.ofMul (Abelianization.of (sphereGeneratorClass 1)))) := by
      rw [cubicalBoundaryHurewicz_sphereGenerator_one]
    _ = cubicalBoundaryHurewiczOneSign •
        HgrpMap 1 (TopCat.ofHom f)
          (hurewiczOnePiOfSpace (Sph 1) (sphereBasepoint 1)
            (Additive.ofMul (Abelianization.of (sphereGeneratorClass 1)))) := by
      rw [map_zsmul]
    _ = cubicalBoundaryHurewiczOneSign •
        hurewiczOnePiOfSpace X x
          (Additive.ofMul (Abelianization.of
            (⟦GenLoop.map f hf (sphereGenerator 1)⟧ : π_ 1 X x))) := by
      exact congrArg (fun z => cubicalBoundaryHurewiczOneSign • z)
        (hurewiczOnePi_of_genLoop_naturality f hf (sphereGenerator 1))
    _ = cubicalBoundaryHurewiczOneSign •
        hurewiczOnePiOfSpace X x
          (Additive.ofMul (Abelianization.of (⟦q⟧ : π_ 1 X x))) := by rw [hq]

/-- Multiplication by the degree-one cubical-boundary orientation sign is bijective on every
additive group. -/
theorem bijective_cubicalBoundaryHurewiczOneSign_smul
    (G : Type) [AddGroup G] :
    Function.Bijective (fun z : G => cubicalBoundaryHurewiczOneSign • z) := by
  rcases cubicalBoundaryHurewiczOneSign_eq_one_or_neg_one with h | h
  · constructor
    · intro a b hab
      simpa [h] using hab
    · intro z
      refine ⟨z, ?_⟩
      simp [h]
  · constructor
    · intro a b hab
      have hab' := congrArg Neg.neg hab
      simpa [h] using hab'
    · intro z
      refine ⟨-z, ?_⟩
      simp [h]

namespace IsNConnected

/-- Degree-two relative Hurewicz for a contractible ambient space when the subspace has abelian
fundamental group.  Degree-one Hurewicz supplies the boundary comparison through
abelianisation. -/
theorem relativeHurewiczAdd_bijective_of_contractibleAmbient_one
    {Z : Type} [TopologicalSpace Z] [ContractibleSpace Z]
    {A : Set Z} (hA : IsNConnected 0 A) (a : A)
    (hcomm : ∀ u v : π_ 1 A a, u * v = v * u) :
    Function.Bijective (relativeHurewiczAdd 0 A a) := by
  letI : PathConnectedSpace A := hA.pathConnected
  letI : CommGroup (π_ 1 A a) :=
    { (inferInstance : Group (π_ 1 A a)) with mul_comm := hcomm }
  let ab : Additive (π_ 1 A a) ≃+ Additive (Abelianization (π_ 1 A a)) :=
    MulEquiv.toAdditive Abelianization.equivOfComm
  let hur : Additive (Abelianization (π_ 1 A a)) ≃+
      (Hgrp 1 (TopCat.of A) : Type) := hurewiczOnePiOfSpace A a
  let g : Additive (π_ 1 A a) → (Hgrp 1 (TopCat.of A) : Type) :=
    fun z => cubicalBoundaryHurewiczOneSign • hur (ab z)
  refine relativeHurewiczAdd_bijective_of_boundary_comparison 0 a g ?_ ?_ ?_ ?_
  · change Function.Bijective (RelHomotopyGroup.bd 1 Z A a)
    exact bijective_bd_of_subsingleton 0 a
      (subsingleton_homotopyGroup_of_contractible (N := Fin 2) (a : Z))
      (subsingleton_homotopyGroup_of_contractible (N := Fin 1) (a : Z))
  · let i := subIncl (Y := TopCat.of Z) A
    letI : IsIso (relδ 1 i) :=
      isIso_relδ i 1
        (isZero_Hgrp_of_contractible (X := TopCat.of Z) 1)
        (isZero_Hgrp_of_contractible (X := TopCat.of Z) 0)
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  · exact (bijective_cubicalBoundaryHurewiczOneSign_smul _).comp
      (hur.bijective.comp ab.bijective)
  · intro q
    simpa [g, ab, hur] using
      (cubicalBoundaryHurewicz_eq_sign_smul_hurewiczOne q)

end IsNConnected

end Submission
