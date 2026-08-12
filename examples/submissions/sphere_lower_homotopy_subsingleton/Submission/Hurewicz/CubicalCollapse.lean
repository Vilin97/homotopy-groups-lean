/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.CubicalBoundary
import Submission.Hurewicz.AbsoluteNaturality
import Submission.Hurewicz.SphereLoopBridge
import Submission.SphereGenerator
import Submission.SphereHomologicalDegree
import Submission.WhiteheadTheorem.HEP.CubeJar

/-!
# Collapsing a cubical boundary jar

The canonical cubical boundary extension of the sphere generator collapses the bottom face and
all sides of an `(n+2)`-cube, while its top face is the quotient
`I^(n+1) / ∂I^(n+1) → S^(n+1)`.  This file begins the geometric proof that this collapse is a
homotopy equivalence.  Its induced map on top homology will therefore carry the chosen cubical
boundary class to a generator, which is the unit-degree input needed by the relative Hurewicz
comparison.
-/

open CategoryTheory
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- Collapse the boundary jar of the `(n+2)`-cube onto the distinguished point of `S^(n+1)`,
using the canonical cubical sphere generator on the top face. -/
noncomputable def cubeBoundaryJarCollapse (n : ℕ) :
    TopCat.cubeBoundary (n + 2) ⟶ TopCat.of (Sph (n + 1)) :=
  GenLoop.cubicalBoundaryExtensionLifted (sphereGenerator (n + 1))

/-- The collapse is constant on the boundary jar. -/
@[simp]
theorem cubeBoundaryJarCollapse_jar (n : ℕ) (z : TopCat.cubeBoundaryJar (n + 2)) :
    cubeBoundaryJarCollapse n (TopCat.cubeBoundaryJarInclToBoundary (n + 2) z) =
      sphereBasepoint (n + 1) := by
  change GenLoop.cubicalBoundaryExtension (sphereGenerator (n + 1))
    ⟨z.down.val, Cube.boundaryJar_subset_boundary (n + 2) z.down.property⟩ = _
  exact GenLoop.cubicalBoundaryExtension_boundaryJar
    (sphereGenerator (n + 1)) z.down.val z.down.property

/-- On the top face, the collapse is the canonical cube-to-sphere quotient. -/
@[simp]
theorem cubeBoundaryJarCollapse_top (n : ℕ) (u : I^Fin (n + 1)) :
    cubeBoundaryJarCollapse n
        (TopCat.cubeBoundary.cubeInclToBotOrTop 1 (⟨u⟩ : TopCat.cube (n + 1))) =
      cubeToSphere (n + 1) u := by
  change GenLoop.cubicalBoundaryExtension (sphereGenerator (n + 1))
    ⟨Cube.inclToTop u, Cube.inclToTop.mem_boundary u⟩ = _
  exact GenLoop.cubicalBoundaryExtension_inclToTop (sphereGenerator (n + 1)) u

/-- The cubical jar collapse is onto. -/
theorem cubeBoundaryJarCollapse_surjective (n : ℕ) :
    Function.Surjective (cubeBoundaryJarCollapse n) := by
  intro z
  obtain ⟨u, hu⟩ := cubeToSphere_surjective n z
  refine ⟨TopCat.cubeBoundary.cubeInclToBotOrTop 1
    (⟨u⟩ : TopCat.cube (n + 1)), ?_⟩
  exact (cubeBoundaryJarCollapse_top n u).trans hu

/-- The cubical jar collapse is a quotient map. -/
theorem isQuotientMap_cubeBoundaryJarCollapse (n : ℕ) :
    Topology.IsQuotientMap (cubeBoundaryJarCollapse n) := by
  letI : CompactSpace (TopCat.cubeBoundary (n + 2)) :=
    (TopCat.diskBoundaryHomeoCubeBoundaryULift (n + 2)).compactSpace
  exact Topology.IsQuotientMap.of_surjective_continuous
    (cubeBoundaryJarCollapse_surjective n) (cubeBoundaryJarCollapse n).hom.continuous

/-- A boundary point is collapsed to the sphere basepoint exactly when it lies in the boundary
jar. -/
theorem cubeBoundaryJarCollapse_eq_basepoint_iff (n : ℕ)
    (z : TopCat.cubeBoundary (n + 2)) :
    cubeBoundaryJarCollapse n z = sphereBasepoint (n + 1) ↔
      z ∈ TopCat.cubeBoundary.jar (n + 1) := by
  constructor
  · intro hz
    rcases Cube.mem_boundaryLid_or_mem_boundaryJar_of_mem_boundary
        z.down.val z.down.property with hlid | hjar
    · let u : I^Fin (n + 1) := (Cube.splitAtLast z.down.val).snd
      have hyTop : z.down.val = Cube.inclToTop u := by
        apply Cube.splitAtLast.injective
        rw [Cube.splitAtLast_inclToTop_eq]
        apply Prod.ext
        · change z.down.val (Fin.last (n + 1)) = 1 at hlid
          simpa only [Cube.splitAtLast_fst_eq] using hlid
        · rfl
      have hzTop : z = TopCat.cubeBoundary.cubeInclToBotOrTop 1
          (⟨u⟩ : TopCat.cube (n + 1)) := by
        apply ULift.ext
        apply Subtype.ext
        exact hyTop
      rw [hzTop, cubeBoundaryJarCollapse_top] at hz
      let v : I^Fin (n + 1) := 0
      have hv : v ∈ ∂I^(n + 1) := ⟨0, Or.inl rfl⟩
      have hvbase : cubeToSphere (n + 1) v = sphereBasepoint (n + 1) :=
        cubeToSphere_boundary (n + 1) v hv
      have huv : cubeToSphere (n + 1) u = cubeToSphere (n + 1) v :=
        hz.trans hvbase.symm
      have hu : u ∈ ∂I^(n + 1) := by
        rcases (cubeToSphere_eq_iff (n + 1) u v).mp huv with huv' | huv'
        · rw [huv']
          exact hv
        · exact huv'.1
      rw [hzTop]
      exact Cube.inclToTop.mem_boundaryJar_of hu
    · exact hjar
  · intro hz
    change GenLoop.cubicalBoundaryExtension (sphereGenerator (n + 1)) z.down = _
    exact GenLoop.cubicalBoundaryExtension_boundaryJar
      (sphereGenerator (n + 1)) z.down.val hz

/-- Every point outside the boundary jar lies uniquely on the interior of the top face. -/
theorem cubeBoundary_exists_top_of_not_mem_jar (n : ℕ)
    (z : TopCat.cubeBoundary (n + 2))
    (hz : z ∉ TopCat.cubeBoundary.jar (n + 1)) :
    ∃ u : I^Fin (n + 1),
      z = TopCat.cubeBoundary.cubeInclToBotOrTop 1
          (⟨u⟩ : TopCat.cube (n + 1)) ∧
        u ∉ ∂I^(n + 1) := by
  rcases Cube.mem_boundaryLid_or_mem_boundaryJar_of_mem_boundary
      z.down.val z.down.property with hlid | hjar
  · let u : I^Fin (n + 1) := (Cube.splitAtLast z.down.val).snd
    have hyTop : z.down.val = Cube.inclToTop u := by
      apply Cube.splitAtLast.injective
      rw [Cube.splitAtLast_inclToTop_eq]
      apply Prod.ext
      · change z.down.val (Fin.last (n + 1)) = 1 at hlid
        simpa only [Cube.splitAtLast_fst_eq] using hlid
      · rfl
    have hzTop : z = TopCat.cubeBoundary.cubeInclToBotOrTop 1
        (⟨u⟩ : TopCat.cube (n + 1)) := by
      apply ULift.ext
      apply Subtype.ext
      exact hyTop
    refine ⟨u, hzTop, ?_⟩
    intro hu
    apply hz
    rw [hzTop]
    exact Cube.inclToTop.mem_boundaryJar_of hu
  · exact (hz hjar).elim

/-- The only nontrivial fibre of the cubical jar collapse is the jar itself. -/
theorem cubeBoundaryJarCollapse_eq_iff (n : ℕ)
    (z w : TopCat.cubeBoundary (n + 2)) :
    cubeBoundaryJarCollapse n z = cubeBoundaryJarCollapse n w ↔
      z = w ∨
        (z ∈ TopCat.cubeBoundary.jar (n + 1) ∧
          w ∈ TopCat.cubeBoundary.jar (n + 1)) := by
  constructor
  · intro h
    by_cases hz : z ∈ TopCat.cubeBoundary.jar (n + 1)
    · right
      refine ⟨hz, (cubeBoundaryJarCollapse_eq_basepoint_iff n w).mp ?_⟩
      exact h.symm.trans ((cubeBoundaryJarCollapse_eq_basepoint_iff n z).mpr hz)
    by_cases hw : w ∈ TopCat.cubeBoundary.jar (n + 1)
    · right
      refine ⟨(cubeBoundaryJarCollapse_eq_basepoint_iff n z).mp ?_, hw⟩
      exact h.trans ((cubeBoundaryJarCollapse_eq_basepoint_iff n w).mpr hw)
    left
    obtain ⟨u, hzu, hu⟩ := cubeBoundary_exists_top_of_not_mem_jar n z hz
    obtain ⟨v, hwv, hv⟩ := cubeBoundary_exists_top_of_not_mem_jar n w hw
    rw [hzu, hwv, cubeBoundaryJarCollapse_top, cubeBoundaryJarCollapse_top] at h
    rcases (cubeToSphere_eq_iff (n + 1) u v).mp h with huv | huv
    · rw [hzu, hwv, huv]
    · exact (hu huv.1).elim
  · rintro (rfl | ⟨hz, hw⟩)
    · rfl
    · rw [(cubeBoundaryJarCollapse_eq_basepoint_iff n z).mpr hz,
        (cubeBoundaryJarCollapse_eq_basepoint_iff n w).mpr hw]

/-- Extend a contraction of the boundary jar across the whole cube boundary.  At the end of the
extension the entire jar is a single point, and throughout the homotopy points of the jar remain
inside the jar. -/
theorem exists_cubeBoundaryJar_contractionExtension (n : ℕ) :
    ∃ a₀ : TopCat.cubeBoundaryJar (n + 2),
      ∃ H : C(TopCat.cubeBoundary (n + 2) × I,
          TopCat.cubeBoundary (n + 2)),
        (∀ y, H (y, 0) = y) ∧
        (∀ a, H (TopCat.cubeBoundaryJarInclToBoundary (n + 2) a, 1) =
          TopCat.cubeBoundaryJarInclToBoundary (n + 2) a₀) ∧
        (∀ a t, H (TopCat.cubeBoundaryJarInclToBoundary (n + 2) a, t) ∈
          TopCat.cubeBoundary.jar (n + 1)) := by
  let A := TopCat.cubeBoundaryJar (n + 2)
  let Y := TopCat.cubeBoundary (n + 2)
  let i := (TopCat.cubeBoundaryJarInclToBoundary (n + 2)).hom
  letI : ContractibleSpace A := Homeomorph.ulift.contractibleSpace
  obtain ⟨a₀, hA⟩ := (contractible_iff_id_nullhomotopic A).mp inferInstance
  let K : ContinuousMap.Homotopy (ContinuousMap.id A) (ContinuousMap.const A a₀) := hA.some
  let h : C(A × I, Y) := i.comp K.toContinuousMap.argSwap
  have hcompat : ⇑(ContinuousMap.id Y) ∘ ⇑i = ⇑h ∘ fun a => (a, 0) := by
    ext a
    change i a = i (K (0, a))
    exact congrArg i (K.map_zero_left a).symm
  obtain ⟨H, hH₀, hHA⟩ :=
    TopCat.cubeBoundaryJarInclToBoundary_hasHEP (n + 1) Y
      (ContinuousMap.id Y) h hcompat
  refine ⟨a₀, H, ?_, ?_, ?_⟩
  · intro y
    have hy := congrFun hH₀ y
    exact hy.symm
  · intro a
    have ha := congrFun hHA (a, 1)
    change i (K (1, a)) = H (i a, 1) at ha
    exact ha.symm.trans (congrArg i (K.map_one_left a))
  · intro a t
    have ha := congrFun hHA (a, t)
    change i (K (t, a)) = H (i a, t) at ha
    rw [← ha]
    exact (K (t, a)).down.property

/-- The chosen point to which the boundary jar is contracted. -/
noncomputable def cubeBoundaryJarContractionPoint (n : ℕ) :
    TopCat.cubeBoundaryJar (n + 2) :=
  (exists_cubeBoundaryJar_contractionExtension n).choose

/-- A chosen extension of the boundary-jar contraction to the whole cube boundary. -/
noncomputable def cubeBoundaryJarContractionExtension (n : ℕ) :
    C(TopCat.cubeBoundary (n + 2) × I, TopCat.cubeBoundary (n + 2)) :=
  (exists_cubeBoundaryJar_contractionExtension n).choose_spec.choose

@[simp]
theorem cubeBoundaryJarContractionExtension_zero (n : ℕ)
    (y : TopCat.cubeBoundary (n + 2)) :
    cubeBoundaryJarContractionExtension n (y, 0) = y :=
  (exists_cubeBoundaryJar_contractionExtension n).choose_spec.choose_spec.1 y

@[simp]
theorem cubeBoundaryJarContractionExtension_jar_one (n : ℕ)
    (a : TopCat.cubeBoundaryJar (n + 2)) :
    cubeBoundaryJarContractionExtension n
        (TopCat.cubeBoundaryJarInclToBoundary (n + 2) a, 1) =
      TopCat.cubeBoundaryJarInclToBoundary (n + 2)
        (cubeBoundaryJarContractionPoint n) :=
  (exists_cubeBoundaryJar_contractionExtension n).choose_spec.choose_spec.2.1 a

theorem cubeBoundaryJarContractionExtension_jar_mem (n : ℕ)
    (a : TopCat.cubeBoundaryJar (n + 2)) (t : I) :
    cubeBoundaryJarContractionExtension n
        (TopCat.cubeBoundaryJarInclToBoundary (n + 2) a, t) ∈
      TopCat.cubeBoundary.jar (n + 1) :=
  (exists_cubeBoundaryJar_contractionExtension n).choose_spec.choose_spec.2.2 a t

/-- The extended homotopy keeps every point of the jar inside the jar. -/
theorem cubeBoundaryJarContractionExtension_mem_jar_of_mem_jar (n : ℕ)
    (z : TopCat.cubeBoundary (n + 2))
    (hz : z ∈ TopCat.cubeBoundary.jar (n + 1)) (t : I) :
    cubeBoundaryJarContractionExtension n (z, t) ∈
      TopCat.cubeBoundary.jar (n + 1) := by
  let a : TopCat.cubeBoundaryJar (n + 2) := ⟨⟨z.down.val, hz⟩⟩
  have ha : TopCat.cubeBoundaryJarInclToBoundary (n + 2) a = z := by
    apply ULift.ext
    apply Subtype.ext
    rfl
  rw [← ha]
  exact cubeBoundaryJarContractionExtension_jar_mem n a t

/-- The endpoint of the extended contraction. -/
noncomputable def cubeBoundaryJarRetraction (n : ℕ) :
    C(TopCat.cubeBoundary (n + 2), TopCat.cubeBoundary (n + 2)) :=
  (cubeBoundaryJarContractionExtension n).comp ⟨fun y => (y, 1), by fun_prop⟩

/-- The endpoint of the extended contraction is constant on the boundary jar. -/
theorem cubeBoundaryJarRetraction_eq_of_mem_jar (n : ℕ)
    (z : TopCat.cubeBoundary (n + 2))
    (hz : z ∈ TopCat.cubeBoundary.jar (n + 1)) :
    cubeBoundaryJarRetraction n z =
      TopCat.cubeBoundaryJarInclToBoundary (n + 2)
        (cubeBoundaryJarContractionPoint n) := by
  let a : TopCat.cubeBoundaryJar (n + 2) := ⟨⟨z.down.val, hz⟩⟩
  have ha : TopCat.cubeBoundaryJarInclToBoundary (n + 2) a = z := by
    apply ULift.ext
    apply Subtype.ext
    rfl
  change cubeBoundaryJarContractionExtension n (z, 1) = _
  rw [← ha]
  exact cubeBoundaryJarContractionExtension_jar_one n a

/-- The endpoint of the contraction is constant on every fibre of the jar collapse. -/
theorem cubeBoundaryJarRetraction_factorsThrough (n : ℕ) :
    Function.FactorsThrough (cubeBoundaryJarRetraction n) (cubeBoundaryJarCollapse n) := by
  intro z w h
  rcases (cubeBoundaryJarCollapse_eq_iff n z w).mp h with rfl | ⟨hz, hw⟩
  · rfl
  · rw [cubeBoundaryJarRetraction_eq_of_mem_jar n z hz,
      cubeBoundaryJarRetraction_eq_of_mem_jar n w hw]

/-- The homotopy inverse induced by the endpoint of the extended jar contraction. -/
noncomputable def cubeBoundaryJarCollapseInv (n : ℕ) :
    C(Sph (n + 1), TopCat.cubeBoundary (n + 2)) :=
  (isQuotientMap_cubeBoundaryJarCollapse n).lift
    (cubeBoundaryJarRetraction n) (cubeBoundaryJarRetraction_factorsThrough n)

/-- Pulling the homotopy inverse back along the quotient recovers the contraction endpoint. -/
@[simp]
theorem cubeBoundaryJarCollapseInv_comp (n : ℕ) :
    (cubeBoundaryJarCollapseInv n).comp (cubeBoundaryJarCollapse n).hom =
      cubeBoundaryJarRetraction n :=
  (isQuotientMap_cubeBoundaryJarCollapse n).lift_comp _ _

/-- The extended contraction is a homotopy from the identity to its endpoint. -/
noncomputable def cubeBoundaryJarRetractionHomotopy (n : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (TopCat.cubeBoundary (n + 2)))
      (cubeBoundaryJarRetraction n) where
  toContinuousMap := (cubeBoundaryJarContractionExtension n).argSwap
  map_zero_left := cubeBoundaryJarContractionExtension_zero n
  map_one_left := fun _ => rfl

/-- Before descent through the quotient, compose the extended jar contraction with the collapse
and curry in the boundary variable. -/
noncomputable def cubeBoundaryJarCollapseHomotopyCurrySource (n : ℕ) :
    C(TopCat.cubeBoundary (n + 2), C(I, Sph (n + 1))) :=
  ((cubeBoundaryJarCollapse n).hom.comp
    (cubeBoundaryJarContractionExtension n)).curry

@[simp]
theorem cubeBoundaryJarCollapseHomotopyCurrySource_apply (n : ℕ)
    (z : TopCat.cubeBoundary (n + 2)) (t : I) :
    cubeBoundaryJarCollapseHomotopyCurrySource n z t =
      cubeBoundaryJarCollapse n (cubeBoundaryJarContractionExtension n (z, t)) :=
  rfl

/-- The curried homotopy source is constant on the fibres of the jar collapse. -/
theorem cubeBoundaryJarCollapseHomotopyCurrySource_factorsThrough (n : ℕ) :
    Function.FactorsThrough (cubeBoundaryJarCollapseHomotopyCurrySource n)
      (cubeBoundaryJarCollapse n) := by
  intro z w h
  apply ContinuousMap.ext
  intro t
  rcases (cubeBoundaryJarCollapse_eq_iff n z w).mp h with rfl | ⟨hz, hw⟩
  · rfl
  · rw [cubeBoundaryJarCollapseHomotopyCurrySource_apply,
      cubeBoundaryJarCollapseHomotopyCurrySource_apply,
      (cubeBoundaryJarCollapse_eq_basepoint_iff n _).mpr
        (cubeBoundaryJarContractionExtension_mem_jar_of_mem_jar n z hz t),
      (cubeBoundaryJarCollapse_eq_basepoint_iff n _).mpr
        (cubeBoundaryJarContractionExtension_mem_jar_of_mem_jar n w hw t)]

/-- Descend the collapse of the extended contraction to a continuous family of sphere paths. -/
noncomputable def cubeBoundaryJarCollapseHomotopyCurry (n : ℕ) :
    C(Sph (n + 1), C(I, Sph (n + 1))) :=
  (isQuotientMap_cubeBoundaryJarCollapse n).lift
    (cubeBoundaryJarCollapseHomotopyCurrySource n)
    (cubeBoundaryJarCollapseHomotopyCurrySource_factorsThrough n)

@[simp]
theorem cubeBoundaryJarCollapseHomotopyCurry_apply_collapse (n : ℕ)
    (z : TopCat.cubeBoundary (n + 2)) (t : I) :
    cubeBoundaryJarCollapseHomotopyCurry n (cubeBoundaryJarCollapse n z) t =
      cubeBoundaryJarCollapse n (cubeBoundaryJarContractionExtension n (z, t)) := by
  have h := congrArg
    (fun f : C(TopCat.cubeBoundary (n + 2), C(I, Sph (n + 1))) => f z t)
    ((isQuotientMap_cubeBoundaryJarCollapse n).lift_comp
      (cubeBoundaryJarCollapseHomotopyCurrySource n)
      (cubeBoundaryJarCollapseHomotopyCurrySource_factorsThrough n))
  exact h

/-- The descended homotopy runs from the identity sphere map to collapse followed by its chosen
inverse. -/
noncomputable def cubeBoundaryJarCollapseRightHomotopy (n : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (Sph (n + 1)))
      ((cubeBoundaryJarCollapse n).hom.comp (cubeBoundaryJarCollapseInv n)) where
  toContinuousMap := (cubeBoundaryJarCollapseHomotopyCurry n).uncurry.comp
    ContinuousMap.prodSwap
  map_zero_left z := by
    obtain ⟨y, rfl⟩ := cubeBoundaryJarCollapse_surjective n z
    change cubeBoundaryJarCollapseHomotopyCurry n (cubeBoundaryJarCollapse n y) 0 =
      cubeBoundaryJarCollapse n y
    rw [cubeBoundaryJarCollapseHomotopyCurry_apply_collapse,
      cubeBoundaryJarContractionExtension_zero]
  map_one_left z := by
    obtain ⟨y, rfl⟩ := cubeBoundaryJarCollapse_surjective n z
    change cubeBoundaryJarCollapseHomotopyCurry n (cubeBoundaryJarCollapse n y) 1 =
      cubeBoundaryJarCollapse n
        (cubeBoundaryJarCollapseInv n (cubeBoundaryJarCollapse n y))
    rw [cubeBoundaryJarCollapseHomotopyCurry_apply_collapse]
    change cubeBoundaryJarCollapse n (cubeBoundaryJarRetraction n y) =
      cubeBoundaryJarCollapse n
        (cubeBoundaryJarCollapseInv n (cubeBoundaryJarCollapse n y))
    have h := ContinuousMap.congr_fun (cubeBoundaryJarCollapseInv_comp n) y
    exact (congrArg (cubeBoundaryJarCollapse n) h).symm

/-- Collapsing the contractible boundary jar is a homotopy equivalence. -/
noncomputable def cubeBoundaryJarCollapseHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (TopCat.cubeBoundary (n + 2)) (Sph (n + 1)) where
  toFun := (cubeBoundaryJarCollapse n).hom
  invFun := cubeBoundaryJarCollapseInv n
  left_inv := by
    rw [cubeBoundaryJarCollapseInv_comp]
    exact ⟨(cubeBoundaryJarRetractionHomotopy n).symm⟩
  right_inv := ⟨(cubeBoundaryJarCollapseRightHomotopy n).symm⟩

/-- Unlifted form of the jar-collapse homotopy equivalence, matching the cube-boundary model used
by singular homology. -/
noncomputable def cubeBoundaryJarCollapseUnliftedHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (∂I^(n + 2)) (Sph (n + 1)) :=
  Homeomorph.ulift.symm.toHomotopyEquiv.trans
    (cubeBoundaryJarCollapseHomotopyEquiv n)

@[simp]
theorem cubeBoundaryJarCollapseUnliftedHomotopyEquiv_toFun (n : ℕ) :
    (cubeBoundaryJarCollapseUnliftedHomotopyEquiv n).toFun =
      (GenLoop.cubicalBoundaryExtension (sphereGenerator (n + 1))).hom :=
  rfl

/-- Integer coordinate of the cubical-boundary Hurewicz value of the canonical sphere
generator. -/
noncomputable def cubicalBoundarySphereGeneratorCoordinate (n : ℕ) : ℤ :=
  (hgrpSphereSelfIsoZ (n + 1)).hom
    (GenLoop.cubicalBoundaryHurewicz (n + 1) (sphereGenerator (n + 2)))

/-- The cubical-boundary Hurewicz value of the canonical sphere generator has unit coordinate.
The sign is intentionally left unspecified. -/
theorem cubicalBoundarySphereGeneratorCoordinate_eq_one_or_neg_one (n : ℕ) :
    cubicalBoundarySphereGeneratorCoordinate n = 1 ∨
      cubicalBoundarySphereGeneratorCoordinate n = -1 := by
  let e := hgrpIsoOfCMHomotopyEquiv
    (cubeBoundaryJarCollapseUnliftedHomotopyEquiv (n + 1)) (n + 2)
  let b := cubeBoundaryTopHomologyIsoInt (n + 1)
  let s := hgrpSphereSelfIsoZ (n + 1)
  have heBij : Function.Bijective e.hom :=
    (ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance
  obtain ⟨v, hv⟩ := heBij.surjective (s.inv (1 : ℤ))
  let k : ℤ := b.hom v
  have hvfund : v = k • cubeBoundaryFundamentalClass (n + 1) := by
    apply ((ConcreteCategory.isIso_iff_bijective b.hom).mp inferInstance).injective
    rw [map_zsmul]
    change b.hom v = k • b.hom (cubeBoundaryFundamentalClass (n + 1))
    rw [cubeBoundaryTopHomologyIsoInt_fundamentalClass]
    simp [k]
  have hcoord := congrArg s.hom hv
  rw [hvfund, map_zsmul, map_zsmul] at hcoord
  have hehom : e.hom = HgrpMap (n + 2)
      (GenLoop.cubicalBoundaryExtension (sphereGenerator (n + 2))) := by
    rfl
  rw [hehom] at hcoord
  have hmul : k * cubicalBoundarySphereGeneratorCoordinate n = 1 := by
    simpa [e, s, cubicalBoundarySphereGeneratorCoordinate,
      GenLoop.cubicalBoundaryHurewicz, smul_eq_mul] using hcoord
  rw [mul_comm] at hmul
  exact Int.eq_one_or_neg_one_of_mul_eq_one hmul

/-- Integer coordinate of the maintained absolute Hurewicz value of the canonical sphere
generator. -/
noncomputable def absoluteHurewiczSphereGeneratorCoordinate (n : ℕ) : ℤ :=
  (hgrpSphereSelfIsoZ (n + 1)).hom
    (absoluteHurewiczAdd n (sphereBasepoint (n + 2))
      (Additive.ofMul (sphereGeneratorClass (n + 2))))

/-- The absolute Hurewicz value of the canonical cubical sphere generator also has unit
coordinate.  This follows from surjectivity and naturality: a preimage of the homology generator
is represented by a sphere self-map, whose action on top homology is multiplication by its
degree. -/
theorem absoluteHurewiczSphereGeneratorCoordinate_eq_one_or_neg_one (n : ℕ) :
    absoluteHurewiczSphereGeneratorCoordinate n = 1 ∨
      absoluteHurewiczSphereGeneratorCoordinate n = -1 := by
  let s := hgrpSphereSelfIsoZ (n + 1)
  let h := absoluteHurewiczAdd n (sphereBasepoint (n + 2))
  have hsurj : Function.Surjective h :=
    (isNConnected_sphere_succ_succ n).absoluteHurewiczAdd_surjective
      (sphereBasepoint (n + 2))
  obtain ⟨z, hz⟩ := hsurj (s.inv (1 : ℤ))
  obtain ⟨f, hf, hfclass⟩ :=
    homotopyGroup_exists_sphereSelfMapRepresentative (n + 1) z.toMul
  have hmapgen :
      HomotopyGroup.map f hf (sphereGeneratorClass (n + 2)) = z.toMul := by
    rw [← hfclass]
    exact (sphereTargetMapClass_eq_map_generator (n + 2) f hf).symm
  have hnat := absoluteHurewiczAdd_naturality n f hf
    (Additive.ofMul (sphereGeneratorClass (n + 2)))
  change HgrpMap (n + 2) (TopCat.ofHom f)
      (h (Additive.ofMul (sphereGeneratorClass (n + 2)))) =
    h (Additive.ofMul
      (HomotopyGroup.map f hf (sphereGeneratorClass (n + 2)))) at hnat
  rw [hmapgen] at hnat
  change HgrpMap (n + 2) (TopCat.ofHom f)
      (h (Additive.ofMul (sphereGeneratorClass (n + 2)))) = h z at hnat
  rw [hz] at hnat
  have hcoord := congrArg s.hom hnat
  have hend : sphereHomologyEnd (n + 1) (TopCat.ofHom f)
      (absoluteHurewiczSphereGeneratorCoordinate n) = 1 := by
    simpa [s, h, sphereHomologyEnd, absoluteHurewiczSphereGeneratorCoordinate] using hcoord
  rw [sphereHomologyEnd_apply] at hend
  have hmul : absoluteHurewiczSphereGeneratorCoordinate n *
      sphereHomologicalDegree (n + 1) (TopCat.ofHom f) = 1 := hend
  exact Int.eq_one_or_neg_one_of_mul_eq_one hmul

/-- The global sign comparing the cubical-boundary and absolute Hurewicz normalizations. -/
noncomputable def cubicalBoundaryAbsoluteSign (n : ℕ) : ℤ :=
  cubicalBoundarySphereGeneratorCoordinate n *
    absoluteHurewiczSphereGeneratorCoordinate n

theorem cubicalBoundaryAbsoluteSign_eq_one_or_neg_one (n : ℕ) :
    cubicalBoundaryAbsoluteSign n = 1 ∨ cubicalBoundaryAbsoluteSign n = -1 := by
  rcases cubicalBoundarySphereGeneratorCoordinate_eq_one_or_neg_one n with hc | hc <;>
    rcases absoluteHurewiczSphereGeneratorCoordinate_eq_one_or_neg_one n with ha | ha <;>
    simp [cubicalBoundaryAbsoluteSign, hc, ha]

/-- On the canonical sphere generator, the cubical-boundary Hurewicz class differs from the
maintained absolute Hurewicz class by the single global orientation sign. -/
theorem cubicalBoundaryHurewicz_sphereGenerator (n : ℕ) :
    GenLoop.cubicalBoundaryHurewicz (n + 1) (sphereGenerator (n + 2)) =
      cubicalBoundaryAbsoluteSign n •
        absoluteHurewiczAdd n (sphereBasepoint (n + 2))
          (Additive.ofMul (sphereGeneratorClass (n + 2))) := by
  let s := hgrpSphereSelfIsoZ (n + 1)
  apply ((ConcreteCategory.isIso_iff_bijective s.hom).mp inferInstance).injective
  rw [map_zsmul]
  change cubicalBoundarySphereGeneratorCoordinate n =
    cubicalBoundaryAbsoluteSign n * absoluteHurewiczSphereGeneratorCoordinate n
  rcases absoluteHurewiczSphereGeneratorCoordinate_eq_one_or_neg_one n with ha | ha <;>
    simp [cubicalBoundaryAbsoluteSign, ha]

/-- Every positive-dimensional generalized loop is obtained by applying its descended based
sphere map to the canonical cubical sphere generator. -/
theorem genLoop_map_sphereGenerator_targetGenLoopSphereMap (n : ℕ)
    {X : Type} [TopologicalSpace X] {x : X}
    (q : Ω^ (Fin (n + 2)) X x) :
    GenLoop.map (targetGenLoopSphereMap (n + 1) q)
        (targetGenLoopSphereMap_basepoint (n + 1) q) (sphereGenerator (n + 2)) = q := by
  apply GenLoop.ext
  intro u
  have h := congrArg (fun f : C(I^Fin (n + 2), X) => f u)
    (targetGenLoopSphereMap_comp_cubeToSphere (n + 1) q)
  exact h

/-- Universal cubical-boundary comparison in every degree at least two.  The two maintained
Hurewicz normalizations agree up to one dimension-dependent sign, independent of the target
space and of the represented homotopy class. -/
theorem cubicalBoundaryHurewicz_eq_sign_smul_absolute (n : ℕ)
    {X : Type} [TopologicalSpace X] {x : X}
    (q : Ω^ (Fin (n + 2)) X x) :
    GenLoop.cubicalBoundaryHurewicz (n + 1) q =
      cubicalBoundaryAbsoluteSign n •
        absoluteHurewiczAdd n x
          (Additive.ofMul (⟦q⟧ : π_ (n + 2) X x)) := by
  let f := targetGenLoopSphereMap (n + 1) q
  let hf := targetGenLoopSphereMap_basepoint (n + 1) q
  have hq : GenLoop.map f hf (sphereGenerator (n + 2)) = q :=
    genLoop_map_sphereGenerator_targetGenLoopSphereMap n q
  have hclass : HomotopyGroup.map f hf (sphereGeneratorClass (n + 2)) =
      (⟦q⟧ : π_ (n + 2) X x) := by
    rw [← sphereTargetMapClass_eq_map_generator (n + 2) f hf]
    exact sphereTargetMapClass_targetGenLoopSphereMap (n + 1) q
  calc
    GenLoop.cubicalBoundaryHurewicz (n + 1) q =
        GenLoop.cubicalBoundaryHurewicz (n + 1)
          (GenLoop.map f hf (sphereGenerator (n + 2))) := by rw [hq]
    _ = HgrpMap (n + 2) (TopCat.ofHom f)
        (GenLoop.cubicalBoundaryHurewicz (n + 1) (sphereGenerator (n + 2))) :=
      GenLoop.cubicalBoundaryHurewicz_map (n + 1) f hf (sphereGenerator (n + 2))
    _ = HgrpMap (n + 2) (TopCat.ofHom f)
        (cubicalBoundaryAbsoluteSign n •
          absoluteHurewiczAdd n (sphereBasepoint (n + 2))
            (Additive.ofMul (sphereGeneratorClass (n + 2)))) := by
      rw [cubicalBoundaryHurewicz_sphereGenerator]
    _ = cubicalBoundaryAbsoluteSign n •
        HgrpMap (n + 2) (TopCat.ofHom f)
          (absoluteHurewiczAdd n (sphereBasepoint (n + 2))
            (Additive.ofMul (sphereGeneratorClass (n + 2)))) := by
      rw [map_zsmul]
    _ = cubicalBoundaryAbsoluteSign n •
        absoluteHurewiczAdd n x
          (Additive.ofMul (HomotopyGroup.map f hf (sphereGeneratorClass (n + 2)))) := by
      exact congrArg (fun z => cubicalBoundaryAbsoluteSign n • z)
        (absoluteHurewiczAdd_naturality
          (X := Sph (n + 2)) (Y := X)
          (x := sphereBasepoint (n + 2)) (y := x) n f hf
          (Additive.ofMul (sphereGeneratorClass (n + 2))))
    _ = cubicalBoundaryAbsoluteSign n •
        absoluteHurewiczAdd n x
          (Additive.ofMul (⟦q⟧ : π_ (n + 2) X x)) := by rw [hclass]

/-- Multiplication by the cubical-boundary orientation sign is a bijection on every additive
group. -/
theorem bijective_cubicalBoundaryAbsoluteSign_smul (n : ℕ)
    (G : Type) [AddGroup G] :
    Function.Bijective (fun z : G => cubicalBoundaryAbsoluteSign n • z) := by
  rcases cubicalBoundaryAbsoluteSign_eq_one_or_neg_one n with h | h
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

/-- **First relative Hurewicz theorem for a contractible ambient space, in degrees at least
three.**  The homotopy and homology boundary maps are isomorphisms, and the universal cubical
boundary comparison identifies the remaining square with absolute Hurewicz up to a harmless
orientation sign. -/
theorem relativeHurewiczAdd_bijective_of_contractibleAmbient
    {n : ℕ} {X : Type} [TopologicalSpace X] [ContractibleSpace X]
    {A : Set X} (hA : IsNConnected (n + 1) A) (a : A) :
    Function.Bijective (relativeHurewiczAdd (n + 1) A a) := by
  refine relativeHurewiczAdd_bijective_of_boundary_comparison (n + 1) a
    (fun z => cubicalBoundaryAbsoluteSign n • absoluteHurewiczAdd n a z) ?_ ?_ ?_ ?_
  · change Function.Bijective (RelHomotopyGroup.bd (n + 2) X A a)
    exact bijective_bd_of_subsingleton (n + 1) a
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 3)) (a : X))
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 2)) (a : X))
  · let i := subIncl (Y := TopCat.of X) A
    letI : IsIso (relδ (n + 2) i) :=
      isIso_relδ i (n + 2)
        (isZero_Hgrp_of_contractible (X := TopCat.of X) (n + 2))
        (isZero_Hgrp_of_contractible (X := TopCat.of X) (n + 1))
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  · exact (bijective_cubicalBoundaryAbsoluteSign_smul n _).comp
      (hA.absoluteHurewiczAdd_bijective a)
  · intro q
    exact cubicalBoundaryHurewicz_eq_sign_smul_absolute n q

end IsNConnected

end Submission
