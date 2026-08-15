/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneProjectiveLinePiTwo
import Submission.ComplexProjectivePlaneTrisectionRelativeHomotopy

/-!
# Connectivity of the projective-line inclusion

The standard inclusion `CP¹ → CP²` is an isomorphism on homotopy groups in degrees below
three and a surjection in degree three.  Its mapping-cylinder pair is therefore three-connected.
The next relative homotopy group is infinite: its boundary surjects onto the infinite cyclic
third homotopy group of `CP¹`, while `π₃(CP²)` vanishes.  Thus the pair is not four-connected.

The same conclusions hold for the canonical comparison from the four-triangle projective-line
realization to geometric `CP²`.  General mapping-cylinder and basepoint-transport lemmas are
proved first so that both conclusions record the actual maps, uniformly at every basepoint.
-/

open CategoryTheory
open scoped Topology Topology.Homotopy TopCat

noncomputable section

namespace Submission

universe u

/-! ## General transport and mapping-cylinder lemmas -/

/-- Injectivity of an induced positive-dimensional homotopy-group map transports along a path
in the source. -/
theorem homotopyGroup_map_injective_of_joined
    {N X Y : Type*} [Fintype N] [Nonempty N] [DecidableEq N]
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x x' : X} (gamma : Path x' x)
    (hinjective : Function.Injective
      (HomotopyGroup.map (N := N) (x := x) (y := f x) f rfl)) :
    Function.Injective
      (HomotopyGroup.map (N := N) (x := x') (y := f x') f rfl) := by
  intro a b hab
  apply (HomotopyGroup.transportMulEquiv gamma).injective
  apply hinjective
  change HomotopyGroup.map f rfl (HomotopyGroup.transport gamma a) =
    HomotopyGroup.map f rfl (HomotopyGroup.transport gamma b)
  rw [HomotopyGroup.map_transport, HomotopyGroup.map_transport, hab]

/-- On a path-connected source, injectivity of an induced positive-dimensional homotopy-group
map is independent of the basepoint. -/
theorem homotopyGroup_map_injective_of_pathConnected
    {N X Y : Type*} [Fintype N] [Nonempty N] [DecidableEq N]
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    (f : C(X, Y)) {x x' : X}
    (hinjective : Function.Injective
      (HomotopyGroup.map (N := N) (x := x) (y := f x) f rfl)) :
    Function.Injective
      (HomotopyGroup.map (N := N) (x := x') (y := f x') f rfl) :=
  homotopyGroup_map_injective_of_joined f
    (PathConnectedSpace.somePath x' x) hinjective

/-- On a path-connected source, bijectivity of an induced positive-dimensional homotopy-group
map is independent of the basepoint. -/
theorem homotopyGroup_map_bijective_of_pathConnected
    {N X Y : Type*} [Fintype N] [Nonempty N] [DecidableEq N]
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    (f : C(X, Y)) {x x' : X}
    (hbijective : Function.Bijective
      (HomotopyGroup.map (N := N) (x := x) (y := f x) f rfl)) :
    Function.Bijective
      (HomotopyGroup.map (N := N) (x := x') (y := f x') f rfl) :=
  ⟨homotopyGroup_map_injective_of_pathConnected f hbijective.injective,
    homotopyGroup_map_surjective_of_pathConnected f hbijective.surjective⟩

/-- Replacing the target basepoint of an induced map by its definitional image preserves
bijectivity. -/
theorem homotopyGroup_map_bijective_to_image_of_eq
    {N X Y : Type*} [Fintype N] [Nonempty N] [DecidableEq N]
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) {y : Y} (h : f x = y)
    (hbijective : Function.Bijective
      (HomotopyGroup.map (N := N) (x := x) (y := y) f h)) :
    Function.Bijective
      (HomotopyGroup.map (N := N) (x := x) (y := f x) f rfl) := by
  subst y
  simpa only using hbijective

/-- A mapping-cylinder pair is three-connected when the original map is bijective in degrees
zero, one, and two and surjective in degree three, uniformly in the basepoint. -/
theorem isThreeConnectedPair_mapCyl_of_bijective_low_of_surjective_three
    {X Y : TopCat} (f : X ⟶ Y)
    (hzero : ∀ x : X, Function.Bijective
      (HomotopyGroup.inducedPointedHom' 0 x f))
    (hone : ∀ x : X, Function.Bijective
      (HomotopyGroup.inducedPointedHom' 1 x f))
    (htwo : ∀ x : X, Function.Bijective
      (HomotopyGroup.inducedPointedHom' 2 x f))
    (hthree : ∀ x : X, Function.Surjective
      (HomotopyGroup.inducedPointedHom' 3 x f)) :
    IsNConnectedPair 3 (TopCat.MapCyl f) (TopCat.MapCyl.top f) where
  surjective_iStar_zero a := by
    obtain ⟨x, rfl⟩ := (TopCat.MapCyl.isHomeomorph_domInclToTop f).surjective a
    exact RelHomotopyGroup.iStar_mapCyl_surjective_of_induced_surjective
      0 f x (hzero x).surjective
  unique_piRel k hk a := by
    obtain ⟨x, rfl⟩ := (TopCat.MapCyl.isHomeomorph_domInclToTop f).surjective a
    have hk' : k ≤ 2 := by omega
    interval_cases k
    · exact RelHomotopyGroup.unique_one_mapCyl_of_surjective_one_of_bijective_zero
        f x (hone x).surjective (hzero x)
    · exact RelHomotopyGroup.unique_succ_mapCyl_of_bijective_adjacent
        1 f x (htwo x) (hone x)
    · haveI htwoIso : IsIso (HomotopyGroup.inducedPointedHom' 2 x f) :=
        (Pointed.isIso_iff_bijective _).mpr (htwo x)
      apply RelHomotopyGroup.unique_of_surjective_iStar_succ_of_injective_iStar
        2 (TopCat.MapCyl f) (TopCat.MapCyl.top f)
        (TopCat.MapCyl.domInclToTop f x)
      · exact RelHomotopyGroup.iStar_mapCyl_surjective_of_induced_surjective
          3 f x (hthree x)
      · exact (RelHomotopyGroup.bijective_iStar_mapCyl_of_isIso
          2 f x htwoIso).injective

/-- If the target has trivial third homotopy groups and the source has an infinite third
homotopy group at `x`, then relative `π₄` of the mapping-cylinder pair is infinite at `x`. -/
theorem RelHomotopyGroup.mapCyl_piFour_infinite_of_piThree
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
    (hsource : Infinite (π_ 3 X x))
    (htarget : ∀ y : Y, Subsingleton (π_ 3 Y y)) :
    Infinite
      (RelHomotopyGroup 4 (TopCat.MapCyl f) (TopCat.MapCyl.top f)
        (TopCat.MapCyl.domInclToTop f x)) := by
  letI : Infinite (π_ 3 X x) := hsource
  letI : Subsingleton
      (π_ 3 (TopCat.MapCyl f) (TopCat.MapCyl.domInclToTop f x)) :=
    subsingleton_homotopyGroup_of_homotopyEquiv
      (TopCat.MapCyl.homotopyEquivBase f) htarget _
  haveI htopIso : IsIso
      (HomotopyGroup.inducedPointedHom 3 x
        (TopCat.MapCyl.domInclToTop f)) := by
    apply HomotopyGroup.isIso_inducedPointedHom_of_isHomeomorph
    exact TopCat.MapCyl.isHomeomorph_domInclToTop f
  letI : Infinite
      (π_ 3 (TopCat.MapCyl.top f) (TopCat.MapCyl.domInclToTop f x)) :=
    Infinite.of_injective
      (fun z : π_ 3 X x =>
        HomotopyGroup.inducedPointedHom 3 x
          (TopCat.MapCyl.domInclToTop f) z)
      ((Pointed.isIso_iff_bijective _).mp htopIso).injective
  apply Infinite.of_surjective
    (RelHomotopyGroup.bd 3 (TopCat.MapCyl f) (TopCat.MapCyl.top f)
      (TopCat.MapCyl.domInclToTop f x))
  intro z
  exact (RelHomotopyGroup.mulExact_bdHom_iStarHom 2
    (TopCat.MapCyl f) (TopCat.MapCyl.top f)
    (TopCat.MapCyl.domInclToTop f x) z).mp (Subsingleton.elim _ _)

/-- An infinite fourth relative homotopy group obstructs four-connectedness. -/
theorem not_isFourConnectedPair_of_infinite_relative_piFour
    {X : Type} [TopologicalSpace X] {A : Set X} (a : A)
    (hinfinite : Infinite (RelHomotopyGroup 4 X A a)) :
    ¬ IsNConnectedPair 4 X A := by
  intro hconnected
  letI : Unique (RelHomotopyGroup 4 X A a) :=
    (hconnected.unique_piRel 3 (by omega) a).some
  letI : Infinite (RelHomotopyGroup 4 X A a) := hinfinite
  haveI : Finite (RelHomotopyGroup 4 X A a) :=
    Finite.of_injective (fun _ => PUnit.unit) fun _ _ _ => Subsingleton.elim _ _
  exact not_finite (RelHomotopyGroup 4 X A a)

/-! ## Absolute homotopy groups of complex projective space -/

/-- Every maintained positive-dimensional complex projective model is path connected. -/
theorem pathConnectedSpace_complexProjectiveModel (n : ℕ) :
    PathConnectedSpace (ComplexProjectiveModel n) := by
  letI : PathConnectedSpace (Sph (2 * n + 1)) := pathConnectedSpace_sph (by omega)
  letI : PathConnectedSpace (ComplexUnitSphere n) :=
    (complexUnitSphereHomeomorphSphere n).symm.surjective.pathConnectedSpace
      (complexUnitSphereHomeomorphSphere n).symm.continuous
  exact (complexHopfMap_isQuotientMap n).surjective.pathConnectedSpace
    (complexHopfMap_isQuotientMap n).continuous

/-- The fundamental group of a positive-dimensional complex projective model is trivial at
every basepoint. -/
theorem piOne_complexProjectiveModel_subsingleton_at
    (n : ℕ) (hn : 1 ≤ n) (x : ComplexProjectiveModel n) :
    Subsingleton (π_ 1 (ComplexProjectiveModel n) x) := by
  letI : PathConnectedSpace (ComplexProjectiveModel n) :=
    pathConnectedSpace_complexProjectiveModel n
  obtain ⟨e⟩ := nonempty_mulEquiv_of_pathConnectedSpace
    (N := Fin 1) x (complexProjectiveModelBasepoint n)
  exact e.toEquiv.subsingleton_congr.mpr
    (piOne_complexProjectiveModel_subsingleton n hn)

/-- The geometric complex projective plane has trivial third homotopy group at every
basepoint. -/
theorem piThree_complexProjectivePlane_subsingleton_at
    (x : ComplexProjectiveModel 2) :
    Subsingleton (π_ 3 (ComplexProjectiveModel 2) x) := by
  letI : PathConnectedSpace (ComplexProjectiveModel 2) :=
    pathConnectedSpace_complexProjectiveModel 2
  obtain ⟨changeBasepoint⟩ := nonempty_mulEquiv_of_pathConnectedSpace
    (N := Fin 3) x (complexProjectiveModelBasepoint 2)
  obtain ⟨changeSpace⟩ :=
    complexProjectiveModel_higher_homotopy_mulEquiv_sphere 2 0 (by omega)
  exact (changeBasepoint.trans changeSpace).toEquiv.subsingleton_congr.mpr
    (subsingleton_homotopyGroup_sphere_of_lt 3 5 (by omega)
      (sphereBasepoint 5))

/-- The geometric projective line has infinite cyclic third homotopy group at the maintained
basepoint. -/
theorem piThree_complexProjectiveLine_mulEquiv_int :
    Nonempty
      (π_ 3 (ComplexProjectiveModel 1) (complexProjectiveModelBasepoint 1) ≃*
        Multiplicative ℤ) := by
  obtain ⟨changeSpace⟩ :=
    complexProjectiveModel_higher_homotopy_mulEquiv_sphere 1 0 (by omega)
  obtain ⟨sphereThree⟩ :=
    sphere_diagonal_sph_at_mulEquiv_int 2 (sphereBasepoint 3)
  exact ⟨changeSpace.trans sphereThree⟩

/-! ## The geometric inclusion `CP¹ → CP²` -/

/-- The standard projective-line inclusion is bijective on path components at every
basepoint. -/
theorem complexProjectivePlaneBottomIncl_piZero_bijective_at
    (x : ComplexProjectiveModel 1) :
    Function.Bijective
      (HomotopyGroup.inducedPointedHom' 0 x
        complexProjectivePlaneBottomInclTopCat) := by
  rw [HomotopyGroup.inducedPointedHom'_eq_inducedPointedHom]
  change Function.Bijective
    (HomotopyGroup.map (N := Fin 0)
      complexProjectivePlaneBottomInclTopCat.hom rfl)
  letI : PathConnectedSpace (ComplexProjectiveModel 1) :=
    pathConnectedSpace_complexProjectiveModel 1
  letI : PathConnectedSpace (ComplexProjectiveModel 2) :=
    pathConnectedSpace_complexProjectiveModel 2
  have hsource : Subsingleton (π_ 0 (ComplexProjectiveModel 1) x) :=
    subsingleton_homotopyGroup_zero x
  have htarget : Subsingleton
      (π_ 0 (ComplexProjectiveModel 2) (complexProjectivePlaneBottomIncl x)) :=
    subsingleton_homotopyGroup_zero _
  constructor
  · intro p q _
    exact hsource.elim p q
  · intro q
    exact ⟨(default : π_ 0 (ComplexProjectiveModel 1) x),
      htarget.elim _ q⟩

/-- The standard projective-line inclusion is bijective on fundamental groups at every
basepoint. -/
theorem complexProjectivePlaneBottomIncl_piOne_bijective_at
    (x : ComplexProjectiveModel 1) :
    Function.Bijective
      (HomotopyGroup.inducedPointedHom' 1 x
        complexProjectivePlaneBottomInclTopCat) := by
  rw [HomotopyGroup.inducedPointedHom'_eq_inducedPointedHom]
  change Function.Bijective
    (HomotopyGroup.map (N := Fin 1)
      complexProjectivePlaneBottomInclTopCat.hom rfl)
  have hsource : Subsingleton (π_ 1 (ComplexProjectiveModel 1) x) :=
    piOne_complexProjectiveModel_subsingleton_at 1 (by omega) x
  have htarget : Subsingleton
      (π_ 1 (ComplexProjectiveModel 2) (complexProjectivePlaneBottomIncl x)) :=
    piOne_complexProjectiveModel_subsingleton_at 2 (by omega) _
  constructor
  · intro p q _
    exact hsource.elim p q
  · intro q
    exact ⟨(default : π_ 1 (ComplexProjectiveModel 1) x),
      htarget.elim _ q⟩

/-- The standard projective-line inclusion is bijective on second homotopy groups at every
basepoint. -/
theorem complexProjectivePlaneBottomIncl_piTwo_bijective_at
    (x : ComplexProjectiveModel 1) :
    Function.Bijective
      (HomotopyGroup.inducedPointedHom' 2 x
        complexProjectivePlaneBottomInclTopCat) := by
  rw [HomotopyGroup.inducedPointedHom'_eq_inducedPointedHom]
  letI : PathConnectedSpace (ComplexProjectiveModel 1) :=
    pathConnectedSpace_complexProjectiveModel 1
  have hbase : Function.Bijective
      (HomotopyGroup.map (N := Fin 2)
        (x := complexProjectiveModelBasepoint 1)
        (y := complexProjectivePlaneBottomIncl
          (complexProjectiveModelBasepoint 1))
        complexProjectivePlaneBottomInclMap rfl) :=
    homotopyGroup_map_bijective_to_image_of_eq
      complexProjectivePlaneBottomInclMap
      (complexProjectiveModelBasepoint 1)
      complexProjectivePlaneBottomInclMap_basepoint
      complexProjectivePlaneBottomIncl_piTwo_bijective
  exact homotopyGroup_map_bijective_of_pathConnected
    (x := complexProjectiveModelBasepoint 1)
    complexProjectivePlaneBottomInclMap
    hbase

/-- The standard projective-line inclusion is surjective on third homotopy groups at every
basepoint. -/
theorem complexProjectivePlaneBottomIncl_piThree_surjective_at
    (x : ComplexProjectiveModel 1) :
    Function.Surjective
      (HomotopyGroup.inducedPointedHom' 3 x
        complexProjectivePlaneBottomInclTopCat) := by
  rw [HomotopyGroup.inducedPointedHom'_eq_inducedPointedHom]
  letI : Subsingleton
      (π_ 3 (ComplexProjectiveModel 2) (complexProjectivePlaneBottomIncl x)) :=
    piThree_complexProjectivePlane_subsingleton_at _
  intro z
  exact ⟨(default : π_ 3 (ComplexProjectiveModel 1) x),
    piThree_complexProjectivePlane_subsingleton_at _ |>.elim _ z⟩

/-- The mapping-cylinder pair of `CP¹ → CP²` is three-connected. -/
theorem complexProjectivePlaneBottomIncl_isThreeConnectedPair :
    IsNConnectedPair 3
      (TopCat.MapCyl complexProjectivePlaneBottomInclTopCat)
      (TopCat.MapCyl.top complexProjectivePlaneBottomInclTopCat) :=
  isThreeConnectedPair_mapCyl_of_bijective_low_of_surjective_three
    complexProjectivePlaneBottomInclTopCat
    complexProjectivePlaneBottomIncl_piZero_bijective_at
    complexProjectivePlaneBottomIncl_piOne_bijective_at
    complexProjectivePlaneBottomIncl_piTwo_bijective_at
    complexProjectivePlaneBottomIncl_piThree_surjective_at

/-- Relative `π₁` of the mapping-cylinder pair of `CP¹ → CP²` is trivial at every
basepoint. -/
theorem complexProjectivePlaneBottomIncl_relative_piOne_unique
    (a : TopCat.MapCyl.top complexProjectivePlaneBottomInclTopCat) :
    Nonempty
      (Unique
        (RelHomotopyGroup 1
          (TopCat.MapCyl complexProjectivePlaneBottomInclTopCat)
          (TopCat.MapCyl.top complexProjectivePlaneBottomInclTopCat) a)) :=
  complexProjectivePlaneBottomIncl_isThreeConnectedPair.unique_piRel 0 (by omega) a

/-- Relative `π₂` of the mapping-cylinder pair of `CP¹ → CP²` is trivial at every
basepoint. -/
theorem complexProjectivePlaneBottomIncl_relative_piTwo_unique
    (a : TopCat.MapCyl.top complexProjectivePlaneBottomInclTopCat) :
    Nonempty
      (Unique
        (RelHomotopyGroup 2
          (TopCat.MapCyl complexProjectivePlaneBottomInclTopCat)
          (TopCat.MapCyl.top complexProjectivePlaneBottomInclTopCat) a)) :=
  complexProjectivePlaneBottomIncl_isThreeConnectedPair.unique_piRel 1 (by omega) a

/-- Relative `π₃` of the mapping-cylinder pair of `CP¹ → CP²` is trivial at every
basepoint. -/
theorem complexProjectivePlaneBottomIncl_relative_piThree_unique
    (a : TopCat.MapCyl.top complexProjectivePlaneBottomInclTopCat) :
    Nonempty
      (Unique
        (RelHomotopyGroup 3
          (TopCat.MapCyl complexProjectivePlaneBottomInclTopCat)
          (TopCat.MapCyl.top complexProjectivePlaneBottomInclTopCat) a)) :=
  complexProjectivePlaneBottomIncl_isThreeConnectedPair.unique_piRel 2 (by omega) a

/-- Relative `π₄` of the mapping-cylinder pair of `CP¹ → CP²` is infinite at the
maintained basepoint. -/
theorem complexProjectivePlaneBottomIncl_relative_piFour_infinite :
    Infinite
      (RelHomotopyGroup 4
        (TopCat.MapCyl complexProjectivePlaneBottomInclTopCat)
        (TopCat.MapCyl.top complexProjectivePlaneBottomInclTopCat)
        (TopCat.MapCyl.domInclToTop complexProjectivePlaneBottomInclTopCat
          (complexProjectiveModelBasepoint 1))) := by
  obtain ⟨line⟩ := piThree_complexProjectiveLine_mulEquiv_int
  letI : Infinite
      (π_ 3 (ComplexProjectiveModel 1) (complexProjectiveModelBasepoint 1)) :=
    Infinite.of_injective line.symm line.symm.injective
  exact RelHomotopyGroup.mapCyl_piFour_infinite_of_piThree
    complexProjectivePlaneBottomInclTopCat
    (complexProjectiveModelBasepoint 1) inferInstance
    piThree_complexProjectivePlane_subsingleton_at

/-- The mapping-cylinder pair of `CP¹ → CP²` is not four-connected. -/
theorem complexProjectivePlaneBottomIncl_not_isFourConnectedPair :
    ¬ IsNConnectedPair 4
      (TopCat.MapCyl complexProjectivePlaneBottomInclTopCat)
      (TopCat.MapCyl.top complexProjectivePlaneBottomInclTopCat) :=
  not_isFourConnectedPair_of_infinite_relative_piFour
    (TopCat.MapCyl.domInclToTop complexProjectivePlaneBottomInclTopCat
      (complexProjectiveModelBasepoint 1))
    complexProjectivePlaneBottomIncl_relative_piFour_infinite

/-- The mapping-cylinder pair of `CP¹ → CP²` has connectivity exactly three. -/
theorem complexProjectivePlaneBottomIncl_connectivity_exactly_three :
    IsNConnectedPair 3
        (TopCat.MapCyl complexProjectivePlaneBottomInclTopCat)
        (TopCat.MapCyl.top complexProjectivePlaneBottomInclTopCat) ∧
      ¬ IsNConnectedPair 4
        (TopCat.MapCyl complexProjectivePlaneBottomInclTopCat)
        (TopCat.MapCyl.top complexProjectivePlaneBottomInclTopCat) :=
  ⟨complexProjectivePlaneBottomIncl_isThreeConnectedPair,
    complexProjectivePlaneBottomIncl_not_isFourConnectedPair⟩

/-! ## The finite projective-line comparison -/

namespace ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The finite projective-line comparison is bijective on path components at every
basepoint. -/
theorem projectiveLineRealizationToComplexProjectivePlane_piZero_bijective_at
    (x : SSet.toTop.obj (orderedSSet projectiveLineCycle)) :
    Function.Bijective
      (HomotopyGroup.inducedPointedHom' 0 x
        projectiveLineRealizationToComplexProjectivePlane) := by
  rw [HomotopyGroup.inducedPointedHom'_eq_inducedPointedHom]
  letI : PathConnectedSpace (ComplexProjectiveModel 2) :=
    pathConnectedSpace_complexProjectiveModel 2
  letI : Subsingleton
      (π_ 0 (SSet.toTop.obj (orderedSSet projectiveLineCycle)) x) :=
    projectiveLinePiZero_subsingleton x
  letI : Subsingleton
      (π_ 0 (ComplexProjectiveModel 2)
        (projectiveLineRealizationToComplexProjectivePlane x)) :=
    subsingleton_homotopyGroup_zero _
  exact function_bijective_of_subsingleton_of_subsingleton _

/-- The finite projective-line comparison is bijective on fundamental groups at every
basepoint. -/
theorem projectiveLineRealizationToComplexProjectivePlane_piOne_bijective_at
    (x : SSet.toTop.obj (orderedSSet projectiveLineCycle)) :
    Function.Bijective
      (HomotopyGroup.inducedPointedHom' 1 x
        projectiveLineRealizationToComplexProjectivePlane) := by
  rw [HomotopyGroup.inducedPointedHom'_eq_inducedPointedHom]
  letI : Subsingleton
      (π_ 1 (SSet.toTop.obj (orderedSSet projectiveLineCycle)) x) :=
    projectiveLinePiOne_subsingleton x
  letI : Subsingleton
      (π_ 1 (ComplexProjectiveModel 2)
        (projectiveLineRealizationToComplexProjectivePlane x)) :=
    piOne_complexProjectiveModel_subsingleton_at 2 (by omega) _
  constructor
  · intro p q _
    exact Subsingleton.elim p q
  · intro q
    exact ⟨default, Subsingleton.elim _ q⟩

/-- The finite projective-line comparison is bijective on second homotopy groups at every
basepoint. -/
theorem projectiveLineRealizationToComplexProjectivePlane_piTwo_bijective_at
    (x : SSet.toTop.obj (orderedSSet projectiveLineCycle)) :
    Function.Bijective
      (HomotopyGroup.inducedPointedHom' 2 x
        projectiveLineRealizationToComplexProjectivePlane) := by
  rw [HomotopyGroup.inducedPointedHom'_eq_inducedPointedHom]
  have hbase : Function.Bijective
      (HomotopyGroup.map (N := Fin 2)
        (x := projectiveLineBasepoint)
        (y := projectiveLineRealizationToComplexProjectivePlane
          projectiveLineBasepoint)
        projectiveLineRealizationToComplexProjectivePlane.hom rfl) :=
    homotopyGroup_map_bijective_to_image_of_eq
      projectiveLineRealizationToComplexProjectivePlane.hom
      projectiveLineBasepoint
      projectiveLineRealizationToComplexProjectivePlane_basepoint
      projectiveLineRealizationToComplexProjectivePlane_piTwo_bijective
  exact homotopyGroup_map_bijective_of_pathConnected
    (x := projectiveLineBasepoint)
    projectiveLineRealizationToComplexProjectivePlane.hom
    hbase

/-- The finite projective-line comparison is surjective on third homotopy groups at every
basepoint. -/
theorem projectiveLineRealizationToComplexProjectivePlane_piThree_surjective_at
    (x : SSet.toTop.obj (orderedSSet projectiveLineCycle)) :
    Function.Surjective
      (HomotopyGroup.inducedPointedHom' 3 x
        projectiveLineRealizationToComplexProjectivePlane) := by
  rw [HomotopyGroup.inducedPointedHom'_eq_inducedPointedHom]
  letI : Subsingleton
      (π_ 3 (ComplexProjectiveModel 2)
        (projectiveLineRealizationToComplexProjectivePlane x)) :=
    piThree_complexProjectivePlane_subsingleton_at _
  intro z
  exact ⟨(default :
      π_ 3 (SSet.toTop.obj (orderedSSet projectiveLineCycle)) x),
    piThree_complexProjectivePlane_subsingleton_at _ |>.elim _ z⟩

/-- The mapping-cylinder pair of the finite projective-line comparison is three-connected. -/
theorem projectiveLineRealizationToComplexProjectivePlane_isThreeConnectedPair :
    IsNConnectedPair 3
      (TopCat.MapCyl projectiveLineRealizationToComplexProjectivePlane)
      (TopCat.MapCyl.top projectiveLineRealizationToComplexProjectivePlane) :=
  isThreeConnectedPair_mapCyl_of_bijective_low_of_surjective_three
    projectiveLineRealizationToComplexProjectivePlane
    projectiveLineRealizationToComplexProjectivePlane_piZero_bijective_at
    projectiveLineRealizationToComplexProjectivePlane_piOne_bijective_at
    projectiveLineRealizationToComplexProjectivePlane_piTwo_bijective_at
    projectiveLineRealizationToComplexProjectivePlane_piThree_surjective_at

/-- Relative `π₁` of the finite projective-line comparison pair is trivial at every
basepoint. -/
theorem projectiveLineRealizationToComplexProjectivePlane_relative_piOne_unique
    (a : TopCat.MapCyl.top projectiveLineRealizationToComplexProjectivePlane) :
    Nonempty
      (Unique
        (RelHomotopyGroup 1
          (TopCat.MapCyl projectiveLineRealizationToComplexProjectivePlane)
          (TopCat.MapCyl.top projectiveLineRealizationToComplexProjectivePlane) a)) :=
  projectiveLineRealizationToComplexProjectivePlane_isThreeConnectedPair.unique_piRel
    0 (by omega) a

/-- Relative `π₂` of the finite projective-line comparison pair is trivial at every
basepoint. -/
theorem projectiveLineRealizationToComplexProjectivePlane_relative_piTwo_unique
    (a : TopCat.MapCyl.top projectiveLineRealizationToComplexProjectivePlane) :
    Nonempty
      (Unique
        (RelHomotopyGroup 2
          (TopCat.MapCyl projectiveLineRealizationToComplexProjectivePlane)
          (TopCat.MapCyl.top projectiveLineRealizationToComplexProjectivePlane) a)) :=
  projectiveLineRealizationToComplexProjectivePlane_isThreeConnectedPair.unique_piRel
    1 (by omega) a

/-- Relative `π₃` of the finite projective-line comparison pair is trivial at every
basepoint. -/
theorem projectiveLineRealizationToComplexProjectivePlane_relative_piThree_unique
    (a : TopCat.MapCyl.top projectiveLineRealizationToComplexProjectivePlane) :
    Nonempty
      (Unique
        (RelHomotopyGroup 3
          (TopCat.MapCyl projectiveLineRealizationToComplexProjectivePlane)
          (TopCat.MapCyl.top projectiveLineRealizationToComplexProjectivePlane) a)) :=
  projectiveLineRealizationToComplexProjectivePlane_isThreeConnectedPair.unique_piRel
    2 (by omega) a

/-- The finite projective-line realization has infinite cyclic third homotopy group at the
maintained basepoint. -/
theorem projectiveLinePiThree_mulEquiv_int :
    Nonempty
      (π_ 3 (SSet.toTop.obj (orderedSSet projectiveLineCycle))
          projectiveLineBasepoint ≃* Multiplicative ℤ) := by
  let sourceEquiv := HomotopyGroup.homeomorphMulEquivOfEq
    (N := Fin 3) projectiveLineRealizationHomeomorphComplexProjectiveLine
    projectiveLineRealizationHomeomorphComplexProjectiveLine_basepoint
  obtain ⟨line⟩ := piThree_complexProjectiveLine_mulEquiv_int
  exact ⟨sourceEquiv.trans line⟩

/-- Relative `π₄` of the finite projective-line comparison pair is infinite at the
maintained basepoint. -/
theorem projectiveLineRealizationToComplexProjectivePlane_relative_piFour_infinite :
    Infinite
      (RelHomotopyGroup 4
        (TopCat.MapCyl projectiveLineRealizationToComplexProjectivePlane)
        (TopCat.MapCyl.top projectiveLineRealizationToComplexProjectivePlane)
        (TopCat.MapCyl.domInclToTop
          projectiveLineRealizationToComplexProjectivePlane
          projectiveLineBasepoint)) := by
  obtain ⟨line⟩ := projectiveLinePiThree_mulEquiv_int
  letI : Infinite
      (π_ 3 (SSet.toTop.obj (orderedSSet projectiveLineCycle))
        projectiveLineBasepoint) :=
    Infinite.of_injective line.symm line.symm.injective
  exact RelHomotopyGroup.mapCyl_piFour_infinite_of_piThree
    projectiveLineRealizationToComplexProjectivePlane
    projectiveLineBasepoint inferInstance
    piThree_complexProjectivePlane_subsingleton_at

/-- The mapping-cylinder pair of the finite projective-line comparison is not
four-connected. -/
theorem projectiveLineRealizationToComplexProjectivePlane_not_isFourConnectedPair :
    ¬ IsNConnectedPair 4
      (TopCat.MapCyl projectiveLineRealizationToComplexProjectivePlane)
      (TopCat.MapCyl.top projectiveLineRealizationToComplexProjectivePlane) :=
  not_isFourConnectedPair_of_infinite_relative_piFour
    (TopCat.MapCyl.domInclToTop projectiveLineRealizationToComplexProjectivePlane
      projectiveLineBasepoint)
    projectiveLineRealizationToComplexProjectivePlane_relative_piFour_infinite

/-- The mapping-cylinder pair of the finite projective-line comparison has connectivity
exactly three. -/
theorem projectiveLineRealizationToComplexProjectivePlane_connectivity_exactly_three :
    IsNConnectedPair 3
        (TopCat.MapCyl projectiveLineRealizationToComplexProjectivePlane)
        (TopCat.MapCyl.top projectiveLineRealizationToComplexProjectivePlane) ∧
      ¬ IsNConnectedPair 4
        (TopCat.MapCyl projectiveLineRealizationToComplexProjectivePlane)
        (TopCat.MapCyl.top projectiveLineRealizationToComplexProjectivePlane) :=
  ⟨projectiveLineRealizationToComplexProjectivePlane_isThreeConnectedPair,
    projectiveLineRealizationToComplexProjectivePlane_not_isFourConnectedPair⟩

end ComplexProjectivePlaneTriangulation

end Submission
