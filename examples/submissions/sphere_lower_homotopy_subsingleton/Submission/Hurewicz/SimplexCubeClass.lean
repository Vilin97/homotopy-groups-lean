/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.NormalizedSimplex
import Submission.Hurewicz.RelativeMap
import Submission.Hurewicz.RelativeSimplex

/-!
# An explicit simplex class for the cube pair

The cube--simplex homeomorphism supplies one top-dimensional singular simplex of the cube.  Its
faces lie in the cube boundary, so it determines an explicit class in
`H_{n+2}(I^{n+2}, ∂I^{n+2})`.  Mapping this class along the cubical reparametrisation of a
normalized simplex recovers the relative singular-simplex class represented by that simplex.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

-- Upstream Mathlib marks these `@[implicit_reducible]`; our pinned revision does not.
attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.alternatingFaceMapComplex AlgebraicTopology.AlternatingFaceMapComplex.obj
  SSet.chainComplexFunctor AlgebraicTopology.singularChainComplexFunctor
  CategoryTheory.Functor.postcompose₂ CategoryTheory.SimplicialObject.whiskering
  CategoryTheory.Functor.whiskeringLeft CategoryTheory.Functor.comp

noncomputable section

namespace Submission

attribute [local implicit_reducible] relComplex Hrel

/-- Under the singular-simplex dictionary, the simplicial map induced by a continuous map is
postcomposition. -/
theorem sngEquiv_map {U V : TopCat.{0}} (f : U ⟶ V) {d : ℕ} (s : Sng U _⦋d⦌) :
    sngEquiv V d ((TopCat.toSSet.map f).app _ s) = f.hom.comp (sngEquiv U d s) :=
  rfl

/-- The inverse simplex--cube reparametrisation carries the simplex boundary to the cube
boundary. -/
theorem cubeHomeoSimplex_symm_mem_boundary (d : ℕ)
    (z : stdSimplex ℝ (Fin (d + 1))) (hz : z ∈ bdry d) :
    (cubeHomeoSimplex d).symm z ∈ ∂I^d := by
  rw [mem_boundary_iff_norm_diskHomeoCube_symm_eq_one]
  rw [show (TopCat.diskHomeoCube.{0} d).symm ((cubeHomeoSimplex d).symm z) =
    simplexHomeoDisk' d z by simp [cubeHomeoSimplex]]
  exact (norm_simplexHomeoBall_eq_one_iff z).2 hz

/-- The singular top simplex of the cube obtained from the simplex--cube homeomorphism. -/
noncomputable def cubeFundamentalSimplex (d : ℕ) :
    Sng (TopCat.of (I^Fin d)) _⦋d⦌ :=
  sng ⟨(cubeHomeoSimplex d).symm, (cubeHomeoSimplex d).continuous_symm⟩

/-- The `i`-th face of `cubeFundamentalSimplex (d+1)`, regarded as a simplex of the cube
boundary. -/
noncomputable def cubeFundamentalFace {d : ℕ} (i : Fin (d + 2)) :
    Sng (TopCat.of (∂I^(d + 1))) _⦋d⦌ :=
  sng ⟨fun y ↦ ⟨(cubeHomeoSimplex (d + 1)).symm (faceMap i y),
      cubeHomeoSimplex_symm_mem_boundary (d + 1) _ (faceMap_mem_bdry i y)⟩,
    Continuous.subtype_mk
      ((cubeHomeoSimplex (d + 1)).continuous_symm.comp (continuous_faceMap i)) _⟩

/-- After inclusion into the cube, `cubeFundamentalFace` is the corresponding face of the top
simplex. -/
theorem sngIncl_cubeFundamentalFace {d : ℕ} (i : Fin (d + 2)) :
    (sngIncl (∂I^(d + 1))).app _ (cubeFundamentalFace i) =
      SSet.face (Sng (TopCat.of (I^Fin (d + 1)))) i (cubeFundamentalSimplex (d + 1)) := by
  refine sng_ext fun y ↦ ?_
  rw [sngEquiv_incl]
  change _ = sngEquiv (TopCat.of (I^Fin (d + 1))) d
    ((Sng (TopCat.of (I^Fin (d + 1)))).δ i (cubeFundamentalSimplex (d + 1))) y
  rw [apply_δ]
  simp only [cubeFundamentalFace, cubeFundamentalSimplex]
  rfl

/-- Every face of the explicit top cube simplex factors through the cube boundary. -/
theorem cubeFundamentalSimplex_face_lift (n : ℕ) (i : Fin (n + 3)) :
    ∃ t : Sng (TopCat.of (∂I^(n + 2))) _⦋n + 1⦌,
      (sngIncl (∂I^(n + 2))).app _ t =
        SSet.face (Sng (TopCat.of (I^Fin (n + 2)))) i (cubeFundamentalSimplex (n + 2)) :=
  ⟨cubeFundamentalFace (d := n + 1) i, sngIncl_cubeFundamentalFace i⟩

/-- The explicit top-dimensional relative class carried by the simplex--cube homeomorphism. -/
noncomputable def cubeSimplexRelativeClass (n : ℕ) :
    HrelSet (Y := TopCat.of (I^Fin (n + 2))) (n + 2) (∂I^(n + 2)) :=
  relativeSimplexClass (X := TopCat.of (I^Fin (n + 2))) (A := ∂I^(n + 2))
    (n := n + 1) (cubeFundamentalSimplex (n + 2))
    (cubeFundamentalSimplex_face_lift n)

/-- The relative Hurewicz evaluator using the explicit simplex class of the source cube pair. -/
noncomputable def simplexRelativeHurewicz (n : ℕ) {X : Type} [TopologicalSpace X]
    (A : Set X) (a : A) :
    π_rel (n + 2) X A a → HrelSet (Y := TopCat.of X) (n + 2) A :=
  RelHomotopyGroup.homologyEval (n := n + 1) (n + 2) (cubeSimplexRelativeClass n)

@[simp]
theorem simplexRelativeHurewicz_mk (n : ℕ) {X : Type} [TopologicalSpace X]
    {A : Set X} {a : A} (p : RelGenLoop (n + 2) X A a) :
    simplexRelativeHurewicz n A a ⟦p⟧ =
      RelGenLoop.hrelMap (n + 2) p (cubeSimplexRelativeClass n) :=
  rfl

/-- The explicit-simplex relative Hurewicz evaluator is natural under based maps of pairs. -/
theorem simplexRelativeHurewicz_naturality (n : ℕ)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} {a : A} {b : B}
    (f : BasedPairMap A B a b) (z : π_rel (n + 2) X A a) :
    f.hrelMap (n + 2) (simplexRelativeHurewicz n A a z) =
      simplexRelativeHurewicz n B b (RelHomotopyGroup.map f z) :=
  RelHomotopyGroup.homologyEval_naturality f (n + 2) (cubeSimplexRelativeClass n) z

namespace BasedPairMap

variable {m : ℕ} {U V : Type} [TopologicalSpace U] [TopologicalSpace V]
  {A : Set U} {B : Set V} {a : A} {b : B}

/-- On explicit relative simplex chains, the relative complex map is postcomposition by the
ambient map. -/
theorem relComplexMap_relativeSimplexChain (f : BasedPairMap A B a b)
    (s : Sng (TopCat.of U) _⦋m⦌) (t : Sng (TopCat.of V) _⦋m⦌)
    (hst : (TopCat.toSSet.map f.ambientHom).app _ s = t) :
    (relComplexMap (subIncl (Y := TopCat.of U) A) (subIncl (Y := TopCat.of V) B)
        (fA := f.subspaceHom) (f := f.ambientHom) f.subIncl_naturality).f m
        (relativeSimplexChain (X := TopCat.of U) A s) =
      relativeSimplexChain (X := TopCat.of V) B t := by
  rw [relativeSimplexChain, relativeSimplexChain, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.comp_f, relProj_comp_relComplexMap, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply, CsingMap_gen, hst]

end BasedPairMap

namespace SimplicialDeformation

variable {M k : ℕ} {Z : TopCat.{0}} {A : Set Z}

/-- The deformation chain map sends a singular generator to the generator indexed by the
deformed simplex. -/
@[simp]
theorem selfMap_gen (c : SimplicialDeformation Z A M) (s : Sng Z _⦋k⦌) :
    c.selfMap.f k (gen s) = gen (c.ρ k s) := by
  rw [selfMap, faceChainMap_f, apply_gen, ι_simpMap]
  rfl

/-- On explicit relative simplex chains, the descended deformation is represented by the
deformed simplex. -/
theorem relativeSelfMap_relativeSimplexChain (c : SimplicialDeformation Z A M)
    (s : Sng Z _⦋k⦌) :
    c.relativeSelfMap.f k (relativeSimplexChain A s) =
      relativeSimplexChain A (c.ρ k s) := by
  rw [relativeSimplexChain, relativeSimplexChain, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.comp_f, c.relProj_comp_relativeSelfMap, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply, c.selfMap_gen]

end SimplicialDeformation

namespace NormalizedSimplex

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

/-- Every face of a normalized simplex factors through the singleton basepoint subspace. -/
theorem singleton_face_lift (s : NormalizedSimplex n X x) (i : Fin (n + 3)) :
    ∃ t : Sng (TopCat.of ({x} : Set X)) _⦋n + 1⦌,
      (sngIncl ({x} : Set X)).app _ t = SSet.face (Sng (TopCat.of X)) i s.simplex := by
  refine ⟨constSimplex (X := TopCat.of ({x} : Set X)) (n + 1) ⟨x, rfl⟩, ?_⟩
  rw [sngIncl_singleton_eq_const]
  exact (s.face_eq i).symm

/-- The explicit relative homology class represented by a normalized simplex. -/
noncomputable def relativeClass (s : NormalizedSimplex n X x) :
    HrelSet (Y := TopCat.of X) (n + 2) ({x} : Set X) :=
  relativeSimplexClass (X := TopCat.of X) (A := ({x} : Set X)) (n := n + 1) s.simplex
    s.singleton_face_lift

/-- A normalized simplex as a relative cubical loop for the point pair. -/
noncomputable def toRelGenLoop (s : NormalizedSimplex n X x) :
    RelGenLoop (n + 2) X ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X)) :=
  RelHomotopyGroup.jStarGen (A := ({x} : Set X)) s.toGenLoop

@[simp]
theorem toRelGenLoop_apply (s : NormalizedSimplex n X x) (y : I^Fin (n + 2)) :
    s.toRelGenLoop.val y = s.cubeMap y :=
  rfl

/-- Mapping the explicit top cube simplex along the cubical reparametrisation of `s` recovers the
underlying singular simplex of `s`. -/
theorem pairMap_cubeFundamentalSimplex (s : NormalizedSimplex n X x) :
    (TopCat.toSSet.map (RelGenLoop.pairMap s.toRelGenLoop).ambientHom).app _
        (cubeFundamentalSimplex (n + 2)) = s.simplex := by
  apply (sngEquiv (TopCat.of X) (n + 2)).injective
  rw [sngEquiv_map]
  ext z
  change s.cubeMap ((cubeHomeoSimplex (n + 2)).symm z) =
    sngEquiv (TopCat.of X) (n + 2) s.simplex z
  rw [cubeMap]
  simp

/-- The induced map of relative chain complexes sends the explicit cube simplex chain to the
relative chain represented by `s`. -/
theorem pairMap_cubeFundamentalChain (s : NormalizedSimplex n X x) :
    (relComplexMap
        (subIncl (Y := TopCat.of (I^Fin (n + 2))) (∂I^(n + 2)))
        (subIncl (Y := TopCat.of X) ({x} : Set X))
        (RelGenLoop.pairMap s.toRelGenLoop).subIncl_naturality).f (n + 2)
      (relativeSimplexChain (X := TopCat.of (I^Fin (n + 2)))
        (∂I^(n + 2)) (cubeFundamentalSimplex (n + 2))) =
        relativeSimplexChain (X := TopCat.of X) ({x} : Set X) s.simplex := by
  rw [relativeSimplexChain, relativeSimplexChain, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.comp_f, relProj_comp_relComplexMap, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply, CsingMap_gen, s.pairMap_cubeFundamentalSimplex]

/-- The relative homology map carried by a normalized simplex sends the explicit source class to
the relative class of the simplex. -/
theorem pairMap_cubeSimplexRelativeClass (s : NormalizedSimplex n X x) :
    HomologicalComplex.homologyMap
        (relComplexMap
          (subIncl (Y := TopCat.of (I^Fin (n + 2))) (∂I^(n + 2)))
          (subIncl (Y := TopCat.of X) ({x} : Set X))
          (RelGenLoop.pairMap s.toRelGenLoop).subIncl_naturality) (n + 2)
        (cubeSimplexRelativeClass n) = s.relativeClass := by
  let F := relComplexMap
    (subIncl (Y := TopCat.of (I^Fin (n + 2))) (∂I^(n + 2)))
    (subIncl (Y := TopCat.of X) ({x} : Set X))
    (RelGenLoop.pairMap s.toRelGenLoop).subIncl_naturality
  have hchain :
      F.f (n + 2)
          (relativeSimplexChain (X := TopCat.of (I^Fin (n + 2)))
            (∂I^(n + 2)) (cubeFundamentalSimplex (n + 2))) =
        relativeSimplexChain (X := TopCat.of X) ({x} : Set X) s.simplex :=
    s.pairMap_cubeFundamentalChain
  exact homologyMap_relativeSimplexClass
    (X := TopCat.of (I^Fin (n + 2))) (Y := TopCat.of X)
    (A := ∂I^(n + 2)) (B := ({x} : Set X)) (n := n + 1) F
    (cubeFundamentalSimplex (n + 2)) (cubeFundamentalSimplex_face_lift n)
    s.simplex s.singleton_face_lift hchain

/-- Evaluating the explicit cube simplex class on the cubical map of a normalized simplex gives
the relative homology class of that simplex. -/
theorem hrelMap_cubeSimplexRelativeClass (s : NormalizedSimplex n X x) :
    RelGenLoop.hrelMap (n + 2) s.toRelGenLoop (cubeSimplexRelativeClass n) =
      s.relativeClass := by
  change HomologicalComplex.homologyMap
      (relComplexMap
        (subIncl (Y := TopCat.of (I^Fin (n + 2))) (∂I^(n + 2)))
        (subIncl (Y := TopCat.of X) ({x} : Set X))
        (RelGenLoop.pairMap s.toRelGenLoop).subIncl_naturality) (n + 2)
      (cubeSimplexRelativeClass n) = s.relativeClass
  exact s.pairMap_cubeSimplexRelativeClass

/-- The explicit-simplex relative Hurewicz evaluator computes on a normalized simplex exactly as
its relative singular-simplex class. -/
@[simp]
theorem simplexRelativeHurewicz_toRelGenLoop (s : NormalizedSimplex n X x) :
    simplexRelativeHurewicz n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))
        (⟦s.toRelGenLoop⟧ : π_rel (n + 2) X ({x} : Set X) ⟨x, rfl⟩) =
      s.relativeClass :=
  s.hrelMap_cubeSimplexRelativeClass

end NormalizedSimplex

namespace IsNConnected

variable {n : ℕ} {X : Type} [TopologicalSpace X]

/-- The relative deformation attached to connectivity sends each top-dimensional generator to
the relative chain of its normalized simplex. -/
theorem pointDeformation_relativeSimplexChain (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 2⦌) :
    (hX.pointDeformation x).relativeSelfMap.f (n + 2)
        (relativeSimplexChain (X := TopCat.of X) ({x} : Set X) s) =
      relativeSimplexChain (X := TopCat.of X) ({x} : Set X)
        (hX.normalizeTopSimplex x s).simplex := by
  change (hX.pointDeformation x).relativeSelfMap.f (n + 2)
      (relativeSimplexChain (X := TopCat.of X) ({x} : Set X) s) =
    relativeSimplexChain (X := TopCat.of X) ({x} : Set X)
      ((hX.pointDeformation x).ρ (n + 2) s)
  exact (hX.pointDeformation x).relativeSelfMap_relativeSimplexChain s

end IsNConnected

end Submission
