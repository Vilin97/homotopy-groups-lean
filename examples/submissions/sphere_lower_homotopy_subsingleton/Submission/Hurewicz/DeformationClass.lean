/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.StickSphere

/-!
# The simplex deformation preserves the represented homotopy class

The point-pair simplex deformation is built from genuine continuous homotopies.  On a normalized
simplex, coherence with the faces makes that homotopy fixed on the whole simplex boundary.  After
the chosen cube--simplex change of coordinates, it is therefore a homotopy of generalized loops.

We also turn an arbitrary generalized loop into a normalized singular simplex by precomposing it
with the simplex--cube homeomorphism.  Together these results identify the normalized
stick-coordinate class with the injective sphere reparameterization of the original cubical
class.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

namespace NormalizedSimplex

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

/-- During the point deformation, a normalized simplex stays fixed on its whole boundary. -/
theorem pointCompHom_boundary (hX : IsNConnected (n + 1) X)
    (s : NormalizedSimplex n X x) (z : stdSimplex ℝ (Fin (n + 3)))
    (hz : z ∈ bdry (n + 2)) (t : I) :
    compHom (hX.pointStep x) (n + 2) s.simplex (z, t) = x := by
  refine bdry_induction (j := n + 1) (P := fun z =>
    compHom (hX.pointStep x) (n + 2) s.simplex (z, t) = x) ?_ hz
  intro i y
  calc
    compHom (hX.pointStep x) (n + 2) s.simplex (faceMap i y, t) =
        compHom (hX.pointStep x) (n + 1)
          ((Sng (TopCat.of X)).δ i s.simplex) (y, t) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using
        compHom_δ (hX.pointStep x) (hX.pointStep_isNext x) (n + 1) i s.simplex y t
    _ = x := by
      rw [s.face_eq i]
      let τ : Sng (TopCat.of ({x} : Set X)) _⦋n + 1⦌ :=
        constSimplex (X := TopCat.of ({x} : Set X)) (n + 1) ⟨x, rfl⟩
      have hfix := compHom_incl (X := TopCat.of X) (A := ({x} : Set X))
        (hX.pointStep x) (n + 1) τ y t
      rw [sngIncl_singleton_eq_const] at hfix
      exact hfix.trans (Set.mem_singleton_iff.mp
        (sngEquiv (TopCat.of ({x} : Set X)) (n + 1) τ y).property)

/-- The cubical map of a normalized simplex is homotopic relative to the cube boundary to the
cubical map of its coherently normalized image. -/
theorem homotopic_normalizeTopSimplex (hX : IsNConnected (n + 1) X)
    (s : NormalizedSimplex n X x) :
    _root_.GenLoop.Homotopic s.toGenLoop
      (hX.normalizeTopSimplex x s.simplex).toGenLoop := by
  refine ⟨⟨⟨⟨fun ty => compHom (hX.pointStep x) (n + 2) s.simplex
      (cubeHomeoSimplex (n + 2) ty.2, ty.1), ?_⟩, ?_, ?_⟩, ?_⟩⟩
  · exact (compHom (hX.pointStep x) (n + 2) s.simplex).continuous.comp
      (((cubeHomeoSimplex (n + 2)).continuous.comp continuous_snd).prodMk continuous_fst)
  · intro y
    exact compHom_zero (hX.pointStep x) (n + 2) s.simplex
      (cubeHomeoSimplex (n + 2) y)
  · intro y
    change compHom (hX.pointStep x) (n + 2) s.simplex
        (cubeHomeoSimplex (n + 2) y, 1) =
      sngEquiv (TopCat.of X) (n + 2)
        ((hX.pointDeformation x).ρ (n + 2) s.simplex)
        (cubeHomeoSimplex (n + 2) y)
    rw [hX.pointDeformation_rho]
    exact (sngEquiv_defRho (hX.pointStep x) (n + 2) s.simplex
      (cubeHomeoSimplex (n + 2) y)).symm
  · intro t y hy
    change compHom (hX.pointStep x) (n + 2) s.simplex
        (cubeHomeoSimplex (n + 2) y, t) = s.cubeMap y
    rw [s.cubeMap_boundary y hy]
    exact s.pointCompHom_boundary hX (cubeHomeoSimplex (n + 2) y)
      (cubeHomeoSimplex_mem_bdry (n + 2) y hy) t

/-- Coherent normalization does not change the ordinary cubical homotopy class of a normalized
simplex. -/
theorem normalizeTopSimplex_homotopyClass (hX : IsNConnected (n + 1) X)
    (s : NormalizedSimplex n X x) :
    (hX.normalizeTopSimplex x s.simplex).homotopyClass = s.homotopyClass := by
  apply Quotient.sound
  exact (s.homotopic_normalizeTopSimplex hX).symm

/-- In stick-breaking coordinates, coherent normalization applies exactly the sphere
reparameterization to the original cubical class. -/
theorem normalizeTopSimplex_stickHomotopyClass (hX : IsNConnected (n + 1) X)
    (s : NormalizedSimplex n X x) :
    (hX.normalizeTopSimplex x s.simplex).stickHomotopyClass =
      stickReparamClass (n + 1) s.homotopyClass := by
  rw [← stickReparamClass_homotopyClass,
    s.normalizeTopSimplex_homotopyClass hX]

/-- Regard an arbitrary cubical generalized loop as a normalized singular simplex using the
chosen simplex--cube homeomorphism. -/
noncomputable def ofGenLoop (p : Ω^ (Fin (n + 2)) X x) : NormalizedSimplex n X x where
  simplex := sng (p.1.comp
    ⟨(cubeHomeoSimplex (n + 2)).symm, (cubeHomeoSimplex (n + 2)).continuous_symm⟩)
  face_eq i := by
    refine sng_ext fun y => ?_
    rw [apply_δ]
    change p ((cubeHomeoSimplex (n + 2)).symm (faceMap i y)) = x
    exact _root_.GenLoop.boundary p _
      (cubeHomeoSimplex_symm_mem_boundary (n + 2) _ (faceMap_mem_bdry i y))

@[simp]
theorem ofGenLoop_cubeMap_apply (p : Ω^ (Fin (n + 2)) X x) (y : I^Fin (n + 2)) :
    (ofGenLoop p).cubeMap y = p y := by
  rw [cubeMap]
  change p ((cubeHomeoSimplex (n + 2)).symm (cubeHomeoSimplex (n + 2) y)) = p y
  rw [Homeomorph.symm_apply_apply]

@[simp]
theorem ofGenLoop_toGenLoop (p : Ω^ (Fin (n + 2)) X x) :
    (ofGenLoop p).toGenLoop = p := by
  apply GenLoop.ext
  exact ofGenLoop_cubeMap_apply p

@[simp]
theorem ofGenLoop_homotopyClass (p : Ω^ (Fin (n + 2)) X x) :
    (ofGenLoop p).homotopyClass = (⟦p⟧ : π_ (n + 2) X x) := by
  rw [homotopyClass, ofGenLoop_toGenLoop]

/-- Normalizing the singular simplex associated to a generalized loop and then taking its stick
class gives the injective stick reparameterization of the original class. -/
theorem normalize_ofGenLoop_stickHomotopyClass (hX : IsNConnected (n + 1) X)
    (p : Ω^ (Fin (n + 2)) X x) :
    (hX.normalizeTopSimplex x (ofGenLoop p).simplex).stickHomotopyClass =
      stickReparamClass (n + 1) (⟦p⟧ : π_ (n + 2) X x) := by
  rw [(ofGenLoop p).normalizeTopSimplex_stickHomotopyClass hX,
    ofGenLoop_homotopyClass]

end NormalizedSimplex

end Submission
