/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct
import Submission.Hurewicz.SingularKan
import Submission.Hurewicz.StickBoundary

/-!
# Simplicial and cubical homotopy addition

Normalized singular simplices are the topological realization of Mathlib's pointed simplices:
a singular `(n + 2)`-simplex has constant codimension-one faces exactly when its Yoneda morphism
is constant on the simplicial boundary.  We make this correspondence an explicit equivalence.

For a multiplication simplex at the final index, its three potentially nonconstant faces are
`g`, `fg`, and `f`.  The remaining faces are constant.  We package these faces as a normalized
simplex boundary, so its stick-breaking cube is a cubical shell with only its final two face
pairs potentially nonconstant.  This connects simplicial Kan multiplication to the existing
cubical homotopy-addition relation.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

namespace NormalizedSimplex

/-- A normalized singular simplex, regarded as a pointed simplex of the singular simplicial
set. -/
def toPtSimplex (s : NormalizedSimplex n X x) :
    (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x) where
  map := SSet.yonedaEquiv.symm s.simplex
  comm := by
    apply SSet.boundary.hom_ext
    intro i
    trans SSet.const (TopCat.toSSetObj₀Equiv.symm x)
    · rw [← Category.assoc, SSet.boundary.ι_ι]
      apply SSet.yonedaEquiv.injective
      calc
        SSet.yonedaEquiv
              (SSet.stdSimplex.δ i ≫ SSet.yonedaEquiv.symm s.simplex) =
            (Sng (TopCat.of X)).δ i s.simplex := by
          simpa using (yonedaEquiv_comp_δ (X := X) (q := n + 1) i
            (SSet.yonedaEquiv.symm s.simplex)).symm
        _ = constSimplex (X := TopCat.of X) (n + 1) x := s.face_eq i
        _ = SSet.yonedaEquiv
              (SSet.const (TopCat.toSSetObj₀Equiv.symm x) :
                Δ[n + 1] ⟶ Sng (TopCat.of X)) := rfl
    · simp

@[simp]
theorem toPtSimplex_map (s : NormalizedSimplex n X x) :
    s.toPtSimplex.map = SSet.yonedaEquiv.symm s.simplex :=
  rfl

/-- A pointed simplex of a singular simplicial set, regarded as a normalized singular
simplex. -/
def ofPtSimplex
    (s : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x)) : NormalizedSimplex n X x where
  simplex := SSet.yonedaEquiv s.map
  face_eq i := by
    calc
      (Sng (TopCat.of X)).δ i (SSet.yonedaEquiv s.map) =
          SSet.yonedaEquiv (SSet.stdSimplex.δ i ≫ s.map) :=
        yonedaEquiv_comp_δ (X := X) (q := n + 1) i s.map
      _ = SSet.yonedaEquiv
          (SSet.const (TopCat.toSSetObj₀Equiv.symm x) :
            Δ[n + 1] ⟶ Sng (TopCat.of X)) := congrArg SSet.yonedaEquiv (s.δ_map i)
      _ = constSimplex (X := TopCat.of X) (n + 1) x := rfl

@[simp]
theorem ofPtSimplex_simplex
    (s : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x)) :
    (ofPtSimplex s).simplex = SSet.yonedaEquiv s.map :=
  rfl

/-- Two normalized simplices with the same underlying singular simplex are equal. -/
@[ext]
theorem ext {s t : NormalizedSimplex n X x} (h : s.simplex = t.simplex) : s = t := by
  cases s with
  | mk s hs =>
      cases t with
      | mk t ht =>
          simp only at h
          subst t
          rfl

@[simp]
theorem ofPtSimplex_toPtSimplex (s : NormalizedSimplex n X x) :
    ofPtSimplex s.toPtSimplex = s := by
  apply ext
  exact SSet.yonedaEquiv.apply_symm_apply s.simplex

@[simp]
theorem toPtSimplex_ofPtSimplex
    (s : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x)) :
    (ofPtSimplex s).toPtSimplex = s := by
  ext
  simp [ofPtSimplex, toPtSimplex]

/-- Normalized singular `(n + 2)`-simplices are equivalent to pointed `(n + 2)`-simplices of
the singular simplicial set. -/
def equivPtSimplex :
    NormalizedSimplex n X x ≃
      (Sng (TopCat.of X)).PtSimplex (n + 2)
        (TopCat.toSSetObj₀Equiv.symm x) where
  toFun := toPtSimplex
  invFun := ofPtSimplex
  left_inv := ofPtSimplex_toPtSimplex
  right_inv := toPtSimplex_ofPtSimplex

/-- The normalized simplex which is constant at the basepoint. -/
def const (n : ℕ) (x : X) : NormalizedSimplex n X x where
  simplex := constSimplex (X := TopCat.of X) ((n + 1) + 1) x
  face_eq i := face_constSimplex (X := TopCat.of X) (n + 1) i x

@[simp]
theorem const_simplex (n : ℕ) (x : X) :
    (const n x).simplex = constSimplex (X := TopCat.of X) ((n + 1) + 1) x :=
  rfl

@[simp]
theorem const_stickMap_apply (n : ℕ) (x : X) (t : I^Fin (n + 2)) :
    (const n x).stickMap t = x := by
  rw [stickMap_apply, const_simplex, constSimplex, sngEquiv_sng]
  rfl

@[simp]
theorem ofPtSimplex_const :
    ofPtSimplex
        (SSet.RelativeMorphism.const :
          (Sng (TopCat.of X)).PtSimplex (n + 2)
            (TopCat.toSSetObj₀Equiv.symm x)) =
      const n x := by
  apply ext
  rfl

end NormalizedSimplex

/-! ### The normalized boundary of a final multiplication simplex -/

variable
  {f g fg : (Sng (TopCat.of X)).PtSimplex (n + 2)
    (TopCat.toSSetObj₀Equiv.symm x)}

/-- The pointed simplex carried by a face of a final-index multiplication simplex.  The final
three faces are `g`, `fg`, and `f`; every earlier face is constant. -/
def lastMulFace
    (_r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1)))
    (j : Fin (n + 4)) :
    (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x) :=
  if j = (Fin.last (n + 1)).castSucc.castSucc then g
  else if j = (Fin.last (n + 1)).castSucc.succ then fg
  else if j = (Fin.last (n + 1)).succ.succ then f
  else .const

/-- The selected pointed face has the same map as the corresponding face of the multiplication
simplex. -/
theorem lastMulFace_map
    (r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1)))
    (j : Fin (n + 4)) :
    (lastMulFace r j).map = SSet.stdSimplex.δ j ≫ r.map := by
  simp only [lastMulFace]
  split
  next h =>
    subst j
    exact r.δ_castSucc_castSucc_map.symm
  next hfirst =>
    split
    next h =>
      subst j
      exact r.δ_succ_castSucc_map.symm
    next hmiddle =>
      split
      next h =>
        subst j
        exact r.δ_succ_succ_map.symm
      next hlast =>
        have hj : j < (Fin.last (n + 1)).castSucc.castSucc := by grind
        exact (r.δ_map_of_lt j hj).symm

/-- A final-index multiplication simplex and all its pointed faces, packaged as a normalized
simplex boundary. -/
def lastMulBoundary
    (r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1))) :
    NormalizedSimplexBoundary n X x where
  simplex := SSet.yonedaEquiv r.map
  face j := NormalizedSimplex.ofPtSimplex (lastMulFace r j)
  face_simplex j := by
    rw [NormalizedSimplex.ofPtSimplex_simplex, lastMulFace_map]
    exact (yonedaEquiv_comp_δ (X := X) (q := n + 2) j r.map).symm

@[simp]
theorem lastMulBoundary_simplex
    (r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1))) :
    (lastMulBoundary r).simplex = SSet.yonedaEquiv r.map :=
  rfl

@[simp]
theorem lastMulBoundary_face_first
    (r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1))) :
    (lastMulBoundary r).face (Fin.last (n + 1)).castSucc.castSucc =
      NormalizedSimplex.ofPtSimplex g := by
  simp [lastMulBoundary, lastMulFace]

@[simp]
theorem lastMulBoundary_face_middle
    (r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1))) :
    (lastMulBoundary r).face (Fin.last (n + 1)).castSucc.succ =
      NormalizedSimplex.ofPtSimplex fg := by
  have hfirst :
      (Fin.last (n + 1)).castSucc.succ ≠
        (Fin.last (n + 1)).castSucc.castSucc := by grind
  simp [lastMulBoundary, lastMulFace, hfirst]

@[simp]
theorem lastMulBoundary_face_last
    (r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1))) :
    (lastMulBoundary r).face (Fin.last (n + 1)).succ.succ =
      NormalizedSimplex.ofPtSimplex f := by
  have hfirst :
      (Fin.last (n + 2 + 1) : Fin (n + 4)) ≠
        (Fin.last (n + 1)).castSucc.castSucc := by grind
  have hmiddle :
      (Fin.last (n + 2 + 1) : Fin (n + 4)) ≠
        (Fin.last (n + 1)).castSucc.succ := by grind
  simp [lastMulBoundary, lastMulFace, hfirst, hmiddle]

@[simp]
theorem lastMulBoundary_face_penultimate
    (r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1))) :
    (lastMulBoundary r).face (Fin.last (n + 2)).castSucc =
      NormalizedSimplex.ofPtSimplex fg := by
  rw [show (Fin.last (n + 2)).castSucc =
      (Fin.last (n + 1)).castSucc.succ by ext; simp]
  exact lastMulBoundary_face_middle r

@[simp]
theorem lastMulBoundary_face_final
    (r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1))) :
    (lastMulBoundary r).face (Fin.last (n + 3)) =
      NormalizedSimplex.ofPtSimplex f := by
  rw [show Fin.last (n + 3) = (Fin.last (n + 1)).succ.succ by ext; simp]
  exact lastMulBoundary_face_last r

/-- Every face before the final three faces of a final multiplication simplex is the constant
normalized simplex. -/
theorem lastMulBoundary_face_of_lt
    (r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1)))
    (j : Fin (n + 4))
    (hj : j < (Fin.last (n + 1)).castSucc.castSucc) :
    (lastMulBoundary r).face j = NormalizedSimplex.const n x := by
  have hfirst : j ≠ (Fin.last (n + 1)).castSucc.castSucc := ne_of_lt hj
  have hmiddle : j ≠ (Fin.last (n + 1)).castSucc.succ := by grind
  have hlast : j ≠ (Fin.last (n + 2 + 1) : Fin (n + 4)) := by grind
  simp [lastMulBoundary, lastMulFace, hfirst, hmiddle, hlast]

/-- The stick-breaking shell of a final multiplication simplex has constant faces in every
direction before its final two coordinate directions. -/
theorem lastMulBoundary_stickShell_leadingFacesConstant
    (r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1))) :
    (lastMulBoundary r).stickShell.LeadingFacesConstant := by
  intro i
  let k : Fin (n + 3) := i.castSucc.castSucc
  constructor
  · exact (lastMulBoundary r).stickShell_lowerFace_isConstant k (by grind)
  · intro t ht
    let u : I^Fin (n + 2) := Fin.removeNth k t
    have hrep : t = cubeFace k 1 u := by
      change t = k.insertNth 1 u
      rw [← ht]
      exact (Fin.insertNth_self_removeNth k t).symm
    rw [hrep]
    change (lastMulBoundary r).stickCubeMap (cubeFace k 1 u) = x
    rw [(lastMulBoundary r).stickCubeMap_upper_face k]
    have hk : k.castSucc < (Fin.last (n + 1)).castSucc.castSucc := by grind
    rw [lastMulBoundary_face_of_lt r k.castSucc hk,
      NormalizedSimplex.const_stickMap_apply]

/-- A final-index simplicial multiplication simplex realizes multiplication of the associated
stick-breaking cubical homotopy classes. -/
theorem stickHomotopyClass_ofPtSimplex_mul
    (r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1))) :
    Additive.ofMul (NormalizedSimplex.ofPtSimplex fg).stickHomotopyClass =
      Additive.ofMul (NormalizedSimplex.ofPtSimplex f).stickHomotopyClass +
        Additive.ofMul (NormalizedSimplex.ofPtSimplex g).stickHomotopyClass := by
  have hrel := CubicalShell.lastTwoFaceClass_relation
    (m := n + 1) (lastMulBoundary r).stickShell
      (lastMulBoundary_stickShell_leadingFacesConstant r)
  have hmul :
      Additive.ofMul (NormalizedSimplex.ofPtSimplex g).stickHomotopyClass +
          Additive.ofMul (NormalizedSimplex.ofPtSimplex f).stickHomotopyClass =
        Additive.ofMul (NormalizedSimplex.ofPtSimplex fg).stickHomotopyClass := by
    simpa using hrel
  calc
    Additive.ofMul (NormalizedSimplex.ofPtSimplex fg).stickHomotopyClass =
        Additive.ofMul (NormalizedSimplex.ofPtSimplex g).stickHomotopyClass +
          Additive.ofMul (NormalizedSimplex.ofPtSimplex f).stickHomotopyClass := hmul.symm
    _ = Additive.ofMul (NormalizedSimplex.ofPtSimplex f).stickHomotopyClass +
          Additive.ofMul (NormalizedSimplex.ofPtSimplex g).stickHomotopyClass :=
      add_comm _ _

/-- Multiplicative form of `stickHomotopyClass_ofPtSimplex_mul`. -/
theorem stickHomotopyClass_ofPtSimplex_mul'
    (r : SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1))) :
    (NormalizedSimplex.ofPtSimplex fg).stickHomotopyClass =
      (NormalizedSimplex.ofPtSimplex f).stickHomotopyClass *
        (NormalizedSimplex.ofPtSimplex g).stickHomotopyClass := by
  exact congrArg Additive.toMul (stickHomotopyClass_ofPtSimplex_mul r)

/-! ### Constructing the multiplication simplex by Kan filling -/

/-- The horn used to multiply two pointed simplices.  Its face at the first of the final three
indices is `g`, its final face is `f`, and every other prescribed face is constant.  The middle
of the final three indices is omitted. -/
def lastMulHornFace
    (f g : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x))
    (j : Fin (n + 4))
    (_hj : j ≠ (Fin.last (n + 1)).castSucc.succ) :
    Δ[n + 2] ⟶ Sng (TopCat.of X) :=
  if j = (Fin.last (n + 1)).castSucc.castSucc then g.map
  else if j = (Fin.last (n + 1)).succ.succ then f.map
  else SSet.const (TopCat.toSSetObj₀Equiv.symm x)

/-- Every codimension-one face of every prescribed horn face is constant. -/
theorem δ_lastMulHornFace
    (f g : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x))
    (j : Fin (n + 4))
    (hj : j ≠ (Fin.last (n + 1)).castSucc.succ)
    (a : Fin (n + 3)) :
    SSet.stdSimplex.δ a ≫ lastMulHornFace f g j hj =
      SSet.const (TopCat.toSSetObj₀Equiv.symm x) := by
  simp only [lastMulHornFace]
  split
  next h =>
    subst j
    exact g.δ_map a
  next hfirst =>
    split
    next h =>
      subst j
      exact f.δ_map a
    next hlast =>
      simp

/-- The faces prescribed for the multiplication horn agree on every intersection. -/
theorem lastMulHornFace_compatible
    (f g : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x)) :
    SSet.horn.IsCompatible (lastMulHornFace f g) := by
  rw [SSet.horn.isCompatible_iff]
  intro j k hj hk hjk
  rw [δ_lastMulHornFace, δ_lastMulHornFace]

/-- The Kan filler of the multiplication horn in the singular simplicial set. -/
def lastMulFiller
    (f g : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x)) :
    Δ[n + 3] ⟶ Sng (TopCat.of X) :=
  (lastMulHornFace_compatible f g).liftOfKanComplex

/-- The Kan filler recovers every prescribed face of the multiplication horn. -/
@[reassoc]
theorem δ_lastMulFiller
    (f g : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x))
    (j : Fin (n + 4))
    (hj : j ≠ (Fin.last (n + 1)).castSucc.succ) :
    SSet.stdSimplex.δ j ≫ lastMulFiller f g = lastMulHornFace f g j hj :=
  (lastMulHornFace_compatible f g).δ_liftOfKanComplex j hj

/-- The missing face of the multiplication horn, with its induced pointed-simplex structure. -/
def lastMulProduct
    (f g : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x)) :
    (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x) where
  map := SSet.stdSimplex.δ (Fin.last (n + 1)).castSucc.succ ≫ lastMulFiller f g
  comm := by
    apply SSet.boundary.hom_ext
    intro a
    trans SSet.const (TopCat.toSSetObj₀Equiv.symm x)
    · rw [← Category.assoc, SSet.boundary.ι_ι]
      by_cases ha : a = Fin.last (n + 2)
      · subst a
        rw [show (Fin.last (n + 1)).castSucc.succ =
            (Fin.last (n + 2)).castSucc by ext; simp]
        rw [← Category.assoc, SSet.stdSimplex.δ_comp_δ_self, Category.assoc]
        have hfinal :
            (Fin.last (n + 2)).succ ≠ (Fin.last (n + 1)).castSucc.succ := by grind
        rw [δ_lastMulFiller f g (Fin.last (n + 2)).succ hfinal]
        exact δ_lastMulHornFace f g (Fin.last (n + 2)).succ hfinal
          (Fin.last (n + 2))
      · let q : Fin (n + 3) := (Fin.last (n + 1)).castSucc
        have haq : a ≤ q := by grind
        have hprescribed :
            a.castSucc ≠ (Fin.last (n + 1)).castSucc.succ := by grind
        rw [show (Fin.last (n + 1)).castSucc.succ = q.succ by rfl]
        rw [← Category.assoc, SSet.stdSimplex.δ_comp_δ haq, Category.assoc,
          δ_lastMulFiller f g a.castSucc hprescribed]
        exact δ_lastMulHornFace f g a.castSucc hprescribed q
    · simp

@[simp]
theorem lastMulProduct_map
    (f g : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x)) :
    (lastMulProduct f g).map =
      SSet.stdSimplex.δ (Fin.last (n + 1)).castSucc.succ ≫ lastMulFiller f g :=
  rfl

/-- The Kan filler, together with its missing face, is a final-index multiplication
simplex. -/
def lastMulStruct
    (f g : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x)) :
    SSet.PtSimplex.MulStruct f g (lastMulProduct f g) (Fin.last (n + 1)) where
  map := lastMulFiller f g
  δ_castSucc_castSucc_map := by
    have hmissing :
        (Fin.last (n + 1)).castSucc.castSucc ≠
          (Fin.last (n + 1)).castSucc.succ := by grind
    rw [δ_lastMulFiller f g (Fin.last (n + 1)).castSucc.castSucc hmissing]
    simp [lastMulHornFace]
  δ_succ_castSucc_map := rfl
  δ_succ_succ_map := by
    have hmissing :
        (Fin.last (n + 1)).succ.succ ≠
          (Fin.last (n + 1)).castSucc.succ := by grind
    rw [δ_lastMulFiller f g (Fin.last (n + 1)).succ.succ hmissing]
    have hfirst :
        (Fin.last (n + 2 + 1) : Fin (n + 4)) ≠
          (Fin.last (n + 1)).castSucc.castSucc := by grind
    simp [lastMulHornFace, hfirst]
  δ_map_of_lt j hj := by
    have hmissing : j ≠ (Fin.last (n + 1)).castSucc.succ := by grind
    rw [δ_lastMulFiller f g j hmissing]
    have hfirst : j ≠ (Fin.last (n + 1)).castSucc.castSucc := ne_of_lt hj
    have hlast : j ≠ (Fin.last (n + 2 + 1) : Fin (n + 4)) := by grind
    simp [lastMulHornFace, hfirst, hlast]
  δ_map_of_gt j hj := by grind

/-- Any two pointed singular simplices have a final-index multiplication simplex. -/
theorem exists_lastMulStruct
    (f g : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x)) :
    ∃ fg, Nonempty (SSet.PtSimplex.MulStruct f g fg (Fin.last (n + 1))) :=
  ⟨lastMulProduct f g, ⟨lastMulStruct f g⟩⟩

/-- The missing face selected by the singular Kan filler realizes ordinary multiplication in
the maintained cubical homotopy group. -/
theorem stickHomotopyClass_lastMulProduct
    (f g : (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x)) :
    (NormalizedSimplex.ofPtSimplex (lastMulProduct f g)).stickHomotopyClass =
      (NormalizedSimplex.ofPtSimplex f).stickHomotopyClass *
        (NormalizedSimplex.ofPtSimplex g).stickHomotopyClass :=
  stickHomotopyClass_ofPtSimplex_mul' (lastMulStruct f g)

end Submission
