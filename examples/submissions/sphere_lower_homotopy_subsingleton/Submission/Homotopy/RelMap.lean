/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ForMathlib.HomotopyGroup.Map
import Submission.Homotopy.RelGroup

/-!
# Functoriality of relative homotopy groups

This file supplies the functoriality layer needed to state homotopy excision. A based map of
pairs sends relative generalized loops to relative generalized loops, respects relative
homotopy and concatenation, and hence induces a monoid homomorphism on every relative homotopy
group of degree at least two.

The induced maps commute with the inclusion, quotient, and boundary homomorphisms in the long
exact sequence of a pair. These naturality squares are the algebraic interface needed to compare
a future Blakers--Massey excision map with the concrete reduced-suspension homomorphism.
-/

open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

universe u v w

/-- A continuous map of pairs carrying a chosen basepoint to a chosen basepoint. -/
structure BasedPairMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (a : A) (b : B) where
  /-- The underlying continuous map of ambient spaces. -/
  toContinuousMap : C(X, Y)
  /-- The underlying map carries the distinguished subspace into the target subspace. -/
  mapsTo' : Set.MapsTo toContinuousMap A B
  /-- The chosen basepoint is preserved. -/
  map_basepoint' : toContinuousMap a = b

namespace BasedPairMap

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {A : Set X} {B : Set Y} {C : Set Z} {a : A} {b : B} {c : C}

/-- Based maps of pairs are determined by their underlying continuous maps. -/
@[ext]
theorem ext {f g : BasedPairMap A B a b}
    (h : f.toContinuousMap = g.toContinuousMap) : f = g := by
  cases f
  cases g
  simp_all

/-- The map induced between the distinguished subspaces. -/
def subspaceMap (f : BasedPairMap A B a b) : C(A, B) where
  toFun x := ⟨f.toContinuousMap x, f.mapsTo' x.property⟩
  continuous_toFun := Continuous.subtype_mk
    (f.toContinuousMap.continuous.comp continuous_subtype_val) _

@[simp]
theorem subspaceMap_apply (f : BasedPairMap A B a b) (x : A) :
    f.subspaceMap x = ⟨f.toContinuousMap x, f.mapsTo' x.property⟩ :=
  rfl

@[simp]
theorem subspaceMap_basepoint (f : BasedPairMap A B a b) : f.subspaceMap a = b :=
  by
    apply Subtype.ext
    exact f.map_basepoint'

/-- The identity based map of a pair. -/
def id : BasedPairMap A A a a where
  toContinuousMap := ContinuousMap.id X
  mapsTo' := fun _ hx => hx
  map_basepoint' := rfl

/-- Composition of based maps of pairs. -/
def comp (g : BasedPairMap B C b c) (f : BasedPairMap A B a b) : BasedPairMap A C a c where
  toContinuousMap := g.toContinuousMap.comp f.toContinuousMap
  mapsTo' := fun _ hx => g.mapsTo' (f.mapsTo' hx)
  map_basepoint' := by
    rw [ContinuousMap.comp_apply, f.map_basepoint', g.map_basepoint']

@[simp]
theorem comp_toContinuousMap (g : BasedPairMap B C b c) (f : BasedPairMap A B a b) :
    (g.comp f).toContinuousMap = g.toContinuousMap.comp f.toContinuousMap :=
  rfl

end BasedPairMap

namespace RelGenLoop

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {A : Set X} {B : Set Y} {C : Set Z} {a : A} {b : B} {c : C} {n : ℕ}

/-- Postcomposition of a relative generalized loop by a based map of pairs. -/
def map (f : BasedPairMap A B a b) (p : RelGenLoop n X A a) : RelGenLoop n Y B b :=
  ⟨f.toContinuousMap.comp p.val,
    fun y hy => f.mapsTo' (p.property.1 y hy),
    fun y hy => by
      rw [ContinuousMap.comp_apply, p.property.2 y hy, f.map_basepoint']⟩

@[simp]
theorem map_apply (f : BasedPairMap A B a b) (p : RelGenLoop n X A a) (y : I^Fin n) :
    (map f p).val y = f.toContinuousMap (p.val y) :=
  rfl

@[simp]
theorem map_const (f : BasedPairMap A B a b) :
    map f (RelGenLoop.const : RelGenLoop n X A a) =
      (RelGenLoop.const : RelGenLoop n Y B b) := by
  refine Subtype.ext (ContinuousMap.ext fun _ => ?_)
  exact f.map_basepoint'

/-- Postcomposition by a based pair map preserves relative homotopy. -/
theorem map_homotopic {p q : RelGenLoop n X A a} (H : RelGenLoop.Homotopic p q)
    (f : BasedPairMap A B a b) :
    RelGenLoop.Homotopic (map f p) (map f q) := by
  obtain ⟨H⟩ := H
  refine ⟨⟨⟨fun sy => f.toContinuousMap (H (sy.1, sy.2)),
      f.toContinuousMap.continuous.comp H.continuous⟩, ?_, ?_⟩, ?_⟩
  · intro y
    exact congrArg f.toContinuousMap (H.map_zero_left y)
  · intro y
    exact congrArg f.toContinuousMap (H.map_one_left y)
  · intro s
    constructor
    · intro y hy
      exact f.mapsTo' ((H.prop s).1 y hy)
    · intro y hy
      change f.toContinuousMap ((H.curry s) y) = (b : Y)
      rw [(H.prop s).2 y hy, f.map_basepoint']

@[simp]
theorem map_id (p : RelGenLoop n X A a) : map BasedPairMap.id p = p := by
  refine Subtype.ext (ContinuousMap.ext fun _ => ?_)
  rfl

@[simp]
theorem map_comp (g : BasedPairMap B C b c) (f : BasedPairMap A B a b)
    (p : RelGenLoop n X A a) :
    map g (map f p) = map (g.comp f) p := by
  refine Subtype.ext (ContinuousMap.ext fun _ => ?_)
  rfl

@[simp]
theorem map_transAt (f : BasedPairMap A B a b) (i : Fin n)
    (p q : RelGenLoop (n + 1) X A a) :
    map f (RelGenLoop.transAt i p q) =
      RelGenLoop.transAt i (map f p) (map f q) := by
  refine Subtype.ext (ContinuousMap.ext fun y => ?_)
  simp only [map_apply, RelGenLoop.transAt_apply]
  split_ifs <;> rfl

@[simp]
theorem map_symmAt (f : BasedPairMap A B a b) (i : Fin n)
    (p : RelGenLoop (n + 1) X A a) :
    map f (RelGenLoop.symmAt i p) = RelGenLoop.symmAt i (map f p) := by
  refine Subtype.ext (ContinuousMap.ext fun y => ?_)
  simp only [map_apply, RelGenLoop.symmAt_apply]

end RelGenLoop

namespace RelHomotopyGroup

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {A : Set X} {B : Set Y} {C : Set Z} {a : A} {b : B} {c : C} {n : ℕ}

/-- The map on relative homotopy classes induced by a based map of pairs. -/
def map (f : BasedPairMap A B a b) : π_rel n X A a → π_rel n Y B b :=
  Quotient.map (RelGenLoop.map f) fun _ _ H => RelGenLoop.map_homotopic H f

@[simp]
theorem map_mk (f : BasedPairMap A B a b) (p : RelGenLoop n X A a) :
    map f (⟦p⟧ : π_rel n X A a) = ⟦RelGenLoop.map f p⟧ :=
  rfl

@[simp]
theorem map_id_apply (x : π_rel n X A a) : map BasedPairMap.id x = x := by
  refine Quotient.inductionOn x ?_
  intro p
  rw [map_mk, RelGenLoop.map_id]

@[simp]
theorem map_comp_apply (g : BasedPairMap B C b c) (f : BasedPairMap A B a b)
    (x : π_rel n X A a) :
    map g (map f x) = map (g.comp f) x := by
  refine Quotient.inductionOn x ?_
  intro p
  rw [map_mk, map_mk, map_mk, RelGenLoop.map_comp]

/-- In degree at least two, a based map of pairs induces a monoid homomorphism on relative
homotopy groups. -/
def mapHom (n : ℕ) (f : BasedPairMap A B a b) :
    π_rel (n + 2) X A a →* π_rel (n + 2) Y B b where
  toFun := map f
  map_one' := by
    rw [RelHomotopyGroup.one_def, map_mk, RelGenLoop.map_const]
    exact RelHomotopyGroup.one_def.symm
  map_mul' x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    simp only [RelHomotopyGroup.mul_spec (k := (0 : Fin (n + 1))), map_mk,
      RelGenLoop.map_transAt]

@[simp]
theorem mapHom_apply (f : BasedPairMap A B a b) (x : π_rel (n + 2) X A a) :
    mapHom n f x = map f x :=
  rfl

@[simp]
theorem mapHom_id :
    mapHom n (BasedPairMap.id : BasedPairMap A A a a) =
      MonoidHom.id (π_rel (n + 2) X A a) :=
  MonoidHom.ext map_id_apply

@[simp]
theorem mapHom_comp (g : BasedPairMap B C b c) (f : BasedPairMap A B a b) :
    (mapHom n g).comp (mapHom n f) = mapHom n (g.comp f) :=
  MonoidHom.ext fun x => map_comp_apply g f x

/-! ### Naturality of the long exact sequence -/

/-- Postcomposition commutes with viewing an absolute loop as a relative loop. -/
theorem map_jStarGen (f : BasedPairMap A B a b) (p : Ω^ (Fin n) X (a : X)) :
    RelGenLoop.map f (RelHomotopyGroup.jStarGen (A := A) p) =
      RelHomotopyGroup.jStarGen (A := B)
        (GenLoop.map f.toContinuousMap f.map_basepoint' p) := by
  refine Subtype.ext (ContinuousMap.ext fun _ => ?_)
  rfl

/-- Postcomposition commutes with restricting a relative loop to its top face. -/
theorem bdGen_map (f : BasedPairMap A B a b) (p : RelGenLoop (n + 1) X A a) :
    RelHomotopyGroup.bdGen (RelGenLoop.map f p) =
      GenLoop.map f.subspaceMap f.subspaceMap_basepoint
        (RelHomotopyGroup.bdGen p) := by
  refine GenLoop.ext _ _ fun y => Subtype.ext ?_
  change f.toContinuousMap (p.val (Cube.inclToTop y)) =
    f.toContinuousMap (p.val (Cube.inclToTop y))
  rfl

/-- Postcomposition commutes with inclusion of a loop in the distinguished subspace. -/
theorem map_iStarGen (f : BasedPairMap A B a b) (p : Ω^ (Fin n) A a) :
    GenLoop.map f.toContinuousMap f.map_basepoint'
        (RelHomotopyGroup.iStarGen (X := X) p) =
      RelHomotopyGroup.iStarGen (X := Y)
        (GenLoop.map f.subspaceMap f.subspaceMap_basepoint p) := by
  refine GenLoop.ext _ _ fun _ => ?_
  change f.toContinuousMap _ = f.toContinuousMap _
  rfl

/-- Naturality of `j_*` for a based map of pairs. -/
theorem map_jStar (f : BasedPairMap A B a b) (x : π_ n X (a : X)) :
    map f (RelHomotopyGroup.jStar n X A a x) =
      RelHomotopyGroup.jStar n Y B b
        (HomotopyGroup.map f.toContinuousMap f.map_basepoint' x) := by
  refine Quotient.inductionOn x ?_
  intro p
  rw [RelHomotopyGroup.jStar_mk, HomotopyGroup.map_mk,
    RelHomotopyGroup.jStar_mk, map_mk, map_jStarGen]

/-- Naturality of the boundary map for a based map of pairs. -/
theorem bd_map (f : BasedPairMap A B a b) (x : π_rel (n + 1) X A a) :
    RelHomotopyGroup.bd n Y B b (map f x) =
      HomotopyGroup.map f.subspaceMap f.subspaceMap_basepoint
        (RelHomotopyGroup.bd n X A a x) := by
  refine Quotient.inductionOn x ?_
  intro p
  rw [map_mk, RelHomotopyGroup.bd_mk, RelHomotopyGroup.bd_mk,
    HomotopyGroup.map_mk, bdGen_map]

/-- Naturality of `i_*` for a based map of pairs. -/
theorem map_iStar (f : BasedPairMap A B a b) (x : π_ n A a) :
    HomotopyGroup.map f.toContinuousMap f.map_basepoint'
        (RelHomotopyGroup.iStar n X A a x) =
      RelHomotopyGroup.iStar n Y B b
        (HomotopyGroup.map f.subspaceMap f.subspaceMap_basepoint x) := by
  refine Quotient.inductionOn x ?_
  intro p
  change (⟦GenLoop.map f.toContinuousMap f.map_basepoint'
      (RelHomotopyGroup.iStarGen p)⟧ : π_ n Y (b : Y)) =
    (⟦RelHomotopyGroup.iStarGen
      (GenLoop.map f.subspaceMap f.subspaceMap_basepoint p)⟧ : π_ n Y (b : Y))
  exact congrArg (fun q => (⟦q⟧ : π_ n Y (b : Y))) (map_iStarGen f p)

/-- The `j_*` square in the relative long exact sequence commutes as a square of monoid
homomorphisms. -/
theorem mapHom_comp_jStarHom (n : ℕ) (f : BasedPairMap A B a b) :
    (mapHom n f).comp (RelHomotopyGroup.jStarHom n X A a) =
      (RelHomotopyGroup.jStarHom n Y B b).comp
        (HomotopyGroup.mapHom f.toContinuousMap f.map_basepoint') :=
  MonoidHom.ext fun x => map_jStar f x

/-- The boundary square in the relative long exact sequence commutes as a square of monoid
homomorphisms. -/
theorem bdHom_comp_mapHom (n : ℕ) (f : BasedPairMap A B a b) :
    (RelHomotopyGroup.bdHom n Y B b).comp (mapHom n f) =
      (HomotopyGroup.mapHom f.subspaceMap f.subspaceMap_basepoint).comp
        (RelHomotopyGroup.bdHom n X A a) :=
  MonoidHom.ext fun x => bd_map f x

/-- A map of pairs induces a bijection on relative homotopy whenever the two boundary maps
and the induced map on the distinguished subspaces are bijective.  This is cancellation in
the natural boundary square. -/
theorem mapHom_bijective_of_bdHom_bijective (n : ℕ) (f : BasedPairMap A B a b)
    (hsource : Function.Bijective (RelHomotopyGroup.bdHom n X A a))
    (htarget : Function.Bijective (RelHomotopyGroup.bdHom n Y B b))
    (hsubspace : Function.Bijective
      (HomotopyGroup.mapHom f.subspaceMap f.subspaceMap_basepoint :
        π_ (n + 1) A a →* π_ (n + 1) B b)) :
    Function.Bijective (mapHom n f) := by
  apply (Function.Bijective.of_comp_iff' htarget (mapHom n f)).mp
  rw [show (RelHomotopyGroup.bdHom n Y B b :
      π_rel (n + 2) Y B b → π_ (n + 1) B b) ∘ mapHom n f =
        (HomotopyGroup.mapHom f.subspaceMap f.subspaceMap_basepoint :
          π_ (n + 1) A a → π_ (n + 1) B b) ∘
            RelHomotopyGroup.bdHom n X A a by
    funext x
    exact DFunLike.congr_fun (bdHom_comp_mapHom n f) x]
  exact hsubspace.comp hsource

/-- The `i_*` square in the relative long exact sequence commutes as a square of monoid
homomorphisms. -/
theorem mapHom_comp_iStarHom (n : ℕ) (f : BasedPairMap A B a b) :
    (HomotopyGroup.mapHom f.toContinuousMap f.map_basepoint').comp
        (RelHomotopyGroup.iStarHom n X A a) =
      (RelHomotopyGroup.iStarHom n Y B b).comp
        (HomotopyGroup.mapHom f.subspaceMap f.subspaceMap_basepoint) :=
  MonoidHom.ext fun x => map_iStar f x

end RelHomotopyGroup

end Submission
