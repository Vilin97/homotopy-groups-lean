/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia

Vendored from https://github.com/jzxia/WhiteheadTheorem (Apache 2.0) via Vilin97/lean-pool.
-/

import Submission.WhiteheadTheorem.Auxiliary
import Submission.WhiteheadTheorem.Compressible.CWComplex
import Submission.WhiteheadTheorem.Compressible.Defs
import Submission.WhiteheadTheorem.Compressible.Disk
import Submission.WhiteheadTheorem.Compressible.WeakEquiv
import Submission.WhiteheadTheorem.CWComplex.Basic
import Submission.WhiteheadTheorem.CWComplex.IProd.Def
import Submission.WhiteheadTheorem.CWComplex.IProd.Iso
import Submission.WhiteheadTheorem.Defs
import Submission.WhiteheadTheorem.Exponential
import Submission.WhiteheadTheorem.HEP.Cofibration
import Submission.WhiteheadTheorem.HEP.Cube
import Submission.WhiteheadTheorem.HEP.CubeJar
import Submission.WhiteheadTheorem.HEP.Retract
import Submission.WhiteheadTheorem.HomotopyGroup.ChangeBasePt
import Submission.WhiteheadTheorem.HomotopyGroup.InducedMaps
import Submission.WhiteheadTheorem.RelHomotopyGroup.Algebra
import Submission.WhiteheadTheorem.RelHomotopyGroup.Compression
import Submission.WhiteheadTheorem.RelHomotopyGroup.Defs
import Submission.WhiteheadTheorem.RelHomotopyGroup.LongExactSeq
import Submission.WhiteheadTheorem.Shapes.Cube
import Submission.WhiteheadTheorem.Shapes.CubeBoundaryMap
import Submission.WhiteheadTheorem.Shapes.Disk
import Submission.WhiteheadTheorem.Shapes.DiskHomeoCube
import Submission.WhiteheadTheorem.Shapes.Jar
import Submission.WhiteheadTheorem.Shapes.MappingCylinder
import Submission.WhiteheadTheorem.Shapes.Maps
import Submission.WhiteheadTheorem.Shapes.Pushout
import Submission.WhiteheadTheorem.Shapes.UnitInterval

/-!
# Submission.WhiteheadTheorem.Basic

Imported Lean Pool material for `Submission.WhiteheadTheorem.Basic`.
-/


open CategoryTheory

universe u

theorem WhiteheadTheorem (X Y : CWComplex.{u}) (f : (X : TopCat.{u}) ⟶ Y) :
    IsWeakHomotopyEquiv f.hom → IsHomotopyEquiv f.hom := by
  intro hf
  obtain ⟨g, hgf⟩ := hf.CWComplex_induced_map_surjective Y (𝟙 _)
  have hfgf : (f ≫ g ≫ f).hom.Homotopic f.hom :=
    hgf.comp (ContinuousMap.Homotopic.refl f.hom)
  use
    { toFun := f.hom
      invFun := g.hom
      left_inv := hf.CWComplex_induced_map_injective X (f ≫ g) (𝟙 _) hfgf
      right_inv := hgf }
