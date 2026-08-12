/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia

Vendored from https://github.com/jzxia/WhiteheadTheorem (Apache 2.0) via Vilin97/lean-pool.
-/

import Submission.WhiteheadTheorem.Auxiliary
import Submission.WhiteheadTheorem.Basic
import Submission.WhiteheadTheorem.CWComplex.Basic
import Submission.WhiteheadTheorem.CWComplex.IProd.Def
import Submission.WhiteheadTheorem.CWComplex.IProd.Iso
import Submission.WhiteheadTheorem.Compressible.CWComplex
import Submission.WhiteheadTheorem.Compressible.Defs
import Submission.WhiteheadTheorem.Compressible.Disk
import Submission.WhiteheadTheorem.Compressible.WeakEquiv
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
# Whitehead's theorem (vendored library)

This module gathers the whole vendored `WhiteheadTheorem` development, which supplies:

* relative homotopy groups `π_rel n X A a` together with their group structure, the maps
  `iStar`, `jStar`, `bd`, and the long exact sequence of a pair;
* functoriality and the change-of-basepoint isomorphism for absolute homotopy groups;
* the homotopy extension property for the cube pair and for CW pairs, and cofibrations;
* the compression lemma and Whitehead's theorem for CW complexes.

The material is vendored verbatim (up to import renaming and the small adaptations noted in the
individual files) from `https://github.com/jzxia/WhiteheadTheorem`, Apache 2.0, © Jiazhen Xia,
by way of `Vilin97/lean-pool`.
-/
