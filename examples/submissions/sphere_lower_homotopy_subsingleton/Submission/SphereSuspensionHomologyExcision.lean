/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.Excision
import Submission.Homology.Sphere
import Submission.SphereSuspensionExcision

/-!
# Relative homology of the sphere suspension cover

The same based cap-inclusion map used by homotopy excision induces a canonical map on relative
singular homology.  Both its source and target in the top relative degree are computed here as
`ℤ`: the source by the boundary map for the contractible lower cap, and the target by the
absolute-to-relative map for the contractible upper cap.  These are the homological comparison
objects needed by a relative Hurewicz or Blakers--Massey argument.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

/-- Reassociation identifies the nested overlap subtype used by relative homotopy with the
ordinary intersection subtype used by Mayer--Vietoris and homological excision. -/
noncomputable def sphCapOverlapToBeltHom (m : ℕ) :
    TopCat.of (sphCapOverlapInLower m) ⟶
      TopCat.of ↑(sphLowerCap m ∩ sphUpperCap m) :=
  (TopCat.isoOfHomeo (sphCapOverlapHomeoBelt m)).hom

/-- Reassociation commutes with inclusion into the lower cap. -/
theorem sphCapOverlapToBelt_subIncl (m : ℕ) :
    subIncl (Y := TopCat.of (sphLowerCap m)) (sphCapOverlapInLower m) ≫
        𝟙 (TopCat.of (sphLowerCap m)) =
      sphCapOverlapToBeltHom m ≫
        mvInclLeft (X := TopCat.of (Sph (m + 1))) (sphLowerCap m) (sphUpperCap m) := by
  ext z
  rfl

/-- The relative homology map induced by reassociating the overlap subtype. -/
noncomputable def sphCapOverlapReassocHrelMap (m k : ℕ) :
    HrelSet (Y := TopCat.of (sphLowerCap m)) k (sphCapOverlapInLower m) ⟶
      Hrel k (mvInclLeft (X := TopCat.of (Sph (m + 1)))
        (sphLowerCap m) (sphUpperCap m)) :=
  HrelMap k
    (subIncl (Y := TopCat.of (sphLowerCap m)) (sphCapOverlapInLower m))
    (mvInclLeft (X := TopCat.of (Sph (m + 1))) (sphLowerCap m) (sphUpperCap m))
    (sphCapOverlapToBelt_subIncl m)

/-- Reassociation of the overlap subtype induces an isomorphism on relative homology. -/
theorem isIso_sphCapOverlapReassocHrelMap (m k : ℕ) :
    IsIso (sphCapOverlapReassocHrelMap m k) := by
  letI : IsIso (sphCapOverlapToBeltHom m) := by
    unfold sphCapOverlapToBeltHom
    infer_instance
  exact @isIso_HrelMap_of_isIso
    (TopCat.of (sphCapOverlapInLower m)) (TopCat.of (sphLowerCap m))
    (TopCat.of ↑(sphLowerCap m ∩ sphUpperCap m)) (TopCat.of (sphLowerCap m)) k
    (subIncl (Y := TopCat.of (sphLowerCap m)) (sphCapOverlapInLower m)) inferInstance
    (mvInclLeft (X := TopCat.of (Sph (m + 1))) (sphLowerCap m) (sphUpperCap m)) inferInstance
    (sphCapOverlapToBeltHom m) (𝟙 (TopCat.of (sphLowerCap m))) inferInstance inferInstance
    (sphCapOverlapToBelt_subIncl m)

/-- The standard relative-homology excision map for the two enlarged sphere caps. -/
noncomputable def sphereCapStandardExcisionHrelMap (m k : ℕ) :
    Hrel k (mvInclLeft (X := TopCat.of (Sph (m + 1)))
      (sphLowerCap m) (sphUpperCap m)) ⟶
      HrelSet (Y := TopCat.of (Sph (m + 1))) k (sphUpperCap m) :=
  mvExcisionHrelMap (X := TopCat.of (Sph (m + 1)))
    (sphLowerCap m) (sphUpperCap m) k

/-- Homological excision makes the standard relative sphere-cap map an isomorphism in every
degree. -/
theorem isIso_sphereCapStandardExcisionHrelMap (m k : ℕ) :
    IsIso (sphereCapStandardExcisionHrelMap m k) := by
  exact isIso_mvExcisionHrelMap (X := TopCat.of (Sph (m + 1)))
    (sphLowerCap m) (sphUpperCap m) (sphCap_interior_union m) k

/-- The relative singular-homology map induced by the canonical lower-cap inclusion. -/
noncomputable def sphereCapInclusionHrelMap (m k : ℕ) :
    HrelSet (Y := TopCat.of (sphLowerCap m)) k (sphCapOverlapInLower m) ⟶
      HrelSet (Y := TopCat.of (Sph (m + 1))) k (sphUpperCap m) :=
  BasedPairMap.hrelMap k (sphCapInclusionPairMap m)

/-- The reassociation map followed by standard homological excision is the relative-homology
map induced by the canonical based sphere-cap inclusion. -/
theorem sphCapOverlapReassocHrelMap_comp_sphereCapStandardExcision (m k : ℕ) :
    sphCapOverlapReassocHrelMap m k ≫ sphereCapStandardExcisionHrelMap m k =
      sphereCapInclusionHrelMap m k := by
  have hsub : sphCapOverlapToBeltHom m ≫
        mvInclRight (X := TopCat.of (Sph (m + 1))) (sphLowerCap m) (sphUpperCap m) =
      (sphCapInclusionPairMap m).subspaceHom := by
    ext z
    rfl
  have hamb : 𝟙 (TopCat.of (sphLowerCap m)) ≫
        subIncl (Y := TopCat.of (Sph (m + 1))) (sphLowerCap m) =
      (sphCapInclusionPairMap m).ambientHom := by
    ext z
    rfl
  unfold sphCapOverlapReassocHrelMap sphereCapStandardExcisionHrelMap
    mvExcisionHrelMap sphereCapInclusionHrelMap BasedPairMap.hrelMap
  rw [HrelMap_comp]
  change HrelMap k
      (subIncl (Y := TopCat.of (sphLowerCap m)) (sphCapOverlapInLower m))
      (subIncl (Y := TopCat.of (Sph (m + 1))) (sphUpperCap m))
      (fA := sphCapOverlapToBeltHom m ≫
        mvInclRight (X := TopCat.of (Sph (m + 1))) (sphLowerCap m) (sphUpperCap m))
      (f := 𝟙 (TopCat.of (sphLowerCap m)) ≫
        subIncl (Y := TopCat.of (Sph (m + 1))) (sphLowerCap m)) _ =
    HrelMap k
      (subIncl (Y := TopCat.of (sphLowerCap m)) (sphCapOverlapInLower m))
      (subIncl (Y := TopCat.of (Sph (m + 1))) (sphUpperCap m))
      (fA := (sphCapInclusionPairMap m).subspaceHom)
      (f := (sphCapInclusionPairMap m).ambientHom) _
  simp only [hsub, hamb]

/-- The canonical sphere-cap inclusion is an isomorphism on relative singular homology in every
degree. -/
theorem isIso_sphereCapInclusionHrelMap (m k : ℕ) :
    IsIso (sphereCapInclusionHrelMap m k) := by
  letI := isIso_sphCapOverlapReassocHrelMap m k
  letI := isIso_sphereCapStandardExcisionHrelMap m k
  rw [← sphCapOverlapReassocHrelMap_comp_sphereCapStandardExcision]
  infer_instance

/-- The standard sphere-cap excision map in the top degree used by suspension excision. -/
noncomputable def sphereSuspensionStandardExcisionHrelMap (n : ℕ) :=
  sphereCapStandardExcisionHrelMap (n + 1) (n + 2)

/-- The top-degree standard sphere-cap excision map is an isomorphism. -/
theorem isIso_sphereSuspensionStandardExcisionHrelMap (n : ℕ) :
    IsIso (sphereSuspensionStandardExcisionHrelMap n) :=
  isIso_sphereCapStandardExcisionHrelMap (n + 1) (n + 2)

/-- The canonical lower-cap inclusion on relative homology in the top suspension degree. -/
noncomputable def sphereSuspensionExcisionHrelMap (n : ℕ) :=
  sphereCapInclusionHrelMap (n + 1) (n + 2)

/-- The top-degree reassociation/excision factorization of the canonical map. -/
theorem sphCapOverlapReassocHrelMap_comp_standardExcision (n : ℕ) :
    sphCapOverlapReassocHrelMap (n + 1) (n + 2) ≫
        sphereSuspensionStandardExcisionHrelMap n =
      sphereSuspensionExcisionHrelMap n :=
  sphCapOverlapReassocHrelMap_comp_sphereCapStandardExcision (n + 1) (n + 2)

/-- The canonical sphere-cap inclusion is an isomorphism on relative singular homology in the
top degree used by suspension excision. -/
theorem isIso_sphereSuspensionExcisionHrelMap (n : ℕ) :
    IsIso (sphereSuspensionExcisionHrelMap n) :=
  isIso_sphereCapInclusionHrelMap (n + 1) (n + 2)

/-- For the contractible lower cap, the relative boundary map in top degree is an isomorphism. -/
noncomputable def sphLowerCapRelativeBoundaryIso (n : ℕ) :
    HrelSet (Y := TopCat.of (sphLowerCap (n + 1))) (n + 2)
        (sphCapOverlapInLower (n + 1)) ≅
      Hgrp (n + 1) (TopCat.of (sphCapOverlapInLower (n + 1))) := by
  let i := subIncl (Y := TopCat.of (sphLowerCap (n + 1)))
    (sphCapOverlapInLower (n + 1))
  letI : IsIso (relδ (n + 1) i) :=
    isIso_relδ i (n + 1)
      (isZero_Hgrp_of_contractible (X := TopCat.of (sphLowerCap (n + 1))) (n + 1))
      (isZero_Hgrp_of_contractible (X := TopCat.of (sphLowerCap (n + 1))) n)
  exact asIso (relδ (n + 1) i)

/-- The top relative homology of the lower-cap/overlap pair is `ℤ`. -/
noncomputable def sphLowerCapRelativeTopHomologyIsoInt (n : ℕ) :
    HrelSet (Y := TopCat.of (sphLowerCap (n + 1))) (n + 2)
        (sphCapOverlapInLower (n + 1)) ≅ AddCommGrpCat.of ℤ :=
  sphLowerCapRelativeBoundaryIso n ≪≫
    hgrpIsoOfCMHomotopyEquiv (sphCapOverlapHomotopyEquiv (n + 1)) (n + 1) ≪≫
      hgrpSphereSelfIsoZ n

/-- For the contractible upper cap, the absolute-to-relative map in top degree is an
isomorphism. -/
noncomputable def sphSphereUpperCapRelativeIso (n : ℕ) :
    Hgrp (n + 2) (TopCat.of (Sph (n + 2))) ≅
      HrelSet (Y := TopCat.of (Sph (n + 2))) (n + 2) (sphUpperCap (n + 1)) := by
  let i := subIncl (Y := TopCat.of (Sph (n + 2))) (sphUpperCap (n + 1))
  have htop : IsZero (Hgrp (n + 2) (TopCat.of (sphUpperCap (n + 1)))) :=
    isZero_Hgrp_of_contractible (X := TopCat.of (sphUpperCap (n + 1))) (n + 1)
  have hprev : IsZero (Hgrp (n + 1) (TopCat.of (sphUpperCap (n + 1)))) :=
    isZero_Hgrp_of_contractible (X := TopCat.of (sphUpperCap (n + 1))) n
  have hz : relIota (n + 2) i = 0 := htop.eq_zero_of_src _
  letI : Mono (relIota (n + 1) i) := hprev.mono _
  letI : IsIso (relJ (n + 2) i) := isIso_relJ i (n + 1) hz inferInstance
  exact asIso (relJ (n + 2) i)

/-- The top relative homology of the sphere/upper-cap pair is `ℤ`. -/
noncomputable def sphSphereUpperCapRelativeTopHomologyIsoInt (n : ℕ) :
    HrelSet (Y := TopCat.of (Sph (n + 2))) (n + 2) (sphUpperCap (n + 1)) ≅
      AddCommGrpCat.of ℤ :=
  (sphSphereUpperCapRelativeIso n).symm ≪≫ hgrpSphereSelfIsoZ (n + 1)

/-- Independently of homotopy excision, the source and target relative homology groups of the
canonical sphere-cap map are isomorphic in their top degree. -/
noncomputable def sphereSuspensionRelativeHomologyIso (n : ℕ) :
    HrelSet (Y := TopCat.of (sphLowerCap (n + 1))) (n + 2)
        (sphCapOverlapInLower (n + 1)) ≅
      HrelSet (Y := TopCat.of (Sph (n + 2))) (n + 2) (sphUpperCap (n + 1)) :=
  sphLowerCapRelativeTopHomologyIsoInt n ≪≫
    (sphSphereUpperCapRelativeTopHomologyIsoInt n).symm

/-- The canonical cap map commutes with the relative-homology connecting maps. -/
theorem sphereSuspensionExcisionHrelMap_boundary_naturality (n : ℕ) :
    relδ (n + 1)
          (subIncl (Y := TopCat.of (sphLowerCap (n + 1)))
            (sphCapOverlapInLower (n + 1))) ≫
        HgrpMap (n + 1) (sphCapInclusionPairMap (n + 1)).subspaceHom =
      sphereSuspensionExcisionHrelMap n ≫
        relδ (n + 1)
          (subIncl (Y := TopCat.of (Sph (n + 2))) (sphUpperCap (n + 1))) :=
  relδ_naturality (n + 1)
    (subIncl (Y := TopCat.of (sphLowerCap (n + 1))) (sphCapOverlapInLower (n + 1)))
    (subIncl (Y := TopCat.of (Sph (n + 2))) (sphUpperCap (n + 1)))
    (sphCapInclusionPairMap (n + 1)).subIncl_naturality

end Submission
