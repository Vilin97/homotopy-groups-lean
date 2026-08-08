import Mathlib

open scoped Topology

namespace HomotopyGroups.StableStems

/-- The unit metric sphere modeling `S^n`. -/
abbrev StableSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The first coordinate vector gives the basepoint used for every modeled sphere. -/
noncomputable def stableSphereBasepoint (n : ℕ) : StableSphere n :=
  ⟨EuclideanSpace.single 0 1, by simp [StableSphere]⟩

/--
Stable stem 0, represented by pi_2(S^2).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z.
The stable degree group: pi_0^S is infinite cyclic.
Sources: iwx2023 Introduction and definition of stable stems: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_000 :
    Nonempty
      (π_ 2 (StableSphere 2) (stableSphereBasepoint 2) ≃*
        Multiplicative ℤ) := by
  sorry

/--
Stable stem 1, represented by pi_4(S^3).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2.
Sources: iwx2023 Table 1, stem 1: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_001 :
    Nonempty
      (π_ 4 (StableSphere 3) (stableSphereBasepoint 3) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

/--
Stable stem 2, represented by pi_6(S^4).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2.
Sources: iwx2023 Table 1, stem 2: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_002 :
    Nonempty
      (π_ 6 (StableSphere 4) (stableSphereBasepoint 4) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

/--
Stable stem 3, represented by pi_8(S^5).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/24.
Sources: iwx2023 Table 1, stem 3: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_003 :
    Nonempty
      (π_ 8 (StableSphere 5) (stableSphereBasepoint 5) ≃*
        Multiplicative (ZMod 24)) := by
  sorry

/--
Stable stem 4, represented by pi_10(S^6).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: 0.
Sources: iwx2023 Table 1, stem 4: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_004 :
    Nonempty
      (π_ 10 (StableSphere 6) (stableSphereBasepoint 6) ≃*
        Multiplicative (ZMod 1)) := by
  sorry

/--
Stable stem 5, represented by pi_12(S^7).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: 0.
Sources: iwx2023 Table 1, stem 5: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_005 :
    Nonempty
      (π_ 12 (StableSphere 7) (stableSphereBasepoint 7) ≃*
        Multiplicative (ZMod 1)) := by
  sorry

/--
Stable stem 6, represented by pi_14(S^8).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2.
Sources: iwx2023 Table 1, stem 6: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_006 :
    Nonempty
      (π_ 14 (StableSphere 8) (stableSphereBasepoint 8) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

/--
Stable stem 7, represented by pi_16(S^9).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/240.
Sources: iwx2023 Table 1, stem 7: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_007 :
    Nonempty
      (π_ 16 (StableSphere 9) (stableSphereBasepoint 9) ≃*
        Multiplicative (ZMod 240)) := by
  sorry

/--
Stable stem 8, represented by pi_18(S^10).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 8: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_008 :
    Nonempty
      (π_ 18 (StableSphere 10) (stableSphereBasepoint 10) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  sorry

/--
Stable stem 9, represented by pi_20(S^11).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 9: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_009 :
    Nonempty
      (π_ 20 (StableSphere 11) (stableSphereBasepoint 11) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2)))) := by
  sorry

/--
Stable stem 10, represented by pi_22(S^12).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/6.
Sources: iwx2023 Table 1, stem 10: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_010 :
    Nonempty
      (π_ 22 (StableSphere 12) (stableSphereBasepoint 12) ≃*
        Multiplicative (ZMod 6)) := by
  sorry

/--
Stable stem 11, represented by pi_24(S^13).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/504.
Sources: iwx2023 Table 1, stem 11: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_011 :
    Nonempty
      (π_ 24 (StableSphere 13) (stableSphereBasepoint 13) ≃*
        Multiplicative (ZMod 504)) := by
  sorry

/--
Stable stem 12, represented by pi_26(S^14).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: 0.
Sources: iwx2023 Table 1, stem 12: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_012 :
    Nonempty
      (π_ 26 (StableSphere 14) (stableSphereBasepoint 14) ≃*
        Multiplicative (ZMod 1)) := by
  sorry

/--
Stable stem 13, represented by pi_28(S^15).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/3.
Sources: iwx2023 Table 1, stem 13: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_013 :
    Nonempty
      (π_ 28 (StableSphere 15) (stableSphereBasepoint 15) ≃*
        Multiplicative (ZMod 3)) := by
  sorry

/--
Stable stem 14, represented by pi_30(S^16).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 14: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_014 :
    Nonempty
      (π_ 30 (StableSphere 16) (stableSphereBasepoint 16) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  sorry

/--
Stable stem 15, represented by pi_32(S^17).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/480.
Sources: iwx2023 Table 1, stem 15: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_015 :
    Nonempty
      (π_ 32 (StableSphere 17) (stableSphereBasepoint 17) ≃*
        Multiplicative (ZMod 2 × (ZMod 480))) := by
  sorry

/--
Stable stem 16, represented by pi_34(S^18).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 16: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_016 :
    Nonempty
      (π_ 34 (StableSphere 18) (stableSphereBasepoint 18) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  sorry

/--
Stable stem 17, represented by pi_36(S^19).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 17: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_017 :
    Nonempty
      (π_ 36 (StableSphere 19) (stableSphereBasepoint 19) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2))))) := by
  sorry

/--
Stable stem 18, represented by pi_38(S^20).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/8.
Sources: iwx2023 Table 1, stem 18: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_018 :
    Nonempty
      (π_ 38 (StableSphere 20) (stableSphereBasepoint 20) ≃*
        Multiplicative (ZMod 2 × (ZMod 8))) := by
  sorry

/--
Stable stem 19, represented by pi_40(S^21).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/264.
Sources: iwx2023 Table 1, stem 19: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_019 :
    Nonempty
      (π_ 40 (StableSphere 21) (stableSphereBasepoint 21) ≃*
        Multiplicative (ZMod 2 × (ZMod 264))) := by
  sorry

/--
Stable stem 20, represented by pi_42(S^22).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/24.
Sources: iwx2023 Table 1, stem 20: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_020 :
    Nonempty
      (π_ 42 (StableSphere 22) (stableSphereBasepoint 22) ≃*
        Multiplicative (ZMod 24)) := by
  sorry

/--
Stable stem 21, represented by pi_44(S^23).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 21: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_021 :
    Nonempty
      (π_ 44 (StableSphere 23) (stableSphereBasepoint 23) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  sorry

/--
Stable stem 22, represented by pi_46(S^24).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 22: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_022 :
    Nonempty
      (π_ 46 (StableSphere 24) (stableSphereBasepoint 24) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  sorry

/--
Stable stem 23, represented by pi_48(S^25).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/24 x Z/65520.
Sources: iwx2023 Table 1, stem 23: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_023 :
    Nonempty
      (π_ 48 (StableSphere 25) (stableSphereBasepoint 25) ≃*
        Multiplicative (ZMod 2 × (ZMod 24 × (ZMod 65520)))) := by
  sorry

/--
Stable stem 24, represented by pi_50(S^26).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 24: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_024 :
    Nonempty
      (π_ 50 (StableSphere 26) (stableSphereBasepoint 26) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  sorry

/--
Stable stem 25, represented by pi_52(S^27).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 25: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_025 :
    Nonempty
      (π_ 52 (StableSphere 27) (stableSphereBasepoint 27) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  sorry

/--
Stable stem 26, represented by pi_54(S^28).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/6.
Sources: iwx2023 Table 1, stem 26: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_026 :
    Nonempty
      (π_ 54 (StableSphere 28) (stableSphereBasepoint 28) ≃*
        Multiplicative (ZMod 2 × (ZMod 6))) := by
  sorry

/--
Stable stem 27, represented by pi_56(S^29).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/24.
Sources: iwx2023 Table 1, stem 27: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_027 :
    Nonempty
      (π_ 56 (StableSphere 29) (stableSphereBasepoint 29) ≃*
        Multiplicative (ZMod 24)) := by
  sorry

/--
Stable stem 28, represented by pi_58(S^30).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2.
Sources: iwx2023 Table 1, stem 28: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_028 :
    Nonempty
      (π_ 58 (StableSphere 30) (stableSphereBasepoint 30) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

/--
Stable stem 29, represented by pi_60(S^31).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/3.
Sources: iwx2023 Table 1, stem 29: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_029 :
    Nonempty
      (π_ 60 (StableSphere 31) (stableSphereBasepoint 31) ≃*
        Multiplicative (ZMod 3)) := by
  sorry

/--
Stable stem 30, represented by pi_62(S^32).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/6.
Sources: iwx2023 Table 1, stem 30: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_030 :
    Nonempty
      (π_ 62 (StableSphere 32) (stableSphereBasepoint 32) ≃*
        Multiplicative (ZMod 6)) := by
  sorry

/--
Stable stem 31, represented by pi_64(S^33).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/16320.
Sources: iwx2023 Table 1, stem 31: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_031 :
    Nonempty
      (π_ 64 (StableSphere 33) (stableSphereBasepoint 33) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 16320)))) := by
  sorry

/--
Stable stem 32, represented by pi_66(S^34).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 32: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_032 :
    Nonempty
      (π_ 66 (StableSphere 34) (stableSphereBasepoint 34) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2))))) := by
  sorry

/--
Stable stem 33, represented by pi_68(S^35).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 33: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_033 :
    Nonempty
      (π_ 68 (StableSphere 35) (stableSphereBasepoint 35) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2)))))) := by
  sorry

/--
Stable stem 34, represented by pi_70(S^36).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/4.
Sources: iwx2023 Table 1, stem 34: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_034 :
    Nonempty
      (π_ 70 (StableSphere 36) (stableSphereBasepoint 36) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4))))) := by
  sorry

/--
Stable stem 35, represented by pi_72(S^37).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/28728.
Sources: iwx2023 Table 1, stem 35: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_035 :
    Nonempty
      (π_ 72 (StableSphere 37) (stableSphereBasepoint 37) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 28728)))) := by
  sorry

/--
Stable stem 36, represented by pi_74(S^38).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/6.
Sources: iwx2023 Table 1, stem 36: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_036 :
    Nonempty
      (π_ 74 (StableSphere 38) (stableSphereBasepoint 38) ≃*
        Multiplicative (ZMod 6)) := by
  sorry

/--
Stable stem 37, represented by pi_76(S^39).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/6.
Sources: iwx2023 Table 1, stem 37: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_037 :
    Nonempty
      (π_ 76 (StableSphere 39) (stableSphereBasepoint 39) ≃*
        Multiplicative (ZMod 2 × (ZMod 6))) := by
  sorry

/--
Stable stem 38, represented by pi_78(S^40).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/60.
Sources: iwx2023 Table 1, stem 38: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_038 :
    Nonempty
      (π_ 78 (StableSphere 40) (stableSphereBasepoint 40) ≃*
        Multiplicative (ZMod 2 × (ZMod 60))) := by
  sorry

/--
Stable stem 39, represented by pi_80(S^41).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/6 x Z/13200.
Sources: iwx2023 Table 1, stem 39: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_039 :
    Nonempty
      (π_ 80 (StableSphere 41) (stableSphereBasepoint 41) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 6 × (ZMod 13200))))))) := by
  sorry

/--
Stable stem 40, represented by pi_82(S^42).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/12.
Sources: iwx2023 Table 1, stem 40: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_040 :
    Nonempty
      (π_ 82 (StableSphere 42) (stableSphereBasepoint 42) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 12))))))) := by
  sorry

/--
Stable stem 41, represented by pi_84(S^43).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 41: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_041 :
    Nonempty
      (π_ 84 (StableSphere 43) (stableSphereBasepoint 43) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2)))))) := by
  sorry

/--
Stable stem 42, represented by pi_86(S^44).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/24.
Sources: iwx2023 Table 1, stem 42: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_042 :
    Nonempty
      (π_ 86 (StableSphere 44) (stableSphereBasepoint 44) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 24)))) := by
  sorry

/--
Stable stem 43, represented by pi_88(S^45).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/552.
Sources: iwx2023 Table 1, stem 43: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_043 :
    Nonempty
      (π_ 88 (StableSphere 45) (stableSphereBasepoint 45) ≃*
        Multiplicative (ZMod 552)) := by
  sorry

/--
Stable stem 44, represented by pi_90(S^46).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/8.
Sources: iwx2023 Table 1, stem 44: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_044 :
    Nonempty
      (π_ 90 (StableSphere 46) (stableSphereBasepoint 46) ≃*
        Multiplicative (ZMod 8)) := by
  sorry

/--
Stable stem 45, represented by pi_92(S^47).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/720.
Sources: iwx2023 Table 1, stem 45: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_045 :
    Nonempty
      (π_ 92 (StableSphere 47) (stableSphereBasepoint 47) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 720))))) := by
  sorry

/--
Stable stem 46, represented by pi_94(S^48).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/6.
Sources: iwx2023 Table 1, stem 46: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_046 :
    Nonempty
      (π_ 94 (StableSphere 48) (stableSphereBasepoint 48) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 6))))) := by
  sorry

/--
Stable stem 47, represented by pi_96(S^49).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/12 x Z/131040.
Sources: iwx2023 Table 1, stem 47: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_047 :
    Nonempty
      (π_ 96 (StableSphere 49) (stableSphereBasepoint 49) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 12 × (ZMod 131040)))))) := by
  sorry

/--
Stable stem 48, represented by pi_98(S^50).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/4.
Sources: iwx2023 Table 1, stem 48: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_048 :
    Nonempty
      (π_ 98 (StableSphere 50) (stableSphereBasepoint 50) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4)))))) := by
  sorry

/--
Stable stem 49, represented by pi_100(S^51).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/6.
Sources: iwx2023 Table 1, stem 49: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_049 :
    Nonempty
      (π_ 100 (StableSphere 51) (stableSphereBasepoint 51) ≃*
        Multiplicative (ZMod 2 × (ZMod 6))) := by
  sorry

/--
Stable stem 50, represented by pi_102(S^52).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/6.
Sources: iwx2023 Table 1, stem 50: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_050 :
    Nonempty
      (π_ 102 (StableSphere 52) (stableSphereBasepoint 52) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 6)))) := by
  sorry

/--
Stable stem 51, represented by pi_104(S^53).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/8 x Z/24.
Sources: iwx2023 Table 1, stem 51: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_051 :
    Nonempty
      (π_ 104 (StableSphere 53) (stableSphereBasepoint 53) ≃*
        Multiplicative (ZMod 2 × (ZMod 8 × (ZMod 24)))) := by
  sorry

/--
Stable stem 52, represented by pi_106(S^54).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/6.
Sources: iwx2023 Table 1, stem 52: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_052 :
    Nonempty
      (π_ 106 (StableSphere 54) (stableSphereBasepoint 54) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 6)))) := by
  sorry

/--
Stable stem 53, represented by pi_108(S^55).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 53: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_053 :
    Nonempty
      (π_ 108 (StableSphere 55) (stableSphereBasepoint 55) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2))))) := by
  sorry

/--
Stable stem 54, represented by pi_110(S^56).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/4.
Sources: iwx2023 Table 1, stem 54: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_054 :
    Nonempty
      (π_ 110 (StableSphere 56) (stableSphereBasepoint 56) ≃*
        Multiplicative (ZMod 2 × (ZMod 4))) := by
  sorry

/--
Stable stem 55, represented by pi_112(S^57).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/3 x Z/6960.
Sources: iwx2023 Table 1, stem 55: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_055 :
    Nonempty
      (π_ 112 (StableSphere 57) (stableSphereBasepoint 57) ≃*
        Multiplicative (ZMod 3 × (ZMod 6960))) := by
  sorry

/--
Stable stem 56, represented by pi_114(S^58).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2.
Sources: iwx2023 Table 1, stem 56: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_056 :
    Nonempty
      (π_ 114 (StableSphere 58) (stableSphereBasepoint 58) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

/--
Stable stem 57, represented by pi_116(S^59).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 57: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_057 :
    Nonempty
      (π_ 116 (StableSphere 59) (stableSphereBasepoint 59) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2)))) := by
  sorry

/--
Stable stem 58, represented by pi_118(S^60).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 58: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_058 :
    Nonempty
      (π_ 118 (StableSphere 60) (stableSphereBasepoint 60) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  sorry

/--
Stable stem 59, represented by pi_120(S^61).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/171864.
Sources: iwx2023 Table 1, stem 59: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_059 :
    Nonempty
      (π_ 120 (StableSphere 61) (stableSphereBasepoint 61) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 171864)))) := by
  sorry

/--
Stable stem 60, represented by pi_122(S^62).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/4.
Sources: iwx2023 Table 1, stem 60: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_060 :
    Nonempty
      (π_ 122 (StableSphere 62) (stableSphereBasepoint 62) ≃*
        Multiplicative (ZMod 4)) := by
  sorry

/--
Stable stem 61, represented by pi_124(S^63).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: 0.
Sources: iwx2023 Table 1, stem 61: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_061 :
    Nonempty
      (π_ 124 (StableSphere 63) (stableSphereBasepoint 63) ≃*
        Multiplicative (ZMod 1)) := by
  sorry

/--
Stable stem 62, represented by pi_126(S^64).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/6.
Sources: iwx2023 Table 1, stem 62: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_062 :
    Nonempty
      (π_ 126 (StableSphere 64) (stableSphereBasepoint 64) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 6))))) := by
  sorry

/--
Stable stem 63, represented by pi_128(S^65).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/4 x Z/32640.
Sources: iwx2023 Table 1, stem 63: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_063 :
    Nonempty
      (π_ 128 (StableSphere 65) (stableSphereBasepoint 65) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 32640))))) := by
  sorry

/--
Stable stem 64, represented by pi_130(S^66).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/4.
Sources: iwx2023 Table 1, stem 64: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_064 :
    Nonempty
      (π_ 130 (StableSphere 66) (stableSphereBasepoint 66) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4)))))))) := by
  sorry

/--
Stable stem 65, represented by pi_132(S^67).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/12.
Sources: iwx2023 Table 1, stem 65: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_065 :
    Nonempty
      (π_ 132 (StableSphere 67) (stableSphereBasepoint 67) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 12))))))))))) := by
  sorry

/--
Stable stem 66, represented by pi_134(S^68).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/8.
Sources: iwx2023 Table 1, stem 66: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_066 :
    Nonempty
      (π_ 134 (StableSphere 68) (stableSphereBasepoint 68) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 8)))))))) := by
  sorry

/--
Stable stem 67, represented by pi_136(S^69).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/4 x Z/24.
Sources: iwx2023 Table 1, stem 67: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_067 :
    Nonempty
      (π_ 136 (StableSphere 69) (stableSphereBasepoint 69) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 24)))))) := by
  sorry

/--
Stable stem 68, represented by pi_138(S^70).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/6.
Sources: iwx2023 Table 1, stem 68: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_068 :
    Nonempty
      (π_ 138 (StableSphere 70) (stableSphereBasepoint 70) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 6)))) := by
  sorry

/--
Stable stem 69, represented by pi_140(S^71).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 69: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_069 :
    Nonempty
      (π_ 140 (StableSphere 71) (stableSphereBasepoint 71) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2))))) := by
  sorry

/--
Stable stem 70, represented by pi_142(S^72).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/4.
Applies the published 2025 correction to the erroneous IWX 2023 2-primary v1-torsion entry.
Sources: bix2025 Section 1.2: https://link.springer.com/article/10.1007/s42543-025-00098-y (DOI https://doi.org/10.1007/s42543-025-00098-y); iwx2023 Table 1, stem 70: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_070 :
    Nonempty
      (π_ 142 (StableSphere 72) (stableSphereBasepoint 72) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4)))))))) := by
  sorry

/--
Stable stem 71, represented by pi_144(S^73).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/4 x Z/8 x Z/138181680.
Applies the published 2025 correction to the erroneous IWX 2023 2-primary v1-torsion entry and retains the unchanged v1-periodic summands.
Sources: bix2025 Section 1.2: https://link.springer.com/article/10.1007/s42543-025-00098-y (DOI https://doi.org/10.1007/s42543-025-00098-y); iwx2023 Table 1, stem 71: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_071 :
    Nonempty
      (π_ 144 (StableSphere 73) (stableSphereBasepoint 73) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 8 × (ZMod 138181680))))))))) := by
  sorry

/--
Stable stem 72, represented by pi_146(S^74).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/6.
Sources: iwx2023 Table 1, stem 72: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_072 :
    Nonempty
      (π_ 146 (StableSphere 74) (stableSphereBasepoint 74) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 6))))))))) := by
  sorry

/--
Stable stem 73, represented by pi_148(S^75).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 73: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_073 :
    Nonempty
      (π_ 148 (StableSphere 75) (stableSphereBasepoint 75) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2)))))))) := by
  sorry

/--
Stable stem 74, represented by pi_150(S^76).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/4 x Z/4 x Z/12.
Sources: iwx2023 Table 1, stem 74: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_074 :
    Nonempty
      (π_ 150 (StableSphere 76) (stableSphereBasepoint 76) ≃*
        Multiplicative (ZMod 2 × (ZMod 4 × (ZMod 4 × (ZMod 12))))) := by
  sorry

/--
Stable stem 75, represented by pi_152(S^77).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/6 x Z/72.
Sources: iwx2023 Table 1, stem 75: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_075 :
    Nonempty
      (π_ 152 (StableSphere 77) (stableSphereBasepoint 77) ≃*
        Multiplicative (ZMod 6 × (ZMod 72))) := by
  sorry

/--
Stable stem 76, represented by pi_154(S^78).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/20.
Sources: iwx2023 Table 1, stem 76: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_076 :
    Nonempty
      (π_ 154 (StableSphere 78) (stableSphereBasepoint 78) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 20)))) := by
  sorry

/--
Stable stem 77, represented by pi_156(S^79).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/4.
Sources: iwx2023 Table 1, stem 77: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_077 :
    Nonempty
      (π_ 156 (StableSphere 79) (stableSphereBasepoint 79) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4))))))) := by
  sorry

/--
Stable stem 78, represented by pi_158(S^80).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/4 x Z/12.
Sources: iwx2023 Table 1, stem 78: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_078 :
    Nonempty
      (π_ 158 (StableSphere 80) (stableSphereBasepoint 80) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 12)))))) := by
  sorry

/--
Stable stem 79, represented by pi_160(S^81).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/4 x Z/1082400.
Sources: iwx2023 Table 1, stem 79: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_079 :
    Nonempty
      (π_ 160 (StableSphere 81) (stableSphereBasepoint 81) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 1082400))))))))) := by
  sorry

/--
Stable stem 80, represented by pi_162(S^82).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 80: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_080 :
    Nonempty
      (π_ 162 (StableSphere 82) (stableSphereBasepoint 82) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2)))))))))) := by
  sorry

/--
Stable stem 81, represented by pi_164(S^83).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/12 x Z/24.
Sources: iwx2023 Table 1, stem 81: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_081 :
    Nonempty
      (π_ 164 (StableSphere 83) (stableSphereBasepoint 83) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 12 × (ZMod 24)))))))) := by
  sorry

/--
Stable stem 82, represented by pi_166(S^84).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/168.
Uses BIX 2025 Theorem 1.1 for the now-complete 2-primary component; odd-primary summands remain from IWX 2023.
Sources: bix2025 Theorem 1.1(1): https://link.springer.com/article/10.1007/s42543-025-00098-y (DOI https://doi.org/10.1007/s42543-025-00098-y); iwx2023 Table 1, stem 82: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_082 :
    Nonempty
      (π_ 166 (StableSphere 84) (stableSphereBasepoint 84) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 168)))))))) := by
  sorry

/--
Stable stem 83, represented by pi_168(S^85).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/8 x Z/758520.
Uses BIX 2025 Theorem 1.1 for the now-complete 2-primary component; odd-primary summands remain from IWX 2023.
Sources: bix2025 Theorem 1.1(2): https://link.springer.com/article/10.1007/s42543-025-00098-y (DOI https://doi.org/10.1007/s42543-025-00098-y); iwx2023 Table 1, stem 83: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_083 :
    Nonempty
      (π_ 168 (StableSphere 85) (stableSphereBasepoint 85) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 8 × (ZMod 758520)))))) := by
  sorry

/--
Stable stem 84, represented by pi_170(S^86).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published complete integral-group alternatives:
* iwx2023-84-a: Z/2 x Z/2 x Z/2 x Z/2 x Z/6 x Z/6.
* iwx2023-84-b: Z/2 x Z/2 x Z/2 x Z/6 x Z/6.
Knowledge status: open computation with published alternatives.
Not exact: IWX 2023 leaves a factor-of-2 ambiguity in the 2-primary v1-torsion component.
Sources: iwx2023 Table 1, stem 84: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_084 :
    (Nonempty
      (π_ 170 (StableSphere 86) (stableSphereBasepoint 86) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 6 × (ZMod 6)))))))) ∨
    (Nonempty
      (π_ 170 (StableSphere 86) (stableSphereBasepoint 86) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 6 × (ZMod 6))))))) := by
  sorry

/--
Stable stem 85, represented by pi_172(S^87).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published complete integral-group alternatives:
* iwx2023-85-a: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/12 x Z/12.
* iwx2023-85-b: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/12 x Z/12.
* iwx2023-85-c: Z/2 x Z/2 x Z/2 x Z/2 x Z/4 x Z/12 x Z/12.
* iwx2023-85-d: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/6 x Z/12.
Knowledge status: open computation with published alternatives.
Not exact: IWX 2023 lists four possible 2-primary additive structures.
Sources: iwx2023 Table 1, stem 85: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_085 :
    (Nonempty
      (π_ 172 (StableSphere 87) (stableSphereBasepoint 87) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 12 × (ZMod 12)))))))))) ∨
    (Nonempty
      (π_ 172 (StableSphere 87) (stableSphereBasepoint 87) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 12 × (ZMod 12))))))))) ∨
    (Nonempty
      (π_ 172 (StableSphere 87) (stableSphereBasepoint 87) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 12 × (ZMod 12))))))))) ∨
    (Nonempty
      (π_ 172 (StableSphere 87) (stableSphereBasepoint 87) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 6 × (ZMod 12)))))))))) := by
  sorry

/--
Stable stem 86, represented by pi_174(S^88).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published complete integral-group alternatives:
* iwx2023-86-a: Z/2 x Z/2 x Z/2 x Z/2 x Z/8 x Z/120.
* iwx2023-86-b: Z/2 x Z/2 x Z/4 x Z/8 x Z/120.
Knowledge status: open computation with published alternatives.
Not exact: IWX 2023 lists two possible 2-primary additive structures.
Sources: iwx2023 Table 1, stem 86: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_086 :
    (Nonempty
      (π_ 174 (StableSphere 88) (stableSphereBasepoint 88) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 8 × (ZMod 120)))))))) ∨
    (Nonempty
      (π_ 174 (StableSphere 88) (stableSphereBasepoint 88) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 8 × (ZMod 120))))))) := by
  sorry

/--
Stable stem 87, represented by pi_176(S^89).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/4 x Z/5520.
Sources: iwx2023 Table 1, stem 87: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_087 :
    Nonempty
      (π_ 176 (StableSphere 89) (stableSphereBasepoint 89) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 5520)))))))) := by
  sorry

/--
Stable stem 88, represented by pi_178(S^90).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2 x Z/4.
Sources: iwx2023 Table 1, stem 88: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_088 :
    Nonempty
      (π_ 178 (StableSphere 90) (stableSphereBasepoint 90) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4))))))) := by
  sorry

/--
Stable stem 89, represented by pi_180(S^91).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published integral group: Z/2 x Z/2 x Z/2 x Z/2 x Z/2.
Sources: iwx2023 Table 1, stem 89: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_089 :
    Nonempty
      (π_ 180 (StableSphere 91) (stableSphereBasepoint 91) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2)))))) := by
  sorry

/--
Stable stem 90, represented by pi_182(S^92).
The equality q = 2n - 2 places this representative in the Freudenthal stable range.
Published complete integral-group alternatives:
* iwx2023-90-a: Z/2 x Z/2 x Z/2 x Z/2 x Z/24.
* iwx2023-90-b: Z/2 x Z/2 x Z/2 x Z/24.
Knowledge status: open computation with published alternatives.
Not exact: IWX 2023 leaves a factor-of-2 ambiguity; the known v1-periodic C2 and odd-primary C3 summands are included in each full-group alternative.
Sources: iwx2023 Table 1, stem 90: https://www.numdam.org/articles/10.1007/s10240-023-00139-1/ (DOI https://doi.org/10.1007/s10240-023-00139-1)
-/
theorem stable_stem_090 :
    (Nonempty
      (π_ 182 (StableSphere 92) (stableSphereBasepoint 92) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 24))))))) ∨
    (Nonempty
      (π_ 182 (StableSphere 92) (stableSphereBasepoint 92) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 24)))))) := by
  sorry

end HomotopyGroups.StableStems
open scoped Topology

namespace HomotopyGroups

/-- The eight finite abelian 3-groups occurring in positive stems through 108. -/
inductive StableThreePrimaryGroupCode where
  | trivial
  | c3
  | c3Squared
  | c3Cubed
  | c9
  | c3TimesC9
  | c27
  | c3SquaredTimesC81

namespace StableThreePrimaryGroupCode

/-- Interpret a table code as an actual bundled multiplicative group. -/
noncomputable def asGrp : StableThreePrimaryGroupCode → GrpCat
  | .trivial => GrpCat.of (Multiplicative (ZMod 1))
  | .c3 => GrpCat.of (Multiplicative (ZMod 3))
  | .c3Squared => GrpCat.of (Multiplicative (ZMod 3 × ZMod 3))
  | .c3Cubed => GrpCat.of (Multiplicative (ZMod 3 × (ZMod 3 × ZMod 3)))
  | .c9 => GrpCat.of (Multiplicative (ZMod 9))
  | .c3TimesC9 => GrpCat.of (Multiplicative (ZMod 3 × ZMod 9))
  | .c27 => GrpCat.of (Multiplicative (ZMod 27))
  | .c3SquaredTimesC81 => GrpCat.of (Multiplicative (ZMod 3 × (ZMod 3 × ZMod 81)))

end StableThreePrimaryGroupCode

/-- Table A3.2 plus image J, in positive stems; index zero represents stable stem one. -/
def stableThreePrimaryGroupCode (stemIndex : Fin 108) : StableThreePrimaryGroupCode :=
  match stemIndex.val with
  | 0 => .trivial
  | 1 => .trivial
  | 2 => .c3
  | 3 => .trivial
  | 4 => .trivial
  | 5 => .trivial
  | 6 => .c3
  | 7 => .trivial
  | 8 => .trivial
  | 9 => .c3
  | 10 => .c9
  | 11 => .trivial
  | 12 => .c3
  | 13 => .trivial
  | 14 => .c3
  | 15 => .trivial
  | 16 => .trivial
  | 17 => .trivial
  | 18 => .c3
  | 19 => .c3
  | 20 => .trivial
  | 21 => .trivial
  | 22 => .c3TimesC9
  | 23 => .trivial
  | 24 => .trivial
  | 25 => .c3
  | 26 => .c3
  | 27 => .trivial
  | 28 => .c3
  | 29 => .c3
  | 30 => .c3
  | 31 => .trivial
  | 32 => .trivial
  | 33 => .trivial
  | 34 => .c27
  | 35 => .c3
  | 36 => .c3
  | 37 => .c3
  | 38 => .c3Squared
  | 39 => .c3
  | 40 => .trivial
  | 41 => .c3
  | 42 => .c3
  | 43 => .trivial
  | 44 => .c9
  | 45 => .c3
  | 46 => .c3TimesC9
  | 47 => .trivial
  | 48 => .c3
  | 49 => .c3
  | 50 => .c3
  | 51 => .c3
  | 52 => .trivial
  | 53 => .trivial
  | 54 => .c3Squared
  | 55 => .trivial
  | 56 => .trivial
  | 57 => .trivial
  | 58 => .c9
  | 59 => .trivial
  | 60 => .trivial
  | 61 => .c3
  | 62 => .c3
  | 63 => .trivial
  | 64 => .c3
  | 65 => .trivial
  | 66 => .c3
  | 67 => .c3
  | 68 => .trivial
  | 69 => .trivial
  | 70 => .c27
  | 71 => .c3
  | 72 => .trivial
  | 73 => .c3
  | 74 => .c3TimesC9
  | 75 => .trivial
  | 76 => .trivial
  | 77 => .c3
  | 78 => .c3
  | 79 => .trivial
  | 80 => .c3Squared
  | 81 => .c3
  | 82 => .c9
  | 83 => .c3Squared
  | 84 => .c3Squared
  | 85 => .c3
  | 86 => .c3
  | 87 => .trivial
  | 88 => .trivial
  | 89 => .c3
  | 90 => .c3Cubed
  | 91 => .c3Squared
  | 92 => .c9
  | 93 => .c3Squared
  | 94 => .c3TimesC9
  | 95 => .trivial
  | 96 => .trivial
  | 97 => .trivial
  | 98 => .c3Squared
  | 99 => .c3
  | 100 => .c3Squared
  | 101 => .c3Squared
  | 102 => .c3
  | 103 => .c3
  | 104 => .trivial
  | 105 => .c3
  | 106 => .c3SquaredTimesC81
  | 107 => .c3
  | _ => .trivial

/-- The finite abelian group represented by `stableThreePrimaryGroupCode`. -/
noncomputable def stableThreePrimaryGroup (stemIndex : Fin 108) : GrpCat :=
  (stableThreePrimaryGroupCode stemIndex).asGrp



end HomotopyGroups
