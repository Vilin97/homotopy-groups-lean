import ChallengeDeps
import Submission

open HomotopyGroups
open scoped Topology

theorem pi5_sphere_two_mulEquiv_zmod_two :
    Nonempty
      (HomotopyGroup.Pi 5 (SphereSpace 2) (sphereBasepoint 2) ≃*
        Multiplicative (ZMod 2)) := by
  exact Submission.pi5_sphere_two_mulEquiv_zmod_two
