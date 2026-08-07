/-
Adapted from leanprover/lean-eval at commit
53348531969dc984e02e3be0379a7282c664abd9.
Modified for homotopy-groups-lean; see NOTICE and LICENSE.
-/

import EvalTools.Manifest

namespace EvalTools

set_option autoImplicit false

/-- Implementation of `lake exe homotopy-groups-lean validate-manifest`. Loads the
manifest (which already enforces id/holes/duplication rules) and cross-checks
against the `@[eval_problem]` inventory built from source.

The Python original also called `gp.validate_hole_shape`, a textual pre-check
for typos in hole names. That check is purely redundant with the inventory
cross-check (which goes through the elaborator), so it is dropped here. -/
def runValidateManifest (root : System.FilePath) : IO UInt32 := do
  try
    let entries ← loadManifest root
    validateManifestAgainstInventory root entries
    IO.println "Manifest and @[eval_problem] declarations are consistent."
    return 0
  catch err =>
    IO.eprintln err
    return 1

end EvalTools
