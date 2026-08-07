# Adapted from leanprover/lean-eval at commit 53348531969dc984e02e3be0379a7282c664abd9.
# Modified for homotopy-groups-lean; see NOTICE and LICENSE.
"""Probes that exercise security-critical behaviour of the homotopy benchmark pipeline.

Each module under this package is a self-contained runnable probe. Probes
are written in a "loud failure" style: exit code 0 means the security
property holds; non-zero with a clear message means it does not.

See SECURITY.md > "Validations done at submission time" for which probes
gate CI versus which are one-shot diagnostics.
"""
