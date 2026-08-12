# Audited Lean 4 formalizations

[`formalizations.json`](formalizations.json) is the dated, machine-readable
inventory behind the website's purple overlay.  The maintained proof sets and
the displayed overlay are Lean 4 only.  Each positive entry has a source path,
model qualification, trust status, and license; public dependencies are
commit-pinned.

The repository includes a sorry-free proof that `pi_k(S^n)` vanishes below the
sphere dimension.  Its minimal twelve-module closure is vendored under
[`examples/submissions/sphere_lower_homotopy_subsingleton`](../examples/submissions/sphere_lower_homotopy_subsingleton/)
and is evaluated against the benchmark-owned statement. The maintained
`DisplayedLowerConnectivity.lean` wrapper strengthens each positive instance
to an explicit `MulEquiv` with `PUnit`, uniformly in the sphere dimension,
degree, and basepoint. The default absolute-degree `(n,m)` view therefore shows
the full 4,186-cell region `1 <= m < n <= 92` in purple; the nonnegative-stem
view remains available alongside it.

Every expanded purple-cell record carries `proof_declaration` and
`proof_source`. The latter is pinned to the audited commit and anchored at the
line where the named Lean theorem begins. The cell inspector exposes both
fields directly. A uniform result therefore appears as the same honest theorem
at each of its instances instead of being expanded into thousands of aliases.

The metric-circle submissions close the model gap for the first row of the
lattice by constructing the homeomorphism from Mathlib's complex `Circle` to
the benchmark's `SphereSpace 1`.  One proof transports the exponential
covering computation to show `pi_1(S^1) = Z`; the earlier general proof ports
covering invariance to show `pi_m(S^1) = 0` for every `m >= 2`.  The higher
row is one general formalized result.  Its named degree corollaries are
conveniences and are not counted separately.

## Twenty additional Lean 4 results

`maintained_lean4_twenty_result_set` records exactly twenty mathematically
distinct Lean 4 declarations in
[`Lean4TwentyResults.lean`](../examples/submissions/sphere_lower_homotopy_subsingleton/Submission/Lean4TwentyResults.lean).
They cover retract injectivity, section surjectivity, strict equivalences,
vanishing transfer, homeomorphism and pointed-homotopy invariance, product
triviality, contractible factors, products of fundamental groups and path
components, basepoint independence, higher-group commutativity, covering-map
injectivity, and exact metric-circle computations at arbitrary basepoints.
Numerical specializations, displayed cells, and aliases are not counted.

## Ten higher-sphere foundations

`maintained_higher_sphere_foundation_set` records ten further, distinct Lean 4
declarations.  They formalize the Serre path fibration, path-space vanishing,
the group-level loop-space shift, degree-one Hurewicz, top and off-diagonal
sphere homology, the complete integral homology pattern of one-fold loop
spheres, a contractible-pair relative comparison principle, and the exact
`pi_2(S^2) = Z` calculation.  Their audited axiom closures contain no
`sorryAx`.

The relative comparison principle is intentionally group-valued: once the
geometric suspension-excision bijection is supplied, it yields an actual
`MulEquiv` between successive sphere homotopy groups, not merely equality of
cardinalities.

The maintained Lean 4 closure now also contains the path fibration, the
degree-one Hurewicz theorem, the needed Mayer--Vietoris and Wang machinery, and
the computation `H_1(ΩS²) = Z`.  Their composition proves `pi_2(S^2) = Z` in
the exact metric-sphere model and adds `(n,k)=(2,0)` to the overlay. The live
stem display now runs through stem 108 and has 110 purple cells. The default
absolute-degree display has 4,279 purple cells: 4,186 lower-connectivity cells,
92 visible circle cells, and `pi_2(S^2)`.
`DisplayedCircleFrontier.lean` packages the higher-circle vanishing theorem as
an explicit `MulEquiv` with `PUnit` at every basepoint and gives named witnesses
for the eighteen newly displayed cells. Those numerical witnesses remain
corollaries of one general result.

The positive diagonal now has a concrete quotient-level foundation. The
canonical map `I^n -> S^n` is a quotient map, every cubical diagonal class is
represented by a based sphere self-map, and equality of the resulting classes
is equivalent to based homotopy. Homological degree descends to these classes,
takes value one on the canonical generator and zero on the null class, and
therefore proves `pi_n(S^n)` nontrivial for every `n >= 1`.

The same closure constructs the geometric suspension function between
successive positive diagonal classes using the explicit homeomorphism
`Susp(S^n) ~= S^(n+1)`. It preserves based homotopies and composition of
self-maps, agrees with suspended self-map representatives, and sends each
canonical generator to the next. The meridian produced by suspending a
constant map is now explicitly contracted through based maps, proving that
diagonal suspension also preserves the group identity and is nonconstant. It
is not yet proved to preserve multiplication or to be an equivalence, and
homological degree is not yet proved additive or complete. These qualitative
diagonal results therefore add no exact purple cells.

Higher exact diagonal and stable sphere stems still require additional degree
classification, Freudenthal, higher-Hurewicz, and Hopf-fibration
infrastructure. Incomplete attempts do not color cells.

`DiagonalInduction.lean` now records the exact equivalence between the two
computed diagonal groups `pi_1(S^1)` and `pi_2(S^2)`, and proves that a uniform
family of successive suspension equivalences propagates the integral
calculation through the whole diagonal. This is a checked reduction of the
next lattice frontier. A geometric suspension function is now available, but
only its identity-preserving property is currently proved at the group level.
`SphereSuspensionPointed.lean` gives a checked reduction from multiplication
compatibility and bijectivity of this specific function to the exact integral
diagonal. Those two properties remain unproved, so the reduction adds no
unsupported purple cells.

The maintained ten-result set is recorded explicitly in
`maintained_independent_result_set`.  Besides the metric-circle computation it
contains nine mathematically distinct structural theorems: the `pi_0` and
`pi_1` comparisons, change of basepoint, homotopy invariance, the binary product
formula, functoriality of induced maps, pointed-homotopy invariance,
covering-space invariance, and contractible-space vanishing.  Only the
metric-circle theorem colors lattice cells; the other nine are reusable
foundations and the inventory says so rather than presenting them as new sphere
computations.

The purple overlay records Lean 4 proofs only and never promotes the underlying
mathematical evidence class.  It does not propagate a stable representative
across an entire diagonal without formal suspension equivalences.

Deleted-source and incomplete attempts remain in `qualified_records` so the
negative audit is reproducible.  They do not color cells.

Three additional public, sorry-free `pi_1(Circle)` submissions are retained as
commit-pinned links in `related_public_proofs`. Their audited snapshots do not
contain an explicit source license, so this repository does not copy them.
