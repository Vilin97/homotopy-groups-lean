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

The maintained closure also constructs the canonical antipodal covering from
the exact metric `n`-sphere to the benchmark's quotient-topology model of real
projective `n`-space.  It proves that every homotopy group in degree at least
two agrees with the corresponding sphere group and, for `n >= 2`, computes the
fundamental group as `Z/2`.  These are two general results in the formalization
index, but they color no sphere-lattice cells because their targets are real
projective spaces.

The canonical `HomotopyGroups.Foundations` benchmark module is now completely
sorry-free as well.  Its ten exact declarations package path-component and
fundamental-group comparisons, connectedness vanishing, higher and H-space
commutativity, homotopy and basepoint invariance, products, and loop-space
shifting.  The last result uses an explicit homeomorphism from one-dimensional
generalized loops to ordinary based paths and the group-level connecting
equivalence of the path fibration.  These structural results add no sphere
lattice cells directly.

The canonical spaces module now also exposes the exponential-covering proof of
`pi_1(Circle) = Z` and the uniform first-Hurewicz computation
`pi_d(S^d) = Z` for every positive `d`, with no `sorry` in either benchmark
declaration. Their challenge-independent cores work on the definitionally
identical metric-sphere model at arbitrary basepoints; the legacy wrappers and
canonical declarations are interfaces to the existing circle and diagonal
formalizations, not additional counted results.

The same independent circle core now proves that every homotopy group above
degree one vanishes at every basepoint of the metric circle. This directly
closes the canonical `sphere_one_higher_homotopy_subsingleton` declaration;
the pre-existing exact theorem, arbitrary-basepoint wrappers, and numerical
corollaries remain one counted general formalization.

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
the exact metric-sphere model and adds `(n,k)=(2,0)` to the overlay. That proof
is now isolated from the generated challenge declarations, works at every
basepoint, and directly closes the canonical `stable_stem_000` theorem in
`HomotopyGroups.StableStems`. The legacy wrapper and canonical theorem are two
interfaces to one formalization, so this adds no duplicate record or lattice
cell. The live
stem display now runs through stem 108 and has 200 purple cells. The default
absolute-degree display has 4,369 purple cells: 4,186 lower-connectivity cells,
91 higher-circle cells, and all 92 positive diagonal cells.
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
is not yet proved to preserve multiplication or to be an equivalence.

A separate reduced-suspension model now collapses both poles and the complete
basepoint meridian. On generalized cubical loops, suspension into this quotient
preserves the constant loop and homotopies relative to the boundary, and it
commutes strictly with concatenation in every old coordinate. It therefore
induces an actual monoid homomorphism on every positive-dimensional homotopy
group. The quotient is now proved compact Hausdorff and identified with the
one-point compactification of its punctured open cylinder. Stereographic
projection then gives a basepoint-preserving homeomorphism from the reduced
suspension of the exact metric `n`-sphere to the exact metric `(n+1)`-sphere.
Together with a multiplicative cubical-coordinate reindexing equivalence, this
transports reduced suspension to an actual monoid homomorphism between
successive exact metric-sphere diagonal groups. Freudenthal bijectivity and a
complete additive degree classification are still missing. These advances
therefore add no exact purple cells yet.

Relative homotopy groups are now functorial for based maps of pairs, as actual
monoid homomorphisms in degree at least two. The induced maps commute with all
three homomorphisms in the long exact sequence of a pair. Applying this API to
the explicit cover of a metric sphere by two enlarged hemispheres gives a
canonical relative cap-inclusion homomorphism: both caps are contractible, and
their overlap is explicitly homotopy-equivalent to the equatorial metric
sphere. Both cap/overlap pairs are now proved connected through the full range
required by homotopy excision. Relative singular homology is now functorial for
the same maps of pairs, with all three long-exact-sequence squares proved
natural. A Mayer--Vietoris chain pushout and the small-simplices comparison give
the full excision theorem `H_k(A,A∩B) ≅ H_k(X,B)` for every interior cover and
every degree. Applied to the sphere caps, it proves that the exact canonical
cap map is a relative-homology isomorphism in every degree and identifies both
top relative groups with `Z`. The bounded singular-simplex compression theorem
is now connected directly to the `IsNConnectedPair` interface as well: it
proves zero relative homology through degree `m` for both cap/overlap pairs and,
after excision, for the sphere/upper-cap target. Thus the complete
vanishing-plus-first-nonzero homology pattern is checked on both sides of the
canonical map. A relative cubical loop is now packaged as a based map of pairs,
and its action on relative homology is proved invariant under relative homotopy
and natural under postcomposition. The top relative homology of the cube pair
is computed as `Z`, with a normalized oriented fundamental class. Evaluating on
that class constructs a natural relative Hurewicz comparison in every degree at
least two.

The comparison is now also pinned down at the boundary: the connecting map
sends the chosen cube-pair class to an oriented boundary class, and naturality
identifies the boundary of every represented relative Hurewicz class with the
homology class carried by the restricted cubical map. On the absolute side, an
`(n+1)`-connected space is converted to the singleton pair `(X,{x})`; the
coherent bounded deformation then makes every face of each deformed
`(n+2)`-simplex constant at `x`. The simplex--disk--cube homeomorphism turns
that normalized simplex into a based cubical loop, and the assignment extends
additively over top-dimensional singular chains. A simplex whose faces lie in
the subspace is now also packaged as an explicit relative cycle and homology
class. The inverse simplex--cube reparametrization supplies an explicit top
simplex of the cube pair, and mapping it along a normalized cubical loop
recovers the normalized singular simplex exactly, first as a chain and then as
a relative homology class. Evaluation on this explicit source class therefore
computes definitionally on normalized representatives. In parallel, the
coherent deformation is descended to the relative chain complex and proved to
induce the identity on relative homology; on top-dimensional simplex
generators it produces exactly the normalized relative chain. The explicit
cube-simplex class is now compared with the canonical oriented fundamental
class as well. Its orientation coefficient is an integer; normalization shows
that multiplication by this coefficient is surjective on the first
potentially nonzero relative homology of every sufficiently connected space.
Applying this to a sphere, whose corresponding relative group is `Z`, forces
the coefficient to be `1` or `-1`. Thus the two source classes agree up to one
global orientation sign, and the canonical relative Hurewicz comparison sends
every normalized simplex to its relative class up to the inverse sign.
Moreover, these canonical Hurewicz values linearly generate the whole first
nonvanishing relative homology group. Cubical concatenation is now replaced by
a homotopic plateau concatenation and analyzed through an induced two-member
small-simplices cover of the cube pair. This proves that the canonical relative
Hurewicz comparison carries multiplication to addition in every degree at
least two, without assuming that the source relative group is commutative.
The comparison is consequently packaged as an additive homomorphism. For an
`(n+1)`-connected space and a chosen point, the normalized top-chain map
factors through its range, upgrading linear generation to genuine
surjectivity of `pi_rel_(n+2)(X,{x}) -> H_(n+2)(X,{x})`.

The cubical quotient bridge has now been generalized from sphere self-maps to
every pointed target: in each positive dimension, generalized cubical loops
are equivalent to based maps from the exact metric sphere, and relative
cubical homotopy is equivalent to based homotopy of those sphere maps. A
coherently deformed `(n+3)`-simplex is packaged together with all of its
normalized `(n+2)`-faces; every codimension-two face is constant at the
basepoint. Its actual topological boundary restriction is based-nullhomotopic
by an explicit affine cone through the higher simplex. On the algebraic side,
applying the normalized class assignment to the singular boundary is proved
to be exactly the alternating sum of the homotopy classes carried by those
faces. Thus descent of the prospective inverse is reduced to one precise
geometric comparison: the class of the common boundary map must agree with
the signed product of its individual face sphere maps. That comparison, and
then the resulting injectivity and general connected-pair theorem, are still
needed before the cap-excision application; no lattice cell is recolored by
this boundary-bridge milestone.

The boundary comparison now has explicit coordinates. The recursive
stick-breaking map from the cube to the simplex takes every upper cube face to
the simplex face of the same index, takes the final lower cube face to the
final simplex face, and sends every other lower face into the codimension-two
skeleton. It also takes the cubical boundary to the simplicial boundary. For a
normalized higher simplex, that skeleton is proved constant at the basepoint,
so all cubical faces become genuine generalized loops. Their oriented cubical
boundary expression is then proved exactly equal to the alternating sum of
the stick-parameterized simplex-face classes, including the final sign. Two
geometric comparisons remain: the generic cubical homotopy-addition relation
must make this shell sum vanish, and the stick-breaking representative must be
compared with the existing cube-homeomorphism representative (or replace it
throughout the normalized-chain construction). This coordinate milestone
therefore adds no unsupported lattice cell.

The cubical homotopy-addition comparison now has a reusable shell abstraction
and its first two supported cases. A map on a cube that collapses the
codimension-two skeleton canonically supplies a based loop on every facet and
an oriented sum of their homotopy classes. Varying one surviving coordinate
proves the opposite-face relation when every transverse facet is constant. For
two surviving coordinate pairs, an explicit convex sweep across their square
relates the bottom-then-right and left-then-top concatenations, giving the
four-face relation with the correct signs. Lean then proves the entire shell
sum is zero in either supported case. The normalized stick-breaking boundary
is packaged as such a shell, its generic and specialized face classes are
identified, and every nonfinal lower face satisfies the shell's ambient
constancy predicate. The unrestricted theorem is still required because all
upper faces of a normalized stick shell may remain nonconstant, so this
milestone does not yet descend the inverse chain map or recolor a lattice cell.

The simplex-side attaching geometry is now explicit as well. For any chosen
face, Lean takes the least barycentric coordinate away from that face,
subtracts it from all the other coordinates, and transfers the removed mass
to the chosen coordinate. This is a continuous retraction onto the
corresponding horn. Straight-line interpolation gives a strong deformation
that fixes the horn pointwise. Restricted to the missing face, it therefore
fixes the complete face boundary and pushes the interior through the union of
all the other faces. After composing with a normalized higher singular
simplex and stick-breaking coordinates, this becomes a homotopy relative to
the cubical boundary from every normalized face loop to its horn attaching
loop. The remaining homotopy-addition step is now the signed decomposition of
that explicit attaching map into the other face loops. The independent
stick-breaking versus cube-homeomorphism representative comparison is also
still needed, so no lattice cell is recolored by this milestone.

The horn attaching map now has a complete finite regional atlas. The missing
face is covered by the closed regions on which a specified barycentric
coordinate is least. On the region indexed by `j`, the attaching map factors
exactly through the remaining face indexed by `i.succAbove j`. Lean constructs
an explicit inverse-coordinate formula and proves that this regional chart is
a homeomorphism with a full standard simplex. Its boundary is characterized
exactly: a chart point is on the simplex boundary precisely when its source is
on the original missing-face boundary or lies in another minimum region.
Distinct regions therefore meet in the codimension-two skeleton, and a
normalized higher simplex sends every such overlap to the basepoint. This is
the local wedge decomposition required by homotopy addition. The remaining
global theorem must convert the map glued across the regional cover into the
correctly signed sum of the regional face classes; the representative
comparison noted above also remains, so the lattice overlay is unchanged.

The same minimum-coordinate geometry now supplies actual horn fillers. On the
ambient simplex, the regions where a fixed coordinate away from the missing
face is least form a finite closed cover. Compatible maps on the horn faces
are evaluated in the corresponding local coordinates; agreement on overlaps
and finite closed-cover gluing make the resulting map continuous. The horn
retraction ensures that this extension restricts to every prescribed face.
Lean then transports the construction through the singular-simplex and
Yoneda equivalences, checks Mathlib's simplicial compatibility equations, and
installs a `KanComplex` instance for the singular simplicial set of every
topological space in the maintained universe. This resolves the singular-Kan
gap documented by the pinned Mathlib API and enables Kan horn filling in the
next simplicial multiplication stage. The signed boundary relation itself is
not yet complete, so the lattice overlay remains unchanged.

That simplicial multiplication stage is now connected to the maintained
cubical homotopy group. Lean proves that normalized singular simplices are
exactly Mathlib pointed simplices: Yoneda turns the constant-face equations
into constancy on the complete simplicial boundary, and boundary
extensionality proves the converse. Given two pointed simplices, their
multiplication horn places them on the first and last of the final three
faces and makes every other prescribed face constant. The singular Kan
instance fills this horn; simplicial identities prove that the omitted middle
face is itself pointed. The resulting `MulStruct` becomes a normalized
higher-simplex boundary whose stick-breaking shell has only its final two
coordinate pairs nonconstant. The previously checked square-shell relation
then proves that the omitted face represents the ordinary product of the two
input cubical homotopy classes. The remaining descent argument must iterate
this three-face multiplication across all faces of an arbitrary normalized
higher-simplex boundary and compare the resulting alternating product with
its full attaching map, so this milestone does not yet recolor a lattice cell.

The three-face relation is now movable. A final-index two-face `RelStruct`
first becomes a one-pair cubical shell, proving that its pointed faces have
the same maintained homotopy class. Lean then reconstructs simplex-index
reversal at the pinned Mathlib revision, including reversal of pointed
simplices, compatible horns, and multiplication structures. Reversing an
arbitrary compatible horn also proves that the opposite of a Kan complex is
Kan. An explicit four-face horn moves a `MulStruct` one position to the left;
reversal gives the right shift. Iterating the right shift carries a
multiplication structure at any face index to the final index, with each step
swapping the outer factors. Commutativity absorbs those swaps, so the existing
final-index cubical product theorem now holds at every index. This supplies
the local relation needed at each stage of the telescoping homotopy-addition
argument. Constructing and summing that full sequence of horns remains, so
the lattice overlay is unchanged.

The full simplicial telescope is now formalized. At stage `q`, a compatible
Kan horn replaces the initial faces by the constant simplex, retains the
later original faces, and produces a new auxiliary face. A second compatible
horn compares that auxiliary face with the distinguished face of the
preceding boundary and the next original face. Its omitted face is proved to
be a `MulStruct` at index `q`, so arbitrary-index multiplication gives the
local identity `previous - original + auxiliary = 0`. The first stage starts
with original face zero, each successor starts with the preceding auxiliary,
and a final `RelStruct` identifies the last auxiliary with the last original
face. Lean packages these as adjacent running terms and applies the finite
alternating-sum telescope to prove that every normalized higher simplex has
zero alternating sum of stick-parameterized face classes. Equivalently, its
complete stick-breaking cubical shell boundary class vanishes. The remaining
bridge is now narrower: compare these stick-breaking representatives with the
cube-homeomorphism representatives used by `normalizedClassChain` (or replace
that coordinate choice throughout).

The chain inverse now descends after making that coordinate choice explicit.
Lean defines the normalized top-simplex assignment directly with the
stick-breaking representatives used by homotopy addition, extends it
additively to singular `(n+2)`-chains, and proves on each `(n+3)`-simplex
generator that its boundary is exactly the alternating stick-face class. The
full telescope makes that value zero, hence the chain map annihilates the
incoming differential. A reusable cycles-modulo-boundaries universal property
then constructs a canonical homomorphism
`H_(n+2)(X) -> pi_(n+2)(X)` for every `(n+1)`-connected space and computes it on
the class of every cycle. The remaining coordinate comparison is no longer
needed for well-definedness; it is needed to identify this map with the
cube-homeomorphism relative Hurewicz comparison already proved surjective and
to establish the two inverse identities. The lattice overlay is therefore
still unchanged.

The relative comparison now also yields a canonical absolute Hurewicz
homomorphism. In every degree `n+2`, the long exact sequence of the singleton
pair identifies `pi_(n+2)(X,x)` multiplicatively with
`pi_rel_(n+2)(X,{x},x)` and identifies `H_(n+2)(X)` with
`H_(n+2)(X,{x})`. Lean transports the additive relative Hurewicz map through
these two equivalences and proves its defining comparison square. Combining
the homotopy equivalence with relative first-nonvanishing surjectivity proves
that `pi_(n+2)(X,x) -> H_(n+2)(X)` is surjective for every `(n+1)`-connected
space. Injectivity remains the missing half of the absolute Hurewicz theorem,
so this milestone does not yet recolor a lattice cell.

The coordinate comparison required by the injectivity argument is now also
formalized. Stick-breaking maps every cube onto its standard simplex, carries
exactly the cubical boundary to the simplicial boundary, and is injective away
from that boundary. Conjugating it by the chosen cube--simplex homeomorphism
therefore preserves exactly the fibres of `I^d -> I^d/partial I^d`. Lean
descends this map to a based self-homeomorphism of the metric sphere and proves
that precomposition by it is injective on homotopy classes. For every normalized
singular simplex, this injective reparameterization sends the cube-coordinate
class used by relative Hurewicz to the stick-coordinate class used by the
simplicial homotopy-addition theorem. The remaining work is the deformation
calculation identifying the descended homology map on Hurewicz representatives;
the lattice overlay is still unchanged.

Bijectivity of the corresponding relative homotopy map yields the next exact
diagonal equivalence; bijectivity of the family from `pi_2(S^2)` onward yields
the full integral diagonal, using the two exact base cases already in Lean. The
remaining bridge is the isomorphism theorem: the point-pair comparison is now
surjective in its first potentially nonzero degree, but injectivity and the
general connected-pair form are still needed to turn the checked connectivity
and homology-excision inputs into relative-homotopy bijectivity. Alternatively,
the full Blakers--Massey homotopy-excision theorem would provide that bridge
directly. This foundation milestone therefore adds no exact purple cells yet.

Higher exact diagonal and stable sphere stems still require additional degree
classification, Freudenthal, higher-Hurewicz, and Hopf-fibration
infrastructure. Incomplete attempts do not color cells.

`DiagonalInduction.lean` now records the exact equivalence between the two
computed diagonal groups `pi_1(S^1)` and `pi_2(S^2)`, and proves that a uniform
family of successive suspension equivalences propagates the integral
calculation through the whole diagonal. A strengthened form starts directly
from the computed `pi_2(S^2)` case, so its suspension hypotheses begin in the
actual Freudenthal isomorphism range. This is a checked reduction of the next
lattice frontier. The earlier unreduced geometric suspension function is
available, but only its identity-preserving property is currently proved at
the group level. Independently, the reduced-suspension construction is now
multiplicative in the exact metric-sphere model. Its checked diagonal reduction
therefore needs only bijectivity of that concrete monoid homomorphism. The two
constructions have not been compared, and Freudenthal bijectivity remains
unproved. A second checked route now uses the canonical relative map induced by
the two-cap cover. Its two pair-connectivity hypotheses and the corresponding
relative-homology excision isomorphism are proved in every required dimension.
It reduces the same diagonal to the remaining first-degree relative Hurewicz
bridge, or equivalently to a direct Blakers--Massey bijectivity theorem for that
map in dimensions at least two. The reductions add no unsupported purple
cells.

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
