## Ch39 Tucker round

Created `ProofsInTheBook/Chapter39Tucker.lean`, importing only
`ProofsInTheBook.Chapter39`.

Closed in the new file:

* `tuckerLemmaStatement_one_base : TuckerLemmaStatement 1`
* `tuckerLemmaStatement_two_base : TuckerLemmaStatement 2`

Both reuse the already verified low-dimensional proofs in `Chapter39.lean`.

Induction skeleton added:

```lean
def TuckerLastCoordinateCollapse (n : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (n + 1) → SignedLabel n,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        ∃ reduced : NonzeroSignedSubset n → SignedLabel (n - 1),
          (∀ X, reduced X.antipode = (reduced X).neg) ∧
            NoComplementaryComparableLabels reduced
```

The formal successor theorem is closed:

```lean
theorem tuckerLemmaStatement_succ_of_lastCoordinateCollapse {n : ℕ}
    (hcollapse : TuckerLastCoordinateCollapse n)
    (htucker : TuckerLemmaStatement n) :
    TuckerLemmaStatement (n + 1)
```

The positive-dimensional induction wrapper is also closed:

```lean
theorem tuckerLemmaStatement_of_lastCoordinateCollapses
    (hcollapse : ∀ n : ℕ, 2 ≤ n → TuckerLastCoordinateCollapse n) :
    ∀ n : ℕ, 1 ≤ n → TuckerLemmaStatement n
```

Precise inductive-step blocker:

```lean
n : ℕ
hn : 2 ≤ n
label : NonzeroSignedSubset (n + 1) → SignedLabel n
hantipodal : ∀ X, label X.antipode = (label X).neg
hno : NoComplementaryComparableLabels label
⊢ ∃ reduced : NonzeroSignedSubset n → SignedLabel (n - 1),
    (∀ X, reduced X.antipode = (reduced X).neg) ∧
      NoComplementaryComparableLabels reduced
```

This is the exact last-coordinate-collapse data needed before the induction
hypothesis can fire.  The missing combinatorial fact is not the final
contradiction: it is the construction of `reduced` from a no-complement
antipodal label in dimension `n + 1`, while handling faces whose original label
uses the top index of `SignedLabel n`.

I also recorded the existing Ky Fan endpoint-packaged version of the same
successor obstruction:

```lean
def TuckerPathEndpointStep (n : ℕ) : Prop :=
  KyFanPrefixPathEndpointDecompositionStatement (n + 1) n
```

with closed bridge:

```lean
theorem tuckerLemmaStatement_succ_of_pathEndpointStep {n : ℕ} (hn : 0 < n)
    (hstep : TuckerPathEndpointStep n) :
    TuckerLemmaStatement (n + 1)
```

The concrete path-following blocker is therefore:

```lean
∀ label : NonzeroSignedSubset (n + 1) → SignedLabel n,
  (∀ X, label X.antipode = (label X).neg) →
    NoComplementaryComparableLabels label →
      Nonempty (KyFanPrefixPathEndpointDecomposition label)
```

Combinatorially, this requires building the Ky Fan path graph for alternating
prefix chains, proving the fixed-point-free antipodal path involution, proving
each path has exactly two endpoints, and classifying endpoints as the two base
endpoints plus positive/negative alternating top chains.

Verification:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter39Tucker.lean
```

passed.  No `lake build` was run.

## Ch39 Tucker round 2

Edited only `ProofsInTheBook/Chapter39Tucker.lean`.

Closed in this round:

```lean
abbrev KyFanEndpointClass {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) :=
  Bool ⊕ (PositivePrefixChainType label ⊕ NegativePrefixChainType label)
```

Endpoint antipode on the two top classes is now formalized:

```lean
positivePrefixChainAntipode
negativePrefixChainAntipode
topPrefixChainEndpointAntipode
topPrefixChainEndpointAntipode_involutive
topPrefixChainEndpointAntipode_fixedPointFree
kyFanEndpointClassAntipode
kyFanEndpointClassAntipode_involutive
kyFanEndpointClassAntipode_fixedPointFree
```

The abstract two-ended path graph induced by an endpoint partner is now closed:

```lean
TwoCyclePath
TwoCycleEndpoint
twoCycleEndpoint_card
twoCycleEndpointClassify
twoCyclePathAntipode
twoCyclePathAntipode_involutive
twoCyclePathAntipode_fixedPointFree
```

The path-decomposition and parity bridge from endpoint pairing is also closed:

```lean
structure KyFanEndpointPairing {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) where
  endpointPartner : KyFanEndpointClass label ≃ KyFanEndpointClass label
  endpointPartner_involutive : Function.Involutive endpointPartner
  endpointPartner_fixedPointFree : ∀ endpoint, endpointPartner endpoint ≠ endpoint
  endpointPartner_comm :
    ∀ endpoint,
      kyFanEndpointClassAntipode label hantipodal (endpointPartner endpoint) =
        endpointPartner (kyFanEndpointClassAntipode label hantipodal endpoint)
  endpointPartner_not_antipodal :
    ∀ endpoint,
      kyFanEndpointClassAntipode label hantipodal endpoint ≠ endpointPartner endpoint
```

Closed bridge:

```lean
kyFanPrefixPathEndpointDecomposition_of_endpointPairing
kyFanPrefixPathEndpointDecompositionStatement_of_endpointPairing
kyFanPrefixParityStatement_of_endpointPairing
tuckerLemmaStatement_of_endpointPairing
```

Successor wrappers:

```lean
def TuckerEndpointPairingStep (n : ℕ) : Prop :=
  KyFanEndpointPairingStatement (n + 1) n

theorem tuckerLemmaStatement_succ_of_endpointPairingStep {n : ℕ} (hn : 0 < n)
    (hstep : TuckerEndpointPairingStep n) :
    TuckerLemmaStatement (n + 1)

theorem tuckerLemmaStatement_of_endpointPairingSteps
    (hstep : ∀ n : ℕ, 2 ≤ n → TuckerEndpointPairingStep n) :
    ∀ n : ℕ, 1 ≤ n → TuckerLemmaStatement n
```

Precise remaining blocker:

```lean
n : ℕ
hn : 2 ≤ n
label : NonzeroSignedSubset (n + 1) → SignedLabel n
hantipodal : ∀ X, label X.antipode = (label X).neg
hno : NoComplementaryComparableLabels label
⊢ Nonempty (KyFanEndpointPairing label hantipodal)
```

Equivalently, the missing object is the actual Ky Fan path-following neighbor
map on endpoint classes:

```lean
endpointPartner : KyFanEndpointClass label ≃ KyFanEndpointClass label
```

with:

```lean
Function.Involutive endpointPartner
∀ endpoint, endpointPartner endpoint ≠ endpoint
∀ endpoint,
  kyFanEndpointClassAntipode label hantipodal (endpointPartner endpoint) =
    endpointPartner (kyFanEndpointClassAntipode label hantipodal endpoint)
∀ endpoint,
  kyFanEndpointClassAntipode label hantipodal endpoint ≠ endpointPartner endpoint
```

This is the real local path graph construction.  It cannot be replaced by an
arbitrary finite pairing: together with the closed bridge above, such a pairing
already implies the target oddness of positive alternating top chains.  The
combinatorial fact still needed is the standard Ky Fan path-following rule
which pairs the two endpoint classes adjacent to the same almost-complementary
alternating prefix chain and proves the four properties above from
`NoComplementaryComparableLabels`.

Verification:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter39Tucker.lean
grep -n "sorry\\|admit\\|axiom" ProofsInTheBook/Chapter39Tucker.lean || true
```

`lake env lean` passed, and the local grep returned no hits.  No `lake build`
was run.

---

Round 6 update: appended the sound Ky Fan parity/Tucker foundations to
`ProofsInTheBook/Chapter39Tucker.lean`, keeping the existing
`tuckerLemmaStatement_of_chain_complementary` base unchanged.

Closed foundations:

```lean
def UpperHemisphere
def Equator
def equatorEmbed
def equatorDrop
def equatorEquiv
def equatorPrefixChain
theorem equatorPrefixChain_projects
```

This is the concrete hemisphere/equator layer:
`B⁺_{r+1}` is `Fin.last r ∉ X.neg`, the equator is
`Fin.last r ∉ X.pos ∧ Fin.last r ∉ X.neg`, and

```lean
equatorEquiv (r) :
  NonzeroSignedSubset r ≃ {X : NonzeroSignedSubset (r + 1) // Equator X}
```

formalizes `∂B⁺_{r+1} ≅ K_r`.  Transported equator prefix chains project back
definitionally through this equivalence to the original `SignedPermutation r`
maximal chain.

Closed non-degenerate Fan parity interface and base:

```lean
def KyFanParityStatement (r m : ℕ) : Prop :=
  1 ≤ r →
    r ≤ m →
      ∀ label : NonzeroSignedSubset r → SignedLabel m,
        (∀ X, label X.antipode = (label X).neg) →
          NoComplementaryComparableLabels label →
            Odd (positiveAlternatingPrefixLabelChains label).card

theorem kyFanParityStatement_one {m : ℕ} (_hm : 1 ≤ m) :
    KyFanParityStatement 1 m
```

The base is now the real `m ≥ 1` base case: the two antipodal vertices give
two alternating one-chains, and antipodality splits them into one positive-first
and one negative-first chain.

Closed label-set `A` / dim-`(n-2)` ridge layer:

```lean
def alternatingLabel
def alternatingLabelSetA
theorem alternatingLabelSetA_card

def AlternatingLabelSetARidge
```

`AlternatingLabelSetARidge` is indexed by `Fin d`, so it has exactly `d`
vertices.  In the Tucker reduction `d = n - 1`, this is the required
dim-`(n-2)` simplex with label set
`A = {+1,-2,+3,...,(-1)^(d-1)d}`.  No full `n`-vertex alternating chain is used.

Closed local sigma deletion count:

```lean
def SigmaDeletionHasAlternatingLabelSet
def sigmaDoorSet

theorem sigmaDoorSet_card_duplicate
theorem sigmaDoorSet_card_opposite
theorem sigmaDoorSet_card_eq_one_iff_extra_opposite
theorem sigma_opposite_extra_gives_complementary_labels
```

For a sigma extending an `A`-ridge:

* if the extra label is `α_k`, deleting either copy gives an `A`-ridge, so the
  sigma degree is `2`;
* if the extra label is `-α_k`, only deleting the extra vertex gives an
  `A`-ridge, so the sigma degree is `1`;
* in the `-α_k` case, the extra vertex and the ridge vertex at `k` have
  complementary labels.

Precise remaining blocker:

The local sigma deletion-count crux is closed.  What remains is the global
handshaking/induction assembly, in particular the geometric coface fact for
`A`-ridges in the hemisphere:

```lean
ρ ⊂ ∂B⁺  -> degree(ρ) = 1
ρ ⊄ ∂B⁺  -> degree(ρ) = 2
```

formalized for dim-`(r-2)` alternating ridges in `B⁺_r`, plus the Fan parity
induction step using this rho-degree manifold property and the equator
equivalence above.

Verification:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter39Tucker.lean
grep -En "\\b(sorry|admit|axiom)\\b" ProofsInTheBook/Chapter39Tucker.lean || true
```

`lake env lean` passed.  The word-boundary grep returned no hits.  No
`lake build` was run.

---

Round 7 update: extended `ProofsInTheBook/Chapter39Tucker.lean` with the
rho-degree/Fan/final-reduction plumbing that can be closed without introducing
empty ridge types.

Closed in this round:

```lean
theorem bipartite_odd_degree_card_eq_mod_two
theorem bipartite_boundary_top_parity

structure RhoDegreeManifoldData
theorem RhoDegreeManifoldData.odd_degree_iff_boundary
theorem RhoDegreeManifoldData.boundary_top_parity

theorem kyFan_parity_step_from_rho_sigma_data
theorem kyFanParityStatement_of_induction_steps
```

This is the finite handshaking core: once the rho side has degree `1` on the
boundary and `2` in the interior, and once the sigma side has odd degree exactly
on alternating/top one-door vertices, the boundary oddness transports to top
oddness mod 2.

Also closed a concrete full-rank represented-ridge local model:

```lean
def UpperPrefixChain
def RepresentedUpperRidgeBoundary
def representedRidgePartner
def representedUpperRidgeLocalCofaces
theorem representedRidgePartner_ne_self
theorem representedUpperRidgeLocalCofaces_card
theorem representedUpperRidgeLocalCofaces_nonempty
```

Here a rho is represented as a signed-permutation full flag with one deleted
rank.  The local partner is the adjacent-rank swap for an internal gap and the
final sign flip for a top gap.  The retained upper coface count is formally
`1` on boundary represented ridges and `2` otherwise.  This is not an empty-type
shortcut; it is a concrete `P,gap` local model.

Closed the final local sigma-to-chain reduction:

```lean
theorem sigmaDoorSet_card_one_gives_complementary_labels
theorem sigmaDoorSet_card_one_gives_chain_complementary_pair
theorem sigmaDoorSet_card_one_gives_ordered_chain_complementary_pair
theorem sigmaDoorSet_card_one_gives_prefixChain_complementary_pair
theorem final_reduction_from_label_set_A_graph
theorem final_reduction_graph_gives_prefixChain_complementary_pair
```

So the final reduction now has a verified shape: odd boundary `A`-ridges plus
rho-degree plus sigma one-door classification yields a one-door top chain, and
the existing sigma-door lemma converts that top chain into same-index
opposite-sign labels on a prefix chain.

Precise remaining blocker:

The remaining unclosed piece is the nonquotiented geometric instantiation:
identify actual dim-`(r-2)` upper-hemisphere ridges with the represented
`P,gap` local model (or quotient represented ridges by equality of punctured
chains), and prove that the graph edge relation used by Fan/final reduction has
exactly the represented local cofaces.  Without that identification, the current
rho theorem is a checked local model plus an explicit `RhoDegreeManifoldData`
interface, not yet the full global manifold theorem over arbitrary ridge
chains.

Verification:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter39Tucker.lean
grep -En "\\b(sorry|admit|axiom)\\b" ProofsInTheBook/Chapter39Tucker.lean || true
```

`lake env lean` passed.  The word-boundary grep returns no proof-placeholder
hits.  No `lake build` was run.

---

Round 8 update: added the actual finite upper-hemisphere label-set-`A` graph
layer in `ProofsInTheBook/Chapter39Tucker.lean`, without empty-type shortcuts.

Closed in this round:

```lean
theorem sigmaDeletionHasAlternatingLabelSet_duplicate_of_door
theorem sigmaDoorSet_card_one_gives_chain_complementary_pair_of_door
theorem sigmaDoorSet_card_one_gives_ordered_chain_complementary_pair_of_door
theorem sigmaDoorSet_card_one_gives_prefixChain_complementary_pair_of_door

theorem SignedPermutation.prefixChain_card
theorem SignedPermutation.prefixChain_injective
theorem SignedPermutation.prefixChain_reindexPositions_swap_gap_succAbove
theorem SignedPermutation.prefixChain_flipSignAt_last_succAbove
theorem representedRidgePartner_deletion_eq

def ActualHemisphereARidge
def ActualHemisphereAChain
def actualHemisphereAEdge
def actualHemisphereABoundary
def actualHemisphereAOneDoor
def actualRidgeOfChainGap
theorem actualRidgeOfChainGap_edge
theorem actualHemisphereAEdge_gives_door
theorem actualRidgeOfChainGap_injective
def actualHemisphereAIncidentDoorEquiv
theorem actualHemisphereA_sigma_degree_card
theorem actualHemisphereA_sigma_degree_one_gives_prefixChain_complementary_pair
theorem actualHemisphereARidge_nonempty_of_boundary_odd
def actualHemisphereRhoDegreeDataOfDegreeCard
```

`ActualHemisphereARidge` is now the genuine finite type of ordered punctured
upper-hemisphere chains whose retained label set is `A`; it is not the empty
positive-alternating full-chain type.  `ActualHemisphereAChain` is the finite
type of upper maximal chains with an ordered `A` deletion.  The incidence
relation is actual deletion equality:

```lean
actualHemisphereAEdge rho sigma :=
  ∃ gap, ∀ a, rho.1 a = sigma.1.prefixChain (gap.succAbove a)
```

The sigma side is closed for the actual graph:

```lean
Fintype.card {rho // actualHemisphereAEdge rho sigma}
  = (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card
```

and degree-one actual top chains now produce the required same-index,
opposite-sign pair on their prefix chain via the set-based door lemma.

Precise remaining blocker:

The left rho-degree enumeration is still not closed:

```lean
∀ rho : ActualHemisphereARidge label,
  Fintype.card {sigma : ActualHemisphereAChain label //
      actualHemisphereAEdge rho sigma}
    = if actualHemisphereABoundary rho then 1 else 2
```

The missing proof is the global coface classification for an arbitrary actual
ridge.  Given a witness `(P, gap)` for `rho`, one must prove every incident
upper chain is either `P` or `representedRidgePartner P gap`, prove the partner
is an upper `A`-chain exactly in the non-boundary case, and prove boundary
coincides with the represented condition
`gap = Fin.last _ ∧ P.order.symm (Fin.last _) = Fin.last _`.  The local
partner preserves the punctured deletion (`representedRidgePartner_deletion_eq`)
and the sigma-side quotient by actual ridge equality is done; the remaining
work is this coface-exhaustion theorem.

Because that enumeration is still open, the equator induction and final
`∀ n, TuckerLemmaStatement n` assembly are not closed in this round.

Verification:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter39Tucker.lean
grep -En "\\b(sorry|admit|axiom)\\b" ProofsInTheBook/Chapter39Tucker.lean
```

`lake env lean` exits 0.  The grep exits 1 with no hits.  No `lake build` was
run.

---

Round 9 blocker before code edits:

The requested final theorem

```lean
theorem tuckerLemma : ∀ n, TuckerLemmaStatement n
```

is inconsistent with the current checked definitions in `Chapter39.lean`.
The imported namespace already contains

```lean
not_tuckerLemmaStatement_zero : ¬ TuckerLemmaStatement 0
```

so the requested theorem would immediately imply `False`:

```lean
import ProofsInTheBook.Chapter39Tucker

namespace ProofsInTheBook.Chapter39

#check not_tuckerLemmaStatement_zero

example (h : ∀ n, TuckerLemmaStatement n) : False :=
  not_tuckerLemmaStatement_zero (h 0)

end ProofsInTheBook.Chapter39
```

Verification run:

```bash
/data/home/xhuan5/.elan/bin/lake env lean /tmp/ch39_impossible.lean
```

This exits 0 and prints:

```text
ProofsInTheBook.Chapter39.not_tuckerLemmaStatement_zero : ¬TuckerLemmaStatement 0
```

Thus the exact `∀ n` target cannot be closed without changing the statement
to the positive-dimensional form, e.g. `∀ n, 1 ≤ n → TuckerLemmaStatement n`,
or changing `TuckerLemmaStatement 0`.  I did not add an inconsistent theorem,
an axiom, `sorry`, or an empty-type shortcut.

---

Round 10 update:

Edited `ProofsInTheBook/Chapter39Tucker.lean`.

Closed the requested coface-exhaustion layer for represented punctured flags:

```lean
theorem deletion_gap_eq_of_prefixChain_eq
theorem eq_or_flipSignAt_last_of_deletion_eq
theorem eq_or_reindex_swap_of_internal_deletion_eq
theorem eq_or_representedRidgePartner_of_deletion_eq
```

This proves the actual cover classification: a coface with the same deleted
flag is either the original `P` or `representedRidgePartner P gap`.  Internally,
the proof fixes all non-gap atoms and shows the two remaining single-coordinate
covers are exactly the adjacent swap; at the top gap it shows the only freedom
is the final sign flip.

Closed the hemisphere filter and actual rho-degree instantiation:

```lean
theorem representedRidgePartner_upperPrefixChain
theorem representedRidgePartner_not_upperPrefixChain_of_boundary
theorem actualHemisphereABoundary_iff_represented
def actualHemisphereAIncidentRepresentedCofaceEquiv
theorem actualHemisphereA_rho_degree_card
def actualHemisphereRhoDegreeData
```

Also corrected `ActualHemisphereAChain` to mean “has a deletion whose retained
label set is `A`”, matching the existing unordered `ActualHemisphereARidge` and
`sigmaDoorSet` definitions.  With that correction, the actual incident cofaces
of any `rho : ActualHemisphereARidge label` are equivalent to the represented
local cofaces, and the degree is:

```lean
Fintype.card {sigma : ActualHemisphereAChain label //
    actualHemisphereAEdge rho sigma}
  = if actualHemisphereABoundary rho then 1 else 2
```

Closed the unordered sigma-door parity classifier:

```lean
theorem sigmaDeletionHasAlternatingLabelSet_retained_image_eq
theorem sigmaDeletionHasAlternatingLabelSet_retained_injOn
theorem sigmaDoorSet_card_duplicate_of_door
theorem sigmaDoorSet_card_opposite_of_door
theorem sigmaDoorSet_odd_iff_card_one_of_door
theorem actualHemisphereA_sigma_odd_degree_iff_oneDoor
```

Precise remaining blocker:

The coface exhaustion is no longer the blocker.  The remaining blocker is the
equator oddness interface.  The current finite graph uses
`ActualHemisphereARidge` with unordered label set `A`:

```lean
∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a
```

but the available induction statement

```lean
KyFanParityStatement r m
```

counts `positiveAlternatingPrefixLabelChains`, whose definition requires the
label indices to be strictly increasing along the prefix-chain order.  Thus it
does not directly imply

```lean
Odd (Fintype.card {rho : ActualHemisphereARidge label //
  actualHemisphereABoundary rho})
```

for the unordered `A`-ridge type now used by the actual coface graph.

To finish `tuckerLemma_pos`, one of these two interface changes is needed:

1. Prove a new equator parity statement for unordered label-set-`A` ridges, and
   use that as `hboundaryOdd`; or
2. Redesign the actual graph around ordered `A`-ridges and ordered door sets,
   then redo the sigma-side incidence count for ordered deletions.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter39Tucker.lean
```

exits 0.  No `lake build` was run.  No `sorry`, `admit`, or `axiom` was added.

---

Round 12 blocker audit:

I did not close the two requested theorems because the current formal interfaces
do not match the handoff's claimed wiring step.

1. `equatorBoundaryCardBridge`

The requested bridge is:

```lean
Fintype.card
  {rho : ActualHemisphereARidge label // actualHemisphereABoundary rho}
=
(positiveAlternatingPrefixLabelChains (equatorRestrictedLabel label)).card
```

But `ActualHemisphereARidge` currently stores unordered label-set-`A` ridges:

```lean
∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a
```

while `positiveAlternatingPrefixLabelChains` is the ordered predicate:

```lean
StrictMono fun i => (label (P.prefixChain i)).index
∀ i, (label (P.prefixChain i)).positive = decide (Even i.val)
```

The missing subgoal is exactly:

```lean
d : ℕ
label : NonzeroSignedSubset (d + 1) → SignedLabel d
hantipodal : ∀ X, label X.antipode = (label X).neg
hno : NoComplementaryComparableLabels label
rho : ActualHemisphereARidge label
hb : actualHemisphereABoundary rho
⊢ PositiveAlternatingPrefixLabels
    (equatorRestrictedLabel label)
    <the signed permutation obtained by dropping rho to the equator>
```

The available data gives only that the `d` retained labels are the set
`{+1,-2,+3,...}`, not that their indices increase in prefix-chain order.
So the advertised `equatorEquiv` transport is not sufficient by itself.

2. KyFan induction step

The requested step is:

```lean
∀ r m, 1 ≤ r → r + 1 ≤ m →
  KyFanParityStatement r m → KyFanParityStatement (r + 1) m
```

The current actual hemisphere graph is specialized to:

```lean
label : NonzeroSignedSubset (d + 1) → SignedLabel d
```

and the degree facts are specialized to the full label set
`A : Fin d → SignedLabel d`.  They do not instantiate the general fixed-`m`
Fan step, where the upper-hemisphere labels have type:

```lean
label : NonzeroSignedSubset (r + 1) → SignedLabel m
```

and the ridge label set should be the first `r` alternating labels embedded in
`SignedLabel m`.

Therefore the current hard-core data proves the diagonal Tucker reduction only
after an external `KyFanParityStatement d d`; it does not yet provide the
general induction step needed by `kyFanParityStatement_of_induction_steps`.

Verification:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter39Tucker.lean
grep -En "\b(sorry|admit|axiom)\b" ProofsInTheBook/Chapter39Tucker.lean
```

The grep prints nothing.  The Lean command exits 0 with only the existing
lint/deprecation warnings.  I did not run `lake build`.

---

Round 11 update:

Edited `ProofsInTheBook/Chapter39Tucker.lean`.

Added the no-complementary variant of the final Tucker reduction:

```lean
theorem tuckerLemmaStatement_of_chain_complementary_of_no_complementary
```

Added the equator restriction plumbing through `equatorEquiv`:

```lean
theorem signedSubsetEquatorEmbed_antipode
theorem equatorEmbed_antipode
def equatorRestrictedLabel
theorem equatorRestrictedLabel_antipodal
theorem equatorRestrictedLabel_noComplementary
theorem equatorRestrictedLabel_positiveAlternating_odd
```

So a diagonal induction hypothesis

```lean
KyFanParityStatement d d
```

now applies cleanly to the equator-restricted labeling and proves oddness of

```lean
(positiveAlternatingPrefixLabelChains (equatorRestrictedLabel label)).card
```

Added the actual-graph closing layer from boundary oddness to the desired chain
complementary pair and then to Tucker:

```lean
theorem actualHemisphereA_boundary_odd_gives_prefixChain_complementary_pair
def ActualHemisphereBoundaryOddStatement
theorem actualHemisphereBoundaryOdd_of_equator_card_bridge
theorem tuckerLemmaStatement_succ_of_actualHemisphere_boundary_odd
theorem tuckerLemmaStatement_succ_of_equator_boundary_card_bridge
```

Precise remaining blocker:

The whole post-boundary pipeline is now closed.  The exact unproved bridge is
the cardinal identification between the actual boundary ridges and the
equator-restricted positive alternating chains:

```lean
def EquatorBoundaryCardBridgeStatement (d : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (d + 1) → SignedLabel d,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Fintype.card
            {rho : ActualHemisphereARidge label //
              actualHemisphereABoundary rho} =
          (positiveAlternatingPrefixLabelChains
            (equatorRestrictedLabel label)).card
```

This is exactly the represented/actual boundary parity mismatch: boundary
`ActualHemisphereARidge` still records an unordered label-set-`A` ridge
(`∀ a, ∃ t, label (rho t) = alternatingLabel a`), while
`positiveAlternatingPrefixLabelChains` records the ordered prefix-chain
condition.  With `EquatorBoundaryCardBridgeStatement d`, the theorem
`tuckerLemmaStatement_succ_of_equator_boundary_card_bridge` already gives
`TuckerLemmaStatement (d + 1)`.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter39Tucker.lean
grep -En "\b(sorry|admit|axiom)\b" ProofsInTheBook/Chapter39Tucker.lean
```

The Lean command exits 0, with only existing lint/deprecation warnings.  The
grep command prints nothing.  No `lake build` was run.

---

Round 13 update:

Read `HANDOFF/TASK_Ch39_Tucker_r13.md` and rechecked the bridge against the
current `Chapter39Tucker.lean`.

Current verified state:

* `ActualHemisphereARidge` is still the unordered label-set-`A` ridge:

```lean
∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a
```

at `ProofsInTheBook/Chapter39Tucker.lean:2014-2021`.

* The bridge still compares this unordered boundary count to
  `positiveAlternatingPrefixLabelChains (equatorRestrictedLabel label)`, whose
  predicate is ordered by chain position:

```lean
StrictMono fun i => (label (P.prefixChain i)).index
∀ i : Fin n, (label (P.prefixChain i)).positive = decide (Even i.val)
```

from `TuckerLemmaCore.lean:963-966`, used by the finset at
`TuckerLemmaCore.lean:1979-1983`.

* The post-boundary pipeline is still closed: with
  `ActualHemisphereBoundaryOddStatement d`, the theorem
  `tuckerLemmaStatement_succ_of_actualHemisphere_boundary_odd` gives
  `TuckerLemmaStatement (d + 1)`; with the current bridge hypothesis,
  `tuckerLemmaStatement_succ_of_equator_boundary_card_bridge` gives the same.
  See `Chapter39Tucker.lean:2517-2531`.

Option A status:

I do not see a valid route to prove "unordered label-set `A` automatically
means positive alternating in chain order" from
`NoComplementaryComparableLabels`.  The available no-complement lemmas only
control comparable pairs with the same absolute index: they force equal signs
for equal index and exclude equal-index opposite signs.  They do not constrain
two comparable vertices whose labels have different indices, so a nonmonotone
permutation of the distinct labels in `A` does not locally create a
complementary comparable pair.  Thus the desired auto-ordering step would need
additional global path/parity information; using it here would be circular with
the Tucker conclusion.

Option B status:

The direct "unordered equator count is odd" replacement is also not compatible
with the current parity interface.  `KyFanParityStatement d d` proves oddness
only for one fixed ordered sign/index pattern, namely
`positiveAlternatingPrefixLabelChains`; it is equivariant under signed
permutations of the label coordinates that commute with `SignedLabel.neg`.
Consequently the same parity statement applies to every fixed ordering of the
label set `A`.  The unordered label-set-`A` count is the disjoint union over all
these order patterns.  For `d ≥ 2`, this introduces an even factorial factor,
so the unordered count should not be expected to be odd from the current
statement.  This is consistent with the current file: the sigma-degree side is
closed for unordered doors (`sigmaDoorSet_odd_iff_card_one_of_door`,
`actualHemisphereA_sigma_odd_degree_iff_oneDoor`), but the equator parity side
available at `Chapter39Tucker.lean:397-404` is ordered.

Precise remaining goal if the existing interface is kept:

```lean
theorem equatorBoundaryCardBridge :
    ∀ d : ℕ, EquatorBoundaryCardBridgeStatement d
```

expanded at `Chapter39Tucker.lean:2497-2505`, this is exactly the false
ordered/unordered cardinal identification unless an additional orientation or
weighting layer is added.

I left `ProofsInTheBook/Chapter39Tucker.lean` unchanged rather than replacing
one mismatch by another.  The file still verifies with:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter39Tucker.lean
grep -RIn "\bsorry\b\|\badmit\b\|\baxiom\b" ProofsInTheBook/Chapter39Tucker.lean
```

The Lean command exits 0 with only existing warnings; the grep prints nothing.

---

Round 15 update:

Edited `ProofsInTheBook/Chapter39Tucker.lean`.

Closed the unordered equator bridge:

```lean
def EquatorActualARidge
noncomputable def equatorBoundaryARidgeEquiv
theorem equatorBoundaryCardBridge
```

`EquatorBoundaryCardBridgeStatement` now has RHS

```lean
Fintype.card (EquatorActualARidge (equatorRestrictedLabel label))
```

not `positiveAlternatingPrefixLabelChains`.  The bridge is a direct
`equatorEquiv` transport between boundary `ActualHemisphereARidge` objects and
the dropped equator objects; no ordered-prefix conversion is used.

I also added the unordered parity interface and the exact conditional final
wiring:

```lean
def KyFanUnorderedParityStatement (d : ℕ) : Prop

theorem actualHemisphereBoundaryOdd_of_equator_card_bridge
theorem tuckerLemmaStatement_succ_of_equator_boundary_card_bridge

theorem tuckerLemma_pos_of_kyFanUnordered
    (hKy : ∀ d : ℕ, 1 ≤ d → KyFanUnorderedParityStatement d) :
    ∀ n : ℕ, 1 ≤ n → TuckerLemmaStatement n
```

The remaining unclosed target is exactly:

```lean
∀ d : ℕ, 1 ≤ d → KyFanUnorderedParityStatement d
```

Expanded at dimension `d`:

```lean
∀ label : NonzeroSignedSubset d → SignedLabel d,
  (∀ X, label X.antipode = (label X).neg) →
    NoComplementaryComparableLabels label →
      Odd (Fintype.card (EquatorActualARidge label))
```

This is not supplied by the currently proven rho/sigma degree facts.  Those
facts prove the Tucker reduction

```lean
Odd boundary ActualHemisphereARidge count
  → ∃ one-door sigma
  → complementary prefix-chain pair
```

but they do not prove the unordered equator count is odd.  Under a hypothetical
no-complement label, the same rho/sigma graph actually gives "one-door sigma
count is zero, hence boundary count is even" unless the separate Ky Fan
equator parity supplies the odd boundary input.  So the unordered bridge is now
clean, but `tuckerLemma_pos` still requires a real proof of
`KyFanUnorderedParityStatement`.

Verification:

```bash
PATH=$HOME/.elan/bin:$PATH timeout 180 lake env lean ProofsInTheBook/Chapter39Tucker.lean
```

exits 0 with only pre-existing warnings.  No `lake build` was run.
No `lake build` was run.

---

2026-06-04 update:

Closed the remaining Chapter 39 Tucker chain in
`ProofsInTheBook/Chapter39Tucker.lean`.

New completed endpoints:

```lean
theorem fan_sphere_parity
theorem kyFanUnordered_all
theorem tuckerLemma_pos
```

The path now uses the already-proved
`simplex_deletionParity_of_noOpposite` for the local deletion parity feeding
`ball_parity`, then proves the sphere induction through the equator/full-chain
bridges:

```lean
equatorActualAlt_card_eq_full_alt_pos
upper_top_card_eq_full_alt_pos
equatorActualARidge_card_eq_full_alt_pos
```

I also added the boundary signed-permutation drop/extend infrastructure needed
to identify equator ridges with full alternating signed-permutation chains.

Verification run:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter39Tucker.lean
grep -nE '\b(sorry|axiom|admit)\b' ProofsInTheBook/Chapter39Tucker.lean
```

The Lean command exits `0` with warnings only.  The grep prints nothing.
No `lake build` was run.

---

Round 19 continuation:

Extended the sign-sequence reduction to the full self-contained local deletion
classifier.

New checked theorems include:

```lean
labelSeq_deletionParity_of_injective_of_noOpposite
labelSeq_deletionParity_of_not_injective_of_noOpposite
labelSeq_deletionParity_of_noOpposite
simplex_deletionParity_of_noOpposite
```

This closes both local cases from the addendum:

* Case B distinct absolute values: sort by `(label ·).index` with
  `Tuple.sort`, prove the sorted index map is `StrictMono`, and apply
  `signSeqDeletionParity`.
* Case A repeated absolute value under `NoOppositeLabelSeq`: non-injective
  image-card analysis reduces any nonempty door set to the fixed-idx duplicate
  door classifier, so the deletion count is `0` or `2`; `IsAltPos` and
  `IsAltNeg` are both impossible.

I also added the self-contained upper-hemisphere graph and proved the formal
ball handshaking step:

```lean
ActualHemisphereAltRidge
ActualHemisphereAltChain
actualHemisphereAlt_rho_degree_card
actualHemisphereAlt_sigma_degree_card
actualHemisphereAlt_sigma_odd_degree_iff_top
ball_parity
```

and the self-contained equator/boundary bridge:

```lean
EquatorActualAltRidge
equatorBoundaryAltRidgeEquiv
equatorBoundaryAltCardBridge
```

Still not closed:

```lean
fan_sphere_parity
kyFanUnordered_all
tuckerLemma_pos
```

The remaining formal gap is now the sphere split, not the local deletion lemma:
prove that for an antipodal labeling, the upper-hemisphere count
`Alt⁺(B_r⁺) ∪ Alt⁻(B_r⁺)` supplied by `ball_parity` is parity-equivalent to
the full-sphere positive alternating count.  `SignedPermutation.antipode` and
`prefixChain_antipode` are available in `Chapter39.lean`; the needed next
lemmas are the self-contained analogues of the existing ordered
`positiveAlternatingPrefixLabels_antipode_iff` and the upper/lower split by the
sign of the last coordinate.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter39Tucker.lean
```

exits `0` with warnings only.  No `lake build` was run.  No `sorry`, `admit`,
or `axiom` was added.

---

Round 14 update:

Read `HANDOFF/TASK_Ch39_Tucker_r14.md` and tested the requested ordered-ridge
restructure.

I did not leave the ordered rewrite in the file.  The obstruction is in the
sigma-degree side, not in the rho coface count.

Precise break if only `ActualHemisphereARidge` is changed to

```lean
∀ a : Fin d, label (rho a) = alternatingLabel a
```

while keeping the current sigma door interface:

```lean
def actualRidgeOfChainGap ...
```

has to build an `ActualHemisphereARidge` from

```lean
gap.2 : SigmaDeletionHasAlternatingLabelSet
  (fun i => label (sigma.1.prefixChain i)) gap.1
```

For the new ordered ridge field the local goal becomes

```lean
label (sigma.1.prefixChain (gap.1.succAbove a)) = alternatingLabel a
```

but the available hypothesis is only

```lean
∃ t : Fin (d + 1), t ≠ gap.1 ∧
  label (sigma.1.prefixChain t) = alternatingLabel a
```

so the existing `actualHemisphereAIncidentDoorEquiv` and hence
`actualHemisphereA_sigma_degree_card` no longer follow.

I also checked the natural repair "make the sigma doors ordered too".  That
does not preserve the final one-door classifier.  For `d = 3`, a full label
sequence

```text
[A0, A1, A0, A2]
```

has an ordered alternating deletion by deleting the third entry, and exactly
one ordered alternating deletion, but the repeated label is same-sign, not an
opposite/complementary label.  Thus ordered-door odd degree does not imply the
complementary pair used by
`actualHemisphereA_sigma_degree_one_gives_prefixChain_complementary_pair`.

Consequently the requested bridge can be made an identity only for a stricter
ordered boundary object, but that stricter object is no longer compatible with
the current sigma-degree / one-door reduction.  The current file was restored
to the previously verified unordered graph state rather than left inconsistent.

No `sorry`, `admit`, or `axiom` was added.  No `lake build` was run.
Verification after restoring the baseline:

```bash
PATH=$HOME/.elan/bin:$PATH timeout 900 lake env lean ProofsInTheBook/Chapter39Tucker.lean
grep -En "\b(sorry|admit|axiom)\b" ProofsInTheBook/Chapter39Tucker.lean
```

The Lean command exits 0 with only existing warnings; the grep prints nothing.

---

Round 16 audit:

Read `HANDOFF/TASK_Ch39_Tucker_r16.md` and rechecked the requested
two-parameter induction against the existing formal interfaces.

I did not add `kyFanUnordered_all`, because the two possible readings split:

1. If `KyFanUnorderedParityStatement2 r m` is the fixed label-set-`A_r`
   count in `SignedLabel m`, the proposed base case is false.  Already for
   `r = 1, m = 2`, an antipodal no-complement labeling of `K_1` can label the
   two vertices by `+2,-2`; the fixed `A_1 = {+1}` count is `0`, not odd.
   This is exactly the m/r bookkeeping failure.

2. If the two-parameter statement instead counts all positive alternating
   unordered maximal chains (the only reading whose `r=1, any m>=1` base is
   true, and whose `m=r` instance collapses to the fixed `A_r` count), then the
   existing fixed-`A` rho/sigma package is not enough by itself.  One still
   needs the standard local sigma-door classifier for arbitrary positive
   alternating deletions:

   ```lean
   Odd (card {deletions leaving a positive alternating r-ridge})
     ↔ top chain is positive- or negative-alternating
   ```

   The proved lemma

   ```lean
   actualHemisphereA_sigma_odd_degree_iff_oneDoor
   ```

   is only the fixed-`A` unordered classifier.  It classifies deletions leaving
   the concrete label set `{+1,-2,+3,...}` in `SignedLabel d`; it does not
   classify arbitrary increasing index sets in `SignedLabel m`.

I verified the current file still checks:

```bash
~/.elan/bin/lake env lean ProofsInTheBook/Chapter39Tucker.lean
```

It exits `0` with only the pre-existing warnings.  No `lake build` was run.
No `sorry`, `admit`, or `axiom` was added.

---

Round 17 update:

Implemented and checked the fixed-`idx` generalization in
`ProofsInTheBook/Chapter39Tucker.lean`.

Added:

```lean
alternatingLabelOf
alternatingLabelSetOf
SigmaDeletionHasAlternatingLabelSetOf
sigmaDoorSetOf
ActualHemisphereIdxRidge
ActualHemisphereIdxChain
EquatorActualIdxRidge
actualHemisphereIdx_rho_degree_card
actualHemisphereIdx_sigma_degree_card
actualHemisphereIdx_sigma_odd_degree_iff_oneDoor
equatorBoundaryIdxRidgeEquiv
KyFanUnorderedParityStatement2
```

The rho coface count is now index-agnostic exactly as expected:

```lean
actualHemisphereIdx_rho_degree_card :
  Fintype.card {sigma : ActualHemisphereIdxChain idx label //
    actualHemisphereIdxEdge rho sigma}
  = if actualHemisphereIdxBoundary rho then 1 else 2
```

The fixed-`idx` sigma classifier is also generalized.  The important correction
for `m > r`: the extra label may lie outside `idx`; in that case the door count
is still `1`.  Thus the generalized proof splits into same-sign duplicate
(`2`) versus not-same-sign-duplicate (`1`), rather than only duplicate/opposite.

I did not close `kyFanUnordered_all` / `tuckerLemma_pos`.  The remaining missing
formal lemma is the aggregate insertion classifier over all increasing
`idx : Fin r -> Fin m`:

```lean
Odd (card { (idx, gap) // deletion gap leaves the positive alternating idx-ridge })
  ↔ the upper top chain is positive- or negative-alternating
```

The fixed-`idx` classifier now proved here is necessary but not sufficient for
that aggregate statement.  It tells the parity of doors for one prescribed
index set; the Fan induction needs the parity after summing over all
`r`-subsets of `Fin m`.

Verification:

```bash
PATH=$HOME/.elan/bin:$PATH timeout 180 lake env lean ProofsInTheBook/Chapter39Tucker.lean
grep -En "\b(sorry|admit|axiom)\b" ProofsInTheBook/Chapter39Tucker.lean
```

The Lean command exits `0` with only existing warnings.  The grep prints
nothing.  No `lake build` was run.

---

Round 18 partial:

Read `HANDOFF/TASK_Ch39_Tucker_r18.md` and
`HANDOFF/CH39_FAN_PIVOT_PROOF.md`.

Implemented the self-contained alternating-simplex layer in
`ProofsInTheBook/Chapter39Tucker.lean`:

```lean
alternatingNegLabelSetOf
simplexLabelSet
IsAltPos
IsAltNeg
IsAltPos.idx_unique
IsAltNeg.idx_unique
```

`IsAltPos` / `IsAltNeg` now take only the simplex enumeration and the label
map.  The index map is an internal witness:

```lean
∃ idx : Fin k → Fin m,
  StrictMono idx ∧ simplexLabelSet label sigma = alternatingLabelSetOf idx
```

and similarly for the negative-first set.  I also proved that this internal
`idx` is unique when two witnesses exist, using `StrictMono.range_inj`; this is
the formal version of "read the index set off the simplex".

I did not close `kyFanUnordered_all` / `tuckerLemma_pos`.  The exact missing
lemma is still the self-contained local deletion classifier, not the old
fixed-`idx` `sigmaDoorSetOf` classifier:

```lean
Odd (card {j : Fin (k+1) //
  IsAltPos label (fun a => sigma (j.succAbove a))})
↔
  IsAltPos label sigma ∨ IsAltNeg label sigma
```

under the no-opposite-label hypothesis for the `(k+1)` labels.  The currently
proved `sigmaDoorSetOf_*` lemmas classify deletion doors for one prescribed
fixed `idx`; they do not give the insertion cases where the extra label has a
new absolute index and another deletion becomes alternating with a different
internal `idx`.  That is precisely the artifact identified in r18.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter39Tucker.lean
```

exits `0` with only pre-existing warnings.  No `lake build` was run.  No
`sorry`, `admit`, or `axiom` was added.

---

Round 19 partial:

Read `HANDOFF/TASK_Ch39_Tucker_r19.md` and the ADDENDUM in
`HANDOFF/CH39_FAN_PIVOT_PROOF.md`.

Implemented and checked the standalone pure sign-sequence layer requested in
`ProofsInTheBook/Chapter39Tucker.lean`:

```lean
signSeqAltPos
signSeqAltNeg
signSeqDoor
signSeqDoorSet
signSeqDoor_iff_bad_cut
signSeqDoor_iff_remove_altPos
signSeqDoorSet_card_le_two
signSeqDoorSet_card_eq_zero_or_one_or_two
signSeqDeletionParity
```

The proved parity theorem is exactly the Bool/door version:

```lean
theorem signSeqDeletionParity {k : ℕ} (s : Fin (k + 1) → Bool) :
  Odd (signSeqDoorSet s).card ↔ signSeqAltPos s ∨ signSeqAltNeg s
```

It also proves the deletion characterization

```lean
signSeqDoor s i ↔ signSeqAltPos (fun a : Fin k => s (i.succAbove a))
```

and the `D ∈ {0,1,2}` card statement.

I also added the first formal reduction layer for Case B, where the simplex
has already been sorted by absolute label and the index map is strictly
increasing:

```lean
IsAltPosLabelSeq
IsAltNegLabelSeq
labelSeqAltPosDeletionSet
sortedLabelSeq_deletionParity
simplexAltPosDeletionSet
sortedSimplex_deletionParity
```

The sorted simplex theorem is:

```lean
theorem sortedSimplex_deletionParity
  {idx : Fin (k + 1) → Fin m} (hidx : StrictMono idx)
  {sgn : Fin (k + 1) → Bool}
  (hlabel :
    ∀ a : Fin (k + 1),
      label (sigma a) = { positive := sgn a, index := idx a }) :
  Odd (simplexAltPosDeletionSet label sigma).card ↔
    IsAltPos label sigma ∨ IsAltNeg label sigma
```

So the standalone sign-sequence theorem is closed, and the distinct-absolute
case is reduced to it for an already sorted enumeration.

Not closed yet:

```lean
-- arbitrary, unsorted simplex with no opposite labels
Odd (simplexAltPosDeletionSet label sigma).card ↔
  IsAltPos label sigma ∨ IsAltNeg label sigma
```

The remaining formal work is exactly the addendum's two missing transport
steps: Case A repeated absolute values (even count by multiplicity), and Case B
sorting an arbitrary distinct-absolute simplex by `Finset.orderEmbOfFin` and
transporting deletion indices through that ordering.  Consequently I did not
close `ball_parity`, `fan_sphere_parity`, `kyFanUnordered_all`, or
`tuckerLemma_pos`.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter39Tucker.lean
grep -En "\b(sorry|admit|axiom)\b" ProofsInTheBook/Chapter39Tucker.lean
```

The Lean command exits `0` with existing warnings.  The grep prints nothing.
No `lake build` was run.

---

Round 20 close:

Closed the remaining Chapter 39 Tucker chain in
`ProofsInTheBook/Chapter39Tucker.lean`.

Completed endpoints:

```lean
theorem fan_sphere_parity
theorem kyFanUnordered_all
theorem tuckerLemma_pos
```

The proof path now runs through the proven local deletion classifier
`simplex_deletionParity_of_noOpposite`, the handshaking lemma `ball_parity`,
the sphere induction `fan_sphere_parity`, and the `m = d` equator/A-ridge
bridge into `KyFanUnorderedParityStatement`.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter39Tucker.lean
grep -nE '\b(sorry|axiom|admit)\b' ProofsInTheBook/Chapter39Tucker.lean
```

The Lean command exits `0` with warnings only.  The grep prints nothing.
No `lake build` was run.
