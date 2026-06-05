2026-06-04

Status:

- Added `FaithfulPairwiseTouching`, an abbrev for the corrected facet-interior
  touching relation `PairwiseTouchingAlongFacetInteriors`.
- Proved
  `pairwiseTouchingAcrossFacets_of_faithfulPairwiseTouching`.
- Added `chapter14_unconditional`, data-free over `FaithfulPairwiseTouching`.

Blocker for the raw requested implication:

The goal

```lean
PairwiseTouching simplices → PairwiseTouchingAcrossFacets simplices
```

cannot be proved from the current definition of `PairwiseTouching`.  Unfolded,
the pair-level missing implication is

```lean
TouchesAlongFacets S T → TouchesAcrossFacets S T
```

but `TouchesAlongFacets` only says:

```lean
Disjoint S.relInterior T.relInterior ∧
  (S.body ∩ T.body).Nonempty ∧
    ∃ i j, S.facetHyperplane i = T.facetHyperplane j
```

It does not require the actual contact to occur in overlapping relative
interiors of those common facets.  Thus it admits same-side lower-dimensional
contacts.  In dimension 2, take triangles with bases on the same line `y = 0`,
meeting only at one base endpoint, and both opposite vertices above the line:

```text
S = conv{(0,0), (1,0), (0,1)}
T = conv{(1,0), (2,0), (1,1)}
```

Their closed bodies meet and their full relative interiors are disjoint; the
base facet hyperplanes agree.  However the opposite vertices are on the same
strict side of the common base hyperplane, so there is no `SOppSide` certificate
and hence no `TouchesAcrossFacets`.

This is already isolated in the file by
`touchesAlongFacets_across_or_exists_commonFacet_no_facetInteriorOverlap`: raw
`TouchesAlongFacets` either gives across-facet touching, or leaves exactly a
common facet hyperplane with no facet-interior overlap.

The corrected faithful condition is the existing
`TouchesAlongFacetInteriors` / `PairwiseTouchingAlongFacetInteriors`: common
facet hyperplane plus overlapping relative interiors of the two facets.  The
same-side alternative is discharged by
`facetInteriorOverlap_relInterior_inter_nonempty_of_vertices_sSameSide`, giving
the across-facet bridge.

Verification:

```bash
~/.elan/bin/lake env lean ProofsInTheBook/Chapter14.lean
grep -nE '\b(sorry|admit|axiom|native_decide)\b' ProofsInTheBook/Chapter14.lean || true
```

The Lean check exits 0.  The grep returns no matches.  I did not run full
`lake build`.
