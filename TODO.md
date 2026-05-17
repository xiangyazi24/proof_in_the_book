# TODO: Remaining Premises to Prove

All 40 chapters compile with 0 `sorry` and 0 `axiom`. However, 8 chapters
take hard mathematical facts as explicit premises (function parameters)
rather than proving them internally. Each premise marks the mathematical
core of its chapter's book proof. This file tracks them for future work.

## Priority 1: Provable with current Mathlib

### Ch33: Hall's condition for Latin square complement
- **File:** `Chapter33.lean` line 42
- **Premise:** `hHall_verified : ∀ S, S.card ≤ (S.biUnion available).card`
- **What it says:** The complement bipartite graph (columns → unused symbols) satisfies Hall's marriage condition.
- **How to prove:** Double counting. Each column has `n - r` available symbols (where `r` rows are filled). The bipartite graph between k columns and their available symbols has at least k distinct symbols, because each symbol appears in exactly `n - r` columns (by Latin square regularity). This is a `≥ k` bound from regularity of the bipartite graph.
- **Estimated effort:** ~40 lines. Need to formalize the regularity argument.

### Ch03: Sylvester smoothness core
- **File:** `Chapter03.lean` line 168
- **Premise:** `hsmooth : n.descFactorial k ∉ (k+1).smoothNumbers`
- **What it says:** Among k consecutive integers n, n-1, ..., n-k+1, at least one has a prime factor > k.
- **How to prove:** The book uses Legendre's formula to bound p-adic valuations. For each prime p ≤ k, its total contribution to the product is bounded. The total smooth part cannot account for the full product. Key Mathlib tools: `Nat.factorization`, `Nat.descFactorial_eq_prod_range`.
- **Estimated effort:** ~80 lines. The prime factorization bookkeeping is the main work.

### Ch11: Slopes count from rotating calipers
- **File:** `Chapter11.lean` line 97
- **Premise:** `hslopes : points.card - 1 ≤ (slopesDeterminedBy points).card`
- **What it says:** n non-collinear points determine at least n-1 distinct slopes.
- **How to prove:** Ungar's rotating-calipers argument: rotate a directed line through all angles. At each of n-1 "events" (line passes through a new pair), a new slope appears. Needs convex hull infrastructure.
- **Estimated effort:** ~120 lines. Convex hull + angular sweep formalization.

### Ch31: Cayley's upper bound (Prüfer encoding)
- **File:** `Chapter31.lean` line 126
- **Premise:** `hCayley : Fintype.card (LabeledTree n) ≤ n ^ (n-2)`
- **What it says:** There are at most n^{n-2} labeled trees on n vertices.
- **How to prove:** Construct the Prüfer encoding: repeatedly remove the smallest leaf and record its neighbor. This gives an injective map to sequences. Needs well-founded recursion on tree size, `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial` for leaf extraction.
- **Estimated effort:** ~150 lines. The recursive algorithm + injectivity proof.

### Ch34: Kernel-perfect extension step
- **File:** `Chapter34.lean` line 124
- **Premise:** `hextension : ∀ colored partialColor, ... → ∃ v c, ...`
- **What it says:** Given a partial proper list-coloring, one more cell can always be colored.
- **How to prove:** Construct a kernel-perfect orientation of the row-column bipartite graph using list orderings. The kernel property guarantees a sink vertex whose list has more colors than colored neighbors. Use `galvin_greedy_step` (already proved) at that vertex.
- **Estimated effort:** ~100 lines. Orientation construction is the core.

## Priority 2: Needs infrastructure not yet in Mathlib

### Ch09: Irrationality of arccos(1/3)/π
- **File:** `Chapter09.lean` line 150
- **Premise:** `hirr : ∀ q : ℚ, Real.arccos (1/3) ≠ q * Real.pi`
- **What it says:** The dihedral angle of the regular tetrahedron is irrational over π.
- **How to prove:** Niven's theorem (rational values of trig functions at rational multiples of π) or direct Chebyshev polynomial argument. Neither is in Mathlib.
- **Estimated effort:** ~200 lines + Niven's theorem formalization.
- **Blocker:** Niven's theorem not in Mathlib.

### Ch10: Gallai geometric construction
- **File:** `Chapter10.lean` lines 130-136
- **Premise:** `hCloser`, `hFoot`, `hCloserMem`, `hCloserOff` — geometric constructions for the closer-pair argument.
- **What it says:** Given a point off a line with ≥3 collinear points, one can construct a strictly closer point-line pair.
- **How to prove:** Euclidean plane geometry: perpendicular foot, triangle inequality for distances to a line.
- **Estimated effort:** ~150 lines + Euclidean geometry formalization.
- **Blocker:** No comprehensive plane geometry library in Lean/Mathlib.

### Ch39: Lovász/Borsuk-Ulam for Kneser graphs
- **File:** `Chapter39.lean` line 153
- **Premise:** `hhard : n ≠ 2*k → ¬ ∃ C, ...`
- **What it says:** KG(n,k) is not (n-2k+1)-colorable when n > 2k.
- **How to prove:** Bárány's proof: embed [n] on a sphere, use hemisphere k-subsets, apply Borsuk-Ulam to the induced coloring map.
- **Estimated effort:** ~300 lines + Borsuk-Ulam formalization.
- **Blocker:** Borsuk-Ulam theorem not in Mathlib. Requires degree theory or Tucker's lemma.

## Summary

| Chapter | Premise | Difficulty | Blocker |
|---------|---------|------------|---------|
| Ch33 | Hall's condition | Easy | None |
| Ch03 | Sylvester smoothness | Medium | None |
| Ch11 | Rotating calipers | Medium | Convex hull |
| Ch31 | Prüfer encoding | Medium | Algorithm formalization |
| Ch34 | Kernel-perfect orientation | Medium-Hard | None |
| Ch09 | arccos(1/3) irrationality | Hard | Niven's theorem |
| Ch10 | Gallai geometry | Hard | Plane geometry |
| Ch39 | Kneser lower bound | Very Hard | Borsuk-Ulam |

Total estimated effort: ~1200 lines across 8 chapters.
Recommended attack order: Ch33 → Ch03 → Ch31 → Ch34 → Ch11 → Ch09 → Ch10 → Ch39.
