# TODO: Remaining Premises to Prove

All 40 chapters compile with 0 `sorry` and 0 `axiom`. Ch03, Ch31, Ch33, and Ch34
have had their original explicit premises eliminated.

## Priority 1: Provable with current Mathlib

### ~~Ch33: Hall's condition for Latin square complement~~ ✅
- **Status:** Proved using double counting. The `hHall_verified` premise eliminated.
  Key lemma: `hall_from_partial_square` — if used symbols have witness cells and
  filled cells ≤ n-1, then Hall's condition holds. Injection via `Finset.card_le_card_of_injOn`.

### ~~Ch03: Sylvester smoothness core~~ ✅
- **File:** `Chapter03.lean` line 168
- **Premise:** `hsmooth : n.descFactorial k ∉ (k+1).smoothNumbers`
- **What it says:** Among k consecutive integers n, n-1, ..., n-k+1, at least one has a prime factor > k.
- **How to prove:** The book uses Legendre's formula to bound p-adic valuations. For each prime p ≤ k, its total contribution to the product is bounded. The total smooth part cannot account for the full product. Key Mathlib tools: `Nat.factorization`, `Nat.descFactorial_eq_prod_range`.
- **Status:** Proved via Erdős's Sylvester-Schur argument, with analytic large-range estimates and finite certificates for the small/below-square residues. `sylvester_general` no longer has the `hsmooth` premise.

### Ch11: Slopes count from rotating calipers
- **File:** `Chapter11.lean` line 97
- **Premise:** `hslopes : points.card - 1 ≤ (slopesDeterminedBy points).card`
- **What it says:** n non-collinear points determine at least n-1 distinct slopes.
- **How to prove:** Ungar's rotating-calipers argument: rotate a directed line through all angles. At each of n-1 "events" (line passes through a new pair), a new slope appears. Needs convex hull infrastructure.
- **Estimated effort:** ~120 lines. Convex hull + angular sweep formalization.

### ~~Ch31: Cayley's upper bound (Prüfer/Joyal encoding)~~ ✅
- **File:** `Chapter31.lean` line 126
- **Premise:** `hCayley : Fintype.card (LabeledTree n) ≤ n ^ (n-2)`
- **What it says:** There are at most n^{n-2} labeled trees on n vertices.
- **Status:** Proved via Joyal's doubly rooted tree to endofunction injection.
  The key theorem is `joyal_tree_adj_iff_recovered`, which reconstructs all tree
  edges from the endofunction.

### ~~Ch34: Kernel-perfect extension step~~ ✅
- **File:** `Chapter34.lean` line 124
- **Premise:** `hextension : ∀ colored partialColor, ... → ∃ v c, ...`
- **What it says:** Given a partial proper list-coloring, one more cell can always be colored.
- **Important correction:** This premise is too strong as stated: arbitrary partial
  proper list-colorings need not be greedily extendable. The next step is to
  replace this false greedy-extension interface with the actual Galvin proof:
  list coloring from a kernel-perfect orientation, then the Dinitz orientation
  and stable-matching kernel argument.
- **Status:** Proved. The false `hextension` premise was removed from `galvin_theorem`.
  The replacement formalizes the kernel-perfect list-coloring induction, the
  Dinitz cyclic orientation, the outdegree bound, and the row-max/column-max
  stable-matching kernel proof for every induced subgraph.

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

| Chapter | Premise | Difficulty | Blocker | Status |
|---------|---------|------------|---------|--------|
| Ch33 | Hall's condition | Easy | None | ✅ **Done** |
| Ch03 | Sylvester smoothness | Medium | None | ✅ **Done** |
| Ch31 | Joyal/Cayley upper bound | Medium | None | ✅ **Done** |
| Ch34 | Kernel-perfect orientation | Medium-Hard | None | ✅ **Done** |
| Ch11 | Rotating calipers | Medium | Convex hull | ⬜ |
| Ch09 | arccos(1/3) irrationality | Hard | Niven's theorem | ⬜ |
| Ch10 | Gallai geometry | Hard | Plane geometry | ⬜ |
| Ch39 | Kneser lower bound | Very Hard | Borsuk-Ulam | ⬜ |

Total estimated effort: ~900 lines across 4 remaining chapters.
Recommended attack order: Ch11 → Ch09 → Ch10 → Ch39.
