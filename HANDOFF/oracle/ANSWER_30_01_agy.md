# ANSWER_30_01_agy — Path type + involution skeleton

## (1) Path type

Yes, `List (ℤ × ℤ)` is the right choice. Reasons:
- DecidableEq on `ℤ × ℤ` is free (Prod of DecidableEq).
- `List.indexOf` (or `List.idxOf` in current Mathlib) gives position lookup we'll need for splitting.
- Lex order on `ℤ × ℤ` via `Prod.lex` gives us `LinearOrder` for picking "smallest first intersection".

Wrap with a step constraint, but keep `List` as the carrier:

```lean
-- N/E lattice steps (you can pick a different alphabet; only DecidableEq matters)
inductive Step : Type where
  | north : Step
  | east  : Step
  deriving DecidableEq

def Step.apply : Step → (ℤ × ℤ) → (ℤ × ℤ)
  | .north, (x, y) => (x, y + 1)
  | .east,  (x, y) => (x + 1, y)

/-- A lattice path is a non-empty list of vertices in (ℤ × ℤ) where consecutive
vertices differ by a `Step`. -/
structure LatticePath where
  vertices : List (ℤ × ℤ)
  nonempty : vertices ≠ []
  consecutive : ∀ i (h : i + 1 < vertices.length),
    ∃ st : Step, vertices[i + 1] = st.apply vertices[i]
```

For LGV, the actual "step" structure is only needed to ensure paths are well-defined
sequences; the involution uses **just the vertex list + endpoints**. So you can defer
the `consecutive` predicate and operate at the `List (ℤ × ℤ)` level for the
involution proof. Add it back for the final concrete lattice-count statement.

Pragmatic suggestion: define `Path V := List V` plus a `source` and `sink` accessor.
The step structure goes into `pathCount`'s specialization.

## (2) Tail-swap involution

Define the involution as a **pure function on `PathFamily V n`** (using
`DecidableEq V` + `LinearOrder V`), then prove it's an involution to get an `Equiv`.

### Helper: first intersection

```lean
variable {V : Type*} [DecidableEq V] [LinearOrder V] {n : ℕ}

-- For two distinct paths, return the lex-smallest common vertex, if any.
def Path.firstIntersection (p q : List V) : Option V :=
  let common := p.toFinset ∩ q.toFinset
  if h : common.Nonempty then some (common.min' h) else none

-- For a family, find the lex-smallest pair (i, j) with i < j and intersecting paths.
def PathFamily.firstBadPair (F : PathFamily Source Sink V n) :
    Option (Fin n × Fin n) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 < p.2 ∧ (F.paths p.1).firstIntersection (F.paths p.2) |>.isSome))
  |>.min  -- min in lex order on Fin n × Fin n
```

(Use `Finset.min` or take `argmin` over a finite set; Mathlib gives both.)

### The swap

Given `(i, j) := F.firstBadPair` (when defined) and `v := (F.paths i).firstIntersection (F.paths j)`:

```lean
def Path.splitAtFirst (p : List V) (v : V) (h : v ∈ p) : List V × List V :=
  let idx := p.idxOf v
  (p.take (idx + 1), p.drop (idx + 1))   -- (prefix-up-to-and-including-v, rest)

def Path.swapTailAt (pi pj : List V) (v : V) (hi : v ∈ pi) (hj : v ∈ pj) :
    List V × List V :=
  let (pi_head, pi_tail) := pi.splitAtFirst v hi
  let (pj_head, pj_tail) := pj.splitAtFirst v hj
  -- new paths: keep prefix, swap tails (both prefixes end at v, both tails START
  -- with the vertex AFTER v in original path).
  (pi_head ++ pj_tail, pj_head ++ pi_tail)
```

Endpoints flip: new `path_i` ends at the original sink of `path_j`, and vice versa.
This is what makes the **permutation swap** happen.

### Putting it together

```lean
noncomputable def PathFamily.tailSwap [LinearOrder Source] [LinearOrder Sink]
    [LinearOrder V] [DecidableEq V] (F : PathFamily Source Sink V n) :
    PathFamily Source Sink V n :=
  match h : F.firstBadPair with
  | none => F  -- non-intersecting → identity
  | some ⟨i, j⟩ =>
    let pi := F.paths i
    let pj := F.paths j
    -- v exists because firstBadPair only returns Some when intersection is nonempty
    let v := (pi.firstIntersection pj).get (by ...)  -- existence from firstBadPair definition
    -- vertex membership facts
    let hi : v ∈ pi := ...
    let hj : v ∈ pj := ...
    let (pi', pj') := Path.swapTailAt pi pj v hi hj
    { perm := F.perm.swap i j  -- transposition of σ values at positions i, j
      paths := fun k =>
        if k = i then pi'
        else if k = j then pj'
        else F.paths k
    }
```

### Involution proof

The key observation: `(F.tailSwap).firstBadPair = F.firstBadPair` (because the swap
exchanges TAILS only, which doesn't change the SET of intersecting pairs OR which
vertex is the first intersection — same `(i, j, v)` triple). Then `tailSwap ∘ tailSwap = id`
because applying the same swap twice restores the original tails.

Concretely:
- After swap, paths `i` and `j` have NEW tails but same FIRST INTERSECTION VERTEX `v`.
- The set of vertices in `path_i` is exactly the swap of original — so the intersection
  set `path_i ∩ path_j` is preserved.
- Hence `firstBadPair` returns the same `(i, j)` triple.
- And swapping back restores the original tails.

Lemma chain (each ~10-30 LOC):
1. `Path.swapTailAt_swapTailAt`: applying the helper twice with same `v` returns original.
2. `PathFamily.tailSwap_firstBadPair`: `(F.tailSwap).firstBadPair = F.firstBadPair`.
3. `PathFamily.tailSwap_tailSwap`: `F.tailSwap.tailSwap = F` (involution).
4. `PathFamily.tailSwap_sign`: `(F.tailSwap).perm.sign = -F.perm.sign` (via `Equiv.Perm.sign_swap`).

Then construct `Equiv` from involution + identity-on-good:
```lean
def PathFamily.badInvolution [LinearOrder ...] : Equiv (PathFamily ...) (PathFamily ...) :=
  Equiv.symm <| Equiv.ofBijective PathFamily.tailSwap (by
    constructor
    · -- injective from involution
      intro F G h
      have := congrArg PathFamily.tailSwap h
      simpa [tailSwap_tailSwap] using this
    · -- surjective from involution
      intro F
      exact ⟨F.tailSwap, tailSwap_tailSwap F⟩)
```

(Slight variant: since involution is symmetric, you can directly construct
`Equiv.mk tailSwap tailSwap tailSwap_tailSwap tailSwap_tailSwap`.)

### Sign-reversing certificate

Build `BadInvolutionCertificate (PathFamily ...) R` (where R = the coefficient ring):

```lean
def lgvCertificate : BadInvolutionCertificate (PathFamily ...) R :=
{ bad := fun F => F.firstBadPair.isSome  -- "F is intersecting"
  involve := PathFamily.badInvolution
  signedWeight := fun F => F.perm.sign * (∏ i, weight(F.paths i))
  involve_bad := fun F hF => ...  -- swap of bad family is still bad
  signedWeight_neg := fun F hF => ...  -- weight changes sign via tailSwap_sign
}
```

The four certificate fields each become ~10-30 LOC lemmas.

## Honest scope

- Path type + helpers: ~40 LOC
- Involution proofs: ~150 LOC (firstBadPair preservation + tailSwap_tailSwap + sign)
- Certificate assembly: ~30 LOC
- Main theorem wiring: ~30 LOC

**Total ~250 LOC.** The `firstBadPair_tailSwap = firstBadPair` lemma is the hardest
single step (~50 LOC); if you hit > 80 LOC on it alone, file Q02.

## Quick wins / pitfalls

- For `LinearOrder` on `Fin n × Fin n`: use `Prod.lex Fin.LE Fin.LE` — already in Mathlib.
- `Finset.min` on a `Finset.filter` requires `Nonempty` — case-split on
  `(filter ...).Nonempty` and return `none` otherwise.
- `noncomputable` is fine for the whole chain (no actual extraction needed).
- DON'T try to make it computable; the Finset operations + LinearOrder.min push
  noncomputability anyway.

Go.
