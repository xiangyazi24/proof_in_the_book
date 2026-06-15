# Ch13 active-component extraction — design brief

## Goal theorem (NEW file `ProofsInTheBook/Ch13ActiveComponent.lean`)
From a SIMPLE triangulated sphere `M : CombMap D` (`IsSphereMap`, `FaceRegular 3`,
`IsSimpleGraph` = no loops/no parallel edges) with an edge-invariant ±/0 signing
`es : D → EdgeSign` (`es (α d) = es d`) and a nonzero edge, conclude:
```
∃ d, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2
```
by building the ACTIVE SUBGRAPH `A` (component of nonzero darts) as a `CombMap`, applying the
PROVEN `active_component_low_vertex` (needs: `(A.V:ℤ)-A.E+A.F=2`, `∑ faceDeg A = 2A.E`,
`∀R, 3≤faceDeg A R`, strict signing `s`, `EdgeInvariant A s`), and transporting back.

## REUSABLE machinery (verified present)
- `SubmapPlanar.lean`: `keptAlpha M Del hsub`, `Equiv.Perm.deleteSet M.σ Del`,
  `keptMap_eulerChar_eq_two (hclosed) (hsphere) (K) (hKσ : K.σ = deleteSet M.σ Del)
   (hKα : K.α = keptAlpha M Del hsub) (d) (hconn : K.Connected) : K.eulerChar = 2`.
  Requires `Del` α-closed: `hclosed : ∀ d ∈ Del, M.α d ∈ Del` and `hsub : ∀ d, d∈Del ↔ α d∈Del`.
- `∑ faceDeg A = 2 A.E` is AUTOMATIC: `faceDeg A R = card of φ_A-orbit`, sum = `card D_A = 2 A.E`
  via `sum_class_card A.φ` + `two_mul_E_eq_card`. (free)
- `PlanarMapSimple.lean`: `IsSimpleGraph`, `no_parallel : dartEdge d = dartEdge e → α.SameCycle d e`.
- `Ch13MarkedReduction.vertexFlipCountSkipZeros_strict_eq_vertexFlip`,
  `Ch13CyclicSigns.cyclicFlipCountSkipZeros_insert_zero`.

## The TWO genuinely-hard pieces (need your attack)

### HARD PIECE 1 — Connectivity / component extraction
`keptMap_eulerChar_eq_two` needs `K.Connected`. The active subgraph (delete inactive darts) may be
DISCONNECTED. So `Del` must be `{d : es d = zero} ∪ {d : d not in the chosen nonzero dart d₀'s
component of the active subgraph}`. Question: cleanest way to define `Del` so that
(a) `Del` is α-closed, (b) the kept map IS connected (it's exactly one active component), and
(c) the strict signing restricted is still edge-invariant and the transport works.
Is it easier to: define `Del = complement of (the kept-component of d₀)` directly, where the kept-
component is a union of σ-orbits AND α-orbits (component-closed)? Give the exact `Del` and the
α-closure + connectivity proof sketch with concrete Lean lemma names.

### HARD PIECE 2 — faceDeg ≥ 3 from M simple (the no-digon topological core)
Need `∀ R : φ_A-orbit, 3 ≤ faceDeg A R`. A face of A of degree ≤ 2 is a self-loop (φ_A d = d) or a
digon (φ_A(φ_A d)=d, φ_A d ≠ d). The math: A-edges ⊆ M-edges, M simple ⇒ no two A-darts share an
edge-pair, and no A-dart is a loop. But A's FACE permutation φ_A = deleteSet(σ)·keptAlpha differs
from M's φ (deleting edges MERGES faces). KEY question: how does a digon face of A
(two A-edges e,e' bounding a 2-gon) force two M-edges sharing both endpoints, contradicting M simple?
Give the precise argument: faceDeg A R = 1 case, = 2 case, mapping back to M.dartEdge equality, and
which `IsSimpleGraph`/`deleteSet` lemmas close it. Concrete Lean goal states please.

Close what you can with Lean 4 / Mathlib (leanprover/lean4:v4.30.0-rc2). Report exact remaining
goal states + which lemmas exist vs missing. NO faking, NO native_decide.
