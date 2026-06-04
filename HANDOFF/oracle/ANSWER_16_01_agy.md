# ANSWER_16_01_agy — Ch16 Tier 1 Borsuk conditional

## Recommended Tier 1 `chapter16`

The book's Ch16 result is **Borsuk's conjecture fails in high dimensions**
(Kahn-Kalai 1993, using Frankl-Wilson combinatorics). Tier 1 captures the
genuine logical structure:

> Given a Kahn-Kalai-style counterexample set S in dimension d,
> Borsuk's conjecture in dimension d is false.

Concrete statement:

```lean
/-- Borsuk's conjecture in dimension d: every bounded set with positive
diameter can be partitioned into d+1 sets, each of strictly smaller diameter. -/
def BorsukConjecture (d : ℕ) : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin d))),
    Bornology.IsBounded S → 0 < Metric.diam S →
    ∃ parts : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)),
      S ⊆ ⋃ i, parts i ∧
      ∀ i, Metric.diam (parts i) < Metric.diam S

/-- Chapter 16 (Borsuk's conjecture in high dimensions, Tier 1 conditional):
Given a Kahn-Kalai-style counterexample — a bounded set with positive diameter
in ℝ^d that cannot be partitioned into d+1 pieces of strictly smaller diameter —
Borsuk's conjecture fails in dimension d.

Tier 2 (construct the actual Kahn-Kalai counterexample via Frankl-Wilson
combinatorics on hypergraph color codes) is deferred. -/
theorem chapter16 {d : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS_bdd : Bornology.IsBounded S)
    (hS_pos : 0 < Metric.diam S)
    (h_no_partition : ¬ ∃ parts : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)),
      S ⊆ ⋃ i, parts i ∧
      ∀ i, Metric.diam (parts i) < Metric.diam S) :
    ¬ BorsukConjecture d := fun h => h_no_partition (h S hS_bdd hS_pos)
```

Total: ~25 LOC (defining `BorsukConjecture` + the theorem).

## Notes

- This is the SAME Tier 1 pattern as Ch30 (LGV with `BadInvolutionCertificate`),
  Ch24 (Herglotz with continuous hypothesis), Ch31 (Cayley with Equiv hypothesis),
  and Ch34 (Galvin alias of full proof).
- `Bornology.IsBounded` is the right Mathlib predicate for "bounded set" in
  a metric/normed space. If not, fallback to `Metric.Bounded S`.
- `EuclideanSpace ℝ (Fin d)` is `Fin d → ℝ` with Euclidean norm; already in Mathlib.
- The proof is literally `fun h => h_no_partition (h S hS_bdd hS_pos)` —
  contraposition trivializes once everything is stated correctly.

## If your file's `kahn_kalai_counterexample_bound` placeholder is useful

If the file's existing scaffolding (Frankl-Wilson hypothesis → True placeholder)
provides a structured hypothesis you want to leverage, the chapter16 theorem
can take that structured `KahnKalaiCertificate` as input instead of the
raw `no_partition` hypothesis. The logic is identical.

```lean
structure KahnKalaiCertificate (d : ℕ) where
  S : Set (EuclideanSpace ℝ (Fin d))
  bounded : Bornology.IsBounded S
  pos_diam : 0 < Metric.diam S
  no_partition : ¬ ∃ parts : Fin (d + 1) → Set _,
    S ⊆ ⋃ i, parts i ∧ ∀ i, Metric.diam (parts i) < Metric.diam S

theorem chapter16 {d : ℕ} (cert : KahnKalaiCertificate d) :
    ¬ BorsukConjecture d := fun h =>
  cert.no_partition (h cert.S cert.bounded cert.pos_diam)
```

This is slightly cleaner and matches Ch30's `BadInvolutionCertificate` style.
Pick whichever feels better.

## Build + commit

Should remote-build to 0 sorry / 0 axiom in seconds.

Add a Tier 2 TODO docstring mentioning Frankl-Wilson combinatorial construction
deferred.

Go.
