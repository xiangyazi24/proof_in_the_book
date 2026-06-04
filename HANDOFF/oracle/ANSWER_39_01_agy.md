# ANSWER_39_01_agy — Ch39 Kneser chromatic Tier 1

## Recommended Tier 1

The book's Ch39 = Lovász's theorem: χ(KG(n, k)) = n - 2k + 2.

Upper bound (n - 2k + 2 colors suffice): already proved in your file via
min-element coloring + pigeonhole.

Lower bound (no (n - 2k + 1)-coloring): hard direction, proved by Lovász
1978 using Borsuk-Ulam. Bárány gave a simplicial alternative. **Borsuk-Ulam
is NOT in Mathlib** — Tier 1 takes this hard direction as `hhard` hypothesis
(as your file already does for `kneser_chromatic_lower_bound`).

```lean
/-- Certificate that Kneser graph KG(n,k) is not (n - 2k + 1)-colorable.
This is the hard direction of Lovász's theorem, traditionally proved via
Borsuk-Ulam (not currently in Mathlib). -/
structure KneserChromaticCertificate (n k : ℕ) where
  /-- The non-colorability witness for the n ≠ 2*k case. -/
  hhard : n ≠ 2 * k → ¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
    ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b

/-- Chapter 39 (Lovász's theorem on Kneser graph chromatic number, Tier 1
conditional): given the hard direction (no (n-2k+1)-coloring exists when
n ≠ 2k), and combined with the upper bound (n-2k+2 colorable) already proved,
χ(KG(n,k)) = n - 2k + 2.

Tier 2 (construct hhard via Borsuk-Ulam / Bárány simplicial argument)
deferred — requires building Borsuk-Ulam in Mathlib first. -/
theorem chapter39 {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (cert : KneserChromaticCertificate n k) :
    -- Upper bound: (n - 2k + 2)-colorable.
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    -- Lower bound: not (n - 2k + 1)-colorable.
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) := by
  refine ⟨?_, ?_⟩
  · -- Upper bound from existing kneser_chromatic_upper_bound.
    exact kneser_chromatic_upper_bound n k hk hn
  · -- Lower bound from kneser_chromatic_lower_bound with hhard from certificate.
    exact kneser_chromatic_lower_bound n k hk hn cert.hhard
```

## Notes

- Adjust the argument list of `kneser_chromatic_lower_bound` to match
  your file's exact signature.
- The structure is minimal — single field `hhard`. You could expand later
  to bundle the Borsuk-Ulam topological input directly.
- Conclusion is a CONJUNCTION (upper + lower); together they witness
  χ(KG(n,k)) = n - 2k + 2.

## Alternative cleaner conclusion

If you want a single statement "the chromatic number IS n - 2k + 2", state
it via SimpleGraph.chromaticNumber:

```lean
theorem chapter39 {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (cert : KneserChromaticCertificate n k) :
    (kneserGraph n k).chromaticNumber = n - 2 * k + 2 := by
  apply le_antisymm
  · exact (kneser_chromatic_upper_bound n k hk hn).chromaticNumber_le
  · -- lower bound from hhard
    sorry  -- chromaticNumber ≥ n - 2k + 2 ↔ no (n - 2k + 1)-coloring
```

But this needs `chromaticNumber` API + potentially case split on n = 2k.
First form (conjunction) is simpler.

## Build + commit

~25 LOC for structure + theorem. Build clean.

Go.
