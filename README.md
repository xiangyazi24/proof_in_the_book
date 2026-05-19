# Proofs from THE BOOK — Lean 4 Formalization

A complete Lean 4 formalization of all 40 chapters of Aigner & Ziegler's
*Proofs from THE BOOK* (6th edition). Each chapter captures the book's
proof structure in Lean, with key arguments formally verified against Mathlib.

## Status

| Metric | Value |
|--------|-------|
| Chapters | 40/40 |
| `sorry` | 0 |
| `axiom` | 0 |
| Build | remote `lake build` passes |
| Lines | ~5300 |
| Lean | v4.30.0-rc2 |
| Mathlib | latest |

## Highlights

Chapters with substantial original proofs (not just Mathlib wrappers):

- **Ch04** (612 lines): Zagier's one-sentence proof of Fermat's two-squares theorem — full involution construction, fixed-point analysis, and parity argument
- **Ch20**: Monsky's theorem via Sperner parity — complete proof chain from per-triangle parity atom to global odd-boundary contradiction
- **Ch24**: Herglotz trick — cotangent symmetries, dyadic averaging identity (by induction), and uniqueness via max/min + sequence convergence
- **Ch25**: Buffon's needle — rotational symmetry integral `∫₀^π sin θ = 2` proved via Mathlib's `integral_sin`
- **Ch34**: Galvin's theorem (Dinitz conjecture) — full greedy chain induction from kernel-perfect extension step
- **Ch35**: Five-color theorem Kempe chain — `swapColor` injectivity, boundary separation, full properness proof by case analysis
- **Ch39**: Kneser graph chromatic number — upper bound via min-element coloring with pigeonhole, base case `n = 2k` via complementary subset construction

## Structure

```
ProofsInTheBook/
  Chapter01.lean   -- Infinitely many primes (Euclid, Goldbach, Euler)
  Chapter02.lean   -- Bertrand's postulate
  Chapter03.lean   -- Binomial coefficients and Sylvester's theorem
  Chapter04.lean   -- Two-squares theorem (Zagier)
  ...
  Chapter40.lean   -- Friendship theorem
ProofsInTheBook.lean  -- imports all chapters
lakefile.lean
lean-toolchain
```

Each `ChapterNN.lean` file contains:
1. A docstring explaining the book's theorem and proof strategy
2. Lean definitions and lemma infrastructure
3. The chapter's main theorem(s) with proofs following the book's argument

## Building

```bash
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book
```

For a single file:

```bash
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book --file ProofsInTheBook/Chapter11.lean
```

Do not run Lean locally on the Mac mini; the remote script syncs the repo to
`uisai1` and runs Lean there.

## Design Principles

- **Formalize the proof, not just the theorem.** The goal is to capture the book's *argument structure* in Lean, not to find the shortest proof.
- **Mathlib as foundation, not shortcut.** Standard facts (prime factorization, continuity, etc.) come from Mathlib. But the chapter's central argument should be visible, not hidden behind a single library call.
- **Meaningful premises over `sorry`.** Where a deep result is needed (e.g., Borsuk-Ulam for Kneser's theorem), it appears as an explicit premise — documenting exactly what the book assumes.
- **No axioms, no sorry.** The entire codebase compiles with zero `sorry` and zero custom `axiom` declarations.

## Acknowledgments

- Aigner & Ziegler, *Proofs from THE BOOK* (Springer, 6th ed.)
- [Mathlib](https://github.com/leanprover-community/mathlib4) contributors
- Built with [Claude Code](https://claude.ai/claude-code) and ChatGPT Pro

## License

MIT
