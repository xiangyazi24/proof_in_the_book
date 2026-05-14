# Repository Understanding

This project is a full-book formalization project, not a theorem-search
exercise.

## Core Objective

For each chapter of *Proofs from THE BOOK*, formalize the mathematical content
and proof strategy of the chapter.  The desired artifact is a Lean development
that teaches Lean the book proof, with enough intermediate lemmas to make the
argument visible and maintainable.

## What Counts as Progress

- A chapter theorem has a theorem-accurate statement.
- The proof follows the book's structure or a clearly documented Lean-friendly
  version of the same argument.
- Supporting lemmas expose the combinatorial, algebraic, analytic, or geometric
  mechanism used in the book.
- The chapter passes its local check and integrates into `ProofsInTheBook.lean`.

## What Does Not Count

- Replacing a chapter proof with a broad Mathlib theorem in one line.
- Keeping a theorem as `True` unless the chapter task is explicitly only a
  temporary scaffold.
- Closing a substantial result with `by trivial`, `simp`, `exact
  Nat.infinite_setOf_prime`, or similar mechanical proof terms that bypass the
  book proof.
- Adding axioms to avoid proof work.

## Chapter Independence

The 40 chapters are independent work units for agent workflow purposes.  Do not
carry large context across many chapters.  After finishing one chapter:

1. Run the chapter-local check.
2. Run any needed integration check.
3. Update `Changelog.md`, `WebappTasks.md`, and `.proof_goals_state` when
   relevant.
4. Commit and push the chapter-sized change.
5. Compact or summarize context before opening the next chapter.

This keeps each chapter auditable and prevents stale proof-state assumptions
from leaking between unrelated chapters.

## Mathlib Policy

Mathlib is the foundation and should be used for standard definitions,
notation, algebraic infrastructure, arithmetic facts, topology, analysis, and
routine lemmas.  It should not be used as a black-box replacement for a chapter
whose purpose is to formalize a specific book proof.

Acceptable:

- Using standard facts such as factorial identities, finite set APIs, prime
  factorization lemmas, order lemmas, or analytic convergence infrastructure.
- Calling a Mathlib theorem for a routine side lemma after the book's main idea
  has been formalized.

Not acceptable:

- Solving a chapter's central theorem by directly invoking an already-proved
  Mathlib theorem for the same result while omitting the book argument.

## Default Agent Loop

For a new chapter:

1. Inspect the theorem statements and existing comments.
2. Identify placeholders and mechanical closures.
3. Choose the smallest next theorem that advances the chapter's book proof.
4. Prove local lemmas in the chapter file.
5. Verify with Lean frequently.
6. Stop the chapter only when the acceptance criteria are met or a precise
   blocker is recorded.
