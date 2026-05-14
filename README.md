# Proofs from THE BOOK in Lean

This repository is a long-running Lean formalization of all 40 chapters of
*Proofs from THE BOOK*.  The objective is not merely to prove statements that
look similar to the book's theorems; the objective is to reconstruct the
book's mathematical arguments as faithfully as Lean and Mathlib reasonably
allow.

## Working Principles

- Formalize the book, not just the headline theorem.  A Mathlib one-liner may
  be useful as a check, but it is not an acceptable replacement for a chapter
  proof when the book gives a substantive argument.
- Preserve theorem statements once a chapter task is assigned.  If a statement
  is too weak, too strong, or only a placeholder, record that explicitly before
  changing it.
- Do not close real work with `sorry`, `admit`, `by trivial`, `: True`, or a
  mechanical wrapper around an unrelated library theorem.
- Local lemmas are encouraged when they expose the same structure used in the
  book proof.
- Chapter files are independent work units.  Finish, verify, record, and commit
  one chapter before moving to the next chapter whenever possible.

## Workflow

1. Pick one chapter, usually the earliest chapter with an unfinished goal.
2. Read the chapter file and the relevant entries in `FormalizationPlan.md`,
   `GOALS.md`, `WebappTasks.md`, and `Changelog.md`.
3. Work inside that chapter file only unless a shared helper is genuinely
   needed.
4. Run the smallest relevant check first, then a full build when the chapter is
   ready.
5. Update the progress records.
6. Commit and push the chapter-sized unit.
7. After a chapter is closed, compact or summarize the working context before
   starting the next chapter.

## Important Files

- `ProofsInTheBook/ChapterNN.lean`: one Lean module per book chapter.
- `ProofsInTheBook.lean`: imports all chapter modules.
- `GOALS.md`: long-run goal order and acceptance criteria.
- `FormalizationPlan.md`: high-level chapter map and execution policy.
- `UNDERSTANDING.md`: operational notes for agents working in this repository.
- `WebappTasks.md`: task log for webapp-assisted proof attempts.
- `Changelog.md`: human-readable progress log.
- `scripts/goal`: helper for chapter goal runs, checks, and progress state.

## Verification

Use chapter-local checks while developing.  Before marking a chapter complete,
the chapter must have no real `sorry`, no placeholder theorem body, and no
mechanical proof that bypasses the book's argument.  A full `lake build` is the
final integration check.
