# Webapp Tasks (Instant batch 1)

1) `ProofsInTheBook/Chapter01.lean`

Please fill the following placeholders with full Lean proofs:
- `chapter01_euclid`
- `chapter01_fermat_coprime`
- `chapter01_mersenne`
- `chapter01_euler`
- `chapter01_furstenberg`
- `chapter01`

2) `ProofsInTheBook/Chapter02.lean`

Please fill the following placeholders with full Lean proofs:
- `chapter02_bertrand`
- `chapter02_landau_trick`
- `chapter02_prime_product_bound`
- `chapter02_legendre`
- `chapter02_binomial_bound`
- `chapter02`

### Local follow-up (2026-05-11)
- Chapter01 all theorem placeholders are currently mechanical and no longer `: True`/`sorry`.
- `chapter01_mersenne`, `chapter01_euler`, `chapter01_furstenberg`, `chapter01` are awaiting book-style replacement once full proof scripts are available.
- Webapp-sourced tasks were completed for chapter01 via local fallback where no upstream proof object was ready.

### Goal run for Chapter 01
- chapter01_euclid
- chapter01_fermat_coprime

### Goal run for Chapter 01
- chapter01_euclid
- chapter01_fermat_coprime

### Goal run for Chapter 01
- chapter01_euclid
- chapter01_fermat_coprime

### Goal run for Chapter 01
- chapter01_euclid
- chapter01_fermat_coprime

### Goal run for Chapter 01
- chapter01_mersenne
- chapter01_euler

### Goal run for Chapter 02
- chapter02_bertrand
- chapter02_landau_trick

### Goal run for Chapter 03 (book-faithful restart)
- chapter03_sylvester (Sylvester-type theorem: `∀ n k, n ≥ 2 * k → k > 0 → ∃ p, p > k ∧ p.Prime ∧ p ∣ Nat.choose n k`)
- chapter03_binomials_coefficients_never_powers (binomial coefficients are (almost) never powers; target statement should match book: `∀ k l m n, 2 ≤ l → 4 ≤ k → k ≤ n - 4 → Nat.choose n k ≠ m ^ l`)

### Goal run for Chapter 03
- chapter03

### Goal run for Chapter 01
- chapter01_euclid
- chapter01_mersenne

### Goal run for Chapter 01
- chapter01_euclid

### Goal run for Chapter 02
- chapter02_bertrand

### Goal run for Chapter 03
- chapter03_sylvester
- chapter03_binomials_coefficients_never_powers

### Goal run for Chapter 03
- chapter03_sylvester

### Goal run for Chapter 03
- chapter03_sylvester
- chapter03_binomials_coefficients_never_powers

### Communication test run (window: dm-codex, mode: instant) at 2026-05-11 12:41:22 CDT
- heartbeat: WebappTasks.md updated from local codex side for proof_in_the_book.
- expected next action: fill next assigned theorem bodies in Chapter03.

### Goal run for Webapp (dm-codex, instant, 2026-05-11)
- window: dm-codex
- sent_at: 2026-05-11 12:42:28 CDT
- file: ProofsInTheBook/Chapter03.lean
- tasks:
  - chapter03_sylvester
  - chapter03_binomials_coefficients_never_powers
  - chapter03


### Channel sync fallback (window mismatch check, 2026-05-11)
- sent_at: 2026-05-11 12:44:16 CDT
- channel: q-series
- task_id: efb5f8e0
- reason: front-end currently reads q-series

### Communication re-route (window: dm-codex) at 2026-05-11 12:48:19 CDT
- task_id: 591d92f2
- channel: dm-codex
- note: previous attempt was sent to q-series; this is corrective route
- action: solve Chapter03 with local grow block and return proof terms only

### DM-codex timestamp test (2026-05-11)
- sent_at: 2026-05-11 12:49:42 CDT
- task_id: c7885062
- note: endpoint /api/ask with channel=dm-codex

### Goal run for Chapter 03
- chapter03_sylvester
- chapter03_binomials_coefficients_never_powers

### Goal run for Chapter 03
- chapter03_sylvester
- chapter03_binomials_coefficients_never_powers

### Goal run for Chapter 03
- chapter03_sylvester
- chapter03_binomials_coefficients_never_powers

### Goal run for Chapter 04
- chapter04

### Goal run for Chapter 04
- chapter04

### DM-codex follow-up (complete repo context, 2026-05-11)
- channel: dm-codex
- commit: 614512b
- repo: /Users/huangx/repos/proof_in_the_book
- message: We have an issue where the bridge previously used wrong window names. Please treat this task as authoritative.
- project files in repo:
  - ProofsInTheBook/Chapter01.lean
  - ProofsInTheBook/Chapter02.lean
  - ProofsInTheBook/Chapter03.lean
  - ProofsInTheBook/Chapter04.lean
  - ProofsInTheBook/Chapter05.lean
  - ProofsInTheBook/Chapter06.lean
  - ProofsInTheBook/Chapter07.lean
  - ProofsInTheBook/Chapter08.lean
  - ProofsInTheBook/Chapter09.lean
  - ProofsInTheBook/Chapter10.lean
  - ProofsInTheBook/Chapter11.lean
  - ProofsInTheBook/Chapter12.lean
  - ProofsInTheBook/Chapter13.lean
  - ProofsInTheBook/Chapter14.lean
  - ProofsInTheBook/Chapter15.lean
  - ProofsInTheBook/Chapter16.lean
  - ProofsInTheBook/Chapter17.lean
  - ProofsInTheBook/Chapter18.lean
  - ProofsInTheBook/Chapter19.lean
  - ProofsInTheBook/Chapter20.lean
  - ProofsInTheBook/Chapter21.lean
  - ProofsInTheBook/Chapter22.lean
  - ProofsInTheBook/Chapter23.lean
  - ProofsInTheBook/Chapter24.lean
  - ProofsInTheBook/Chapter25.lean
  - ProofsInTheBook/Chapter26.lean
  - ProofsInTheBook/Chapter27.lean
  - ProofsInTheBook/Chapter28.lean
  - ProofsInTheBook/Chapter29.lean
  - ProofsInTheBook/Chapter30.lean
  - ProofsInTheBook/Chapter31.lean
  - ProofsInTheBook/Chapter32.lean
  - ProofsInTheBook/Chapter33.lean
  - ProofsInTheBook/Chapter34.lean
  - ProofsInTheBook/Chapter35.lean
  - ProofsInTheBook/Chapter36.lean
  - ProofsInTheBook/Chapter37.lean
  - ProofsInTheBook/Chapter38.lean
  - ProofsInTheBook/Chapter39.lean
  - ProofsInTheBook/Chapter40.lean
  - ProofsInTheBook.lean
  - GOALS.md
  - FormalizationPlan.md
  - Changelog.md
  - COMMUNICATION_PROTOCOL.md
  - lakefile.lean
  - lean-toolchain
  - lake-manifest.json
  - scripts/goal
- current next task for book-faithful workflow:
  - file: ProofsInTheBook/Chapter04.lean
  - theorem: chapter04
  - goal: replace placeholder proof only; keep declaration unchanged.
  - branch: use previous book-style structure; if no direct theorem exists, return a direct constructive proof term matching the existing statement.

### Goal run for Chapter 04
- chapter04

### Goal run for Chapter 01
- chapter01_euclid
- chapter01

### Goal run for Chapter 01
- chapter01_euclid
- chapter01

### Goal run for Chapter 02
- chapter02

### Goal run for Chapter 04
- chapter04

### Goal run for Chapter 01
- chapter01_euclid
- chapter01_fermat_coprime

### Goal run for Chapter 01
- chapter01_euclid
- chapter01_fermat_coprime

### Goal run for Chapter 04
- chapter04

### Goal run for Chapter 05
- chapter05

### Goal run for Chapter 04
- chapter04

### Goal run for Chapter 04
- chapter04

### Goal run for Chapter 04
- chapter04

### Chapter 04 - dm-codex (book-faithful rewrite request)
- file: ProofsInTheBook/Chapter04.lean
- theorem: chapter04
- requirement: replace the current placeholder proof with a non-mechanical book-style proof term for the chapter's goal. Keep declaration unchanged.
- preference:
  - do not answer with `exact Nat.infinite_setOf_prime`, `simpa using Nat.infinite_setOf_prime`, or any direct single-line witness-reuse pattern.
  - if needed, refactor by introducing local lemmas that are derivable from earlier book lemmas.
  - return only Lean code for `chapter04` body so it can be applied directly.

### Goal run for Chapter 01
- chapter01_euclid
- chapter01_fermat_coprime

### Goal run for Chapter 02
- chapter02_bertrand
- chapter02_landau_trick
