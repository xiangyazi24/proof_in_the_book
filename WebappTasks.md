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

