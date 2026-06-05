2026-06-04 Chapter22 Gurvits status

- Read `HANDOFF/TASK_Ch22full.md` and `HANDOFF/TASK_Ch22.md`.
- `HANDOFF/CH22_GURVITS_CAPACITY.md` is not present in this checkout.
- Extended `ProofsInTheBook/Chapter22Gurvits.lean` without proof placeholders.
- Added the algebraic last-mile interface:
  - `GurvitsIteratedCapacityCertificate n`
  - `squarefreeCoefficientCore_of_iteratedCapacityCertificate`
  - `vanDerWaerdenAnalyticCore_of_iteratedCapacityCertificate`
  - `chapter22_from_iteratedCapacityCertificate`
- The new theorem uses the existing `gurvits_product_telescopes` identity to turn
  the iterated product `∏ m ∈ Finset.Icc 2 n, G m` into `n! / n^n`.
- Also re-exported the already proved `n ≤ 2` squarefree core from `Chapter22`.

Verified:

```bash
PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter22Gurvits.lean
```

Remaining exact Lean frontier:

```lean
theorem gurvits_iterated_capacity_certificate
    (n : ℕ) (hn : 3 ≤ n) :
    ProofsInTheBook.Chapter22Gurvits.GurvitsIteratedCapacityCertificate n
```

Equivalently, after introducing the fields:

```lean
A : Matrix (Fin n) (Fin n) ℝ
hA : ∀ i j, 0 ≤ A i j
hcap : ProofsInTheBook.Chapter22.RowLinearCapacityAtLeastOne A
⊢ (∏ m ∈ Finset.Icc 2 n, ProofsInTheBook.Chapter22Gurvits.G m) ≤
    ProofsInTheBook.Chapter22.rowLinearSquarefreeCoefficient A
```

This is exactly the missing analytic/stability Gurvits step; the product
telescoping and Chapter 22 conditional endpoint are now wired.
