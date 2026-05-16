import Mathlib
#find _ (p n k : ℕ), p.Prime → k ≤ n → p ∣ Nat.choose n k
#find _ (n k p : ℕ), p.Prime → p > k → n ≥ 2 * k → n ≥ p → p ∣ Nat.choose n k
