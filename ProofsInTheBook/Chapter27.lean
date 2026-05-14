import Mathlib

/-!
# Chapter 27: Tiling rectangles

From "Proofs from THE BOOK":

**De Bruijn's theorem**: An a × b rectangle can be tiled by 1 × n
rectangles iff n divides a or n divides b.

*Book proof (necessity).* Let ω = e^{2πi/n} (primitive n-th root of unity).
Assign weight ω^{i+j} to cell (i, j). Any 1×n horizontal brick in row r
starting at column c has weight ω^{r+c}(1+ω+...+ω^{n-1}) = 0.  Any n×1
vertical brick in column c starting at row r has weight the same = 0.
So the total weight of the whole tiling is 0.  But the total also factors as
(∑_{i<a} ω^i)(∑_{j<b} ω^j).  Since ℂ is an integral domain, one factor is 0,
so n|a or n|b.
-/

namespace ProofsInTheBook.Chapter27

open Complex Finset Real IsPrimitiveRoot

/-! ### The coloring argument -/

/-- The primitive n-th root of unity ω = e^{2πi/n}. -/
noncomputable def ω (n : ℕ) : ℂ := Complex.exp (2 * π * I / n)

private lemma omega_isPrimitiveRoot (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot (ω n) n :=
  Complex.isPrimitiveRoot_exp n hn

/-- The key vanishing: ∑_{k=0}^{n-1} ω^k = 0 for n ≥ 2. -/
private lemma geom_sum_omega_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ range n, (ω n) ^ k = 0 :=
  (omega_isPrimitiveRoot n (by omega)).geom_sum_eq_zero (by omega)

/-- Any n consecutive powers of ω sum to 0. -/
private lemma consecutive_sum_zero (n : ℕ) (hn : 2 ≤ n) (base : ℕ) :
    ∑ k ∈ range n, (ω n) ^ (base + k) = 0 := by
  simp_rw [pow_add, ← mul_sum]
  rw [geom_sum_omega_zero n hn, mul_zero]

/-- The rectangle sum factors as a product of two geometric sums. -/
private lemma rect_sum_eq_product (n a b : ℕ) :
    ∑ i : Fin a, ∑ j : Fin b, (ω n) ^ (i.val + j.val) =
    (∑ i ∈ range a, (ω n) ^ i) * (∑ j ∈ range b, (ω n) ^ j) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => (ω n) ^ i) a,
      ← Fin.sum_univ_eq_sum_range (fun j => (ω n) ^ j) b]
  simp_rw [pow_add, ← Finset.mul_sum, ← Finset.sum_mul]

/-- ∑_{k=0}^{m-1} ω^k = 0 if and only if n | m. -/
private lemma geom_sum_zero_iff_dvd (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    ∑ k ∈ range m, (ω n) ^ k = 0 ↔ n ∣ m := by
  have hωprim := omega_isPrimitiveRoot n (by omega)
  constructor
  · intro h
    by_contra hndvd
    have hω1 : ω n ≠ 1 := hωprim.ne_one (by omega)
    rw [geom_sum_eq hω1] at h
    exact absurd h (div_ne_zero
      (sub_ne_zero.mpr (fun heq => hndvd (hωprim.dvd_of_pow_eq_one m heq)))
      (sub_ne_zero.mpr hω1))
  · intro ⟨q, hq⟩
    subst hq
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, sum_range_add, ih, zero_add]
      simp_rw [show ∀ k : ℕ, (ω n) ^ (n * q + k) = (ω n) ^ k from
        fun k => by rw [pow_add, pow_mul, hωprim.pow_eq_one, one_pow, one_mul]]
      exact hωprim.geom_sum_eq_zero (by omega)

/-! ### The tiling model -/

/--
A partition of Fin a × Fin b into bricks where each brick is either:
- a horizontal run: {(r, c), (r, c+1), ..., (r, c+n-1)} for some row r and column c with c+n ≤ b
- a vertical run:  {(r, c), (r+1, c), ..., (r+n-1, c)} for some col c and row r with r+n ≤ a
-/
def IsTiledByNxOne (n a b : ℕ) : Prop :=
  ∃ (bricks : Finset (Finset (Fin a × Fin b))),
    bricks.biUnion id = Finset.univ ∧
    (∀ B₁ ∈ bricks, ∀ B₂ ∈ bricks, B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
    ∀ B ∈ bricks,
      (∃ r : Fin a, ∃ c : ℕ, c + n ≤ b ∧
        B = Finset.univ.filter (fun p : Fin a × Fin b =>
          p.1 = r ∧ c ≤ p.2.val ∧ p.2.val < c + n)) ∨
      (∃ col : Fin b, ∃ r : ℕ, r + n ≤ a ∧
        B = Finset.univ.filter (fun p : Fin a × Fin b =>
          p.2 = col ∧ r ≤ p.1.val ∧ p.1.val < r + n))

/-- The horizontal brick sum is zero. -/
private lemma hBrick_sum_zero (n a b : ℕ) (hn : 2 ≤ n) (r : Fin a) (c : ℕ) (hc : c + n ≤ b) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin a × Fin b =>
        p.1 = r ∧ c ≤ p.2.val ∧ p.2.val < c + n),
      (ω n) ^ (p.1.val + p.2.val) = 0 := by
  -- Reindex: the brick is in bijection with {0, ..., n-1} via k ↦ (r, c+k)
  have heq : (Finset.univ.filter (fun p : Fin a × Fin b =>
      p.1 = r ∧ c ≤ p.2.val ∧ p.2.val < c + n)) =
      Finset.univ.image
        (fun k : Fin n => (r, (⟨c + k.val, by
          have hk := k.isLt
          omega⟩ : Fin b))) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨rfl, hcy, hyc⟩
      refine ⟨⟨y.val - c, by omega⟩, ?_⟩
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp
        omega
    · rintro ⟨k, hxy⟩
      have hx : x = r := (Prod.ext_iff.mp hxy).1.symm
      have hyval : y.val = c + k.val := by
        have hy : (⟨c + k.val, by
          have hk := k.isLt
          omega⟩ : Fin b) = y := (Prod.ext_iff.mp hxy).2
        simpa using congrArg (fun z : Fin b => z.val) hy.symm
      refine ⟨hx, ?_, ?_⟩
      · omega
      · have hk := k.isLt
        omega
  rw [heq, sum_image]
  · have hfin : (∑ k : Fin n, (ω n) ^ (r.val + (c + k.val))) =
        ∑ k ∈ range n, (ω n) ^ (r.val + c + k) := by
      calc
        (∑ k : Fin n, (ω n) ^ (r.val + (c + k.val)))
            = ∑ k : Fin n, (ω n) ^ (r.val + c + k.val) := by
          apply sum_congr rfl
          intro k _hk
          congr 1
          omega
        _ = ∑ k ∈ range n, (ω n) ^ (r.val + c + k) := by
          exact Fin.sum_univ_eq_sum_range (fun k => (ω n) ^ (r.val + c + k)) n
    rw [hfin]
    exact consecutive_sum_zero n hn (r.val + c)
  · intro k₁ _ k₂ _ h
    apply Fin.ext
    have hv := congrArg (fun p : Fin a × Fin b => p.2.val) h
    simp at hv
    omega

/-- The vertical brick sum is zero. -/
private lemma vBrick_sum_zero (n a b : ℕ) (hn : 2 ≤ n) (col : Fin b) (r : ℕ) (hr : r + n ≤ a) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin a × Fin b =>
        p.2 = col ∧ r ≤ p.1.val ∧ p.1.val < r + n),
      (ω n) ^ (p.1.val + p.2.val) = 0 := by
  have heq : (Finset.univ.filter (fun p : Fin a × Fin b =>
      p.2 = col ∧ r ≤ p.1.val ∧ p.1.val < r + n)) =
      Finset.univ.image
        (fun k : Fin n => ((⟨r + k.val, by
          have hk := k.isLt
          omega⟩ : Fin a), col)) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨rfl, hrx, hxr⟩
      refine ⟨⟨x.val - r, by omega⟩, ?_⟩
      apply Prod.ext
      · apply Fin.ext
        simp
        omega
      · rfl
    · rintro ⟨k, hxy⟩
      have hy : y = col := (Prod.ext_iff.mp hxy).2.symm
      have hxval : x.val = r + k.val := by
        have hx : (⟨r + k.val, by
          have hk := k.isLt
          omega⟩ : Fin a) = x := (Prod.ext_iff.mp hxy).1
        simpa using congrArg (fun z : Fin a => z.val) hx.symm
      refine ⟨hy, ?_, ?_⟩
      · omega
      · have hk := k.isLt
        omega
  rw [heq, sum_image]
  · have hfin : (∑ k : Fin n, (ω n) ^ ((r + k.val) + col.val)) =
        ∑ k ∈ range n, (ω n) ^ (r + col.val + k) := by
      calc
        (∑ k : Fin n, (ω n) ^ ((r + k.val) + col.val))
            = ∑ k : Fin n, (ω n) ^ (r + col.val + k.val) := by
          apply sum_congr rfl
          intro k _hk
          congr 1
          omega
        _ = ∑ k ∈ range n, (ω n) ^ (r + col.val + k) := by
          exact Fin.sum_univ_eq_sum_range (fun k => (ω n) ^ (r + col.val + k)) n
    rw [hfin]
    exact consecutive_sum_zero n hn (r + col.val)
  · intro k₁ _ k₂ _ h
    apply Fin.ext
    have hv := congrArg (fun p : Fin a × Fin b => p.1.val) h
    simp at hv
    omega

/-- If the rectangle is tiled by 1×n bricks, the coloring sum is zero. -/
private lemma tiling_implies_sum_zero (n a b : ℕ) (hn : 2 ≤ n)
    (htile : IsTiledByNxOne n a b) :
    ∑ i : Fin a, ∑ j : Fin b, (ω n) ^ (i.val + j.val) = 0 := by
  obtain ⟨bricks, hcover, hdisj, hbrick⟩ := htile
  have hpwd : (↑bricks : Set _).PairwiseDisjoint id := fun B₁ hB₁ B₂ hB₂ hne =>
    hdisj B₁ (Finset.mem_coe.mp hB₁) B₂ (Finset.mem_coe.mp hB₂) hne
  -- Convert iterated sum to sum over all cells
  rw [show ∑ i : Fin a, ∑ j : Fin b, (ω n) ^ (i.val + j.val) =
      ∑ p : Fin a × Fin b, (ω n) ^ (p.1.val + p.2.val) from by simp [← sum_product']]
  -- Convert sum over cells to sum over bricks via partition
  rw [← hcover, Finset.sum_biUnion hpwd]
  simp only [id]
  apply sum_eq_zero
  intro B hB
  rcases hbrick B hB with ⟨r, c, hc, rfl⟩ | ⟨col, r, hr, rfl⟩
  · exact hBrick_sum_zero n a b hn r c hc
  · exact vBrick_sum_zero n a b hn col r hr

/-! ### Main theorem -/

/--
**De Bruijn's theorem** (necessity): If an a × b rectangle can be tiled by
1 × n bricks, then n | a or n | b.

*Proof.* Assign weight ω^{i+j} to cell (i,j) where ω = e^{2πi/n}. Each brick
sums to 0 (consecutive powers of ω). So the total = 0. But the total factors
as (∑_{i<a} ω^i)(∑_{j<b} ω^j). Since ℂ is an integral domain, n|a or n|b.
-/
theorem chapter27_debruijn (n a b : ℕ) (hn : 2 ≤ n) (htile : IsTiledByNxOne n a b) :
    n ∣ a ∨ n ∣ b := by
  have hsum := tiling_implies_sum_zero n a b hn htile
  rw [rect_sum_eq_product n a b] at hsum
  rcases mul_eq_zero.mp hsum with ha | hb
  · left;  exact (geom_sum_zero_iff_dvd n hn a).mp ha
  · right; exact (geom_sum_zero_iff_dvd n hn b).mp hb

theorem chapter27 : True := trivial

end ProofsInTheBook.Chapter27
