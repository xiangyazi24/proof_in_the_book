# Finite Bool cyclic-flip extraction: `> 2` flips gives four alternating indices

This is a self-contained Lean module for the pure combinatorial extraction needed downstream.  I state it on `ZMod n`; the cyclic order conclusion is given by natural representatives

```lean
k0 < k1 < k2 < k3 < n
```

and the indices are `(kᵣ : ZMod n)`.  This is the most convenient form for a cyclic vertex link.  A `Fin n` wrapper is included at the end.

The proof avoids sorted-list plumbing.  It defines a scanner `flipBlocksFrom p pos len` that walks the cyclic sequence through `len` consecutive edges starting at `pos`; whenever it sees a flip, it records the pre-flip position together with the pre-flip Bool value.  The scanner proves three facts by induction:

1. recorded positions are strictly increasing and bounded;
2. recorded Bool values alternate;
3. the number of recorded flips is even for a full cycle.

Then `cyclicFlips p > 2`, plus evenness, gives at least four recorded flips.  The first four recorded positions are the required cyclically ordered alternating indices.

```lean
import Mathlib

noncomputable section

namespace ProofsInTheBook.Ch13BoolCyclicExtraction

/-- Encode a Bool in `ZMod 2` for the parity telescope. -/
def boolZ : Bool → ZMod 2
  | false => 0
  | true => 1

@[simp] lemma boolZ_false : boolZ false = 0 := rfl
@[simp] lemma boolZ_true : boolZ true = 1 := rfl

lemma boolZ_self_add (b : Bool) : boolZ b + boolZ b = 0 := by
  cases b <;> decide

/-- The mod-2 indicator of a Bool flip is the sum of the two endpoint values. -/
lemma flipIndicator_cast (a b : Bool) :
    ((if a ≠ b then 1 else 0 : ℕ) : ZMod 2) = boolZ a + boolZ b := by
  cases a <;> cases b <;> decide

/-- Scan `len` cyclic adjacent edges starting at natural position `pos`.
When the edge `pos+t → pos+t+1` flips, record the pre-flip natural position
and the pre-flip Bool value. -/
def flipBlocksFrom {n : ℕ} [NeZero n]
    (p : ZMod n → Bool) (pos : ℕ) : ℕ → List (ℕ × Bool)
  | 0 => []
  | len + 1 =>
      let rest := flipBlocksFrom p (pos + 1) len
      if p (pos : ZMod n) ≠ p ((pos + 1 : ℕ) : ZMod n) then
        (pos, p (pos : ZMod n)) :: rest
      else
        rest

/-- The cyclic flip count of a Bool-labelled `ZMod n` cycle.  This is exactly
the number of cyclic adjacent positions `i → i+1` where `p` changes value. -/
def cyclicFlips {n : ℕ} [NeZero n] (p : ZMod n → Bool) : ℕ :=
  (flipBlocksFrom p 0 n).length

/-- Strictly increasing/bounded position chain.  `PosChain N lo xs` says every
recorded position in `xs` is at least `lo`, below `N`, and later positions are
strictly after earlier positions. -/
def PosChain (N lo : ℕ) : List (ℕ × Bool) → Prop
  | [] => True
  | x :: xs => lo ≤ x.1 ∧ x.1 < N ∧ PosChain N (x.1 + 1) xs

lemma PosChain.mono_left {N lo lo' : ℕ} {xs : List (ℕ × Bool)}
    (hlo : lo ≤ lo') : PosChain N lo' xs → PosChain N lo xs := by
  cases xs with
  | nil => simp [PosChain]
  | cons x xs =>
      intro h
      rcases h with ⟨hlo', hxN, htail⟩
      exact ⟨le_trans hlo hlo', hxN, htail⟩

/-- The scanner records positions in increasing order and below the supplied
upper bound. -/
theorem flipBlocksFrom_posChain {n : ℕ} [NeZero n]
    (p : ZMod n → Bool) (N pos len : ℕ)
    (hN : pos + len ≤ N) :
    PosChain N pos (flipBlocksFrom p pos len) := by
  induction len generalizing pos with
  | zero =>
      simp [flipBlocksFrom, PosChain]
  | succ len ih =>
      by_cases hflip : p (pos : ZMod n) ≠ p ((pos + 1 : ℕ) : ZMod n)
      · have hposN : pos < N := by omega
        have htail : PosChain N (pos + 1) (flipBlocksFrom p (pos + 1) len) := by
          exact ih (pos + 1) (by omega)
        simp [flipBlocksFrom, hflip, PosChain, hposN, htail]
      · have htail : PosChain N (pos + 1) (flipBlocksFrom p (pos + 1) len) := by
          exact ih (pos + 1) (by omega)
        exact PosChain.mono_left (Nat.le_succ pos) (by
          simpa [flipBlocksFrom, hflip] using htail)

/-- Every recorded pair stores the actual Bool value at its recorded natural
position. -/
theorem flipBlocksFrom_sound {n : ℕ} [NeZero n]
    (p : ZMod n → Bool) :
    ∀ pos len x, x ∈ flipBlocksFrom p pos len → x.2 = p (x.1 : ZMod n) := by
  intro pos len
  induction len generalizing pos with
  | zero =>
      intro x hx
      simp [flipBlocksFrom] at hx
  | succ len ih =>
      intro x hx
      by_cases hflip : p (pos : ZMod n) ≠ p ((pos + 1 : ℕ) : ZMod n)
      · simp [flipBlocksFrom, hflip] at hx
        rcases hx with hx | hx
        · rcases hx with rfl
          rfl
        · exact ih (pos + 1) x hx
      · have hx' : x ∈ flipBlocksFrom p (pos + 1) len := by
          simpa [flipBlocksFrom, hflip] using hx
        exact ih (pos + 1) x hx'

/-- If the scanner output is nonempty, its first stored Bool is the value at
`pos`.  This is the key invariant saying that no unrecorded flip occurred before
the first recorded one. -/
theorem flipBlocksFrom_head_value {n : ℕ} [NeZero n]
    (p : ZMod n → Bool) :
    ∀ pos len x xs,
      flipBlocksFrom p pos len = x :: xs → x.2 = p (pos : ZMod n) := by
  intro pos len
  induction len generalizing pos with
  | zero =>
      intro x xs h
      simp [flipBlocksFrom] at h
  | succ len ih =>
      intro x xs h
      by_cases hflip : p (pos : ZMod n) ≠ p ((pos + 1 : ℕ) : ZMod n)
      · simp [flipBlocksFrom, hflip] at h
        rcases h with ⟨rfl, rfl⟩
        rfl
      · have hEq : p (pos : ZMod n) = p ((pos + 1 : ℕ) : ZMod n) := not_ne.mp hflip
        have hrest : flipBlocksFrom p (pos + 1) len = x :: xs := by
          simpa [flipBlocksFrom, hflip] using h
        have hx := ih (pos + 1) x xs hrest
        simpa [hEq] using hx

/-- Adjacent stored Bool values alternate. -/
def AlternatingValues : List (ℕ × Bool) → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x.2 ≠ y.2 ∧ AlternatingValues (y :: xs)

/-- The scanner output alternates in Bool value.  Consecutive records are
consecutive maximal constant blocks. -/
theorem flipBlocksFrom_alternatingValues {n : ℕ} [NeZero n]
    (p : ZMod n → Bool) :
    ∀ pos len, AlternatingValues (flipBlocksFrom p pos len) := by
  intro pos len
  induction len generalizing pos with
  | zero =>
      simp [flipBlocksFrom, AlternatingValues]
  | succ len ih =>
      by_cases hflip : p (pos : ZMod n) ≠ p ((pos + 1 : ℕ) : ZMod n)
      · cases hrest : flipBlocksFrom p (pos + 1) len with
        | nil =>
            simp [flipBlocksFrom, hflip, hrest, AlternatingValues]
        | cons y ys =>
            have hy : y.2 = p ((pos + 1 : ℕ) : ZMod n) := by
              exact flipBlocksFrom_head_value p (pos + 1) len y ys hrest
            have htail : AlternatingValues (y :: ys) := by
              simpa [hrest] using ih (pos + 1)
            have hne : p (pos : ZMod n) ≠ y.2 := by
              simpa [hy] using hflip
            simp [flipBlocksFrom, hflip, hrest, AlternatingValues, hne, htail]
      · simpa [flipBlocksFrom, hflip] using ih (pos + 1)

/-- Mod-2 telescope for an arbitrary scanned segment: the parity of the number
of flips from `pos` through `len` edges is the mod-2 sum of the endpoint Bool
values. -/
theorem flipBlocksFrom_length_mod_two {n : ℕ} [NeZero n]
    (p : ZMod n → Bool) :
    ∀ pos len,
      (((flipBlocksFrom p pos len).length : ℕ) : ZMod 2)
        = boolZ (p (pos : ZMod n)) + boolZ (p ((pos + len : ℕ) : ZMod n)) := by
  intro pos len
  induction len generalizing pos with
  | zero =>
      simpa [flipBlocksFrom, boolZ_self_add]
        using (boolZ_self_add (p (pos : ZMod n))).symm
  | succ len ih =>
      have hNat : pos + 1 + len = pos + (len + 1) := by omega
      have ih' := ih (pos + 1)
      rw [hNat] at ih'
      by_cases hflip : p (pos : ZMod n) ≠ p ((pos + 1 : ℕ) : ZMod n)
      · have hInd := flipIndicator_cast (p (pos : ZMod n))
          (p ((pos + 1 : ℕ) : ZMod n))
        have hOne : ((1 : ℕ) : ZMod 2)
            = boolZ (p (pos : ZMod n)) + boolZ (p ((pos + 1 : ℕ) : ZMod n)) := by
          simpa [hflip] using hInd
        calc
          (((flipBlocksFrom p pos (len + 1)).length : ℕ) : ZMod 2)
              = ((1 : ℕ) : ZMod 2)
                  + (((flipBlocksFrom p (pos + 1) len).length : ℕ) : ZMod 2) := by
                    simp [flipBlocksFrom, hflip, Nat.cast_add]
          _ = (boolZ (p (pos : ZMod n)) + boolZ (p ((pos + 1 : ℕ) : ZMod n)))
                + (boolZ (p ((pos + 1 : ℕ) : ZMod n))
                    + boolZ (p ((pos + (len + 1) : ℕ) : ZMod n))) := by
                    rw [hOne, ih']
          _ = boolZ (p (pos : ZMod n))
                + boolZ (p ((pos + (len + 1) : ℕ) : ZMod n)) := by
                    cases p (pos : ZMod n) <;>
                    cases p ((pos + 1 : ℕ) : ZMod n) <;>
                    cases p ((pos + (len + 1) : ℕ) : ZMod n) <;>
                    decide
      · have hEq : p (pos : ZMod n) = p ((pos + 1 : ℕ) : ZMod n) := not_ne.mp hflip
        calc
          (((flipBlocksFrom p pos (len + 1)).length : ℕ) : ZMod 2)
              = (((flipBlocksFrom p (pos + 1) len).length : ℕ) : ZMod 2) := by
                    simp [flipBlocksFrom, hflip]
          _ = boolZ (p ((pos + 1 : ℕ) : ZMod n))
                + boolZ (p ((pos + (len + 1) : ℕ) : ZMod n)) := ih'
          _ = boolZ (p (pos : ZMod n))
                + boolZ (p ((pos + (len + 1) : ℕ) : ZMod n)) := by
                    rw [hEq]

/-- The cyclic Bool flip count is even. -/
theorem cyclicFlips_even {n : ℕ} [NeZero n] (p : ZMod n → Bool) :
    Even (cyclicFlips p) := by
  have hmod := flipBlocksFrom_length_mod_two p 0 n
  have hzero : (((cyclicFlips p : ℕ) : ZMod 2) = 0) := by
    simpa [cyclicFlips, Nat.zero_add, ZMod.natCast_self, boolZ_self_add]
      using hmod
  exact ZMod.natCast_eq_zero_iff_even.mp hzero

lemma bool_eq_of_ne_ne {a b c : Bool} (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Main extraction theorem, in natural cyclic representatives.

If the cyclic Bool sequence has more than two flips, then, since the flip count
is even, it has at least four flips.  The first four recorded flip-block
representatives are cyclically ordered and alternate in value. -/
theorem exists_four_ordered_alternating_of_two_lt_cyclicFlips
    {n : ℕ} [NeZero n] (p : ZMod n → Bool)
    (hgt : 2 < cyclicFlips p) :
    ∃ k0 k1 k2 k3 : ℕ,
      k0 < k1 ∧ k1 < k2 ∧ k2 < k3 ∧ k3 < n ∧
      p (k0 : ZMod n) = p (k2 : ZMod n) ∧
      p (k1 : ZMod n) = p (k3 : ZMod n) ∧
      p (k0 : ZMod n) ≠ p (k1 : ZMod n) := by
  classical
  let L : List (ℕ × Bool) := flipBlocksFrom p 0 n
  have hLenEven : Even L.length := by
    simpa [L, cyclicFlips] using cyclicFlips_even p
  have hLenGt : 2 < L.length := by
    simpa [L, cyclicFlips] using hgt
  have hLen4 : 4 ≤ L.length := by
    rcases hLenEven with ⟨r, hr⟩
    omega
  have hchain : PosChain n 0 L := by
    simpa [L] using flipBlocksFrom_posChain p n 0 n (by omega)
  have halt : AlternatingValues L := by
    simpa [L] using flipBlocksFrom_alternatingValues p 0 n
  have hsound : ∀ x ∈ L, x.2 = p (x.1 : ZMod n) := by
    intro x hx
    exact flipBlocksFrom_sound p 0 n x (by simpa [L] using hx)

  rcases L with _ | x0 L1
  · simp at hLen4
  rcases L1 with _ | x1 L2
  · simp at hLen4
  rcases L2 with _ | x2 L3
  · simp at hLen4
  rcases L3 with _ | x3 rest
  · simp at hLen4

  -- Position order and bound.
  rcases hchain with ⟨_, hx0N, hchain⟩
  rcases hchain with ⟨hx01, hx1N, hchain⟩
  rcases hchain with ⟨hx12, hx2N, hchain⟩
  rcases hchain with ⟨hx23, hx3N, _⟩
  have hk01 : x0.1 < x1.1 := by omega
  have hk12 : x1.1 < x2.1 := by omega
  have hk23 : x2.1 < x3.1 := by omega

  -- Alternating stored values.
  simp [AlternatingValues] at halt
  rcases halt with ⟨h01, h12, h23, _⟩
  have h02val : x0.2 = x2.2 := bool_eq_of_ne_ne h01 h12
  have h13val : x1.2 = x3.2 := bool_eq_of_ne_ne h12 h23

  -- Stored values are actual values of `p` at the stored natural positions.
  have hs0 : x0.2 = p (x0.1 : ZMod n) := hsound x0 (by simp)
  have hs1 : x1.2 = p (x1.1 : ZMod n) := hsound x1 (by simp)
  have hs2 : x2.2 = p (x2.1 : ZMod n) := hsound x2 (by simp)
  have hs3 : x3.2 = p (x3.1 : ZMod n) := hsound x3 (by simp)

  refine ⟨x0.1, x1.1, x2.1, x3.1, hk01, hk12, hk23, hx3N, ?_, ?_, ?_⟩
  · rw [← hs0, ← hs2]
    exact h02val
  · rw [← hs1, ← hs3]
    exact h13val
  · rw [← hs0, ← hs1]
    exact h01

/-- A `Fin n` wrapper.  It uses `ZMod.val` to read a `ZMod n` index as the
corresponding `Fin n` index. -/
def cyclicFlipsFin {n : ℕ} [NeZero n] (p : Fin n → Bool) : ℕ :=
  cyclicFlips (fun z : ZMod n => p ⟨z.val, z.val_lt⟩)

/-- The same extraction theorem for `p : Fin n → Bool`. -/
theorem exists_four_ordered_alternating_of_two_lt_cyclicFlipsFin
    {n : ℕ} [NeZero n] (p : Fin n → Bool)
    (hgt : 2 < cyclicFlipsFin p) :
    ∃ k0 k1 k2 k3 : ℕ,
      k0 < k1 ∧ k1 < k2 ∧ k2 < k3 ∧ k3 < n ∧
      p ⟨k0, by omega⟩ = p ⟨k2, by omega⟩ ∧
      p ⟨k1, by omega⟩ = p ⟨k3, by omega⟩ ∧
      p ⟨k0, by omega⟩ ≠ p ⟨k1, by omega⟩ := by
  classical
  let q : ZMod n → Bool := fun z => p ⟨z.val, z.val_lt⟩
  obtain ⟨k0, k1, k2, k3, hk01, hk12, hk23, hk3n, h02, h13, h01⟩ :=
    exists_four_ordered_alternating_of_two_lt_cyclicFlips q (by
      simpa [cyclicFlipsFin, q] using hgt)
  have hk0n : k0 < n := by omega
  have hk1n : k1 < n := by omega
  have hk2n : k2 < n := by omega
  have hv0 : ((k0 : ZMod n).val) = k0 := by
    exact ZMod.val_natCast_of_lt hk0n
  have hv1 : ((k1 : ZMod n).val) = k1 := by
    exact ZMod.val_natCast_of_lt hk1n
  have hv2 : ((k2 : ZMod n).val) = k2 := by
    exact ZMod.val_natCast_of_lt hk2n
  have hv3 : ((k3 : ZMod n).val) = k3 := by
    exact ZMod.val_natCast_of_lt hk3n
  refine ⟨k0, k1, k2, k3, hk01, hk12, hk23, hk3n, ?_, ?_, ?_⟩
  · simpa [q, hv0, hv2] using h02
  · simpa [q, hv1, hv3] using h13
  · simpa [q, hv0, hv1] using h01

end ProofsInTheBook.Ch13BoolCyclicExtraction
```

## Notes for integrating with the repo’s list-facing API

The theorem above defines `cyclicFlips` by a scanner over `ZMod n`, rather than by `cyclicFlips (List.ofFn p)`.  It counts the same cyclic adjacent changes: for every natural `k < n`, it inspects the edge

```lean
(k : ZMod n) → (k + 1 : ZMod n)
```

exactly once.  If the repo already has a list-level definition in `ZinanCh13LinkInterval.lean`, add only a compatibility theorem:

```lean
-- schematic adapter; names depend on the landed file
 theorem cyclicFlips_listOfFn_eq_cyclicFlipsFin
    {n : ℕ} [NeZero n] (p : Fin n → Bool) :
    ZinanCh13LinkInterval.cyclicFlips (List.ofFn p) = cyclicFlipsFin p := by
  -- unfold both definitions; both are a fold over the same cyclic edges.
  -- Use `List.ofFn_get`, `List.length_ofFn`, `Fin.val_add`, and
  -- `ZMod.val_natCast_of_lt` for the wrap case.
  ...
```

Once that adapter is in place, the repo-facing theorem is just:

```lean
 theorem exists_four_ordered_alternating_of_two_lt_list_cyclicFlips
    {n : ℕ} [NeZero n] (p : Fin n → Bool)
    (hgt : 2 < ZinanCh13LinkInterval.cyclicFlips (List.ofFn p)) :
    ∃ k0 k1 k2 k3 : ℕ,
      k0 < k1 ∧ k1 < k2 ∧ k2 < k3 ∧ k3 < n ∧
      p ⟨k0, by omega⟩ = p ⟨k2, by omega⟩ ∧
      p ⟨k1, by omega⟩ = p ⟨k3, by omega⟩ ∧
      p ⟨k0, by omega⟩ ≠ p ⟨k1, by omega⟩ := by
  apply exists_four_ordered_alternating_of_two_lt_cyclicFlipsFin
  rwa [← cyclicFlips_listOfFn_eq_cyclicFlipsFin]
```

Mathlib/API items used in the self-contained proof: `ZMod`, `ZMod.natCast_self`, `ZMod.natCast_eq_zero_iff_even`, `ZMod.val_natCast_of_lt`, `Nat.le_induction`-style induction through `omega`, ordinary `List` pattern matching, and `simp` over recursively defined list scanners.
