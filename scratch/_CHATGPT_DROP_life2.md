# Finite Bool cyclic-flip extraction: `> 2` flips gives four alternating indices

This is the requested pure combinatorial extraction lemma for Chapter 13 Route B.  It is list-facing: the main theorem assumes exactly

```lean
2 < ProofsInTheBook.Ch13ArmVertex.cyclicFlips (List.ofFn p)
```

for `p : Fin n → Bool`, and returns four strictly ordered `Fin n` indices whose values alternate.

The proof uses the landed list API in `ProofsInTheBook.Ch13ArmVertex`:

* `flips : List Bool → ℕ`, the linear adjacent flip count;
* `cyclicFlips : List Bool → ℕ`, defined by closing a nonempty list with its head;
* `cyclicFlips_even`, the already landed parity theorem.

No geometry, no cyclic order topology, and no turning-number argument appears.  The only extraction structure added below is a small list scanner `flipRecordsFrom`: while walking the closed list, it records every flip position together with the value immediately before the flip.  These records are strictly ordered, their stored values alternate, and their length is exactly the landed `cyclicFlips` count.  Since `cyclicFlips` is even, `2 < cyclicFlips` gives at least four records; the first four are the desired alternating indices.

```lean
import Mathlib
import ProofsInTheBook.Ch13ArmVertex

noncomputable section

namespace ProofsInTheBook.Ch13BoolCyclicExtraction

open ProofsInTheBook.Ch13ArmVertex

/-- `flipRecordsFrom k xs` scans the linear list `xs`, starting with absolute
position `k`.  For every adjacent pair `a,b` with `a ≠ b`, it records the
pre-flip position and the pre-flip value `(k,a)`. -/
def flipRecordsFrom : ℕ → List Bool → List (ℕ × Bool)
  | _, [] => []
  | _, [_] => []
  | k, a :: b :: xs =>
      if a ≠ b then
        (k, a) :: flipRecordsFrom (k + 1) (b :: xs)
      else
        flipRecordsFrom (k + 1) (b :: xs)

/-- The record scanner has exactly the same length as the landed linear flip
count `Ch13ArmVertex.flips`. -/
theorem flipRecordsFrom_length :
    ∀ (k : ℕ) (xs : List Bool), (flipRecordsFrom k xs).length = flips xs
  | k, [] => by simp [flipRecordsFrom, flips]
  | k, [a] => by simp [flipRecordsFrom, flips]
  | k, a :: b :: xs => by
      by_cases h : a ≠ b
      · simp [flipRecordsFrom, flips, h, flipRecordsFrom_length (k + 1) (b :: xs)]
      · simp [flipRecordsFrom, flips, h, flipRecordsFrom_length (k + 1) (b :: xs)]

/-- Records for the cyclic flip count: close a nonempty list by appending its head,
then record the linear flips of that closed list. -/
def cyclicFlipRecords : List Bool → List (ℕ × Bool)
  | [] => []
  | h :: t => flipRecordsFrom 0 ((h :: t) ++ [h])

/-- The scanner records exactly the landed cyclic flip count. -/
theorem cyclicFlipRecords_length (l : List Bool) :
    (cyclicFlipRecords l).length = cyclicFlips l := by
  cases l with
  | nil => simp [cyclicFlipRecords, cyclicFlips]
  | cons h t =>
      simp [cyclicFlipRecords, cyclicFlips, flipRecordsFrom_length]

/-- A strict increasing/bounded chain of recorded natural positions.  `PosChain N lo xs`
says: every record in `xs` has position at least `lo`, below `N`, and later records
are strictly after earlier records. -/
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

/-- The linear record scanner produces increasing positions below `N`, provided the
scanned edge positions fit below `N`. -/
theorem flipRecordsFrom_posChain (N : ℕ) :
    ∀ (k : ℕ) (xs : List Bool), k + xs.length ≤ N + 1 →
      PosChain N k (flipRecordsFrom k xs)
  | k, [], _ => by simp [flipRecordsFrom, PosChain]
  | k, [a], _ => by simp [flipRecordsFrom, PosChain]
  | k, a :: b :: xs, hbound => by
      have htail : PosChain N (k + 1) (flipRecordsFrom (k + 1) (b :: xs)) := by
        exact flipRecordsFrom_posChain N (k + 1) (b :: xs) (by omega)
      by_cases h : a ≠ b
      · have hkN : k < N := by omega
        simp [flipRecordsFrom, h, PosChain, hkN, htail]
      · exact PosChain.mono_left (Nat.le_succ k) (by
          simpa [flipRecordsFrom, h] using htail)

/-- The cyclic record scanner produces positions strictly below the original list length. -/
theorem cyclicFlipRecords_posChain (l : List Bool) :
    PosChain l.length 0 (cyclicFlipRecords l) := by
  cases l with
  | nil => simp [cyclicFlipRecords, PosChain]
  | cons h t =>
      have hbound : 0 + ((h :: t) ++ [h]).length ≤ (h :: t).length + 1 := by simp
      simpa [cyclicFlipRecords] using
        flipRecordsFrom_posChain (h :: t).length 0 ((h :: t) ++ [h]) hbound

/-- If the linear record scanner is nonempty, the first stored value is the first
value of the scanned list.  If there was no flip at the current edge, the proof
moves to the tail, using that the current and next values are equal. -/
theorem flipRecordsFrom_head_value :
    ∀ (k : ℕ) (a : Bool) (xs : List Bool) (x : ℕ × Bool) (rest : List (ℕ × Bool)),
      flipRecordsFrom k (a :: xs) = x :: rest → x.2 = a
  | k, a, [], x, rest, h => by simp [flipRecordsFrom] at h
  | k, a, b :: xs, x, rest, hrec => by
      by_cases h : a ≠ b
      · simp [flipRecordsFrom, h] at hrec
        rcases hrec with ⟨rfl, rfl⟩
        rfl
      · have hab : a = b := not_ne.mp h
        have htail : flipRecordsFrom (k + 1) (b :: xs) = x :: rest := by
          simpa [flipRecordsFrom, h] using hrec
        have hx := flipRecordsFrom_head_value (k + 1) b xs x rest htail
        simpa [hab] using hx

/-- Stored Bool values alternate along the record list. -/
def AlternatingValues : List (ℕ × Bool) → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x.2 ≠ y.2 ∧ AlternatingValues (y :: xs)

/-- Consecutive records are consecutive constant blocks, hence their stored Bool values alternate. -/
theorem flipRecordsFrom_alternatingValues :
    ∀ (k : ℕ) (xs : List Bool), AlternatingValues (flipRecordsFrom k xs)
  | k, [] => by simp [flipRecordsFrom, AlternatingValues]
  | k, [a] => by simp [flipRecordsFrom, AlternatingValues]
  | k, a :: b :: xs => by
      by_cases h : a ≠ b
      · cases htail : flipRecordsFrom (k + 1) (b :: xs) with
        | nil =>
            simp [flipRecordsFrom, h, htail, AlternatingValues]
        | cons y ys =>
            have hy : y.2 = b := flipRecordsFrom_head_value (k + 1) b xs y ys htail
            have halt : AlternatingValues (y :: ys) := by
              simpa [htail] using flipRecordsFrom_alternatingValues (k + 1) (b :: xs)
            have hay : a ≠ y.2 := by simpa [hy] using h
            simp [flipRecordsFrom, h, htail, AlternatingValues, hay, halt]
      · simpa [flipRecordsFrom, h] using flipRecordsFrom_alternatingValues (k + 1) (b :: xs)

/-- The cyclic record list has alternating stored values. -/
theorem cyclicFlipRecords_alternatingValues (l : List Bool) :
    AlternatingValues (cyclicFlipRecords l) := by
  cases l with
  | nil => simp [cyclicFlipRecords, AlternatingValues]
  | cons h t =>
      simpa [cyclicFlipRecords] using
        flipRecordsFrom_alternatingValues 0 ((h :: t) ++ [h])

lemma bool_eq_of_ne_ne {a b c : Bool} (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Getting from the left side of an append agrees with getting from the original list.
This local lemma avoids relying on a particular Mathlib name for the same fact. -/
theorem get_append_left' {α : Type*} (l r : List α) {i : ℕ}
    (hi : i < l.length) (hi' : i < (l ++ r).length) :
    (l ++ r).get ⟨i, hi'⟩ = l.get ⟨i, hi⟩ := by
  induction l generalizing i with
  | nil => cases hi
  | cons a l ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi_l : i < l.length := by simpa using hi
          have hi_app : i < (l ++ r).length := by
            simpa [List.cons_append] using hi'
          simpa [List.cons_append] using ih r hi_l hi_app

/-- A record stores the actual value of the scanned list at its recorded position. -/
theorem flipRecordsFrom_sound_get :
    ∀ (k : ℕ) (xs : List Bool) (x : ℕ × Bool),
      x ∈ flipRecordsFrom k xs →
        k ≤ x.1 ∧ ∃ hx : x.1 - k < xs.length,
          x.2 = xs.get ⟨x.1 - k, hx⟩
  | k, [], x, hx => by simp [flipRecordsFrom] at hx
  | k, [a], x, hx => by simp [flipRecordsFrom] at hx
  | k, a :: b :: xs, x, hx => by
      by_cases h : a ≠ b
      · simp [flipRecordsFrom, h] at hx
        rcases hx with hx | hx
        · rcases hx with rfl
          refine ⟨by omega, ?_⟩
          refine ⟨by simp, ?_⟩
          simp
        · obtain ⟨hge, hlt, hval⟩ := flipRecordsFrom_sound_get (k + 1) (b :: xs) x hx
          refine ⟨by omega, ?_⟩
          have hlt' : x.1 - k < (a :: b :: xs).length := by omega
          refine ⟨hlt', ?_⟩
          have hsub : x.1 - k = (x.1 - (k + 1)) + 1 := by omega
          calc
            x.2 = (b :: xs).get ⟨x.1 - (k + 1), hlt⟩ := hval
            _ = (a :: b :: xs).get ⟨x.1 - k, hlt'⟩ := by
                simpa [hsub]
      · have hxTail : x ∈ flipRecordsFrom (k + 1) (b :: xs) := by
          simpa [flipRecordsFrom, h] using hx
        obtain ⟨hge, hlt, hval⟩ := flipRecordsFrom_sound_get (k + 1) (b :: xs) x hxTail
        refine ⟨by omega, ?_⟩
        have hlt' : x.1 - k < (a :: b :: xs).length := by omega
        refine ⟨hlt', ?_⟩
        have hsub : x.1 - k = (x.1 - (k + 1)) + 1 := by omega
        calc
          x.2 = (b :: xs).get ⟨x.1 - (k + 1), hlt⟩ := hval
          _ = (a :: b :: xs).get ⟨x.1 - k, hlt'⟩ := by
              simpa [hsub]

/-- A cyclic record stores the actual value of the original, unclosed list at its
recorded position.  The extra final head appended for the cyclic close is never a
record position, because `cyclicFlipRecords_posChain` gives positions `< l.length`. -/
theorem cyclicFlipRecords_value_get (l : List Bool) {x : ℕ × Bool}
    (hx : x ∈ cyclicFlipRecords l) (hk : x.1 < l.length) :
    x.2 = l.get ⟨x.1, hk⟩ := by
  cases l with
  | nil => simp [cyclicFlipRecords] at hx
  | cons h t =>
      obtain ⟨_hge, hlt, hval⟩ :=
        flipRecordsFrom_sound_get 0 ((h :: t) ++ [h]) x (by
          simpa [cyclicFlipRecords] using hx)
      have hlt' : x.1 < ((h :: t) ++ [h]).length := by simpa using hlt
      have hget := get_append_left' (h :: t) [h] hk hlt'
      calc
        x.2 = ((h :: t) ++ [h]).get ⟨x.1, hlt'⟩ := by simpa using hval
        _ = (h :: t).get ⟨x.1, hk⟩ := hget

/-- List-level extraction.  If a Bool list has more than two cyclic flips, then four
strictly ordered positions carry alternating values. -/
theorem exists_four_ordered_alternating_get_of_two_lt_cyclicFlips
    {l : List Bool} (hgt : 2 < cyclicFlips l) :
    ∃ k0 k1 k2 k3 : ℕ,
    ∃ hk0 : k0 < l.length, ∃ hk1 : k1 < l.length,
    ∃ hk2 : k2 < l.length, ∃ hk3 : k3 < l.length,
      k0 < k1 ∧ k1 < k2 ∧ k2 < k3 ∧
      l.get ⟨k0, hk0⟩ = l.get ⟨k2, hk2⟩ ∧
      l.get ⟨k1, hk1⟩ = l.get ⟨k3, hk3⟩ ∧
      l.get ⟨k0, hk0⟩ ≠ l.get ⟨k1, hk1⟩ := by
  classical
  let R : List (ℕ × Bool) := cyclicFlipRecords l
  have hLenEq : R.length = cyclicFlips l := by
    simpa [R] using cyclicFlipRecords_length l
  have hLenEven : Even R.length := by
    rw [hLenEq]
    exact cyclicFlips_even l
  have hLenGt : 2 < R.length := by
    rwa [hLenEq]
  have hLen4 : 4 ≤ R.length := by
    rcases hLenEven with ⟨r, hr⟩
    omega
  have hchain : PosChain l.length 0 R := by
    simpa [R] using cyclicFlipRecords_posChain l
  have halt : AlternatingValues R := by
    simpa [R] using cyclicFlipRecords_alternatingValues l
  have hvalue : ∀ x ∈ R, ∀ hk : x.1 < l.length, x.2 = l.get ⟨x.1, hk⟩ := by
    intro x hx hk
    exact cyclicFlipRecords_value_get l (by simpa [R] using hx) hk

  rcases R with _ | x0 R1
  · simp at hLen4
  rcases R1 with _ | x1 R2
  · simp at hLen4
  rcases R2 with _ | x2 R3
  · simp at hLen4
  rcases R3 with _ | x3 rest
  · simp at hLen4

  -- Positional order and bounds.
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

  -- Stored values are actual list values at the stored positions.
  have hv0 := hvalue x0 (by simp) hx0N
  have hv1 := hvalue x1 (by simp) hx1N
  have hv2 := hvalue x2 (by simp) hx2N
  have hv3 := hvalue x3 (by simp) hx3N

  refine ⟨x0.1, x1.1, x2.1, x3.1, hx0N, hx1N, hx2N, hx3N,
    hk01, hk12, hk23, ?_, ?_, ?_⟩
  · rw [← hv0, ← hv2]
    exact h02val
  · rw [← hv1, ← hv3]
    exact h13val
  · rw [← hv0, ← hv1]
    exact h01

/-- Main `Fin n` / `List.ofFn` extraction theorem.  This is the requested statement:
`cyclicFlips (List.ofFn p) > 2` gives four strictly ordered cyclic indices whose
Bool values alternate. -/
theorem exists_four_ordered_alternating_of_two_lt_cyclicFlips_ofFn
    {n : ℕ} (p : Fin n → Bool)
    (hgt : 2 < cyclicFlips (List.ofFn p)) :
    ∃ i0 i1 i2 i3 : Fin n,
      i0 < i1 ∧ i1 < i2 ∧ i2 < i3 ∧
      p i0 = p i2 ∧ p i1 = p i3 ∧ p i0 ≠ p i1 := by
  classical
  obtain ⟨k0, k1, k2, k3, hk0, hk1, hk2, hk3,
    hk01, hk12, hk23, h02, h13, h01⟩ :=
      exists_four_ordered_alternating_get_of_two_lt_cyclicFlips
        (l := List.ofFn p) hgt
  let i0 : Fin n := ⟨k0, by simpa using hk0⟩
  let i1 : Fin n := ⟨k1, by simpa using hk1⟩
  let i2 : Fin n := ⟨k2, by simpa using hk2⟩
  let i3 : Fin n := ⟨k3, by simpa using hk3⟩
  have hi01 : i0 < i1 := by simpa [i0, i1] using hk01
  have hi12 : i1 < i2 := by simpa [i1, i2] using hk12
  have hi23 : i2 < i3 := by simpa [i2, i3] using hk23
  have hv0 : (List.ofFn p).get ⟨k0, hk0⟩ = p i0 := by simp [i0]
  have hv1 : (List.ofFn p).get ⟨k1, hk1⟩ = p i1 := by simp [i1]
  have hv2 : (List.ofFn p).get ⟨k2, hk2⟩ = p i2 := by simp [i2]
  have hv3 : (List.ofFn p).get ⟨k3, hk3⟩ = p i3 := by simp [i3]
  refine ⟨i0, i1, i2, i3, hi01, hi12, hi23, ?_, ?_, ?_⟩
  · rw [← hv0, ← hv2]
    exact h02
  · rw [← hv1, ← hv3]
    exact h13
  · rw [← hv0, ← hv1]
    exact h01

/-- Same theorem with the two explicit Bool patterns exposed. -/
theorem exists_four_ordered_alternating_bool_cases_of_two_lt_cyclicFlips_ofFn
    {n : ℕ} (p : Fin n → Bool)
    (hgt : 2 < cyclicFlips (List.ofFn p)) :
    ∃ i0 i1 i2 i3 : Fin n,
      i0 < i1 ∧ i1 < i2 ∧ i2 < i3 ∧
      ((p i0 = true ∧ p i1 = false ∧ p i2 = true ∧ p i3 = false) ∨
       (p i0 = false ∧ p i1 = true ∧ p i2 = false ∧ p i3 = true)) := by
  obtain ⟨i0, i1, i2, i3, hi01, hi12, hi23, h02, h13, h01⟩ :=
    exists_four_ordered_alternating_of_two_lt_cyclicFlips_ofFn p hgt
  refine ⟨i0, i1, i2, i3, hi01, hi12, hi23, ?_⟩
  cases h0 : p i0
  · right
    have h2 : p i2 = false := by rw [← h02, h0]
    have h1 : p i1 = true := by
      cases h1' : p i1 <;> simp_all
    have h3 : p i3 = true := by rw [← h13, h1]
    exact ⟨h0, h1, h2, h3⟩
  · left
    have h2 : p i2 = true := by rw [← h02, h0]
    have h1 : p i1 = false := by
      cases h1' : p i1 <;> simp_all
    have h3 : p i3 = false := by rw [← h13, h1]
    exact ⟨h0, h1, h2, h3⟩

end ProofsInTheBook.Ch13BoolCyclicExtraction
```

## Integration note

The theorem above is intentionally phrased against the landed list count:

```lean
ProofsInTheBook.Ch13ArmVertex.cyclicFlips (List.ofFn p)
```

so the Route B caller does not need any adapter theorem.  Apply

```lean
ProofsInTheBook.Ch13BoolCyclicExtraction
  .exists_four_ordered_alternating_of_two_lt_cyclicFlips_ofFn p hgt
```

or, if the downstream contradiction wants the explicit `true/false/true/false` disjunction, apply

```lean
ProofsInTheBook.Ch13BoolCyclicExtraction
  .exists_four_ordered_alternating_bool_cases_of_two_lt_cyclicFlips_ofFn p hgt
```

The only Mathlib/list ingredients used are ordinary recursive `List` pattern matching, `List.get`, `List.ofFn` simp lemmas (`length_ofFn` and `get_ofFn`), `Fin` order, Bool case splits, and `omega`.  The parity input is the repo theorem `ProofsInTheBook.Ch13ArmVertex.cyclicFlips_even`.
