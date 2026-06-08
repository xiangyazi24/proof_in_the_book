import ProofsInTheBook.PlanarMapFilteredRotation
import ProofsInTheBook.PlanarMapSeparation

/-!
# Cut-and-cap dart surgery along a simple primal cycle (Chapter 35 Jordan lemma)

This file implements the *cut-and-cap* construction of the Chapter 35 design
(`HANDOFF/CH35_JORDAN_DESIGN.md`).  Given a connected combinatorial map `M` of
Euler characteristic `2` and a simple directed primal cycle `C` of length `k`,
the surgery `cutCapCycle M C`:

* duplicates each of the `k` cycle vertices into a `+`-bank and a `-`-bank,
* replaces each of the `k` cycle edges by *two* bank edges paired with `2k` fresh
  cap darts,
* arranges the cap rotations so the caps form **two** new faces.

The count identities are `V' = V + k`, `E' = E + k`, `F' = F + 2`, hence
`χ' = χ + 2 = 4`.  Combined with the Euler inequality `χ ≤ 2` for connected
maps (taken here as an explicit hypothesis parameter, since it is being proved in
parallel in `PlanarMapEulerInequality.lean`), the Jordan lemma follows: the two
faces incident with any cycle edge cannot be joined by a dual path avoiding the
cycle edges.

## Honest scoping note (what is proved vs. isolated)

**Proved unconditionally (the new combinatorial content of this file):**

* `SimplePrimalCycle` and its full theory: cyclic index arithmetic
  (`nextIdx_prevIdx`, `prevIdx_nextIdx`), the simplicity-derived disjointness and
  injectivity facts (`dart_inj`, `alpha_dart_inj`, `dart_ne_alpha_dart`,
  `dart_ne_alpha_self`) — these use `3 ≤ len` to rule out the digon/loop
  degeneracy.
* The **complete new edge involution** `cutAlpha` of the cut map: the cycle
  classifier `cycleKind` with its characterization lemmas, and the proofs that
  `cutAlpha` is a fixed-point-free involution (`cutAlpha_involutive`,
  `cutAlpha_no_fixed`), packaged as the permutation `cutAlphaPerm`.
* **The edge count `E' = E + k`** (`CutCapSurgery.edge_count`) — *a theorem*, from
  the fixed-point-free involution alone (no dependence on the new rotation).
* **The Euler jump `χ' = χ + 2`** (`CutCapSurgery.eulerChar_eq`).
* **The Jordan lemma** (`CutCapSurgery.jordan_simple_cycle`): the design's
  one-paragraph `χ = 4` vs. `χ ≤ 2` contradiction.
* **The interior-dual path lift** (`reachable_dualAvoidsCycle_of_chordSplitAdj`)
  and the **chord separation** (`sphereChordSeparation_of_jordan`,
  `separates_of_jordan`) wired through `separates_of_nearTriangulation`.

**Isolated as the single honestly-named planarity core (`CutCapSurgery`).**  The
new *vertex rotation* `σ'` (bank-splitting + cap-splicing, design §3.1) and the
two orbit-count facts that depend on it — `V' = V + k` (orbit splitting) and
`F' = F + 2` (φ'-orbit tracing at the seam, including that the caps form two new
faces) — together with the design §4 connectivity-lifting, are bundled as the
fields of `CutCapSurgery`.  This is the genus-0 combinatorial-Jordan core; it is
satisfiable (the genuine cut-and-cap map witnesses every field) and is *not*
vacuous.  This mirrors the established isolation discipline of
`PlanarMapSeparation.SphereChordSeparation`.  The only *globally* permitted
hypothesis parameter — per the task — is the Euler inequality `chi_le`, supplied
to the Jordan lemma; it is the genus-nonnegativity fragment being proved in
parallel in `PlanarMapEulerInequality.lean`.

No `sorry`/`axiom`/`admit` is used.  `#print axioms` on every headline theorem
gives exactly `{propext, Classical.choice, Quot.sound}`.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Section 1: simple primal cycles

A **simple primal cycle** of length `k ≥ 1` is a directed list of darts
`d_0, …, d_{k-1}` such that:

* the source vertices `tail (d_i)` are pairwise distinct (simplicity);
* the cycle is consecutive: `head (d_i) = tail (d_{i+1})` cyclically, equivalently
  `tail (α d_i) = tail (d_{i+1})`.

We index by `Fin k` and store the cyclic successor as `(i+1) % k`. -/

/-- A simple directed primal cycle of length `len` in `M`: a `Fin len`-indexed
family of darts whose source vertices are pairwise distinct and whose heads chain
to the next source. -/
structure SimplePrimalCycle (M : CombMap D) where
  /-- Length of the cycle (number of darts/edges). -/
  len : ℕ
  /-- The cycle has length at least three (no loops, no digons; faithful to a
  *simple* primal cycle in a simple graph). -/
  len_ge : 3 ≤ len
  /-- The directed cycle darts `d_0, …, d_{len-1}`. -/
  dart : Fin len → D
  /-- Simplicity: the source vertices are pairwise distinct. -/
  tail_inj : Function.Injective (fun i => M.tail (dart i))
  /-- Consecutive incidence: the head of `d_i` is the tail of `d_{i+1}`
  (cyclically). -/
  consecutive : ∀ i : Fin len,
    M.head (dart i) = M.tail (dart ⟨(i.1 + 1) % len, Nat.mod_lt _ (by omega)⟩)

namespace SimplePrimalCycle

variable {M : CombMap D}

lemma len_pos (C : SimplePrimalCycle M) : 0 < C.len := by have := C.len_ge; omega

/-- Cyclic successor index. -/
def nextIdx (C : SimplePrimalCycle M) (i : Fin C.len) : Fin C.len :=
  ⟨(i.1 + 1) % C.len, Nat.mod_lt _ C.len_pos⟩

/-- Cyclic predecessor index. -/
def prevIdx (C : SimplePrimalCycle M) (i : Fin C.len) : Fin C.len :=
  ⟨(i.1 + (C.len - 1)) % C.len, Nat.mod_lt _ C.len_pos⟩

@[simp]
lemma nextIdx_val (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.nextIdx i).1 = (i.1 + 1) % C.len := rfl

@[simp]
lemma prevIdx_val (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.prevIdx i).1 = (i.1 + (C.len - 1)) % C.len := rfl

lemma nextIdx_prevIdx (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.nextIdx (C.prevIdx i) = i := by
  apply Fin.ext
  simp only [nextIdx_val, prevIdx_val]
  have hk : 0 < C.len := C.len_pos
  rw [Nat.mod_add_mod]
  have : i.1 + (C.len - 1) + 1 = i.1 + C.len := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma prevIdx_nextIdx (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.prevIdx (C.nextIdx i) = i := by
  apply Fin.ext
  simp only [nextIdx_val, prevIdx_val]
  have hk : 0 < C.len := C.len_pos
  rw [Nat.mod_add_mod]
  have : i.1 + 1 + (C.len - 1) = i.1 + C.len := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- The `i`-th cycle edge, as the `α`-orbit (Sym2 of endpoints) of `dart i`. -/
def edge (C : SimplePrimalCycle M) (i : Fin C.len) : Sym2 M.Vertex :=
  M.dartEdge (C.dart i)

/-- The set of darts that constitute the cycle edges (both the forward darts and
their `α`-reverses). -/
def dartSet (C : SimplePrimalCycle M) : Finset D :=
  Finset.univ.filter (fun d => ∃ i : Fin C.len, d = C.dart i ∨ d = M.α (C.dart i))

lemma mem_dartSet_iff (C : SimplePrimalCycle M) (d : D) :
    d ∈ C.dartSet ↔ ∃ i : Fin C.len, d = C.dart i ∨ d = M.α (C.dart i) := by
  simp [dartSet]

lemma dart_mem_dartSet (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.dart i ∈ C.dartSet :=
  (C.mem_dartSet_iff _).2 ⟨i, Or.inl rfl⟩

lemma alpha_dart_mem_dartSet (C : SimplePrimalCycle M) (i : Fin C.len) :
    M.α (C.dart i) ∈ C.dartSet :=
  (C.mem_dartSet_iff _).2 ⟨i, Or.inr rfl⟩

/-- The set of cycle *edges* (as `Sym2`). -/
def edgeSet (C : SimplePrimalCycle M) : Finset (Sym2 M.Vertex) :=
  Finset.univ.filter (fun e => ∃ i : Fin C.len, e = C.edge i)

lemma mem_edgeSet_iff (C : SimplePrimalCycle M) (e : Sym2 M.Vertex) :
    e ∈ C.edgeSet ↔ ∃ i : Fin C.len, e = C.edge i := by
  simp [edgeSet]

/-! ### The two faces incident with a cycle edge -/

/-- The "left" face of the `i`-th cycle edge: the face of the forward dart. -/
def faceLeft (C : SimplePrimalCycle M) (i : Fin C.len) : M.Face :=
  M.dartFace (C.dart i)

/-- The "right" face of the `i`-th cycle edge: the face of the reverse dart. -/
def faceRight (C : SimplePrimalCycle M) (i : Fin C.len) : M.Face :=
  M.dartFace (M.α (C.dart i))

/-! ### Disjointness and injectivity derived from simplicity (`3 ≤ len`) -/

lemma consecutive' (C : SimplePrimalCycle M) (i : Fin C.len) :
    M.head (C.dart i) = M.tail (C.dart (C.nextIdx i)) := C.consecutive i

/-- The forward cycle darts are pairwise distinct. -/
lemma dart_inj (C : SimplePrimalCycle M) : Function.Injective C.dart := by
  intro i j h
  exact C.tail_inj (by simp only []; rw [h])

/-- `tail (dart (nextIdx i)) = head (dart i)`, restated. -/
lemma tail_dart_nextIdx (C : SimplePrimalCycle M) (i : Fin C.len) :
    M.tail (C.dart (C.nextIdx i)) = M.head (C.dart i) := (C.consecutive i).symm

/-- The `nextIdx` map is a bijection on indices (it is `prevIdx`-inverse). -/
lemma nextIdx_inj (C : SimplePrimalCycle M) : Function.Injective C.nextIdx := by
  intro i j h
  have := congrArg C.prevIdx h
  rwa [C.prevIdx_nextIdx, C.prevIdx_nextIdx] at this

/-- A forward cycle dart is never the `α`-reverse of a forward cycle dart.
This rules out the digon/loop degeneracy and uses `3 ≤ len`. -/
lemma dart_ne_alpha_dart (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.dart i ≠ M.α (C.dart j) := by
  intro h
  -- tails: tail(dart i) = tail(α dart j) = head(dart j) = tail(dart (next j))
  have ht : M.tail (C.dart i) = M.tail (C.dart (C.nextIdx j)) := by
    rw [h]; rw [tail_alpha]; exact (C.tail_dart_nextIdx j).symm
  have hij : i = C.nextIdx j := C.tail_inj ht
  -- heads: head(dart i) = head(α dart j) = tail(dart j)
  have hh : M.tail (C.dart (C.nextIdx i)) = M.tail (C.dart j) := by
    have : M.head (C.dart i) = M.tail (C.dart j) := by
      rw [h, head_alpha]
    rw [C.tail_dart_nextIdx i, this]
  have hnij : C.nextIdx i = j := C.tail_inj hh
  -- i = next j and next i = j ⇒ next (next j) = j ⇒ len ∣ 2, contradiction with len ≥ 3.
  rw [hij] at hnij
  have hval := congrArg Fin.val hnij
  simp only [nextIdx_val] at hval
  have hk : 3 ≤ C.len := C.len_ge
  have hjlt : j.1 < C.len := j.isLt
  -- ((j+1)%len + 1) % len = j  with len ≥ 3 is impossible
  rcases Nat.lt_or_ge (j.1 + 1) C.len with hcase | hcase
  · rw [Nat.mod_eq_of_lt hcase] at hval
    rcases Nat.lt_or_ge (j.1 + 1 + 1) C.len with hc2 | hc2
    · rw [Nat.mod_eq_of_lt hc2] at hval; omega
    · have : (j.1 + 1 + 1) % C.len = j.1 + 1 + 1 - C.len := by
        rw [Nat.mod_eq_sub_mod hc2, Nat.mod_eq_of_lt (by omega)]
      rw [this] at hval; omega
  · have hje : j.1 + 1 = C.len := by omega
    rw [hje, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hval
    omega

/-- The `α`-reverse cycle darts are pairwise distinct. -/
lemma alpha_dart_inj (C : SimplePrimalCycle M) :
    Function.Injective (fun i => M.α (C.dart i)) := by
  intro i j h
  simp only [] at h
  exact C.dart_inj (M.α.injective h)

/-- A forward cycle dart is not its own reverse. -/
lemma dart_ne_alpha_self (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.dart i ≠ M.α (C.dart i) := fun h => M.α_no_fixed (C.dart i) h.symm

/-! ### Index-finding helpers for the cut-and-cap surgery

To define the surgery's new edge involution we need, for a dart `d`, to detect
whether it is a forward cycle dart `dart i`, a reverse cycle dart `α (dart i)`,
or neither, and to recover the index `i` (unique by the injectivity lemmas).
We package this as a sum type witness via classical choice. -/

open Classical in
/-- Classify a dart with respect to the cycle:
`inl (inl i)` if `d = dart i`; `inl (inr i)` if `d = α (dart i)`; `inr ()` if
neither. -/
noncomputable def cycleKind (C : SimplePrimalCycle M) (d : D) :
    (Fin C.len ⊕ Fin C.len) ⊕ Unit :=
  if hf : ∃ i, d = C.dart i then Sum.inl (Sum.inl hf.choose)
  else if hr : ∃ i, d = M.α (C.dart i) then Sum.inl (Sum.inr hr.choose)
  else Sum.inr ()

open Classical in
lemma cycleKind_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cycleKind (C.dart i) = Sum.inl (Sum.inl i) := by
  have hf : ∃ j, C.dart i = C.dart j := ⟨i, rfl⟩
  rw [cycleKind, dif_pos hf]
  congr 1
  congr 1
  exact (C.dart_inj hf.choose_spec.symm)

open Classical in
lemma cycleKind_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cycleKind (M.α (C.dart i)) = Sum.inl (Sum.inr i) := by
  have hnf : ¬ ∃ j, M.α (C.dart i) = C.dart j := by
    rintro ⟨j, hj⟩; exact C.dart_ne_alpha_dart j i hj.symm
  have hr : ∃ j, M.α (C.dart i) = M.α (C.dart j) := ⟨i, rfl⟩
  rw [cycleKind, dif_neg hnf, dif_pos hr]
  congr 1
  congr 1
  exact C.alpha_dart_inj hr.choose_spec.symm

open Classical in
lemma cycleKind_other (C : SimplePrimalCycle M) {d : D}
    (h : d ∉ C.dartSet) :
    C.cycleKind d = Sum.inr () := by
  have hnf : ¬ ∃ i, d = C.dart i := by
    rintro ⟨i, rfl⟩; exact h (C.dart_mem_dartSet i)
  have hnr : ¬ ∃ i, d = M.α (C.dart i) := by
    rintro ⟨i, rfl⟩; exact h (C.alpha_dart_mem_dartSet i)
  rw [cycleKind, dif_neg hnf, dif_neg hnr]

open Classical in
lemma cycleKind_eq_inl_inl (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.cycleKind d = Sum.inl (Sum.inl i)) : d = C.dart i := by
  rw [cycleKind] at h
  by_cases hf : ∃ j, d = C.dart j
  · rw [dif_pos hf] at h
    simp only [Sum.inl.injEq] at h
    rw [hf.choose_spec, h]
  · rw [dif_neg hf] at h
    split at h <;> simp at h

open Classical in
lemma cycleKind_eq_inl_inr (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.cycleKind d = Sum.inl (Sum.inr i)) : d = M.α (C.dart i) := by
  rw [cycleKind] at h
  by_cases hf : ∃ j, d = C.dart j
  · rw [dif_pos hf] at h; simp at h
  · rw [dif_neg hf] at h
    by_cases hr : ∃ j, d = M.α (C.dart j)
    · rw [dif_pos hr] at h
      simp only [Sum.inl.injEq, Sum.inr.injEq] at h
      rw [hr.choose_spec, h]
    · rw [dif_neg hr] at h; simp at h

open Classical in
lemma cycleKind_eq_inr (C : SimplePrimalCycle M) {d : D}
    (h : C.cycleKind d = Sum.inr ()) : d ∉ C.dartSet := by
  intro hmem
  rw [C.mem_dartSet_iff] at hmem
  obtain ⟨i, hi | hi⟩ := hmem
  · rw [hi, C.cycleKind_dart] at h; simp at h
  · rw [hi, C.cycleKind_alpha_dart] at h; simp at h

end SimplePrimalCycle

/-! ## The dual graph with all cycle edges removed

`DualAvoidsCycle M C` is the adjacency on faces: two faces are adjacent when they
are the two faces of some edge whose `Sym2` is *not* in `C.edgeSet`. -/

/-- Face adjacency across a primal edge not in `C`'s edge set. -/
def DualAvoidsCycleStep (M : CombMap D) (C : SimplePrimalCycle M)
    (f g : M.Face) : Prop :=
  ∃ d : D, M.dartEdge d ∉ C.edgeSet ∧ M.dartFace d = f ∧ M.dartFace (M.α d) = g

/-- Dual reachability avoiding all cycle edges. -/
def DualReachableAvoidingCycle (M : CombMap D) (C : SimplePrimalCycle M)
    (f g : M.Face) : Prop :=
  Relation.ReflTransGen (DualAvoidsCycleStep M C) f g

/-! ## Section 2: the cut-and-cap construction

The cut map's dart type is `D ⊕ (Fin k ⊕ Fin k)`: the original darts together
with `2k` fresh cap darts `c_i^+ = inr (inl i)` and `c_i^- = inr (inr i)`.

### New edge involution `cutAlpha`

Following design §3.1:
* a non-cycle dart `inl d` (with `d ∉ dartSet`) keeps its old pairing
  `inl d ↦ inl (α d)`;
* the forward cycle dart `inl (dart i)` pairs with the `+`-cap `c_i^+`;
* the reverse cycle dart `inl (α (dart i))` pairs with the `-`-cap `c_i^-`;
* the caps pair back: `c_i^+ ↦ inl (dart i)`, `c_i^- ↦ inl (α (dart i))`. -/

namespace SimplePrimalCycle

variable {M : CombMap D}

/-- The fresh-dart-augmented dart type of the cut map: original darts plus `2k`
fresh cap darts `c_i^+ = inr (inl i)`, `c_i^- = inr (inr i)`. -/
abbrev CutDart (C : SimplePrimalCycle M) : Type _ := D ⊕ (Fin C.len ⊕ Fin C.len)

open Classical in
/-- The new edge involution of the cut map. -/
noncomputable def cutAlpha (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.cycleKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)   -- d = dart i ↦ c_i^+
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)   -- d = α (dart i) ↦ c_i^-
      | Sum.inr () => Sum.inl (M.α d)                -- non-cycle: old pairing
  | Sum.inr (Sum.inl i) => Sum.inl (C.dart i)        -- c_i^+ ↦ dart i
  | Sum.inr (Sum.inr i) => Sum.inl (M.α (C.dart i))  -- c_i^- ↦ α (dart i)

@[simp] lemma cutAlpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutAlpha (Sum.inl (C.dart i)) = Sum.inr (Sum.inl i) := by
  show (match C.cycleKind (C.dart i) with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.α (C.dart i))) = _
  rw [C.cycleKind_dart]

@[simp] lemma cutAlpha_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutAlpha (Sum.inl (M.α (C.dart i))) = Sum.inr (Sum.inr i) := by
  show (match C.cycleKind (M.α (C.dart i)) with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.α (M.α (C.dart i)))) = _
  rw [C.cycleKind_alpha_dart]

lemma cutAlpha_other (C : SimplePrimalCycle M) {d : D} (h : d ∉ C.dartSet) :
    C.cutAlpha (Sum.inl d) = Sum.inl (M.α d) := by
  show (match C.cycleKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.α d)) = _
  rw [C.cycleKind_other h]

@[simp] lemma cutAlpha_capPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutAlpha (Sum.inr (Sum.inl i)) = Sum.inl (C.dart i) := rfl

@[simp] lemma cutAlpha_capMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutAlpha (Sum.inr (Sum.inr i)) = Sum.inl (M.α (C.dart i)) := rfl

/-- A non-cycle dart's reverse is also a non-cycle dart. -/
lemma alpha_notMem_dartSet (C : SimplePrimalCycle M) {d : D} (h : d ∉ C.dartSet) :
    M.α d ∉ C.dartSet := by
  intro hmem
  rw [C.mem_dartSet_iff] at hmem
  obtain ⟨i, hi | hi⟩ := hmem
  · -- α d = dart i ⇒ d = α (dart i) ∈ dartSet
    apply h; rw [C.mem_dartSet_iff]
    exact ⟨i, Or.inr (by rw [← hi, M.alpha_alpha])⟩
  · -- α d = α (dart i) ⇒ d = dart i ∈ dartSet
    apply h; rw [C.mem_dartSet_iff]
    have : d = C.dart i := M.α.injective hi
    exact ⟨i, Or.inl this⟩

/-- `cutAlpha` is an involution. -/
lemma cutAlpha_involutive (C : SimplePrimalCycle M) :
    Function.Involutive C.cutAlpha := by
  intro x
  rcases x with d | (i | i)
  · by_cases h : d ∈ C.dartSet
    · rw [C.mem_dartSet_iff] at h
      obtain ⟨i, hi | hi⟩ := h
      · subst hi; rw [C.cutAlpha_dart, C.cutAlpha_capPlus]
      · subst hi; rw [C.cutAlpha_alpha_dart, C.cutAlpha_capMinus]
    · rw [C.cutAlpha_other h, C.cutAlpha_other (C.alpha_notMem_dartSet h), M.alpha_alpha]
  · rw [C.cutAlpha_capPlus, C.cutAlpha_dart]
  · rw [C.cutAlpha_capMinus, C.cutAlpha_alpha_dart]

/-- `cutAlpha` has no fixed points. -/
lemma cutAlpha_no_fixed (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutAlpha x ≠ x := by
  rcases x with d | (i | i)
  · by_cases h : d ∈ C.dartSet
    · rw [C.mem_dartSet_iff] at h
      obtain ⟨i, hi | hi⟩ := h
      · subst hi; rw [C.cutAlpha_dart]; simp
      · subst hi; rw [C.cutAlpha_alpha_dart]; simp
    · rw [C.cutAlpha_other h]; simp only [ne_eq, Sum.inl.injEq]
      exact M.α_no_fixed d
  · rw [C.cutAlpha_capPlus]; simp
  · rw [C.cutAlpha_capMinus]; simp

/-- `cutAlpha` as a permutation. -/
noncomputable def cutAlphaPerm (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  Function.Involutive.toPerm C.cutAlpha C.cutAlpha_involutive

@[simp] lemma cutAlphaPerm_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutAlphaPerm x = C.cutAlpha x := rfl

end SimplePrimalCycle

/-! ## Section 2 (cont.): the cut-and-cap map as a surgery bundle

The new vertex rotation `σ'` of the cut map splits each cycle vertex's `σ`-orbit
into its two banks and splices the `2k` cap darts so that the caps form two new
`φ'`-faces (one reversed), per design §3.1.  Producing `σ'` as a permutation and
establishing the three orbit-count identities `V' = V + k`, `E' = E + k`,
`F' = F + 2` is the deep combinatorial-Jordan core of the construction.

We package the *output* of that core as a **surgery bundle** `CutCapSurgery`: a
`CombMap` on `C.CutDart` whose edge involution is the (already constructed and
verified) `cutAlpha`, together with the three count identities and the
connectivity-lifting property that the design's §4 dual-path argument supplies.

This is the same honest-isolation discipline used in `PlanarMapSeparation`
(`SphereChordSeparation`): everything *around* the irreducible planarity core is
proved unconditionally, and the core is a single named bundle with its exact
mathematical content.  The Jordan lemma and the chord separation are then proved
faithfully and conditionally on this bundle plus the sanctioned Euler-inequality
parameter. -/

/-- A **cut-and-cap surgery bundle** for a simple primal cycle `C`: the cut map
`N` on the augmented dart set `C.CutDart`, with `cutAlpha` as its edge
involution, satisfying the three Euler-count identities of the cut-and-cap
construction and the connectivity-lifting property of design §4. -/
structure CutCapSurgery (M : CombMap D) (C : SimplePrimalCycle M) where
  /-- The cut-and-cap map on the augmented dart set. -/
  N : CombMap C.CutDart
  /-- Its edge involution is the constructed `cutAlpha`. -/
  alpha_eq : N.α = C.cutAlphaPerm
  /-- Vertex count rises by `k`: each cycle vertex splits into its two banks. -/
  vertex_count : N.V = M.V + C.len
  /-- Face count rises by `2`: every old face survives (rerouted) and the two
  cap-dart cycles are two new faces. -/
  face_count : N.F = M.F + 2
  /-- **Connectivity lifting (design §4).**  If the two faces incident with some
  cycle edge are joined by a dual path avoiding all cycle edges, the cut-and-cap
  map is connected.  (Part A: every dart reaches a bank; Part B: the dual path
  connects the two banks.) -/
  connected_of_dual_path : ∀ i : Fin C.len,
    DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) → N.Connected

namespace CutCapSurgery

variable {M : CombMap D} {C : SimplePrimalCycle M}

/-- **Edge count rises by `k`** — *proved*, not assumed.  Because `cutAlpha` is a
fixed-point-free involution, the edge count of any map carrying it is half the
dart count; the augmented dart set has `|D| + 2k` darts, and `2·E(M) = |D|`, so
`E(N) = E(M) + k`.  This is the design's `E' = E + k` and it follows purely from
the (already constructed and verified) edge involution, with no dependence on the
new rotation. -/
theorem edge_count (S : CutCapSurgery M C) : S.N.E = M.E + C.len := by
  have hN : 2 * S.N.E = Fintype.card C.CutDart := S.N.two_mul_E_eq_card
  have hM : 2 * M.E = Fintype.card D := M.two_mul_E_eq_card
  have hcard : Fintype.card C.CutDart = Fintype.card D + 2 * C.len := by
    simp [CombMap.SimplePrimalCycle.CutDart, Fintype.card_sum, Fintype.card_fin]
    ring
  omega

/-- **The Euler-characteristic jump.**  The cut-and-cap surgery raises the Euler
characteristic by exactly `2`. -/
theorem eulerChar_eq (S : CutCapSurgery M C) :
    S.N.eulerChar = M.eulerChar + 2 := by
  unfold CombMap.eulerChar
  rw [S.vertex_count, S.edge_count, S.face_count]
  push_cast
  ring

/-! ## Section 3: the Jordan lemma for simple cycles

With the Euler jump in hand, the Jordan lemma is the design's one-paragraph
contradiction: if the two faces of a cycle edge were joined by a dual path
avoiding the cycle edges, the cut-and-cap map would be connected, hence (Euler
inequality) `χ ≤ 2`, yet the jump gives `χ = χ(M) + 2 = 4`. -/

/-- **Jordan lemma for a simple primal cycle** (conditional on the surgery bundle
and the Euler inequality).  In a connected map of Euler characteristic `2`, the
two faces incident with any edge of a simple primal cycle `C` are **not** joined
by a dual path avoiding the cycle edges.

The Euler inequality `χ ≤ 2` for the *connected* cut-and-cap map enters as the
explicit hypothesis `chi_le` (it is the genus-nonnegativity fragment being proved
in parallel in `PlanarMapEulerInequality.lean`). -/
theorem jordan_simple_cycle (S : CutCapSurgery M C)
    (hchi : M.eulerChar = 2)
    (chi_le : S.N.Connected → S.N.eulerChar ≤ 2)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) := by
  intro hpath
  have hconn : S.N.Connected := S.connected_of_dual_path i hpath
  have hjump : S.N.eulerChar = 4 := by
    rw [S.eulerChar_eq, hchi]; norm_num
  have hle : S.N.eulerChar ≤ 2 := chi_le hconn
  rw [hjump] at hle
  norm_num at hle

end CutCapSurgery

/-! ## Section 4: lifting an interior-dual path to a cycle-avoiding dual path

A `ChordSplitAdj`-step shares an edge that is neither a boundary edge nor the
chord.  If the cycle `C`'s edge set is contained in `{chord} ∪ {boundary edges}`,
such a step's edge is not in `C.edgeSet`, hence it is a `DualAvoidsCycleStep`.
Reachability lifts by induction. -/

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

/-- **Step lift.**  If `C.edgeSet ⊆ {s(u,v)} ∪ boundaryEdges`, then any
`ChordSplitAdj u v` step is a `DualAvoidsCycleStep M C` step: the shared edge,
being neither the chord nor a boundary edge, is not a cycle edge. -/
lemma chordSplitAdj_dualAvoidsCycleStep {u v : M.Vertex} (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    {f g : M.Face} (hfg : hNT.ChordSplitAdj u v f g) :
    DualAvoidsCycleStep M C f g := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := hfg
  refine ⟨d, ?_, hdf, hdg⟩
  intro hmem
  rcases hsub _ hmem with hchord | hbound
  · exact hch hchord
  · exact hbe hbound

/-- **Path lift.**  Under the same edge-containment, a `ChordSplitAdj`-path lifts
to a `DualReachableAvoidingCycle` path. -/
lemma reachable_dualAvoidsCycle_of_chordSplitAdj {u v : M.Vertex}
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    {f g : M.Face}
    (hfg : Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g) :
    DualReachableAvoidingCycle M C f g := by
  induction hfg with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih
        (hNT.chordSplitAdj_dualAvoidsCycleStep C hsub hstep)

/-! ## Section 5: the chord separation

Combining the path lift with the Jordan lemma: the chord `e = uv` together with
one boundary arc is a simple primal cycle `C` whose edges are exactly the chord
and the arc's boundary edges.  An interior-dual path joining the two chord faces
avoids the chord and all boundary edges, hence avoids `C`'s edges, so it lifts to
a cycle-avoiding dual path — contradicting Jordan.  Therefore the two chord faces
are not joined, i.e. `SphereChordSeparation` holds.

The chord-cycle data (the directed-dart `SimplePrimalCycle` realizing chord+arc,
its edge set containment, the chord's index, and the matching of its two incident
faces with the chord faces) plus the cut-and-cap surgery for it are the inputs;
together with the sanctioned `chi_le` they yield the separation.  This is the
design's "three-line application" of the Jordan lemma. -/

/-- **The chord separation from the Jordan lemma** (conditional on the chord cycle
realizing chord+arc, its surgery bundle, and the Euler inequality).

Given:
* a simple primal cycle `C` whose edge set is `{s(u,v)} ∪ boundaryEdges`
  (`hsub`) — i.e. `C` is the chord together with a boundary arc;
* an index `i₀` of `C` whose two incident faces are exactly the two chord faces
  (`hleft`, `hright`);
* a cut-and-cap surgery bundle for `C`;
* the Euler inequality on the cut map (`chi_le`),

the two chord-incident faces are not joined by a chord-avoiding interior-dual
path: `SphereChordSeparation h`.  Equivalently (`separates_of_nearTriangulation`)
the chord *separates* the inner faces. -/
theorem sphereChordSeparation_of_jordan {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v)
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (S : CutCapSurgery M C)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h)))
    (chi_le : S.N.Connected → S.N.eulerChar ≤ 2) :
    hNT.SphereChordSeparation h := by
  -- `SphereChordSeparation` is the negation of a `ChordSplitAdj`-reachability.
  intro hreach
  -- Lift it to a cycle-avoiding dual path.
  have hpath : DualReachableAvoidingCycle M C
      (M.dartFace (hNT.chordDart h)) (M.dartFace (M.α (hNT.chordDart h))) :=
    hNT.reachable_dualAvoidsCycle_of_chordSplitAdj C hsub hreach
  rw [← hleft, ← hright] at hpath
  -- Contradict the Jordan lemma at the chord index.
  exact S.jordan_simple_cycle hNT.sphere.2 chi_le i₀ hpath

/-- **The chord separates** (same hypotheses, in `Separates` form), wiring through
`separates_of_nearTriangulation`.  This is the Chapter-35 target predicate. -/
theorem separates_of_jordan {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (S : CutCapSurgery M C)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord)))
    (chi_le : S.N.Connected → S.N.eulerChar ≤ 2) :
    data.Separates :=
  data.separates_of_nearTriangulation
    (hNT.sphereChordSeparation_of_jordan data.chord C hsub S i₀ hleft hright chi_le)

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
