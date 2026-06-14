import ProofsInTheBook.Ch13ArmVertex

/-!
# `Ch13ArmVertexFull` — the FULL closed-link cyclic sign-change count (Ch13, layer D, Step 5′).

`Ch13ArmVertex.signChanges` counts cyclic sign flips of `jointAngle B i − jointAngle A i` over the
`n-1` ARM joints `i : Fin (n-1)`.  But the vertex **link** is a CLOSED convex spherical polygon with
`n+1` vertices, hence `n+1` dihedral angles around the vertex — the arm presentation EXPOSES only the
`n-1` interior joints and HIDES the two angles at link-vertices `0` and `n` (which involve the closing
edge `A n → A 0`).  This file fixes the count.

## `linkAngle` — the angle at EVERY link vertex (cyclic)

For `i : Fin (n+1)`, `linkAngle A i := sphAngle (A (i-1)) (A i) (A (i+1))` with cyclic `Fin (n+1)`
arithmetic — the genuine spherical angle of the closed polygon at vertex `i`.  For interior `i`
(`1 ≤ i ≤ n-1`) this equals an arm `jointAngle`; for `i = 0` and `i = n` it is the closing-edge angle
the arm presentation hides (`linkAngle_zero` / `linkAngle_last`).

## `signChangesFull` and its parity

`signChangesFull A B := cyclicFlips (nzSigns (fun i : Fin (n+1) => linkAngle B i − linkAngle A i))`,
the FULL closed-link cyclic flip count over all `n+1` angles (zeros skipped).  `signChangesFull_even`
is a GENUINE theorem (cyclic parity, via `cyclicFlips_even`).

## `cauchyArmVertexFull_of_links`

`Chapter13.CauchyArmVertex` with `signChanges := signChangesFull A B`.  The `zero`/`two` obstructions
are built over the FULL cycle:

* `signChangesFull = 0` ⟹ all `n+1` link-angle differences share one sign (incl. the 2 closing ones)
  ⟹ in particular the `n-1` arm joints are monotone, with the strict witness `hactive` ⟹ a fixed-chord
  opening/closing obstruction, refuted by the proven arm lemma (reuses
  `Ch13ArmVertex.zeroSignChanges_obstruction`'s engine through `linkAngle_interior`).
* `signChangesFull = 2` ⟹ the genuine two-arc split data (taken as a hypothesis `htwoArc`, exactly as
  the existing `Ch13ArmVertex` file does) ⟹ `False` via `cauchy_two_signchange_split`.

Hence `CauchyArmVertex.four_le_signChanges` now fires on the FULL `n+1` count, matching the downstream
`vertexFlipCountSkipZeros` (the σ-cycle over all incident edges).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace ProofsInTheBook.Ch13ArmVertexFull

open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13LemmaII
open ProofsInTheBook.Ch13ArmVertex

open scoped Classical

/-! ## `linkAngle` — the closed-polygon spherical angle at every link vertex. -/

/-- The spherical angle of the closed link polygon at vertex `i : Fin (n+1)`, taken between its two
**cyclic** neighbours `A (i-1)` and `A (i+1)`. -/
noncomputable def linkAngle {n : ℕ} (A : Fin (n + 1) → S2) (i : Fin (n + 1)) : ℝ :=
  sphAngle (A (i - 1)) (A i) (A (i + 1))

/-- **Interior link angles ARE arm joints.**  For an interior joint index `i : Fin (n-1)`, the link
angle at vertex `i+1` equals the arm joint angle `jointAngle A i`.  (No wraparound: `1 ≤ i+1 ≤ n-1`.) -/
theorem linkAngle_interior {n : ℕ} (A : Fin (n + 1) → S2) (i : Fin (n - 1)) :
    linkAngle A ⟨i.val + 1, by have := i.isLt; omega⟩ = jointAngle A i := by
  have hi := i.isLt
  unfold linkAngle jointAngle
  -- the three cyclic indices i+1-1, i+1, i+1+1 are ⟨i⟩, ⟨i+1⟩, ⟨i+2⟩ (no wrap)
  have e0 : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) - 1 = ⟨i.val, by omega⟩ := by
    apply Fin.ext
    rw [Fin.sub_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
    show (n + 1 - 1 + (i.val + 1)) % (n + 1) = i.val
    rw [show n + 1 - 1 + (i.val + 1) = i.val + (n + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have e2 : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) + 1 = ⟨i.val + 2, by omega⟩ := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
      Nat.mod_eq_of_lt (show i.val + 1 + 1 < n + 1 by omega)]
  rw [e0, e2]

/-- The closing angle at link vertex `0`: between the closing edge `n → 0` and edge `0 → 1`. -/
theorem linkAngle_zero {n : ℕ} (A : Fin (n + 1) → S2) :
    linkAngle A 0 = sphAngle (A (Fin.last n)) (A 0) (A 1) := by
  unfold linkAngle
  have em1 : (0 : Fin (n + 1)) - 1 = Fin.last n :=
    sub_eq_of_eq_add (Fin.last_add_one n).symm
  have ep1 : (0 : Fin (n + 1)) + 1 = 1 := by simp
  rw [em1, ep1]

/-- The closing angle at link vertex `n` (= `Fin.last n`): between edge `n-1 → n` and the closing
edge `n → 0`. -/
theorem linkAngle_last {n : ℕ} (A : Fin (n + 1) → S2) :
    linkAngle A (Fin.last n) = sphAngle (A (Fin.last n - 1)) (A (Fin.last n)) (A 0) := by
  unfold linkAngle
  rw [Fin.last_add_one]

/-! ## `signChangesFull` and its parity. -/

/-- The signed change of the link angle at vertex `i : Fin (n+1)`. -/
noncomputable def linkDiff {n : ℕ} (A B : Fin (n + 1) → S2) (i : Fin (n + 1)) : ℝ :=
  linkAngle B i - linkAngle A i

/-- **The FULL closed-link cyclic sign-change count.**  The genuine cyclic flip count of the nonzero
dihedral-change signs around ALL `n+1` link vertices (the closing angles included). -/
noncomputable def signChangesFull {n : ℕ} (A B : Fin (n + 1) → S2) : ℕ :=
  cyclicFlips (nzSigns (linkDiff A B))

/-- `signChangesFull` is even (cyclic parity), a genuine theorem. -/
theorem signChangesFull_even {n : ℕ} (A B : Fin (n + 1) → S2) : Even (signChangesFull A B) :=
  cyclicFlips_even _

/-- **The full link-diff restricts to the arm joint-diff.**  At the interior link vertex `i+1`, the
full `linkDiff` equals the arm `jointDiff` (`Ch13ArmVertex.jointDiff`). -/
theorem linkDiff_interior {n : ℕ} (A B : Fin (n + 1) → S2) (i : Fin (n - 1)) :
    linkDiff A B ⟨i.val + 1, by have := i.isLt; omega⟩ = jointDiff A B i := by
  unfold linkDiff jointDiff
  rw [linkAngle_interior, linkAngle_interior]

/-! ## The `signChangesFull = 0` obstruction — fully DERIVED over the FULL cycle.

`signChangesFull A B = 0` forces ALL `n+1` link-angle differences to share one sign
(`cyclicFlips_eq_zero_iff_all_eq` + `all_same_sign` on `linkDiff`), the two closing angles included.
Restricting to the `n-1` interior link vertices (`linkDiff_interior`), the arm joints are monotone in
that one direction; with `hactive` (some arm joint differs) we get the fixed-chord opening/closing
obstruction, refuted by the proven arm lemma. -/

/-- **The `signChangesFull = 0` fixed-chord obstruction.**  Same conclusion as
`Ch13ArmVertex.zeroSignChanges_obstruction`, but the hypothesis is now `0` changes over the FULL
`n+1`-cycle (closing angles included), which is *stronger* and so still yields the obstruction. -/
noncomputable def zeroSignChangesFull_obstruction {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (hactive : ∃ i : Fin (n - 1), jointAngle A i ≠ jointAngle B i)
    (hzero : signChangesFull A B = 0) :
    CauchyArmFixedChordObstruction := by
  -- Some interior arm joint differs ⟹ the corresponding FULL link-diff is nonzero.
  have hactive' : ∃ k, linkDiff A B k ≠ 0 := by
    obtain ⟨i, hi⟩ := hactive
    refine ⟨⟨i.val + 1, by have := i.isLt; omega⟩, ?_⟩
    rw [linkDiff_interior]
    exact sub_ne_zero.mpr (Ne.symm hi)
  have hne : nzSigns (linkDiff A B) ≠ [] := nzSigns_ne_nil _ hactive'
  have hall : ∀ x ∈ nzSigns (linkDiff A B), ∀ y ∈ nzSigns (linkDiff A B), x = y :=
    (cyclicFlips_eq_zero_iff_all_eq _).mp hzero
  have hdir := all_same_sign (linkDiff A B) hne hall
  by_cases hpos : ∀ k, 0 ≤ linkDiff A B k
  · -- opening: every interior joint A ≤ B (read off from the full diff at vertex i+1)
    refine CauchyArmFixedChordObstruction.opening
      { n := n, hn := hn, A := A, B := B, hA := hA, hB := hB,
        equal_sides := hsides
        opened := fun i => ?_
        some_angle_strictly_opened := ?_
        fixed_chord := hclose }
    · have hk := hpos ⟨i.val + 1, by have := i.isLt; omega⟩
      rw [linkDiff_interior] at hk
      simp only [jointDiff] at hk; linarith
    · obtain ⟨i, hi⟩ := hactive
      refine ⟨i, ?_⟩
      have hk := hpos ⟨i.val + 1, by have := i.isLt; omega⟩
      rw [linkDiff_interior] at hk
      simp only [jointDiff] at hk
      have hne' : jointAngle B i - jointAngle A i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
      linarith [lt_of_le_of_ne hk (Ne.symm hne')]
  · -- closing: every interior joint B ≤ A
    have hneg : ∀ k, linkDiff A B k ≤ 0 := hdir.resolve_left hpos
    refine CauchyArmFixedChordObstruction.closing
      { n := n, hn := hn, A := A, B := B, hA := hA, hB := hB,
        equal_sides := hsides
        closed := fun i => ?_
        some_angle_strictly_closed := ?_
        fixed_chord := hclose }
    · have hk := hneg ⟨i.val + 1, by have := i.isLt; omega⟩
      rw [linkDiff_interior] at hk
      simp only [jointDiff] at hk; linarith
    · obtain ⟨i, hi⟩ := hactive
      refine ⟨i, ?_⟩
      have hk := hneg ⟨i.val + 1, by have := i.isLt; omega⟩
      rw [linkDiff_interior] at hk
      simp only [jointDiff] at hk
      have hne' : jointAngle B i - jointAngle A i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
      linarith [lt_of_le_of_ne hk hne']

/-! ## The genuine `CauchyArmVertex` of a vertex link pair, over the FULL cycle.

`cauchyArmVertexFull_of_links` assembles `Chapter13.CauchyArmVertex` with `signChanges` set to the
FULL closed-link cyclic count `signChangesFull A B`:

* `signChanges_even` = the genuine full-cycle cyclic-parity theorem (`signChangesFull_even`);
* `zero_sign_changes_obstruction` = `zeroSignChangesFull_obstruction` (derived from the proven arm
  lemma over the full cycle: 0 full changes ⟹ all `n+1` link angles monotone — the 2 closing ones
  included — ⟹ in particular the `n-1` arm joints monotone with `hactive` strict ⟹ obstruction);
* `two_sign_changes_obstruction` = the two-arc split routed through `cauchy_two_signchange_split`, with
  the genuine `TwoArcSplitData` (real spherical sub-arms + real side/joint comparisons) supplied by the
  hypothesis `htwoArc` — exactly the single isolated residual the `Ch13ArmVertex` file already takes.

Because `signChanges := signChangesFull A B`, the downstream `CauchyArmVertex.four_le_signChanges`
fires on the FULL `n+1` count, matching the σ-cycle `vertexFlipCountSkipZeros` over all incident edges.
The arm presentation no longer hides 2 of the dihedral signs. -/
noncomputable def cauchyArmVertexFull_of_links (n : ℕ) (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (hactive : ∃ i : Fin (n - 1), jointAngle A i ≠ jointAngle B i)
    (htwoArc : signChangesFull A B = 2 → TwoArcSplitData A B) :
    Chapter13.CauchyArmVertex where
  signChanges := signChangesFull A B
  signChanges_even := signChangesFull_even A B
  zero_sign_changes_obstruction :=
    fun hzero => zeroSignChangesFull_obstruction hn A B hA hB hsides hclose hactive hzero
  two_sign_changes_obstruction :=
    fun htwo => twoSignChanges_obstruction (htwoArc htwo)

/-! ## Non-vacuity of `signChangesFull_even`.

`signChangesFull_even` is unconditional over all link pairs; for the single-vertex link
(`A B : Fin 1 → S2`) the nonzero-sign list has length ≤ 1, so `signChangesFull A B = 0` for EVERY
such pair — a concrete realized value of `signChangesFull` (witnessing `Even 0` non-vacuously, no
`Nonempty S2` needed).  (The geometric obstructions are exercised on genuine `StrictConvexSphArm`
inputs through the `Ch13ArmVertex` consumers; see that file's non-vacuity discussion.) -/
example (A B : Fin 1 → S2) : signChangesFull A B = 0 := by
  have hlen : (nzSigns (linkDiff A B)).length ≤ 1 := by
    unfold nzSigns
    rw [List.length_map]
    calc (List.filter _ (List.finRange 1)).length
        ≤ (List.finRange 1).length := List.length_filter_le _ _
      _ = 1 := by simp
  -- cyclicFlips of any length-≤1 list is 0.
  unfold signChangesFull
  match h : nzSigns (linkDiff A B), hlen with
  | [], _ => simp [cyclicFlips]
  | [a], _ => simp [cyclicFlips, flips]

end ProofsInTheBook.Ch13ArmVertexFull

#print axioms ProofsInTheBook.Ch13ArmVertexFull.linkAngle_interior
#print axioms ProofsInTheBook.Ch13ArmVertexFull.linkAngle_zero
#print axioms ProofsInTheBook.Ch13ArmVertexFull.linkAngle_last
#print axioms ProofsInTheBook.Ch13ArmVertexFull.signChangesFull_even
#print axioms ProofsInTheBook.Ch13ArmVertexFull.zeroSignChangesFull_obstruction
#print axioms ProofsInTheBook.Ch13ArmVertexFull.cauchyArmVertexFull_of_links
