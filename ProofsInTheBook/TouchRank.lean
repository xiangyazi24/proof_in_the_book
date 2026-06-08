import ProofsInTheBook.FaceCorrWord
import ProofsInTheBook.RelationComponentCount

/-!
# The touch-rank lower bound: `numCycles (p · W) ≥ numCycles p − touchRank` (Chapter 35)

This file closes the corrected Chapter 35 face count by the **position-free** route of
`HANDOFF/CH35_SPLITS_DESIGN.md`.  The split positions of the `faceCorr₂` correction word
are cut-dependent and have no uniform symbolic rule (the constraint `F' = F + 2` holds with
slack `0`, kernel-anchored in `FaceCorrWord.lean`); the *touch-rank* is what is stable.

## The conservation law

A transposition word `W` supported on the orbits of a base permutation `p` can reduce the
cycle count by at most the **rank** of the graph by which it connects those orbits:

```
numCycles (prefixPerm p W m) ≥ numCycles p − (touched.card − #components)
```

where `touched` is the set of `p`-orbits met by `W` and `#components` counts the connected
components of the touched orbits under the relation "some letter of `W` joins these two
orbits".  No split positions appear; the order of the letters is irrelevant.

## Layered contents

* **Layer A (the core counting theorem, unconditional).**  `POrb`/`pOrbOf` (the `p`-orbit
  quotient, definitionally `numCycles`' setoid), `wordTouchedOrbits`, the **coloring
  certificate** `TouchColorCertBound`, and the headline
  `numCycles_prefixPerm_ge_of_touchColorCert :
     numCycles (prefixPerm p W m) ≥ numCycles p − B`.
  The proof is the design's §5 block-injection: the prefix product preserves the block
  colour, so untouched `p`-orbits survive verbatim and each used colour anchors at least
  one new `q`-orbit, giving an injection `({untouched} ⊕ Color) ↪ POrb q`.
* **Layer B (the generator-graph compression, unconditional).**  `TouchCompressionCert`
  (`B` generator edges whose reachability connects every letter's endpoints) and
  `touchColorCert_of_touchCompressionCert`, via the graph-rank fact
  `vertices − components ≤ edges` of `RelationComponentCount.lean`.  Hence
  `numCycles_prefixPerm_ge_of_touchCompressionCert`.
* **Layer C (the cut-and-cap application).**  Instantiated at `p := phiLift`,
  `W := concatWord Ls`, `B := 2·len − 2`.  The one genuinely topological input — that the
  `faceCorr₂` word's endpoints are reachable through the `2·len − 2`-edge bank generator
  graph — is isolated as the `FaceCorrTouchCert` data (parallel to the `FaceCorrSplitCert`
  of `FaceCorrWord.lean`).  Everything else is closed: `cutCapMap2_F_lower_of_touchCert`
  (`F' ≥ F + 2`) and the Jordan / chord-separation corollary.

The triangle / `K₄`-sphere / `K₄`-torus kernel data are checked in the comments of
`FaceCorrWord.lean`; the touch-rank bound `2·len − 2` is the rank of the two bank path
forests (`len − 1` edges each).

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ProofsInTheBook.TouchRank

open ForcedSplits

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Layer A: the `p`-orbit quotient and touched orbits -/

/-- The quotient of `X` by the `SameCycle p` relation: the set of `p`-orbits.  This is
*definitionally* the setoid underlying `numCycles p`. -/
def POrb (p : Equiv.Perm X) := Quotient (SameCycle.setoid p)

/-- `POrb p` is finite (quotient of a finite type). -/
instance (p : Equiv.Perm X) : Finite (POrb p) :=
  inferInstanceAs (Finite (Quotient (SameCycle.setoid p)))

noncomputable instance (p : Equiv.Perm X) : Fintype (POrb p) := Fintype.ofFinite _

noncomputable instance (p : Equiv.Perm X) : DecidableEq (POrb p) := Classical.decEq _

/-- The `p`-orbit of an element. -/
def pOrbOf (p : Equiv.Perm X) (x : X) : POrb p := Quotient.mk (SameCycle.setoid p) x

@[simp] lemma pOrbOf_out (p : Equiv.Perm X) (o : POrb p) :
    pOrbOf p (Quotient.out o) = o := Quotient.out_eq o

@[simp] lemma pOrbOf_eq_iff (p : Equiv.Perm X) (x y : X) :
    pOrbOf p x = pOrbOf p y ↔ p.SameCycle x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- `numCycles p` counts the `p`-orbits (as `Nat.card`, instance-free). -/
lemma numCycles_eq_natCard_POrb (p : Equiv.Perm X) :
    numCycles p = Nat.card (POrb p) := by
  classical
  show Fintype.card (Quotient (SameCycle.setoid p)) = Nat.card (POrb p)
  rw [Fintype.card_eq_nat_card]
  rfl

/-- `p` fixes its own orbit: `pOrbOf p (p x) = pOrbOf p x`. -/
@[simp] lemma pOrbOf_apply (p : Equiv.Perm X) (x : X) :
    pOrbOf p (p x) = pOrbOf p x :=
  Quotient.sound (sameCycle_apply_left.mpr SameCycle.rfl)

/-- The `p`-orbits met by the word `W`: for each letter, the orbits of its two endpoints. -/
noncomputable def wordTouchedOrbits (p : Equiv.Perm X) {m : ℕ} (W : Fin m → Swap X) :
    Finset (POrb p) :=
  Finset.univ.biUnion fun j : Fin m => {pOrbOf p (W j).x, pOrbOf p (W j).y}

lemma mem_wordTouchedOrbits (p : Equiv.Perm X) {m : ℕ} (W : Fin m → Swap X)
    (o : POrb p) :
    o ∈ wordTouchedOrbits p W ↔
      ∃ j : Fin m, o = pOrbOf p (W j).x ∨ o = pOrbOf p (W j).y := by
  simp only [wordTouchedOrbits, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]

/-- The endpoints of every letter are touched orbits. -/
lemma touched_x (p : Equiv.Perm X) {m : ℕ} (W : Fin m → Swap X) (j : Fin m) :
    pOrbOf p (W j).x ∈ wordTouchedOrbits p W :=
  (mem_wordTouchedOrbits p W _).mpr ⟨j, Or.inl rfl⟩

lemma touched_y (p : Equiv.Perm X) {m : ℕ} (W : Fin m → Swap X) (j : Fin m) :
    pOrbOf p (W j).y ∈ wordTouchedOrbits p W :=
  (mem_wordTouchedOrbits p W _).mpr ⟨j, Or.inr rfl⟩

/-! ## The coloring certificate

A `TouchColorCertBound p W B` is the design's §4 finite witness that the touched-orbit
graph of `W` has rank `≤ B`: a finite colour type, a colouring of the `p`-orbits in which
every touched orbit is coloured, every colour is used, and every letter's two endpoints
share a colour, together with the rank bound `touched.card − card Color ≤ B`. -/

/-- The coloring certificate bounding the touch-rank of `W` by `B`. -/
structure TouchColorCertBound (p : Equiv.Perm X) {m : ℕ} (W : Fin m → Swap X) (B : ℕ) where
  /-- The finite colour type (one colour per touched component). -/
  Color : Type*
  colorFintype : Fintype Color
  colorDecEq : DecidableEq Color
  /-- The partial colouring of `p`-orbits. -/
  color : POrb p → Option Color
  /-- Every touched `p`-orbit is coloured. -/
  color_some_of_touched : ∀ o ∈ wordTouchedOrbits p W, ∃ c, color o = some c
  /-- Every untouched `p`-orbit is uncoloured (colours mark exactly the touched
  components). -/
  color_none_of_untouched : ∀ o ∉ wordTouchedOrbits p W, color o = none
  /-- Every colour is used by some touched `p`-orbit. -/
  color_used : ∀ c : Color, ∃ o ∈ wordTouchedOrbits p W, color o = some c
  /-- Each letter's endpoints share a colour. -/
  endpoint_color_eq : ∀ j : Fin m, color (pOrbOf p (W j).x) = color (pOrbOf p (W j).y)
  /-- The rank bound. -/
  rank_bound : (wordTouchedOrbits p W).card - Fintype.card Color ≤ B

attribute [instance] TouchColorCertBound.colorFintype TouchColorCertBound.colorDecEq

variable {p : Equiv.Perm X} {m B : ℕ} {W : Fin m → Swap X}

/-- The block label of an element: the colour of its `p`-orbit (`none` if untouched). -/
def blockLabel (C : TouchColorCertBound p W B) (x : X) : Option C.Color :=
  C.color (pOrbOf p x)

/-- `p` preserves the block label (it fixes its own orbits). -/
lemma blockLabel_apply_base (C : TouchColorCertBound p W B) (x : X) :
    blockLabel C (p x) = blockLabel C x := by
  simp [blockLabel]

/-- Each letter's swap preserves the block label: the two endpoints share a colour and
every other point is fixed by the swap. -/
lemma blockLabel_swap (C : TouchColorCertBound p W B) (j : Fin m) (x : X) :
    blockLabel C ((W j).perm x) = blockLabel C x := by
  unfold blockLabel Swap.perm
  by_cases hx : x = (W j).x
  · subst hx
    rw [Equiv.swap_apply_left]
    exact (C.endpoint_color_eq j).symm
  · by_cases hy : x = (W j).y
    · subst hy
      rw [Equiv.swap_apply_right]
      exact C.endpoint_color_eq j
    · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

/-- The prefix product preserves the block label, for every prefix length `n`. -/
lemma blockLabel_prefixPerm (C : TouchColorCertBound p W B) (n : ℕ) (x : X) :
    blockLabel C (prefixPerm p W n x) = blockLabel C x := by
  induction n generalizing x with
  | zero => exact blockLabel_apply_base C x
  | succ n ih =>
      by_cases h : n < m
      · rw [prefixPerm_succ p W h, Equiv.Perm.mul_apply, ih, blockLabel_swap]
      · rw [prefixPerm, dif_neg h, ih]

/-! ## Untouched orbits survive verbatim

A `p`-orbit not met by `W` is fixed pointwise by every letter; hence the prefix product
acts on it exactly as `p`, and its `q`-orbit coincides with its `p`-orbit. -/

/-- A point whose `p`-orbit is untouched is not an endpoint of any letter. -/
lemma untouched_not_endpoint {m : ℕ} {W : Fin m → Swap X} {x : X}
    (hx : pOrbOf p x ∉ wordTouchedOrbits p W) (j : Fin m) :
    x ≠ (W j).x ∧ x ≠ (W j).y := by
  constructor
  · rintro rfl; exact hx (touched_x p W j)
  · rintro rfl; exact hx (touched_y p W j)

/-- Every letter's swap fixes a point of an untouched orbit. -/
lemma swap_fixes_untouched {m : ℕ} {W : Fin m → Swap X} {x : X}
    (hx : pOrbOf p x ∉ wordTouchedOrbits p W) (j : Fin m) :
    (W j).perm x = x := by
  obtain ⟨hxx, hxy⟩ := untouched_not_endpoint hx j
  rw [Swap.perm, Equiv.swap_apply_of_ne_of_ne hxx hxy]

/-- The prefix product acts as `p` on a point of an untouched orbit, for every prefix
length `n`. -/
lemma prefixPerm_eq_base_on_untouched {m : ℕ} {W : Fin m → Swap X} {x : X}
    (hx : pOrbOf p x ∉ wordTouchedOrbits p W) (n : ℕ) :
    prefixPerm p W n x = p x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases h : n < m
      · rw [prefixPerm_succ p W h, Equiv.Perm.mul_apply, swap_fixes_untouched hx ⟨n, h⟩, ih]
      · rw [prefixPerm, dif_neg h, ih]

/-- On an untouched orbit, iterating the prefix product matches iterating `p`. -/
lemma prefixPerm_pow_eq_base_on_untouched {m : ℕ} {W : Fin m → Swap X} {x : X}
    (hx : pOrbOf p x ∉ wordTouchedOrbits p W) (k : ℕ) :
    (prefixPerm p W m ^ k) x = (p ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
      -- `p ^ k x` is in the same (untouched) `p`-orbit as `x`.
      have hsc : pOrbOf p ((p ^ k) x) = pOrbOf p x :=
        Quotient.sound (sameCycle_pow_left.mpr SameCycle.rfl)
      have hx' : pOrbOf p ((p ^ k) x) ∉ wordTouchedOrbits p W := by rw [hsc]; exact hx
      exact prefixPerm_eq_base_on_untouched hx' m

/-- **Untouched orbits do not fuse.**  If `x` lies in an untouched `p`-orbit and is
`q`-`SameCycle` to `y`, then `x` and `y` are already `p`-`SameCycle`. -/
lemma sameCycle_base_of_untouched {m : ℕ} {W : Fin m → Swap X} {x y : X}
    (hx : pOrbOf p x ∉ wordTouchedOrbits p W)
    (hsc : (prefixPerm p W m).SameCycle x y) :
    p.SameCycle x y := by
  obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
  exact ⟨(k : ℤ), by rw [zpow_natCast, ← hk]; exact (prefixPerm_pow_eq_base_on_untouched hx k).symm⟩

/-! ## The block-injection counting bound

`q := prefixPerm p W m`.  The block label descends to a function `qLabel : POrb q →
Option Color`.  We inject `({untouched p-orbit} ⊕ Color) ↪ POrb q` by sending an untouched
orbit to its (verbatim) `q`-orbit and a colour to the `q`-orbit of a chosen touched
representative; `qLabel` separates the two families and distinct colours, while
`sameCycle_base_of_untouched` separates distinct untouched orbits. -/

/-- The block label descends to the `q`-orbit quotient. -/
noncomputable def qLabel (C : TouchColorCertBound p W B) :
    POrb (prefixPerm p W m) → Option C.Color :=
  Quotient.lift (blockLabel C) (by
    intro x y hxy
    -- `hxy : (prefixPerm p W m).SameCycle x y`; block label is constant on `q`-orbits.
    obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
    have : blockLabel C ((prefixPerm p W m ^ k) x) = blockLabel C x := by
      clear hk
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, blockLabel_prefixPerm, ih]
    rw [← hk, this])

@[simp] lemma qLabel_mk (C : TouchColorCertBound p W B) (x : X) :
    qLabel C (pOrbOf (prefixPerm p W m) x) = blockLabel C x := rfl

/-- A representative of an untouched `p`-orbit is untouched. -/
lemma out_untouched (o : {o : POrb p // o ∉ wordTouchedOrbits p W}) :
    pOrbOf p (Quotient.out o.1) ∉ wordTouchedOrbits p W := by
  rw [pOrbOf_out]; exact o.2

/-- The injection's color half: a representative carrying colour `c`. -/
lemma exists_colorRep (C : TouchColorCertBound p W B) (c : C.Color) :
    ∃ x : X, blockLabel C x = some c := by
  obtain ⟨o, _, hc⟩ := C.color_used c
  exact ⟨Quotient.out o, by rw [blockLabel, pOrbOf_out]; exact hc⟩

open Classical in
/-- The block-injection from untouched orbits and colours into `q`-orbits. -/
noncomputable def blockInj (C : TouchColorCertBound p W B) :
    ({o : POrb p // o ∉ wordTouchedOrbits p W} ⊕ C.Color) → POrb (prefixPerm p W m) :=
  fun s => s.elim
    (fun o => pOrbOf (prefixPerm p W m) (Quotient.out o.1))
    (fun c => pOrbOf (prefixPerm p W m) (Classical.choose (exists_colorRep C c)))

/-- `qLabel` of an untouched representative is `none`. -/
lemma qLabel_blockInj_inl (C : TouchColorCertBound p W B)
    (o : {o : POrb p // o ∉ wordTouchedOrbits p W}) :
    qLabel C (blockInj C (Sum.inl o)) = none := by
  show blockLabel C (Quotient.out o.1) = none
  rw [blockLabel, pOrbOf_out]
  exact C.color_none_of_untouched o.1 o.2

/-- `qLabel` of a colour-`c` representative is `some c`. -/
lemma qLabel_blockInj_inr (C : TouchColorCertBound p W B) (c : C.Color) :
    qLabel C (blockInj C (Sum.inr c)) = some c := by
  show blockLabel C (Classical.choose (exists_colorRep C c)) = some c
  exact Classical.choose_spec (exists_colorRep C c)

lemma blockInj_injective (C : TouchColorCertBound p W B) :
    Function.Injective (blockInj C) := by
  rintro (⟨o₁, ho₁⟩ | c₁) (⟨o₂, ho₂⟩ | c₂) hEq
  · -- two untouched orbits: their `q`-orbits coincide ⇒ they are the same `p`-orbit.
    have hx₁ : pOrbOf p (Quotient.out (⟨o₁, ho₁⟩ : {o : POrb p // _}).1)
        ∉ wordTouchedOrbits p W := out_untouched ⟨o₁, ho₁⟩
    have hsc : (prefixPerm p W m).SameCycle
        (Quotient.out o₁) (Quotient.out o₂) := Quotient.exact hEq
    have hpsc : p.SameCycle (Quotient.out o₁) (Quotient.out o₂) :=
      sameCycle_base_of_untouched (by simpa using hx₁) hsc
    have : pOrbOf p (Quotient.out o₁) = pOrbOf p (Quotient.out o₂) := Quotient.sound hpsc
    rw [pOrbOf_out, pOrbOf_out] at this
    simp [this]
  · -- untouched (label none) vs colour (label some): contradiction via `qLabel`.
    exfalso
    have h₁ := qLabel_blockInj_inl C ⟨o₁, ho₁⟩
    have h₂ := qLabel_blockInj_inr C c₂
    rw [hEq, h₂] at h₁
    exact absurd h₁ (by simp)
  · exfalso
    have h₁ := qLabel_blockInj_inr C c₁
    have h₂ := qLabel_blockInj_inl C ⟨o₂, ho₂⟩
    rw [hEq, h₂] at h₁
    exact absurd h₁ (by simp)
  · -- two colours: distinct labels ⇒ distinct, hence equal colours.
    have h₁ := qLabel_blockInj_inr C c₁
    have h₂ := qLabel_blockInj_inr C c₂
    rw [hEq, h₂] at h₁
    simp only [Option.some.injEq] at h₁
    rw [h₁]

/-- The number of untouched `p`-orbits is `numCycles p − touched.card`. -/
lemma card_untouched (p : Equiv.Perm X) {m : ℕ} (W : Fin m → Swap X) :
    Fintype.card {o : POrb p // o ∉ wordTouchedOrbits p W}
      = numCycles p - (wordTouchedOrbits p W).card := by
  classical
  have hsub : Fintype.card {o : POrb p // o ∈ wordTouchedOrbits p W}
      = (wordTouchedOrbits p W).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext o
    simp
  rw [Fintype.card_subtype_compl (fun o => o ∈ wordTouchedOrbits p W), hsub]
  congr 1
  rw [numCycles_eq_natCard_POrb, Nat.card_eq_fintype_card]

/-- **The core counting theorem (coloring form).**  A `TouchColorCertBound p W B` forces
`numCycles (prefixPerm p W m) ≥ numCycles p − B`.  The block-injection
`({untouched} ⊕ Color) ↪ POrb q` gives `numCycles q ≥ #untouched + #Color`, and
`#untouched = numCycles p − touched.card`, so the loss `touched.card − #Color ≤ B`. -/
theorem numCycles_prefixPerm_ge_of_touchColorCert (C : TouchColorCertBound p W B) :
    (numCycles (prefixPerm p W m) : ℤ) ≥ (numCycles p : ℤ) - (B : ℤ) := by
  classical
  -- the injection
  have hinj := blockInj_injective C
  have hcardLe : Fintype.card
      ({o : POrb p // o ∉ wordTouchedOrbits p W} ⊕ C.Color)
        ≤ Fintype.card (POrb (prefixPerm p W m)) :=
    Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_sum] at hcardLe
  -- identify the two cardinals
  have hun : Fintype.card {o : POrb p // o ∉ wordTouchedOrbits p W}
      = numCycles p - (wordTouchedOrbits p W).card := card_untouched p W
  have hq : Fintype.card (POrb (prefixPerm p W m)) = numCycles (prefixPerm p W m) := by
    rw [numCycles_eq_natCard_POrb, Nat.card_eq_fintype_card]
  rw [hun, hq] at hcardLe
  -- arithmetic: numCycles q ≥ (numCycles p − touched) + #Color ≥ numCycles p − B
  have htouch_le : (wordTouchedOrbits p W).card ≤ numCycles p := by
    rw [numCycles_eq_natCard_POrb, Nat.card_eq_fintype_card]
    exact (wordTouchedOrbits p W).card_le_univ.trans (le_of_eq (Finset.card_univ))
  have hrank := C.rank_bound
  -- to ℤ
  have key : (numCycles p : ℤ) - (wordTouchedOrbits p W).card + Fintype.card C.Color
      ≤ (numCycles (prefixPerm p W m) : ℤ) := by
    have : (numCycles p - (wordTouchedOrbits p W).card + Fintype.card C.Color : ℕ)
        ≤ numCycles (prefixPerm p W m) := hcardLe
    have hcast : ((numCycles p - (wordTouchedOrbits p W).card : ℕ) : ℤ)
        = (numCycles p : ℤ) - (wordTouchedOrbits p W).card := by
      omega
    push_cast [hcast] at this ⊢
    omega
  -- touched.card − #Color ≤ B  ⇒  −touched.card + #Color ≥ −B
  have hrankZ : ((wordTouchedOrbits p W).card : ℤ) - Fintype.card C.Color ≤ (B : ℤ) := by
    omega
  linarith

/-! ## Layer B: the generator-graph compression certificate

A `TouchCompressionCert p W B` is the design's §6 finite witness: `B` *generator edges*
on `POrb p` whose reflexive-transitive(-symmetric) closure already connects the two
endpoints of every letter of `W`.  These are not split positions — they are orbit-fusion
witnesses ("which `p`-orbits the seam may merge").  From `B` edges the touched-orbit graph
has rank `≤ B` (the graph fact `vertices − components ≤ edges`), so a `TouchCompressionCert`
yields a `TouchColorCertBound` and hence `numCycles (prefixPerm p W m) ≥ numCycles p − B`.

The component machinery (`numComp`, `addEdge`, and the two recursion lemmas
`numComp_addEdge_of_eqvGen` / `numComp_addEdge_of_not_eqvGen`) is imported from
`RelationComponentCount.lean`. -/

/-- The symmetric edge relation of a generator list `gen : Fin B → POrb p × POrb p`. -/
def genRel {p : Equiv.Perm X} {B : ℕ} (gen : Fin B → POrb p × POrb p)
    (u v : POrb p) : Prop :=
  ∃ i : Fin B, (u = (gen i).1 ∧ v = (gen i).2) ∨ (u = (gen i).2 ∧ v = (gen i).1)

/-- The generator-graph compression certificate: `B` edges on `POrb p` whose reachability
connects every letter's two endpoints. -/
structure TouchCompressionCert (p : Equiv.Perm X) {m : ℕ} (W : Fin m → Swap X) (B : ℕ) where
  /-- The `B` generator edges (ordered pairs of `p`-orbits). -/
  gen : Fin B → POrb p × POrb p
  /-- Every letter's endpoints are connected through the generator edges. -/
  endpoint_reachable : ∀ j : Fin m,
    Relation.EqvGen (genRel gen) (pOrbOf p (W j).x) (pOrbOf p (W j).y)

/-! ### The graph-rank fact `vertices − components ≤ edges`

We bound the component count of `genRel gen` from below by `card(POrb p) − B`, by induction
on `B` using `RelationComponentCount`'s edge-addition recursion: each generator edge drops
the component count by at most one, starting from the discrete graph
(`numComp ⊥ = card(POrb p)`). -/

/-- `EqvGen` of the empty relation is plain equality. -/
lemma eqvGen_bot_iff {α : Type*} (x y : α) :
    Relation.EqvGen (fun _ _ : α => False) x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact absurd h (by simp)
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · rintro rfl; exact Relation.EqvGen.refl _

/-- The empty relation has every vertex as its own component. -/
lemma numComp_bot (p : Equiv.Perm X) :
    numComp (fun _ _ : POrb p => False) = Nat.card (POrb p) := by
  classical
  unfold numComp
  apply Nat.card_congr
  refine
    { toFun := Quotient.lift id (fun x y h => (eqvGen_bot_iff x y).mp h)
      invFun := Quotient.mk (compSetoid (fun _ _ : POrb p => False))
      left_inv := ?_
      right_inv := ?_ }
  · intro q; refine Quotient.inductionOn q ?_; intro x; rfl
  · intro x; rfl

/-- `numComp` depends only on the equivalence closure of the relation. -/
lemma numComp_congr_eqvGen {α : Type*} [Fintype α] {r s : α → α → Prop}
    (h : ∀ x y, Relation.EqvGen r x y ↔ Relation.EqvGen s x y) :
    numComp r = numComp s := by
  classical
  unfold numComp
  apply Nat.card_congr
  refine
    { toFun := Quotient.map' id (fun x y hxy => (h x y).mp hxy)
      invFun := Quotient.map' id (fun x y hxy => (h x y).mpr hxy)
      left_inv := ?_
      right_inv := ?_ }
  · intro q; refine Quotient.inductionOn' q ?_; intro x; rfl
  · intro q; refine Quotient.inductionOn' q ?_; intro x; rfl

/-- `genRel` over the first `n+1` generators, as `genRel` over the first `n` plus the
`n`-th edge (`EqvGen`-level equivalence with `addEdge`). -/
lemma eqvGen_genRel_succ {p : Equiv.Perm X} {B : ℕ} (gen : Fin (B + 1) → POrb p × POrb p)
    (x y : POrb p) :
    Relation.EqvGen (genRel gen) x y ↔
      Relation.EqvGen
        (addEdge (genRel (fun i : Fin B => gen i.castSucc))
          (gen (Fin.last B)).1 (gen (Fin.last B)).2) x y := by
  have hrel : ∀ u v : POrb p, genRel gen u v ↔
      addEdge (genRel (fun i : Fin B => gen i.castSucc))
        (gen (Fin.last B)).1 (gen (Fin.last B)).2 u v := by
    intro u v
    constructor
    · rintro ⟨i, hi⟩
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · exact Or.inl ⟨i', hi⟩
      · rcases hi with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · exact Or.inr (Or.inl ⟨hu, hv⟩)
        · exact Or.inr (Or.inr ⟨hu, hv⟩)
    · rintro (⟨i', hi'⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩)
      · exact ⟨i'.castSucc, hi'⟩
      · exact ⟨Fin.last B, Or.inl ⟨hu, hv⟩⟩
      · exact ⟨Fin.last B, Or.inr ⟨hu, hv⟩⟩
  constructor
  · exact fun h => h.mono (fun a b hab => (hrel a b).mp hab)
  · exact fun h => h.mono (fun a b hab => (hrel a b).mpr hab)

/-- **The graph-rank lower bound on the component count.**  With `B` generator edges, the
number of components of `POrb p` under `genRel gen` is at least `card(POrb p) − B`: the
discrete graph has `card(POrb p)` components and each edge drops the count by at most one. -/
lemma numComp_genRel_ge {p : Equiv.Perm X} :
    ∀ {B : ℕ} (gen : Fin B → POrb p × POrb p),
      numComp (genRel gen) + B ≥ Nat.card (POrb p) := by
  intro B
  induction B with
  | zero =>
      intro gen
      have hbot : numComp (genRel gen) = Nat.card (POrb p) := by
        refine (numComp_congr_eqvGen ?_).trans (numComp_bot p)
        intro x y
        constructor
        · refine fun h => h.mono (fun a b hab => ?_)
          obtain ⟨i, _⟩ := hab; exact absurd i.isLt (by omega)
        · exact fun h => h.mono (fun a b hab => hab.elim)
      omega
  | succ n ih =>
      intro gen
      set a := (gen (Fin.last n)).1
      set b := (gen (Fin.last n)).2
      set r := genRel (fun i : Fin n => gen i.castSucc) with hr
      have hcong : numComp (genRel gen) = numComp (addEdge r a b) :=
        numComp_congr_eqvGen (fun x y => eqvGen_genRel_succ gen x y)
      have ihn : numComp r + n ≥ Nat.card (POrb p) := ih (fun i : Fin n => gen i.castSucc)
      by_cases hconn : Relation.EqvGen r a b
      · rw [hcong, numComp_addEdge_of_eqvGen r hconn]; omega
      · have hadd := numComp_addEdge_of_not_eqvGen r hconn
        rw [hcong]; omega

/-! ### From a compression certificate to a coloring certificate

The colours are the connected components of `genRel` that contain a touched orbit.  Every
touched orbit gets the colour of its component (`some`); untouched orbits get `none`.  Each
letter's endpoints share a colour by `endpoint_reachable`, and the rank bound
`touched.card − #colours ≤ B` is the graph-rank fact `numComp_genRel_ge`. -/

namespace TouchCompressionCert

variable {p : Equiv.Perm X} {m B : ℕ} {W : Fin m → Swap X}

/-- The component quotient of the generator graph. -/
abbrev comp (K : TouchCompressionCert p W B) := Quotient (compSetoid (genRel K.gen))

/-- The component of a `p`-orbit. -/
def compMk (K : TouchCompressionCert p W B) (o : POrb p) : K.comp :=
  Quotient.mk (compSetoid (genRel K.gen)) o

lemma compMk_eq_iff (K : TouchCompressionCert p W B) (u v : POrb p) :
    K.compMk u = K.compMk v ↔ Relation.EqvGen (genRel K.gen) u v :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The colour type: components meeting a touched orbit. -/
def Color (K : TouchCompressionCert p W B) : Type _ :=
  {c : K.comp // ∃ o ∈ wordTouchedOrbits p W, K.compMk o = c}

instance (K : TouchCompressionCert p W B) : Finite K.comp :=
  inferInstanceAs (Finite (Quotient (compSetoid (genRel K.gen))))

noncomputable instance (K : TouchCompressionCert p W B) : Fintype K.comp :=
  Fintype.ofFinite _

noncomputable instance (K : TouchCompressionCert p W B) : DecidableEq K.comp :=
  Classical.decEq _

noncomputable instance (K : TouchCompressionCert p W B) : Fintype K.Color := by
  classical
  have : Finite K.Color := Subtype.finite
  exact Fintype.ofFinite _

noncomputable instance (K : TouchCompressionCert p W B) : DecidableEq K.Color :=
  Classical.decEq _

open Classical in
/-- The partial colouring: a touched orbit gets the colour of its component; an untouched
orbit gets `none`. -/
noncomputable def colorOf (K : TouchCompressionCert p W B) (o : POrb p) : Option K.Color :=
  if h : o ∈ wordTouchedOrbits p W then some ⟨K.compMk o, o, h, rfl⟩ else none

lemma colorOf_touched (K : TouchCompressionCert p W B) {o : POrb p}
    (ho : o ∈ wordTouchedOrbits p W) :
    K.colorOf o = some ⟨K.compMk o, o, ho, rfl⟩ := by
  classical simp [colorOf, ho]

lemma colorOf_untouched (K : TouchCompressionCert p W B) {o : POrb p}
    (ho : o ∉ wordTouchedOrbits p W) :
    K.colorOf o = none := by
  classical simp [colorOf, ho]

/-- The colour map factors through the component: two touched orbits in the same component
get the same colour. -/
lemma colorOf_eq_of_compMk (K : TouchCompressionCert p W B) {u v : POrb p}
    (hu : u ∈ wordTouchedOrbits p W) (hv : v ∈ wordTouchedOrbits p W)
    (hc : K.compMk u = K.compMk v) :
    K.colorOf u = K.colorOf v := by
  rw [colorOf_touched K hu, colorOf_touched K hv]
  simp only [Option.some.injEq]
  exact Subtype.ext hc

/-- The touched components: the image of `wordTouchedOrbits` under `compMk`. -/
noncomputable def touchedComps (K : TouchCompressionCert p W B) : Finset K.comp :=
  (wordTouchedOrbits p W).image K.compMk

/-- The number of colours equals the number of touched components. -/
lemma card_Color (K : TouchCompressionCert p W B) :
    Fintype.card K.Color = K.touchedComps.card := by
  classical
  have hpred : ∀ c : K.comp, (∃ o ∈ wordTouchedOrbits p W, K.compMk o = c)
      ↔ c ∈ K.touchedComps := by
    intro c
    rw [touchedComps, Finset.mem_image]
  rw [show Fintype.card K.Color
      = Fintype.card {c : K.comp // c ∈ K.touchedComps} from
        Fintype.card_congr (Equiv.subtypeEquivRight hpred)]
  exact Fintype.card_coe _

/-- The component count equals the number of components. -/
lemma card_comp (K : TouchCompressionCert p W B) :
    Fintype.card K.comp = numComp (genRel K.gen) := by
  rw [numComp, Nat.card_eq_fintype_card]

/-- A non-touched component's representative is an untouched orbit. -/
lemma out_untouched_of_notMem_touchedComps (K : TouchCompressionCert p W B) {c : K.comp}
    (hc : c ∉ K.touchedComps) :
    Quotient.out c ∉ wordTouchedOrbits p W := by
  classical
  intro o_touched
  apply hc
  rw [touchedComps, Finset.mem_image]
  exact ⟨Quotient.out c, o_touched, Quotient.out_eq c⟩

/-- Non-touched components inject into untouched orbits via `Quotient.out`. -/
lemma card_untouchedComps_le (K : TouchCompressionCert p W B) :
    Fintype.card {c : K.comp // c ∉ K.touchedComps}
      ≤ Fintype.card {o : POrb p // o ∉ wordTouchedOrbits p W} := by
  classical
  refine Fintype.card_le_of_injective
    (fun c => ⟨Quotient.out c.1, K.out_untouched_of_notMem_touchedComps c.2⟩) ?_
  rintro ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ hEq
  simp only [Subtype.mk.injEq] at hEq
  exact Subtype.ext (Quotient.out_injective hEq)

/-- **The rank bound.**  `touched.card − #colours ≤ B`.  Combine the graph-rank fact
`card(POrb p) − numComp ≤ B`, the count of components (`#comp = #colours + #untouched-comps`)
and the injection of untouched components into untouched orbits. -/
lemma rank_bound_of_cert (K : TouchCompressionCert p W B) :
    (wordTouchedOrbits p W).card - Fintype.card K.Color ≤ B := by
  classical
  -- the graph-rank fact
  have hgraph : Nat.card (POrb p) ≤ numComp (genRel K.gen) + B := numComp_genRel_ge K.gen
  have hcardP : Nat.card (POrb p) = Fintype.card (POrb p) := Nat.card_eq_fintype_card
  -- #comp = #colours + #(untouched components)
  have hcompl : Fintype.card {c : K.comp // c ∉ K.touchedComps}
      = (Finset.univ \ K.touchedComps).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext c
    simp [Finset.mem_sdiff]
  have hcompcard : K.touchedComps.card + (Finset.univ \ K.touchedComps).card
      = Fintype.card K.comp := by
    have h := Finset.card_sdiff_add_card_eq_card (s := K.touchedComps)
      (t := (Finset.univ : Finset K.comp)) (Finset.subset_univ _)
    rw [Finset.card_univ] at h; omega
  have hsplit : Fintype.card K.comp
      = Fintype.card K.Color + Fintype.card {c : K.comp // c ∉ K.touchedComps} := by
    rw [card_Color, hcompl]; omega
  -- #untouched components ≤ #untouched orbits = card(POrb p) − touched.card
  have huntcomp := card_untouchedComps_le K
  have huntorb : Fintype.card {o : POrb p // o ∉ wordTouchedOrbits p W}
      = Fintype.card (POrb p) - (wordTouchedOrbits p W).card := by
    have := card_untouched p W
    rw [numCycles_eq_natCard_POrb, Nat.card_eq_fintype_card] at this
    exact this
  have hcomp := card_comp K
  -- assemble
  have htouchle : (wordTouchedOrbits p W).card ≤ Fintype.card (POrb p) :=
    (wordTouchedOrbits p W).card_le_univ.trans (le_of_eq Finset.card_univ)
  rw [huntorb] at huntcomp
  omega

/-- **The coloring certificate from a compression certificate.**  Packages the component
colouring with the rank bound `rank_bound_of_cert`. -/
noncomputable def toColorCert (K : TouchCompressionCert p W B) :
    TouchColorCertBound p W B where
  Color := K.Color
  colorFintype := inferInstance
  colorDecEq := inferInstance
  color := K.colorOf
  color_some_of_touched := fun o ho => ⟨_, colorOf_touched K ho⟩
  color_none_of_untouched := fun o ho => colorOf_untouched K ho
  color_used := by
    rintro ⟨c, o, ho, rfl⟩
    exact ⟨o, ho, colorOf_touched K ho⟩
  endpoint_color_eq := fun j =>
    colorOf_eq_of_compMk K (touched_x p W j) (touched_y p W j)
      ((compMk_eq_iff K _ _).mpr (K.endpoint_reachable j))
  rank_bound := rank_bound_of_cert K

end TouchCompressionCert

/-- **The core counting theorem (compression form), unconditional.**  A
`TouchCompressionCert p W B` forces `numCycles (prefixPerm p W m) ≥ numCycles p − B`. -/
theorem numCycles_prefixPerm_ge_of_touchCompressionCert
    (K : TouchCompressionCert p W B) :
    (numCycles (prefixPerm p W m) : ℤ) ≥ (numCycles p : ℤ) - (B : ℤ) :=
  numCycles_prefixPerm_ge_of_touchColorCert K.toColorCert

/-! ## Non-vacuity of the touch-compression certificate

A concrete witness that the `TouchCompressionCert` hypotheses are jointly satisfiable with
`B = 1` (one generator edge) producing a *non-degenerate, tight* bound, ruling out the
"vacuous conditional" failure mode for the generic compression reduction.  Base `p = 1` on
`Fin 2` has two distinct orbits `{0}`, `{1}`; the one-letter word `W 0 = swap 0 1` touches
both; a single generator edge `(⟦0⟧, ⟦1⟧)` connects them (`B = 1`).  The theorem then yields
`numCycles (1 · swap 0 1) ≥ numCycles 1 − 1`, i.e. `1 ≥ 2 − 1`, which is tight. -/

/-- The one-edge touch-compression certificate on `Fin 2`: `swap 0 1` over the identity,
with the single generator edge connecting the two singleton orbits. -/
noncomputable def witnessCert :
    TouchCompressionCert (1 : Equiv.Perm (Fin 2)) (fun _ : Fin 1 => (⟨0, 1⟩ : Swap (Fin 2))) 1 where
  gen := fun _ => (pOrbOf 1 0, pOrbOf 1 1)
  endpoint_reachable := fun _ =>
    Relation.EqvGen.rel _ _ ⟨0, Or.inl ⟨rfl, rfl⟩⟩

/-- **Non-vacuity**: the touch-compression bound is realised non-degenerately and tightly.
`numCycles (1 · swap 0 1) = 1 ≥ numCycles 1 − 1 = 1` on `Fin 2`. -/
example :
    (numCycles (prefixPerm (1 : Equiv.Perm (Fin 2))
      (fun _ : Fin 1 => (⟨0, 1⟩ : Swap (Fin 2))) 1) : ℤ)
      ≥ (numCycles (1 : Equiv.Perm (Fin 2)) : ℤ) - 1 := by
  have h := numCycles_prefixPerm_ge_of_touchCompressionCert witnessCert
  simpa using h

end ProofsInTheBook.TouchRank

/-! ## Layer C: the cut-and-cap application

We instantiate the unconditional core counting theorem at the corrected cut-and-cap data
`p := phiLift`, `W := concatWord Ls` (the cycle-decomposition word of `faceCorr₂`, available
by `exists_cycleListProd`), `B := 2·len − 2`.  The one genuinely topological input — that
the `faceCorr₂` word's endpoints are reachable through the `2·len − 2`-edge **bank generator
graph** (the design's two `len − 1`-edge bank path forests) — is isolated as the
`FaceCorrTouchCert` data, exactly parallel to the `FaceCorrSplitCert` of `FaceCorrWord.lean`.
Everything else is closed unconditionally.

### The chain

```
numCycles φ'₂ = numCycles (phiLift · faceCorr₂)
              ≥ numCycles phiLift − (2·len − 2)        (touch-rank core)
              = (F + 2·len) − (2·len − 2)              (numCycles_phiLift)
              = F + 2.
```

### Kernel anchors

The bank-generator graph has `2·(len − 1) = 2·len − 2` edges (one path forest per bank).
The kernel `#eval`s of `FaceCorrWord.lean` (triangle / `K₄`-sphere / `K₄`-torus, all
genus) confirm `concatWord Ls` realises `phiLift · faceCorr₂` (`prefix_eq`); the bank
reachability of the endpoints through the `2·len − 2` generator edges is the topological
content the cert supplies. -/

namespace ProofsInTheBook.PlanarMap

open ForcedSplits CombMap CombMap.SimplePrimalCycle
open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

/-- **The touch-rank certificate for `faceCorr₂`.**  Carries the cycle-decomposition word
data (always available, by `exists_cycleListProd`) plus the genuinely topological residue:
the `2·len − 2` bank generator edges on `phiLift`-orbits whose reachability connects the two
endpoints of every letter of the word.  This is the position-free analogue of
`FaceCorrSplitCert`: no split positions, only the orbit-fusion rank bound. -/
structure FaceCorrTouchCert (C : SimplePrimalCycle M) where
  /-- The cycle-decomposition support lists of `faceCorr₂`. -/
  Ls : List (List C.CutDart)
  /-- Each cycle list is nonempty. -/
  Ls_pos : ∀ L ∈ Ls, 0 < L.length
  /-- The cycle-decomposition product reconstructs `faceCorr₂`. -/
  factor : FaceCorrWord.cycleListProd Ls = C.faceCorr2
  /-- The `2·len − 2` bank generator edges on `phiLift`-orbits. -/
  gen : Fin (2 * C.len - 2) →
    POrb C.phiLift × POrb C.phiLift
  /-- Every letter's endpoints are connected through the bank generator edges. -/
  endpoint_reachable : ∀ j : Fin (FaceCorrWord.concatLen Ls),
    Relation.EqvGen (genRel gen)
      (pOrbOf C.phiLift (FaceCorrWord.concatWord Ls j).x)
      (pOrbOf C.phiLift (FaceCorrWord.concatWord Ls j).y)

/-- The underlying touch-compression certificate of a `FaceCorrTouchCert`. -/
def FaceCorrTouchCert.toCompressionCert {C : SimplePrimalCycle M}
    (cert : C.FaceCorrTouchCert) :
    TouchCompressionCert C.phiLift (FaceCorrWord.concatWord cert.Ls) (2 * C.len - 2) where
  gen := cert.gen
  endpoint_reachable := cert.endpoint_reachable

/-- **The touch-rank lower bound on `numCycles φ'₂`.**  From the core counting theorem and
`numCycles phiLift = F + 2·len`, the loss is at most `2·len − 2`, so
`numCycles (phiLift · faceCorr₂) ≥ F + 2`. -/
theorem numCycles_phiLift_faceCorr2_ge_of_touchCert (C : SimplePrimalCycle M)
    (cert : C.FaceCorrTouchCert) :
    (_root_.numCycles (C.phiLift * C.faceCorr2) : ℤ) ≥ (M.F : ℤ) + 2 := by
  -- the generic touch-rank bound on the prefix product
  have hgen := numCycles_prefixPerm_ge_of_touchCompressionCert cert.toCompressionCert
  -- identify the full prefix with `phiLift · faceCorr₂`
  have hprefix : ForcedSplits.prefixPerm C.phiLift
      (FaceCorrWord.concatWord cert.Ls) (FaceCorrWord.concatLen cert.Ls)
        = C.phiLift * C.faceCorr2 := by
    rw [FaceCorrWord.prefixPerm_concatWord C.phiLift cert.Ls cert.Ls_pos, cert.factor]
  rw [hprefix] at hgen
  -- `numCycles phiLift = F + 2·len`
  have hphi : (_root_.numCycles C.phiLift : ℤ) = (M.F : ℤ) + 2 * (C.len : ℤ) := by
    rw [C.numCycles_phiLift]; push_cast; ring
  rw [hphi] at hgen
  -- `2·len − 2` in ℕ casts to `2·len − 2` in ℤ since `len ≥ 1`
  have hlen : 1 ≤ C.len := C.len_pos
  have hBcast : ((2 * C.len - 2 : ℕ) : ℤ) = 2 * (C.len : ℤ) - 2 := by
    have : 2 ≤ 2 * C.len := by omega
    omega
  rw [hBcast] at hgen
  linarith

/-- **The corrected face-count lower bound from a touch-rank certificate** (position-free,
unconditional in the word/`prefix_eq`).  `(cutCapMap2).F ≥ M.F + 2`. -/
theorem cutCapMap2_F_lower_of_touchCert (C : SimplePrimalCycle M)
    (cert : C.FaceCorrTouchCert) :
    (C.cutCapMap2).F ≥ M.F + 2 := by
  have h := numCycles_phiLift_faceCorr2_ge_of_touchCert C cert
  rw [CombMap.F_eq_numCycles, cutCapPhi2_eq_phiLift_mul]
  have : (M.F : ℤ) + 2 ≤ (_root_.numCycles (C.phiLift * C.faceCorr2) : ℤ) := h
  omega

/-- **The lower-bound Jordan / chord-separation theorem from a touch-rank certificate.**
No cut edge of a simple primal cycle on a sphere is straddled by a cycle-avoiding dual
path, consuming only the position-free lower bound (via the touch-rank certificate) and the
standing connectivity / Euler parameters. -/
theorem jordan_simple_cycle2_lower_of_touchCert (C : SimplePrimalCycle M)
    (cert : C.FaceCorrTouchCert)
    (hchi : M.eulerChar = 2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) := by
  intro hpath
  have hconnected : (C.cutCapMap2).Connected := hconn i hpath
  have hle : (C.cutCapMap2).F ≤ M.F :=
    C.cutCapMap2_F_le_of_connected hchi hconnected
  have hge : (C.cutCapMap2).F ≥ M.F + 2 := C.cutCapMap2_F_lower_of_touchCert cert
  omega

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.TouchRank.numCycles_prefixPerm_ge_of_touchColorCert
#print axioms ProofsInTheBook.TouchRank.numCycles_prefixPerm_ge_of_touchCompressionCert
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.cutCapMap2_F_lower_of_touchCert
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.jordan_simple_cycle2_lower_of_touchCert
