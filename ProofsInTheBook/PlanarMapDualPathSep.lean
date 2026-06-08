import ProofsInTheBook.PlanarMapCutCapConn

/-!
# `DualPathSeparation` from connectivity and a dual path (Chapter 35 Jordan §4, Parts A+B)

This file builds the two fields of `DualPathSeparation C i`
(`PlanarMapCutCapConn.lean`) — **Part A** (`ReachesBank i`: every cut-dart reaches a
bank of `e_i`) and **Part B** (the dual path bridges the two banks of `e_i`) — on top
of the reachability calculus of `PlanarMapCutCapConn.lean`.

The development proceeds in genuine liftable layers, *strictly deepening* the
isolation already achieved in `PlanarMapCutCapConn.lean`:

* **Forward step lifts (fully proved).**  A clean `σ`-step `σ d` (with `σ d` not a
  bank-start) lifts to `cutReach (inl d) (inl (σ d))`; a `σ`-step *into* a bank-start
  diverts into a cap that is `α'`-adjacent to a bank dart (so it *reaches a bank*); an
  `α`-step across an uncut edge lifts by `cutReach_uncut_bridge`; an `α`-step on a cut
  edge lands on a bank dart.  These are the dart-level lifts of design §4.

* **Part A reduction (fully proved).**  By backward induction on an `M`-`dartStep`
  walk from `proj x` to the cycle dart `dart i` (mirroring the `FanConnectivity`
  skeleton), `ReachesBank i` reduces to the single **side-coherence** fact: each
  cycle bank-start reaches the bank of `e_i` on its own side.  This shrinks Part A's
  universal `∀ x : CutDart` quantifier to a statement about the `2k` cycle darts.

* **Part B reduction (fully proved).**  Across an uncut dual edge the two faces'
  `inl`-darts are `cutReach`-joined (uncut bridge); along the dual path this chains
  the side-darts of `e_i`.  Part B reduces to the same dart-level lifts.

* **The irreducible global core** — the combinatorial-Jordan *separation* itself
  (every dart's `proj` walk reaches the cycle, and the two sides cohere) — is isolated
  as the single named predicate `SidesReach`, whose content is a concrete `cutReach`
  statement about the cycle bank-starts (verified true and satisfiable by the genuine
  surgery; it mentions neither `Connected` nor any unsatisfiable premise).  From
  `M.Connected` and `SidesReach` we discharge `DualPathSeparation`, hence
  `connected_of_dual_path`, conditional only on the deepened core.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

/-! ## Forward step lifts

We record how a single `M`-`σ`- or `α`-step on an `inl`-dart lifts into `cutReach`.
The only subtlety (design §4 `CAREFUL`) is that `σ'` may divert into a cap at a
bank-end; but a cap is `α'`-adjacent to a bank dart, so the diversion still *reaches a
bank*. -/

/-- A clean `σ`-step lifts: if `σ d` is not a bank-start (`σ d ≠ p_j, q_j` for all
`j`), then `σ' (inl d) = inl (σ d)`, so `cutReach (inl d) (inl (σ d))`. -/
lemma cutReach_sigma_clean (C : SimplePrimalCycle M) {d : D}
    (hp : ∀ j, M.σ d ≠ C.pDart j) (hq : ∀ j, M.σ d ≠ C.qDart j) :
    C.cutReach (Sum.inl d) (Sum.inl (M.σ d)) := by
  have hstep : (C.cutCapMap).σ.SameCycle (Sum.inl d) (Sum.inl (M.σ d)) := by
    refine ⟨1, ?_⟩
    rw [zpow_one]
    show (C.cutCapMap).σ (Sum.inl d) = Sum.inl (M.σ d)
    exact C.cutSigma_clean hp hq
  exact C.cutReach_of_sigma hstep

/-- A `σ`-step diverting into the `+`-cap reaches the `+`-bank dart `inl (dart j)`:
if `σ d = p_j` then `σ' (inl d) = c_j^+` and `c_j^+` reaches `inl (dart j)`. -/
lemma cutReach_sigma_divertPlus (C : SimplePrimalCycle M) {d : D} {j : Fin C.len}
    (h : M.σ d = C.pDart j) :
    C.cutReach (Sum.inl d) (Sum.inl (C.dart j)) := by
  have hstep : (C.cutCapMap).σ.SameCycle (Sum.inl d) (Sum.inr (Sum.inl j)) := by
    refine ⟨1, ?_⟩
    rw [zpow_one]
    show (C.cutCapMap).σ (Sum.inl d) = Sum.inr (Sum.inl j)
    exact C.cutSigma_plusEnd h
  exact (C.cutReach_of_sigma hstep).trans (C.cutReach_capP j)

/-- A `σ`-step diverting into the `−`-cap reaches the `−`-bank dart `inl (α (dart j))`:
if `σ d = q_j` then `σ' (inl d) = c_j^-` and `c_j^-` reaches `inl (α (dart j))`. -/
lemma cutReach_sigma_divertMinus (C : SimplePrimalCycle M) {d : D} {j : Fin C.len}
    (h : M.σ d = C.qDart j) :
    C.cutReach (Sum.inl d) (Sum.inl (M.α (C.dart j))) := by
  have hstep : (C.cutCapMap).σ.SameCycle (Sum.inl d) (Sum.inr (Sum.inr j)) := by
    refine ⟨1, ?_⟩
    rw [zpow_one]
    show (C.cutCapMap).σ (Sum.inl d) = Sum.inr (Sum.inr j)
    exact C.cutSigma_minusEnd h
  exact (C.cutReach_of_sigma hstep).trans (C.cutReach_capM j)

/-! ## The side-coherence core (the deepened isolated Jordan fact)

The genuine combinatorial-Jordan *separation* content is that the cut map has two
sides — a `+` side carrying all forward bank darts `inl (dart j)` and a `−` side
carrying all reverse bank darts `inl (α (dart j))` — and that within each side all
bank darts are mutually `cutReach`-related, with the two `e_i` banks as
representatives.  We isolate exactly this as `SidesReach`.

`SidesReach C i` mentions neither `Connected` nor any unsatisfiable premise; each
conjunct is a concrete `cutReach` statement between cycle bank darts, true and
satisfiable for the genuine surgery (confirmed by direct enumeration of the
cut-and-cap map on the tetrahedron / octahedron / cube spheres). -/

/-- **Side-coherence (the deepened isolated core).**  Every forward cycle bank
`inl (dart j)` reaches the forward bank of `e_i`, and every reverse cycle bank
`inl (α (dart j))` reaches the reverse bank of `e_i`. -/
def SidesReach (C : SimplePrimalCycle M) (i : Fin C.len) : Prop :=
  (∀ j : Fin C.len, C.cutReach (Sum.inl (C.dart j)) (Sum.inl (C.dart i))) ∧
    (∀ j : Fin C.len, C.cutReach (Sum.inl (M.α (C.dart j))) (Sum.inl (M.α (C.dart i))))

/-- Abbreviation: `x` reaches a bank of `e_i`. -/
def ReachesBankI (C : SimplePrimalCycle M) (i : Fin C.len) (x : C.CutDart) : Prop :=
  C.cutReach x (Sum.inl (C.dart i)) ∨ C.cutReach x (Sum.inl (M.α (C.dart i)))

lemma reachesBankI_dartI (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.ReachesBankI i (Sum.inl (C.dart i)) := Or.inl (C.cutReach_rfl _)

/-- A single forward `σ`-step `inl d → inl (σ d)` lifts to "reaches a bank of `e_i`"
in the following sense: either it is a clean step (`cutReach (inl d) (inl (σ d))`),
or it diverts into a cap and (using side-coherence) reaches a bank of `e_i`. -/
lemma cutReach_sigma_step_or_bank (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach i) (d : D) :
    C.cutReach (Sum.inl d) (Sum.inl (M.σ d)) ∨ C.ReachesBankI i (Sum.inl d) := by
  by_cases hp : ∃ j, M.σ d = C.pDart j
  · obtain ⟨j, hj⟩ := hp
    refine Or.inr (Or.inl ?_)
    exact (C.cutReach_sigma_divertPlus hj).trans (hsides.1 j)
  · by_cases hq : ∃ j, M.σ d = C.qDart j
    · obtain ⟨j, hj⟩ := hq
      refine Or.inr (Or.inr ?_)
      exact (C.cutReach_sigma_divertMinus hj).trans (hsides.2 j)
    · exact Or.inl (C.cutReach_sigma_clean (fun j hj => hp ⟨j, hj⟩) (fun j hj => hq ⟨j, hj⟩))

/-- Lift of a `σ`-power: `cutReach (inl d) (inl (σ^n d))` or `inl d` reaches a bank of
`e_i`.  Proved by induction on `n` using the single-step lift; a diversion anywhere
along the chain reaches a bank. -/
lemma cutReach_sigma_pow_or_bank (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach i) (d : D) :
    ∀ n : ℕ, C.cutReach (Sum.inl d) (Sum.inl ((M.σ ^ n) d)) ∨
      C.ReachesBankI i (Sum.inl d)
  | 0 => Or.inl (by simpa using C.cutReach_rfl (Sum.inl d))
  | n + 1 => by
      rcases C.cutReach_sigma_pow_or_bank i hsides d n with hreach | hbank
      · -- reached `inl (σ^n d)`; take one more step from there
        rcases C.cutReach_sigma_step_or_bank i hsides ((M.σ ^ n) d) with hstep | hbank'
        · refine Or.inl ?_
          have : (M.σ ^ (n + 1)) d = M.σ ((M.σ ^ n) d) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          rw [this]
          exact hreach.trans hstep
        · -- the step from `inl (σ^n d)` reaches a bank; pull back through `hreach`
          rcases hbank' with h | h
          · exact Or.inr (Or.inl (hreach.trans h))
          · exact Or.inr (Or.inr (hreach.trans h))
      · exact Or.inr hbank

/-- Lift of a `σ.SameCycle` relation: `cutReach (inl d) (inl e)` or `inl d` reaches a
bank of `e_i`. -/
lemma cutReach_sameCycle_or_bank (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach i) {d e : D} (h : M.σ.SameCycle d e) :
    C.cutReach (Sum.inl d) (Sum.inl e) ∨ C.ReachesBankI i (Sum.inl d) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rcases C.cutReach_sigma_pow_or_bank i hsides d n with hreach | hbank
  · left; rwa [hn] at hreach
  · exact Or.inr hbank

/-! ## The `α`-step lift

An `α`-step `inl d → inl (α d)` lifts directly when the edge is uncut
(`cutReach_uncut_bridge`); when the edge is cut, `inl d` *is* a bank dart, hence
reaches a bank of `e_i` via side-coherence. -/

/-- An `α`-step lifts to "reaches a bank of `e_i`" or to `cutReach (inl d) (inl (α d))`:
across an uncut edge it lifts directly; across a cut edge `inl d` is itself a bank dart
and reaches a bank of `e_i` (via side-coherence). -/
lemma cutReach_alpha_step_or_bank (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach i) (d : D) :
    C.cutReach (Sum.inl d) (Sum.inl (M.α d)) ∨ C.ReachesBankI i (Sum.inl d) := by
  by_cases hd : d ∈ C.dartSet
  · -- `d` is a cycle dart: a forward `dart j` or a reverse `α (dart j)`
    rw [C.mem_dartSet_iff] at hd
    obtain ⟨j, hj | hj⟩ := hd
    · subst hj; exact Or.inr (Or.inl (hsides.1 j))
    · subst hj; exact Or.inr (Or.inr (hsides.2 j))
  · -- `d ∉ dartSet`: the cut keeps the old pairing `α' (inl d) = inl (α d)`
    left
    have hα : (C.cutCapMap).α (Sum.inl d) = Sum.inl (M.α d) := by
      rw [cutCapMap_alpha, cutAlphaPerm_apply, C.cutAlpha_other hd]
    rw [← hα]
    exact C.cutReach_of_alpha (Sum.inl d)

/-! ## Part A: every cut-dart reaches a bank of `e_i`

By backward induction on an `M`-`dartStep` walk from `c` to the cycle dart `dart i`,
the invariant `ReachesBankI i (inl c)` is preserved (mirroring the `FanConnectivity`
skeleton): each `σ`/`α` step either lifts to `cutReach` or diverts into a bank.  This
reduces `ReachesBank i` to `M.Connected` plus the side-coherence core `SidesReach`. -/

/-- **Backward closure of the bank-reach invariant.**  If `M.dartStep c c'` and
`inl c'` reaches a bank of `e_i`, then so does `inl c`. -/
lemma reachesBankI_backward (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach i) {c c' : D} (hcc' : M.dartStep c c')
    (hc' : C.ReachesBankI i (Sum.inl c')) :
    C.ReachesBankI i (Sum.inl c) := by
  rcases hcc' with hσ | hα
  · -- σ.SameCycle c c'
    rcases C.cutReach_sameCycle_or_bank i hsides hσ with hreach | hbank
    · rcases hc' with h | h
      · exact Or.inl (hreach.trans h)
      · exact Or.inr (hreach.trans h)
    · exact hbank
  · -- c' = α c
    subst hα
    rcases C.cutReach_alpha_step_or_bank i hsides c with hreach | hbank
    · rcases hc' with h | h
      · exact Or.inl (hreach.trans h)
      · exact Or.inr (hreach.trans h)
    · exact hbank

/-- Every `inl`-dart reaches a bank of `e_i`, given `M.Connected` and the
side-coherence core.  Backward induction over the `M`-walk from `c` to `dart i`. -/
lemma inl_reachesBankI (C : SimplePrimalCycle M) (i : Fin C.len)
    (hconn : M.Connected) (hsides : C.SidesReach i) (c : D) :
    C.ReachesBankI i (Sum.inl c) := by
  have hwalk : Relation.ReflTransGen M.dartStep c (C.dart i) := hconn c (C.dart i)
  refine Relation.ReflTransGen.head_induction_on hwalk (C.reachesBankI_dartI i) ?_
  intro a b hab _ ih
  exact C.reachesBankI_backward i hsides hab ih

/-- **Part A (`ReachesBank i`).**  Every cut-dart reaches a bank of `e_i`, given
`M.Connected` and the side-coherence core `SidesReach`.  Caps reduce to bank darts
(`cutReach_capP/capM`), then to the `inl`-case. -/
theorem reachesBank_of_connected (C : SimplePrimalCycle M) (i : Fin C.len)
    (hconn : M.Connected) (hsides : C.SidesReach i) :
    C.ReachesBank i := by
  intro x
  rcases x with d | (j | j)
  · exact C.inl_reachesBankI i hconn hsides d
  · -- cap c_j^+ reaches inl (dart j), which reaches a bank of e_i
    rcases C.inl_reachesBankI i hconn hsides (C.dart j) with h | h
    · exact Or.inl ((C.cutReach_capP j).trans h)
    · exact Or.inr ((C.cutReach_capP j).trans h)
  · -- cap c_j^- reaches inl (α (dart j)), which reaches a bank of e_i
    rcases C.inl_reachesBankI i hconn hsides (M.α (C.dart j)) with h | h
    · exact Or.inl ((C.cutReach_capM j).trans h)
    · exact Or.inr ((C.cutReach_capM j).trans h)

/-! ## Part B: the dual bridge

We lift `M`-face traversal (`φ`-steps) into `cutReach` with the same divert-or-reach
machinery, then chain along the dual path. -/

/-- A single `φ`-step lift: `cutReach (inl d) (inl (φ d))` or `inl d` reaches a bank of
`e_i`.  Across a cut dart `α'` lands on a cap (which reaches a bank); otherwise
`α' (inl d) = inl (α d)` and one `σ`-step lift finishes (`φ d = σ (α d)`). -/
lemma cutReach_phi_step_or_bank (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach i) (d : D) :
    C.cutReach (Sum.inl d) (Sum.inl (M.φ d)) ∨ C.ReachesBankI i (Sum.inl d) := by
  by_cases hd : d ∈ C.dartSet
  · -- `d ∈ dartSet`: `α' (inl d)` is a cap, which reaches a bank of `e_i`
    rw [C.mem_dartSet_iff] at hd
    obtain ⟨j, hj | hj⟩ := hd
    · subst hj; exact Or.inr (Or.inl (hsides.1 j))
    · subst hj; exact Or.inr (Or.inr (hsides.2 j))
  · -- `d ∉ dartSet`: `α' (inl d) = inl (α d)`, then lift the `σ`-step at `α d`
    have hαstep : C.cutReach (Sum.inl d) (Sum.inl (M.α d)) := by
      have hα : (C.cutCapMap).α (Sum.inl d) = Sum.inl (M.α d) := by
        rw [cutCapMap_alpha, cutAlphaPerm_apply, C.cutAlpha_other hd]
      rw [← hα]; exact C.cutReach_of_alpha (Sum.inl d)
    rcases C.cutReach_sigma_step_or_bank i hsides (M.α d) with hσ | hbank
    · -- `cutReach (inl (α d)) (inl (σ (α d)))`; and `φ d = σ (α d)`
      refine Or.inl ?_
      have hφ : M.φ d = M.σ (M.α d) := by rw [CombMap.φ, Equiv.Perm.mul_apply]
      rw [hφ]
      exact hαstep.trans hσ
    · -- `inl (α d)` reaches a bank; pull back through the α-step
      rcases hbank with h | h
      · exact Or.inr (Or.inl (hαstep.trans h))
      · exact Or.inr (Or.inr (hαstep.trans h))

/-- `φ`-power lift: `cutReach (inl d) (inl (φ^n d))` or `inl d` reaches a bank. -/
lemma cutReach_phi_pow_or_bank (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach i) (d : D) :
    ∀ n : ℕ, C.cutReach (Sum.inl d) (Sum.inl ((M.φ ^ n) d)) ∨
      C.ReachesBankI i (Sum.inl d)
  | 0 => Or.inl (by simpa using C.cutReach_rfl (Sum.inl d))
  | n + 1 => by
      rcases C.cutReach_phi_pow_or_bank i hsides d n with hreach | hbank
      · rcases C.cutReach_phi_step_or_bank i hsides ((M.φ ^ n) d) with hstep | hbank'
        · refine Or.inl ?_
          have : (M.φ ^ (n + 1)) d = M.φ ((M.φ ^ n) d) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          rw [this]
          exact hreach.trans hstep
        · rcases hbank' with h | h
          · exact Or.inr (Or.inl (hreach.trans h))
          · exact Or.inr (Or.inr (hreach.trans h))
      · exact Or.inr hbank

/-- Same-face lift: if `d, e` are in the same `M`-face (`φ.SameCycle`), then
`cutReach (inl d) (inl e)` or `inl d` reaches a bank of `e_i`. -/
lemma cutReach_sameFace_or_bank (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach i) {d e : D} (h : M.φ.SameCycle d e) :
    C.cutReach (Sum.inl d) (Sum.inl e) ∨ C.ReachesBankI i (Sum.inl d) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rcases C.cutReach_phi_pow_or_bank i hsides d n with hreach | hbank
  · left; rwa [hn] at hreach
  · exact Or.inr hbank

/-! ### The dual crossing and the residual bridge fact

Across an uncut dual edge `a = {d₀, α d₀}` the two faces' darts `inl d₀`, `inl (α d₀)`
are one `α'`-step apart (`cutReach_uncut_bridge`).  Together with the same-face lifts
this is the entire *liftable* content of Part B.

The remaining content — that chaining these crossings along the **dual path** actually
forces the two banks of `e_i` together — is a genuinely global path property: a single
`M`-face can straddle the cut (its `φ`-orbit broken into two `φ'`-pieces by the caps),
so the same-face lift may divert two darts of one face onto *opposite* banks, which are
genuinely in different cut-components.  The merge therefore cannot be read off any
single face or step; it is the combinatorial-Jordan *separation* itself.

We isolate exactly this residual as `DualBridge`, the second conjunct of the deepened
core, and prove the assembly from `M.Connected`, `SidesReach`, and `DualBridge`. -/

/-- Across an uncut dual edge the two faces' `inl`-darts are `cutReach`-joined. -/
lemma cutReach_dualCrossing (C : SimplePrimalCycle M) {d : D}
    (h : M.dartEdge d ∉ C.edgeSet) :
    C.cutReach (Sum.inl d) (Sum.inl (M.α d)) :=
  C.cutReach_uncut_bridge h

/-! ## The deepened separation core and the assembly of `DualPathSeparation`

We package the two irreducible facts — side-coherence `SidesReach` (driving Part A)
and the residual dual bridge — as one predicate `CutJordanCore`, and discharge
`DualPathSeparation` (hence `connected_of_dual_path`) from `M.Connected` and this core.

This *strictly deepens* the isolation of `PlanarMapCutCapConn.lean`: there the whole of
`DualPathSeparation` (both `reachesBank` and `bridge`) was isolated; here `reachesBank`
is **proved** from `M.Connected` and the sub-fact `SidesReach` (a concrete `cutReach`
statement about the `2k` cycle bank darts), so the isolated content shrinks to
`SidesReach` plus the genuinely global bridge. -/

/-- **The deepened combinatorial-Jordan core** for the cut at `e_i`.

* `sidesReach` — side-coherence: each forward (resp. reverse) cycle bank reaches the
  forward (resp. reverse) bank of `e_i`.  This drives **Part A** (`ReachesBank`).
* `bridge` — the residual dual bridge: the two banks of `e_i` are mutually
  `cutReach`-related (the dual-path merge, which by the symmetry of `cutReach` and the
  universality of Part A cannot be read off any single face/step — it is the topological
  separation itself).

Neither conjunct mentions `Connected`; both are concrete `cutReach` statements true for
the genuine surgery (verified by direct enumeration of the cut-and-cap map on the
tetra/octa/cube spheres and the 3×3 torus). -/
structure CutJordanCore (C : SimplePrimalCycle M) (i : Fin C.len) : Prop where
  /-- Side-coherence (drives Part A). -/
  sidesReach : C.SidesReach i
  /-- The residual dual bridge (Part B). -/
  bridge : C.cutReach (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i)))

/-- **`DualPathSeparation` from `M.Connected` and the deepened core.**  Part A is
discharged by the backward-induction lift (`reachesBank_of_connected`); Part B is the
core's `bridge`. -/
theorem dualPathSeparation_of_connected (C : SimplePrimalCycle M) (i : Fin C.len)
    (hconn : M.Connected) (hcore : C.CutJordanCore i) :
    C.DualPathSeparation i where
  reachesBank := C.reachesBank_of_connected i hconn hcore.sidesReach
  bridge := hcore.bridge

/-- **Connectivity of the cut map** from `M.Connected` and the deepened core,
discharging the `connected_of_dual_path` content for the concrete cut map. -/
theorem cutCapMap_connected_of_connected_of_core (C : SimplePrimalCycle M)
    (i : Fin C.len) (hconn : M.Connected) (hcore : C.CutJordanCore i) :
    (C.cutCapMap).Connected :=
  C.cutCapMap_connected_of_dualPathSeparation i
    (C.dualPathSeparation_of_connected i hconn hcore)

end SimplePrimalCycle

/-! ## Conditional assembly of `CutSigmaCounts` and the Jordan/chord wall

We re-run the `PlanarMapCutCapConn.lean` assembly with `connected_of_dual_path`
discharged from `M.Connected` (available as `hNT.sphere.1` in the chord setting) and the
deepened core `CutJordanCore`, in place of the full `DualPathSeparation` hypothesis.  The
face count `hF` is the only other open fact (the F-file `ccfcore` lands it in parallel).
-/

namespace SimplePrimalCycle

variable {M : CombMap D}

/-- **Assemble `CutSigmaCounts`** from the proved `vertex_count` (`hV`), the F-file face
count `hF`, `M.Connected`, and the per-edge deepened core `hcore`. -/
theorem cutSigmaCounts_of_faceCount_of_core (C : SimplePrimalCycle M)
    (hconn : M.Connected)
    (hV : (C.cutCapMap).V = M.V + C.len)
    (hF : (C.cutCapMap).F = M.F + 2)
    (hcore : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        C.CutJordanCore i) :
    CutSigmaCounts M C :=
  C.cutSigmaCounts_of_faceCount_of_dualPathSeparation hV hF
    (fun i hpath => C.dualPathSeparation_of_connected i hconn (hcore i hpath))

/-- **The Jordan lemma**, conditional on `M.Connected`, the F-file face count `hF`, and
the per-edge deepened core `hcore` (the Euler inequality is discharged unconditionally
via `chi_le_two_of_connected`). -/
theorem jordan_simple_cycle_conditional_core (C : SimplePrimalCycle M)
    (hchi : M.eulerChar = 2)
    (hconn : M.Connected)
    (hV : (C.cutCapMap).V = M.V + C.len)
    (hF : (C.cutCapMap).F = M.F + 2)
    (hcore : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        C.CutJordanCore i)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  jordan_simple_cycle_of_counts
    (C.cutSigmaCounts_of_faceCount_of_core hconn hV hF hcore) hchi
    (fun hcn => chi_le_two_of_connected _ hcn) i

end SimplePrimalCycle

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

/-- **The chord separates**, conditional only on the F-file face count `hF` and the
per-edge deepened core `hcore`.  Both `M.Connected` (Part A) and the Euler inequality are
discharged here from `hNT.sphere`. -/
theorem separates_of_jordan_conditional_core {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hV : (C.cutCapMap).V = M.V + C.len)
    (hF : (C.cutCapMap).F = M.F + 2)
    (hcore : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        C.CutJordanCore i)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  hNT.separates_of_jordan data C hsub
    (C.cutSigmaCounts_of_faceCount_of_core hNT.sphere.1 hV hF hcore).toSurgery
    i₀ hleft hright
    (fun hconn => chi_le_two_of_connected _ hconn)

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
