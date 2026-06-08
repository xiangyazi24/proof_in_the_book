import ProofsInTheBook.PlanarMapCutCap2FWalk
import ProofsInTheBook.PlanarMapDualPathSep

/-!
# The two-layer fragment bridge for the CORRECTED cut-and-cap map (Chapter 35, Part B)

This file implements the complete bridge design of `HANDOFF/CH35_BRIDGE_DESIGN.md`
for the **corrected** cut-and-cap map `C.cutCapMap2` (from
`PlanarMapCutCapSigma2.lean`).  It discharges the connectivity parameter `hconn` of
`jordan_simple_cycle2_walk`:

```
∀ i, DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
       (C.cutCapMap2).Connected
```

from a **fragment-level dual path** between the two cycle-sides of an edge `e_i`.

## The design's central correction

A bare face sequence in the ordinary dual graph is too weak: a *straddling* old face
(whose `φ`-orbit is broken by the cut into two `φ'₂`-pieces sitting on opposite banks)
can "teleport" the lift across it.  The right object carries **fragments**: each
position in the lifted path is one connected component of the survives-the-cut
relation inside an old face, and consecutive fragments are joined **only** across
actual uncut primal edges.  We never prove "entry and exit fragment of the same old
face are connected" — that is false.

## Two layers (per the design)

* **Layer 1** — `banks_connected2_of_fragment_dual_path` : lifting along a
  fragment-level path.  Each step is `α'`-joined across an uncut gate; each fragment is
  `φ'₂`-internal (so cut-connected); the endpoints attach to the two banks via the cap
  `α'`-edges.  This proves the bridge `cutReach2 (inl (dart i)) (inl (α (dart i)))`.

* **Layer 2** — `fragmentDualPath2_of_ordinary` : refine an *ordinary* dual path that
  carries the no-teleport (`SameFragment`) compatibility data into a
  `FragmentDualPath2`.  This is where the same-fragment-at-gates argument lives.

Combined with the **Part A** lift (every cut-dart of the corrected map reaches a bank
of `e_i`, ported here from the corrected `σ'₂` action) the two layers force
`(cutCapMap2).Connected`, discharging `hconn`.

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

/-! ## Layer 0: the corrected-map reachability calculus `cutReach2`

`N := C.cutCapMap2`.  `α'` is unchanged (`cutCapMap2.α = cutAlphaPerm`), so all the
`α'`-bridges (uncut gate, cap attachment) transfer *verbatim* from the buggy map; only
`σ'₂` differs, and its three-way action (`cutSigma2_inl_cases`) has the same shape
(clean | divert into `+`-cap | divert into `−`-cap). -/

/-- `cutReach2 x y`: `x` and `y` are joined by a chain of `cutCapMap2.dartStep`s. -/
def cutReach2 (C : SimplePrimalCycle M) (x y : C.CutDart) : Prop :=
  Relation.ReflTransGen (C.cutCapMap2).dartStep x y

@[refl] lemma cutReach2_rfl (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutReach2 x x := Relation.ReflTransGen.refl

lemma cutReach2_trans (C : SimplePrimalCycle M) {x y z : C.CutDart}
    (h₁ : C.cutReach2 x y) (h₂ : C.cutReach2 y z) :
    C.cutReach2 x z := Relation.ReflTransGen.trans h₁ h₂

/-- `cutCapMap2.dartStep` is symmetric. -/
lemma cutDartStep2_symm (C : SimplePrimalCycle M) {x y : C.CutDart}
    (h : (C.cutCapMap2).dartStep x y) :
    (C.cutCapMap2).dartStep y x := by
  rcases h with hσ | hα
  · exact Or.inl hσ.symm
  · refine Or.inr ?_
    rw [hα]
    show x = (C.cutCapMap2).α ((C.cutCapMap2).α x)
    rw [show (C.cutCapMap2).α ((C.cutCapMap2).α x) = x from
      congrArg (fun f : Equiv.Perm C.CutDart => f x) (C.cutCapMap2).α_invol]

lemma cutReach2_symm (C : SimplePrimalCycle M) {x y : C.CutDart} (h : C.cutReach2 x y) :
    C.cutReach2 y x :=
  Relation.ReflTransGen.symmetric (fun _ _ => C.cutDartStep2_symm) h

/-- A single `σ'₂`-step is a reachability. -/
lemma cutReach2_of_sigma (C : SimplePrimalCycle M) {x y : C.CutDart}
    (h : (C.cutCapMap2).σ.SameCycle x y) :
    C.cutReach2 x y :=
  Relation.ReflTransGen.single (Or.inl h)

/-- A single `α'`-step is a reachability. -/
lemma cutReach2_of_alpha (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutReach2 x ((C.cutCapMap2).α x) :=
  Relation.ReflTransGen.single (Or.inr rfl)

/-- A single `φ'₂`-step is a reachability (`α'` then `σ'₂`). -/
lemma cutReach2_of_phi_step (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutReach2 x ((C.cutCapMap2).φ x) := by
  have h1 : C.cutReach2 x ((C.cutCapMap2).α x) := C.cutReach2_of_alpha x
  have h2 : C.cutReach2 ((C.cutCapMap2).α x) ((C.cutCapMap2).σ ((C.cutCapMap2).α x)) :=
    C.cutReach2_of_sigma ⟨1, by rw [zpow_one]⟩
  refine C.cutReach2_trans h1 ?_
  have : (C.cutCapMap2).φ x = (C.cutCapMap2).σ ((C.cutCapMap2).α x) := by
    rw [CombMap.φ, Equiv.Perm.mul_apply]
  rw [this]; exact h2

lemma cutReach2_of_phi_pow (C : SimplePrimalCycle M) (x : C.CutDart) :
    ∀ n : ℕ, C.cutReach2 x (((C.cutCapMap2).φ ^ n) x)
  | 0 => by simpa using C.cutReach2_rfl x
  | n + 1 => by
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact C.cutReach2_trans (C.cutReach2_of_phi_step x)
        (C.cutReach2_of_phi_pow ((C.cutCapMap2).φ x) n)

/-- Same face (`φ'₂`-cycle) ⇒ reachable. -/
lemma cutReach2_of_phi_sameCycle (C : SimplePrimalCycle M) {x y : C.CutDart}
    (h : (C.cutCapMap2).φ.SameCycle x y) :
    C.cutReach2 x y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have := C.cutReach2_of_phi_pow x n
  rwa [hn] at this

/-! ### The `α'`-bridges (unchanged from the buggy map: `cutCapMap2.α = cutAlphaPerm`) -/

@[simp] lemma cutCapMap2_alpha_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    (C.cutCapMap2).α x = C.cutAlpha x := by
  rw [cutCapMap2_alpha, cutAlphaPerm_apply]

/-- **The uncut bridge.**  Across an uncut edge `dartEdge d ∉ E(C)`, the corrected cut
map joins `inl d` to `inl (α d)` by one `α'`-step. -/
lemma cutReach2_uncut_bridge (C : SimplePrimalCycle M) {d : D}
    (h : M.dartEdge d ∉ C.edgeSet) :
    C.cutReach2 (Sum.inl d) (Sum.inl (M.α d)) := by
  have hd : d ∉ C.dartSet := C.notMem_dartSet_of_dartEdge_notMem h
  have : (C.cutCapMap2).α (Sum.inl d) = Sum.inl (M.α d) := by
    rw [cutCapMap2_alpha_apply, C.cutAlpha_other hd]
  rw [← this]
  exact C.cutReach2_of_alpha (Sum.inl d)

/-- `c_i^+` reaches the forward bank dart `inl (dart i)`. -/
lemma cutReach2_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutReach2 (Sum.inr (Sum.inl i)) (Sum.inl (C.dart i)) := by
  have : (C.cutCapMap2).α (Sum.inr (Sum.inl i)) = Sum.inl (C.dart i) := by
    rw [cutCapMap2_alpha_apply, cutAlpha_capPlus]
  rw [← this]; exact C.cutReach2_of_alpha _

/-- `c_i^-` reaches the reverse bank dart `inl (α (dart i))`. -/
lemma cutReach2_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutReach2 (Sum.inr (Sum.inr i)) (Sum.inl (M.α (C.dart i))) := by
  have : (C.cutCapMap2).α (Sum.inr (Sum.inr i)) = Sum.inl (M.α (C.dart i)) := by
    rw [cutCapMap2_alpha_apply, cutAlpha_capMinus]
  rw [← this]; exact C.cutReach2_of_alpha _

/-! ## Layer 0b: the corrected forward step lifts (Part A machinery)

These port `cutReach_sigma_*`, `cutReach_alpha_step_or_bank`, `cutReach_phi_*` from
`PlanarMapDualPathSep.lean` to the corrected map, using `cutSigma2_clean`,
`cutSigma2_plusEnd`, `cutSigma2_minusEnd`.  The corrected `+`-cap diverts into the
*previous* cap `c_{prevIdx j}^+`, but that cap still `α'`-attaches to a `+`-bank dart
`inl (dart (prevIdx j))`, so it still **reaches a bank**; the side-coherence core
`SidesReach2` absorbs the index shift. -/

/-- A clean `σ'₂`-step lifts: if `σ d` is not a bank-start, `σ'₂ (inl d) = inl (σ d)`. -/
lemma cutReach2_sigma_clean (C : SimplePrimalCycle M) {d : D}
    (hp : ∀ j, M.σ d ≠ C.pDart j) (hq : ∀ j, M.σ d ≠ C.qDart j) :
    C.cutReach2 (Sum.inl d) (Sum.inl (M.σ d)) := by
  refine C.cutReach2_of_sigma ⟨1, ?_⟩
  rw [zpow_one]
  show (C.cutCapMap2).σ (Sum.inl d) = Sum.inl (M.σ d)
  exact C.cutSigma2_clean hp hq

/-- A `σ'₂`-step diverting at a `+`-bank-end `σ d = p_j` lands on the previous `+`-cap
`c_{prevIdx j}^+`, which reaches the `+`-bank dart `inl (dart (prevIdx j))`. -/
lemma cutReach2_sigma_divertPlus (C : SimplePrimalCycle M) {d : D} {j : Fin C.len}
    (h : M.σ d = C.pDart j) :
    C.cutReach2 (Sum.inl d) (Sum.inl (C.dart (C.prevIdx j))) := by
  have hstep : (C.cutCapMap2).σ.SameCycle (Sum.inl d) (Sum.inr (Sum.inl (C.prevIdx j))) := by
    refine ⟨1, ?_⟩
    rw [zpow_one]
    show (C.cutCapMap2).σ (Sum.inl d) = Sum.inr (Sum.inl (C.prevIdx j))
    exact C.cutSigma2_plusEnd h
  exact (C.cutReach2_of_sigma hstep).trans (C.cutReach2_capP (C.prevIdx j))

/-- A `σ'₂`-step diverting at a `−`-bank-end `σ d = q_j` lands on `c_j^-`, which reaches
the `−`-bank dart `inl (α (dart j))`. -/
lemma cutReach2_sigma_divertMinus (C : SimplePrimalCycle M) {d : D} {j : Fin C.len}
    (h : M.σ d = C.qDart j) :
    C.cutReach2 (Sum.inl d) (Sum.inl (M.α (C.dart j))) := by
  have hstep : (C.cutCapMap2).σ.SameCycle (Sum.inl d) (Sum.inr (Sum.inr j)) := by
    refine ⟨1, ?_⟩
    rw [zpow_one]
    show (C.cutCapMap2).σ (Sum.inl d) = Sum.inr (Sum.inr j)
    exact C.cutSigma2_minusEnd h
  exact (C.cutReach2_of_sigma hstep).trans (C.cutReach2_capM j)

/-! ## Side-coherence core for the corrected map -/

/-- **Side-coherence (the corrected isolated core).**  Every forward cycle bank
`inl (dart j)` reaches the forward bank of `e_i`, and every reverse cycle bank
`inl (α (dart j))` reaches the reverse bank of `e_i`. -/
def SidesReach2 (C : SimplePrimalCycle M) (i : Fin C.len) : Prop :=
  (∀ j : Fin C.len, C.cutReach2 (Sum.inl (C.dart j)) (Sum.inl (C.dart i))) ∧
    (∀ j : Fin C.len, C.cutReach2 (Sum.inl (M.α (C.dart j))) (Sum.inl (M.α (C.dart i))))

/-- Abbreviation: `x` reaches a bank of `e_i` (corrected map). -/
def ReachesBankI2 (C : SimplePrimalCycle M) (i : Fin C.len) (x : C.CutDart) : Prop :=
  C.cutReach2 x (Sum.inl (C.dart i)) ∨ C.cutReach2 x (Sum.inl (M.α (C.dart i)))

lemma reachesBankI2_dartI (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.ReachesBankI2 i (Sum.inl (C.dart i)) := Or.inl (C.cutReach2_rfl _)

/-- A single forward `σ`-step lifts to "reaches a bank of `e_i`" (corrected map). -/
lemma cutReach2_sigma_step_or_bank (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach2 i) (d : D) :
    C.cutReach2 (Sum.inl d) (Sum.inl (M.σ d)) ∨ C.ReachesBankI2 i (Sum.inl d) := by
  by_cases hp : ∃ j, M.σ d = C.pDart j
  · obtain ⟨j, hj⟩ := hp
    refine Or.inr (Or.inl ?_)
    exact (C.cutReach2_sigma_divertPlus hj).trans (hsides.1 (C.prevIdx j))
  · by_cases hq : ∃ j, M.σ d = C.qDart j
    · obtain ⟨j, hj⟩ := hq
      refine Or.inr (Or.inr ?_)
      exact (C.cutReach2_sigma_divertMinus hj).trans (hsides.2 j)
    · exact Or.inl (C.cutReach2_sigma_clean (fun j hj => hp ⟨j, hj⟩) (fun j hj => hq ⟨j, hj⟩))

/-- `σ`-power lift (corrected map). -/
lemma cutReach2_sigma_pow_or_bank (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach2 i) (d : D) :
    ∀ n : ℕ, C.cutReach2 (Sum.inl d) (Sum.inl ((M.σ ^ n) d)) ∨
      C.ReachesBankI2 i (Sum.inl d)
  | 0 => Or.inl (by simpa using C.cutReach2_rfl (Sum.inl d))
  | n + 1 => by
      rcases C.cutReach2_sigma_pow_or_bank i hsides d n with hreach | hbank
      · rcases C.cutReach2_sigma_step_or_bank i hsides ((M.σ ^ n) d) with hstep | hbank'
        · refine Or.inl ?_
          have : (M.σ ^ (n + 1)) d = M.σ ((M.σ ^ n) d) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          rw [this]
          exact hreach.trans hstep
        · rcases hbank' with h | h
          · exact Or.inr (Or.inl (hreach.trans h))
          · exact Or.inr (Or.inr (hreach.trans h))
      · exact Or.inr hbank

lemma cutReach2_sameCycle_or_bank (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach2 i) {d e : D} (h : M.σ.SameCycle d e) :
    C.cutReach2 (Sum.inl d) (Sum.inl e) ∨ C.ReachesBankI2 i (Sum.inl d) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rcases C.cutReach2_sigma_pow_or_bank i hsides d n with hreach | hbank
  · left; rwa [hn] at hreach
  · exact Or.inr hbank

/-- An `α`-step lifts (corrected map). -/
lemma cutReach2_alpha_step_or_bank (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach2 i) (d : D) :
    C.cutReach2 (Sum.inl d) (Sum.inl (M.α d)) ∨ C.ReachesBankI2 i (Sum.inl d) := by
  by_cases hd : d ∈ C.dartSet
  · rw [C.mem_dartSet_iff] at hd
    obtain ⟨j, hj | hj⟩ := hd
    · subst hj; exact Or.inr (Or.inl (hsides.1 j))
    · subst hj; exact Or.inr (Or.inr (hsides.2 j))
  · left
    have hα : (C.cutCapMap2).α (Sum.inl d) = Sum.inl (M.α d) := by
      rw [cutCapMap2_alpha_apply, C.cutAlpha_other hd]
    rw [← hα]
    exact C.cutReach2_of_alpha (Sum.inl d)

/-! ## Part A: every cut-dart of the corrected map reaches a bank of `e_i` -/

/-- **Backward closure of the bank-reach invariant** (corrected map). -/
lemma reachesBankI2_backward (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach2 i) {c c' : D} (hcc' : M.dartStep c c')
    (hc' : C.ReachesBankI2 i (Sum.inl c')) :
    C.ReachesBankI2 i (Sum.inl c) := by
  rcases hcc' with hσ | hα
  · rcases C.cutReach2_sameCycle_or_bank i hsides hσ with hreach | hbank
    · rcases hc' with h | h
      · exact Or.inl (hreach.trans h)
      · exact Or.inr (hreach.trans h)
    · exact hbank
  · subst hα
    rcases C.cutReach2_alpha_step_or_bank i hsides c with hreach | hbank
    · rcases hc' with h | h
      · exact Or.inl (hreach.trans h)
      · exact Or.inr (hreach.trans h)
    · exact hbank

/-- Every `inl`-dart reaches a bank of `e_i` (corrected map). -/
lemma inl_reachesBankI2 (C : SimplePrimalCycle M) (i : Fin C.len)
    (hconn : M.Connected) (hsides : C.SidesReach2 i) (c : D) :
    C.ReachesBankI2 i (Sum.inl c) := by
  have hwalk : Relation.ReflTransGen M.dartStep c (C.dart i) := hconn c (C.dart i)
  refine Relation.ReflTransGen.head_induction_on hwalk (C.reachesBankI2_dartI i) ?_
  intro a b hab _ ih
  exact C.reachesBankI2_backward i hsides hab ih

/-- **Part A predicate (corrected map).**  Every cut-dart reaches a bank of `e_i`. -/
def ReachesBank2 (C : SimplePrimalCycle M) (i : Fin C.len) : Prop :=
  ∀ x : C.CutDart,
    C.cutReach2 x (Sum.inl (C.dart i)) ∨ C.cutReach2 x (Sum.inl (M.α (C.dart i)))

/-- **Part A (`ReachesBank2`).**  Every cut-dart reaches a bank of `e_i`, given
`M.Connected` and the side-coherence core. -/
theorem reachesBank2_of_connected (C : SimplePrimalCycle M) (i : Fin C.len)
    (hconn : M.Connected) (hsides : C.SidesReach2 i) :
    C.ReachesBank2 i := by
  intro x
  rcases x with d | (j | j)
  · exact C.inl_reachesBankI2 i hconn hsides d
  · rcases C.inl_reachesBankI2 i hconn hsides (C.dart j) with h | h
    · exact Or.inl ((C.cutReach2_capP j).trans h)
    · exact Or.inr ((C.cutReach2_capP j).trans h)
  · rcases C.inl_reachesBankI2 i hconn hsides (M.α (C.dart j)) with h | h
    · exact Or.inl ((C.cutReach2_capM j).trans h)
    · exact Or.inr ((C.cutReach2_capM j).trans h)

/-- **The connectivity reduction (corrected map).**  Part A + the bridge ⇒ connected. -/
theorem cutCapMap2_connected_of_reachesBank_of_bridge (C : SimplePrimalCycle M)
    (i : Fin C.len)
    (hbank : C.ReachesBank2 i)
    (hbridge : C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i)))) :
    (C.cutCapMap2).Connected := by
  have hreach_r : ∀ x : C.CutDart, C.cutReach2 x (Sum.inl (C.dart i)) := by
    intro x
    rcases hbank x with h | h
    · exact h
    · exact h.trans (C.cutReach2_symm hbridge)
  intro a b
  exact (hreach_r a).trans (C.cutReach2_symm (hreach_r b))

/-! ## Layer 1: the fragment formalism and the bridge

We follow `CH35_BRIDGE_DESIGN.md` §1–§4.  The *old face* of a dart is `M.dartFace d`
(`= faceOf d` in the design).  The **surviving face step** is the old-face adjacency
that survives the cut as a `φ'₂`-adjacency: -/

/-- `SurvivingFaceStep f d e`: `d` and `e` lie in old face `f`, and the cut map joins
`inl d` to `inl e` by a single `φ'₂`-step (in either direction).  This is the design's
`SurvivingFaceStep` (the *only* safe intra-face adjacency: an actual `φ'₂`-edge, never
the false same-old-face relay). -/
def SurvivingFaceStep (C : SimplePrimalCycle M) (f : M.Face) (d e : D) : Prop :=
  M.dartFace d = f ∧ M.dartFace e = f ∧
    ((C.cutCapMap2).φ (Sum.inl d) = Sum.inl e ∨ (C.cutCapMap2).φ (Sum.inl e) = Sum.inl d)

/-- `SameFragment f d e`: `d` and `e` are in the same face-fragment of old face `f`
(the reflexive-transitive closure of `SurvivingFaceStep f`).  This is the design's
`SameFragment`; a *fragment* is one of its equivalence classes inside `f`. -/
def SameFragment (C : SimplePrimalCycle M) (f : M.Face) (d e : D) : Prop :=
  Relation.ReflTransGen (C.SurvivingFaceStep f) d e

@[refl] lemma sameFragment_rfl (C : SimplePrimalCycle M) (f : M.Face) (d : D) :
    C.SameFragment f d d := Relation.ReflTransGen.refl

lemma sameFragment_trans (C : SimplePrimalCycle M) {f : M.Face} {d e g : D}
    (h₁ : C.SameFragment f d e) (h₂ : C.SameFragment f e g) :
    C.SameFragment f d g := Relation.ReflTransGen.trans h₁ h₂

/-- `SurvivingFaceStep f` is symmetric (it is the symmetric `φ'₂`-adjacency inside `f`). -/
lemma survivingFaceStep_symm (C : SimplePrimalCycle M) {f : M.Face} {d e : D}
    (h : C.SurvivingFaceStep f d e) : C.SurvivingFaceStep f e d :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

/-- `SameFragment f` is symmetric. -/
lemma sameFragment_symm (C : SimplePrimalCycle M) {f : M.Face} {d e : D}
    (h : C.SameFragment f d e) : C.SameFragment f e d :=
  Relation.ReflTransGen.symmetric (fun _ _ hstep => C.survivingFaceStep_symm hstep) h

/-- **A surviving face step is a cut-reachability** (design §1.3
`cutConn_of_survivingFaceStep`).  A `φ'₂`-step is one `α'`-then-`σ'₂` move. -/
lemma cutReach2_of_survivingFaceStep (C : SimplePrimalCycle M) {f : M.Face} {d e : D}
    (h : C.SurvivingFaceStep f d e) :
    C.cutReach2 (Sum.inl d) (Sum.inl e) := by
  rcases h.2.2 with hde | hed
  · rw [← hde]; exact C.cutReach2_of_phi_step (Sum.inl d)
  · have hstep : C.cutReach2 (Sum.inl e) (Sum.inl d) := by
      rw [← hed]; exact C.cutReach2_of_phi_step (Sum.inl e)
    exact C.cutReach2_symm hstep

/-- **Same fragment ⇒ cut-connected** (design §1.3 `cutConn_of_sameFragment`).  The
*only* safe same-old-face connectivity statement: `same fragment ⇒ cut-connected`
(never `same old face ⇒ cut-connected`, which is false for a straddling face). -/
lemma cutReach2_of_sameFragment (C : SimplePrimalCycle M) {f : M.Face} {d e : D}
    (h : C.SameFragment f d e) :
    C.cutReach2 (Sum.inl d) (Sum.inl e) := by
  induction h with
  | refl => exact C.cutReach2_rfl _
  | tail _ hstep ih => exact ih.trans (C.cutReach2_of_survivingFaceStep hstep)

/-! ### Uncut dual gates (design §3.1) -/

/-- **`α'` across an uncut gate** (design §3.1 `alpha'_old_of_not_cycle`): if `a`'s
`Sym2`-edge is not a cycle edge, then `α' (inl a) = inl (α a)`. -/
lemma cutAlpha2_old_of_not_cycle (C : SimplePrimalCycle M) {a : D}
    (h : M.dartEdge a ∉ C.edgeSet) :
    (C.cutCapMap2).α (Sum.inl a) = Sum.inl (M.α a) := by
  rw [cutCapMap2_alpha_apply, C.cutAlpha_other (C.notMem_dartSet_of_dartEdge_notMem h)]

/-- **Cut-reach across an uncut dual gate** (design §3.1
`cutConn_across_uncut_dual_gate`): one `α'`-step joins the two faces' `inl`-darts. -/
lemma cutReach2_across_uncut_dual_gate (C : SimplePrimalCycle M) {a : D}
    (h : M.dartEdge a ∉ C.edgeSet) :
    C.cutReach2 (Sum.inl a) (Sum.inl (M.α a)) :=
  C.cutReach2_uncut_bridge h

/-! ### The fragment-level dual path (design §3.2–§3.3)

A `FragmentDualPath2` carries, at each position `j : Fin (n+1)`, an old face `face j`
together with a *fragment representative* `rep j` of that face, and, at each crossing
`j : Fin n`, an uncut edge dart `edge j`.  The **no-teleport** rule is encoded by the
two `SameFragment` fields: the dart used to *leave* a face and the dart used to *enter*
it must lie in the **same fragment** (the design's `left_mem`/`right_mem`, here phrased
relative to the representative). -/

/-- A **fragment-level dual path** with `n` uncut crossings (design §3.2).  Carries a
fragment representative at each position and the no-teleport `SameFragment` data. -/
structure FragmentDualPath2 (C : SimplePrimalCycle M) where
  /-- Number of uncut crossings. -/
  n : ℕ
  /-- The old face at each position. -/
  face : Fin (n + 1) → M.Face
  /-- A representative dart of the fragment at each position. -/
  rep : Fin (n + 1) → D
  /-- The representative lies in its old face. -/
  rep_face : ∀ j, M.dartFace (rep j) = face j
  /-- The uncut crossing dart at each step. -/
  edge : Fin n → D
  /-- Each crossing dart is across an uncut edge (not a cycle edge). -/
  edge_uncut : ∀ j, M.dartEdge (edge j) ∉ C.edgeSet
  /-- The crossing dart leaves the left face, in the left fragment. -/
  left_face : ∀ j : Fin n, M.dartFace (edge j) = face j.castSucc
  /-- The crossing dart enters the right face, in the right fragment. -/
  right_face : ∀ j : Fin n, M.dartFace (M.α (edge j)) = face j.succ
  /-- **No teleport (exit side):** the dart used to leave `face j` lies in the same
  fragment as the representative `rep j`. -/
  exit_sameFrag : ∀ j : Fin n, C.SameFragment (face j.castSucc) (rep j.castSucc) (edge j)
  /-- **No teleport (entry side):** the dart used to enter `face (j+1)` lies in the
  same fragment as the representative `rep (j+1)`. -/
  entry_sameFrag : ∀ j : Fin n, C.SameFragment (face j.succ) (rep j.succ) (M.α (edge j))

/-- **Consecutive representatives along the path are cut-connected** (design §4
`fragCutConn_step_across_uncut_edge`).  Leaving fragment `rep j` to its boundary
`edge j` (same fragment), crossing the uncut edge by `α'`, then walking from the entry
dart `α (edge j)` to `rep (j+1)` (same fragment). -/
lemma fragmentDualPath2_step (C : SimplePrimalCycle M) (P : C.FragmentDualPath2)
    (j : Fin P.n) :
    C.cutReach2 (Sum.inl (P.rep j.castSucc)) (Sum.inl (P.rep j.succ)) := by
  have h1 : C.cutReach2 (Sum.inl (P.rep j.castSucc)) (Sum.inl (P.edge j)) :=
    C.cutReach2_of_sameFragment (P.exit_sameFrag j)
  have h2 : C.cutReach2 (Sum.inl (P.edge j)) (Sum.inl (M.α (P.edge j))) :=
    C.cutReach2_across_uncut_dual_gate (P.edge_uncut j)
  have h3 : C.cutReach2 (Sum.inl (M.α (P.edge j))) (Sum.inl (P.rep j.succ)) :=
    C.cutReach2_symm (C.cutReach2_of_sameFragment (P.entry_sameFrag j))
  exact (h1.trans h2).trans h3

/-- **All representatives along the path are cut-connected** (design §4
`all_path_fragments_cut_connected`).  Induction on the position. -/
lemma fragmentDualPath2_rep_connected (C : SimplePrimalCycle M) (P : C.FragmentDualPath2)
    (j : Fin (P.n + 1)) :
    C.cutReach2 (Sum.inl (P.rep 0)) (Sum.inl (P.rep j)) := by
  obtain ⟨jv, hjv⟩ := j
  induction jv with
  | zero => exact C.cutReach2_rfl _
  | succ m ih =>
      have hm1 : m < P.n + 1 := Nat.lt_of_succ_lt hjv
      have hmn : m < P.n := Nat.lt_of_succ_lt_succ hjv
      have ihm := ih hm1
      have hstep := C.fragmentDualPath2_step P ⟨m, hmn⟩
      have hcast : (⟨m, hmn⟩ : Fin P.n).castSucc = (⟨m, hm1⟩ : Fin (P.n + 1)) := by
        apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE]
      have hsucc : (⟨m, hmn⟩ : Fin P.n).succ = (⟨m + 1, hjv⟩ : Fin (P.n + 1)) := by
        apply Fin.ext; simp [Fin.succ]
      rw [hcast] at hstep
      rw [hsucc] at hstep
      exact ihm.trans hstep

/-! ### The cycle-side endpoint version and Layer 1 bridge (design §3.3, §4) -/

/-- A **fragment-level dual path between the two sides of cycle edge `e_i`** (design
§3.3 `FragmentDualPathBetweenCycleSides`).  Adds the endpoint data: the start
representative is in the fragment of the forward cycle dart `dart i`, and the end
representative is in the fragment of the reverse cycle dart `α (dart i)`. -/
structure FragmentDualPath2BetweenCycleSides (C : SimplePrimalCycle M) (i : Fin C.len)
    extends C.FragmentDualPath2 where
  /-- The start representative shares a fragment with the forward cycle dart `dart i`. -/
  start_sameFrag : C.SameFragment (face 0) (C.dart i) (rep 0)
  /-- The start face is the forward cycle dart's face. -/
  start_face : face 0 = M.dartFace (C.dart i)
  /-- The end representative shares a fragment with the reverse cycle dart `α dart i`. -/
  end_sameFrag :
    C.SameFragment (face (Fin.last n)) (M.α (C.dart i)) (rep (Fin.last n))
  /-- The end face is the reverse cycle dart's face. -/
  end_face : face (Fin.last n) = M.dartFace (M.α (C.dart i))

/-- **Layer 1 — the bridge** (design §4
`banks_connected_of_fragment_dual_path_between_cycle_faces`).  A fragment-level dual
path between the two sides of `e_i` forces the two banks `inl (dart i)`,
`inl (α (dart i))` to be cut-reachable.

Proof: the forward cycle dart shares a fragment with `rep 0` (start), so reaches it;
the path connects `rep 0` to `rep (last n)`; the last representative shares a fragment
with the reverse cycle dart (end).  Chain. -/
theorem banks_connected2_of_fragment_dual_path (C : SimplePrimalCycle M) {i : Fin C.len}
    (P : C.FragmentDualPath2BetweenCycleSides i) :
    C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i))) := by
  have hstart : C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (P.rep 0)) :=
    C.cutReach2_of_sameFragment P.start_sameFrag
  have hpath : C.cutReach2 (Sum.inl (P.rep 0)) (Sum.inl (P.rep (Fin.last P.n))) :=
    C.fragmentDualPath2_rep_connected P.toFragmentDualPath2 (Fin.last P.n)
  have hend : C.cutReach2 (Sum.inl (P.rep (Fin.last P.n))) (Sum.inl (M.α (C.dart i))) :=
    C.cutReach2_symm (C.cutReach2_of_sameFragment P.end_sameFrag)
  exact (hstart.trans hpath).trans hend

/-! ## The combined connectivity theorem (discharges the `hconn` parameter)

Given a fragment-level dual path between the two sides of `e_i` (Layer 1 bridge) and
the side-coherence core driving Part A, the corrected cut map is connected. -/

/-- **The corrected cut map is connected** from a fragment-level dual path (Layer 1)
plus the Part-A core.  This is the corrected-map analogue of
`cutCapMap_connected_of_dualPathSeparation`. -/
theorem cutCapMap2_connected_of_fragment_dual_path (C : SimplePrimalCycle M)
    {i : Fin C.len} (hconn : M.Connected) (hsides : C.SidesReach2 i)
    (P : C.FragmentDualPath2BetweenCycleSides i) :
    (C.cutCapMap2).Connected :=
  C.cutCapMap2_connected_of_reachesBank_of_bridge i
    (C.reachesBank2_of_connected i hconn hsides)
    (C.banks_connected2_of_fragment_dual_path P)

/-! ## Layer 2: refining an ordinary dual path (design §7, Option C)

The repo's `DualReachableAvoidingCycle` is a *bare* face sequence (`ReflTransGen
(DualAvoidsCycleStep)`): exactly the design's "too weak" object that can teleport
across a straddling face.  Per design §7 the honest refinement keeps an **ordinary
dual path carrying explicit crossing darts** together with a separate **fragment
compatibility predicate** (the no-teleport data), and lifts the pair to a
`FragmentDualPath2BetweenCycleSides`.

This is the place where "consecutive gates through the same old face lie in the same
face-fragment" is *required as input*, never derived from the bare face sequence — the
design's central correction. -/

/-- An **ordinary dual path** with explicit crossing darts (design §7 Option C
`OrdinaryDualPath`).  A bare face sequence augmented with the witnessing darts. -/
structure OrdinaryDualPath2 (C : SimplePrimalCycle M) where
  /-- Number of crossings. -/
  n : ℕ
  /-- The old face at each position. -/
  face : Fin (n + 1) → M.Face
  /-- The uncut crossing dart at each step. -/
  edge : Fin n → D
  /-- Each crossing dart is across an uncut (non-cycle) edge. -/
  edge_uncut : ∀ j, M.dartEdge (edge j) ∉ C.edgeSet
  /-- The crossing dart leaves the left face. -/
  left_face : ∀ j : Fin n, M.dartFace (edge j) = face j.castSucc
  /-- The crossing dart enters the right face. -/
  right_face : ∀ j : Fin n, M.dartFace (M.α (edge j)) = face j.succ

/-- **Fragment compatibility (the no-teleport data)** for an ordinary dual path between
the two sides of `e_i` (design §7 Option C `FragmentCompatible`, with endpoint
handling).  Carries, for each intermediate face, a `SameFragment` witness that the
entry dart and the exit dart of that face are in the same fragment; plus the two
endpoint witnesses (forward cycle dart ↔ first exit; last entry ↔ reverse cycle dart).

For `n = 0` the only requirement is the single endpoint witness binding the forward
and reverse cycle darts in one fragment of the start face. -/
structure FragmentCompatible2 (C : SimplePrimalCycle M) (i : Fin C.len)
    (P : C.OrdinaryDualPath2) : Prop where
  /-- Start face is the forward cycle dart's face. -/
  start_face : P.face 0 = M.dartFace (C.dart i)
  /-- End face is the reverse cycle dart's face. -/
  end_face : P.face (Fin.last P.n) = M.dartFace (M.α (C.dart i))
  /-- **Start endpoint:** the forward cycle dart and the first-exit dart are in the
  same fragment of the start face (for `n = 0` the "first-exit dart" is taken as the
  reverse cycle dart `α (dart i)` via `end_link`). -/
  start_link : ∀ h : 0 < P.n,
    C.SameFragment (P.face 0) (C.dart i) (P.edge ⟨0, h⟩)
  /-- **Intermediate faces:** entry dart `α (edge (j))` and exit dart `edge (j+1)` of
  the face at position `j+1` are in the same fragment. -/
  mid_link : ∀ j : Fin P.n, ∀ hj : (j : ℕ) + 1 < P.n,
    C.SameFragment (P.face j.succ) (M.α (P.edge j)) (P.edge ⟨(j : ℕ) + 1, hj⟩)
  /-- **End endpoint:** the last-entry dart and the reverse cycle dart are in the same
  fragment of the end face (for `n = 0` this directly binds the two cycle darts). -/
  end_link :
    C.SameFragment (P.face (Fin.last P.n))
      (if h : 0 < P.n then M.α (P.edge ⟨P.n - 1, by omega⟩) else C.dart i)
      (M.α (C.dart i))

/-- **Layer 2 refinement** (design §7 `fragment_dual_path_of_interior_dual_path…`):
an ordinary dual path plus fragment-compatibility data refines to a
`FragmentDualPath2BetweenCycleSides`.  The fragment representative at each position is
taken to be the **entry dart** (or the forward cycle dart at the start); the
compatibility witnesses supply the `exit`/`entry` `SameFragment` fields.

We choose `rep 0 := dart i`, `rep (j+1) := α (edge j)` (the entry dart of position
`j+1`).  Then `exit_sameFrag` at step `j` is exactly the start/mid link, and
`entry_sameFrag` at step `j` is `SameFragment (α (edge j)) (α (edge j)) …` which is
reflexive. -/
noncomputable def fragmentDualPath2_of_ordinary (C : SimplePrimalCycle M) (i : Fin C.len)
    (P : C.OrdinaryDualPath2) (hcompat : C.FragmentCompatible2 i P) :
    C.FragmentDualPath2BetweenCycleSides i where
  n := P.n
  face := P.face
  rep := fun j => if h : (j : ℕ) = 0 then C.dart i else M.α (P.edge ⟨(j : ℕ) - 1, by omega⟩)
  rep_face := by
    intro j
    by_cases h : (j : ℕ) = 0
    · simp only [h, dif_pos]
      have : j = 0 := Fin.ext h
      rw [this, hcompat.start_face]
    · simp only [h]
      have hj1 : (j : ℕ) - 1 < P.n := by omega
      have hjeq : (⟨(j : ℕ) - 1, hj1⟩ : Fin P.n).succ = j := by
        apply Fin.ext; simp only [Fin.succ]; omega
      have := P.right_face ⟨(j : ℕ) - 1, hj1⟩
      rw [hjeq] at this
      exact this
  edge := P.edge
  edge_uncut := P.edge_uncut
  left_face := P.left_face
  right_face := P.right_face
  exit_sameFrag := by
    intro j
    -- rep (j.castSucc) is `dart i` if j = 0, else `α (edge (j-1))`; must reach `edge j`.
    by_cases h0 : (j : ℕ) = 0
    · -- start: rep 0 = dart i, edge 0 = edge j; use start_link
      have hcast0 : ((j.castSucc : Fin (P.n + 1)) : ℕ) = 0 := by
        simp only [Fin.val_castSucc]; exact h0
      simp only [hcast0, dif_pos]
      have hjpos : 0 < P.n := by have := j.isLt; omega
      have hje : (⟨0, hjpos⟩ : Fin P.n) = j := Fin.ext h0.symm
      have hfeq : P.face j.castSucc = P.face 0 := by
        congr 1; apply Fin.ext; simp [Fin.val_castSucc, h0]
      rw [hfeq, ← hje]
      exact hcompat.start_link hjpos
    · -- mid: rep (j.castSucc) = α (edge (j-1)); use mid_link
      have hcast : ((j.castSucc : Fin (P.n + 1)) : ℕ) = (j : ℕ) := by
        simp only [Fin.val_castSucc]
      simp only [hcast, h0]
      have hj1 : (j : ℕ) - 1 < P.n := by omega
      have hsucceq : (⟨(j : ℕ) - 1, hj1⟩ : Fin P.n).succ = j.castSucc := by
        apply Fin.ext; simp only [Fin.succ, Fin.val_castSucc]; omega
      have hlink := hcompat.mid_link ⟨(j : ℕ) - 1, hj1⟩ (by simp only []; omega)
      have hedgeeq : (⟨((⟨(j : ℕ) - 1, hj1⟩ : Fin P.n) : ℕ) + 1,
          (by simp only []; omega)⟩ : Fin P.n) = j := by
        apply Fin.ext; simp only []; omega
      rw [hsucceq] at hlink
      rw [hedgeeq] at hlink
      exact hlink
  entry_sameFrag := by
    intro j
    -- rep (j.succ) = α (edge j) (since (j.succ : ℕ) = j+1 ≠ 0); entry dart = α (edge j).
    have hrep : (if h : ((j.succ : Fin (P.n + 1)) : ℕ) = 0 then C.dart i
        else M.α (P.edge ⟨((j.succ : Fin (P.n + 1)) : ℕ) - 1, by omega⟩))
        = M.α (P.edge j) := by
      have hne : ((j.succ : Fin (P.n + 1)) : ℕ) ≠ 0 := by simp [Fin.val_succ]
      rw [dif_neg hne]
      congr 1
    show C.SameFragment (P.face j.succ)
      (if h : ((j.succ : Fin (P.n + 1)) : ℕ) = 0 then C.dart i
        else M.α (P.edge ⟨((j.succ : Fin (P.n + 1)) : ℕ) - 1, by omega⟩))
      (M.α (P.edge j))
    rw [hrep]
  start_sameFrag := by
    show C.SameFragment (P.face 0)
      (C.dart i)
      (if h : ((0 : Fin (P.n + 1)) : ℕ) = 0 then C.dart i
        else M.α (P.edge ⟨((0 : Fin (P.n + 1)) : ℕ) - 1, by omega⟩))
    rw [dif_pos (by rfl)]
  start_face := hcompat.start_face
  end_sameFrag := by
    by_cases h0 : 0 < P.n
    · -- rep (last n) = α (edge ⟨n-1⟩); end_link (with dif_pos) binds it to α (dart i)
      have hrep : (if h : ((Fin.last P.n : Fin (P.n + 1)) : ℕ) = 0 then C.dart i
          else M.α (P.edge ⟨((Fin.last P.n : Fin (P.n + 1)) : ℕ) - 1, by omega⟩))
          = M.α (P.edge ⟨P.n - 1, by omega⟩) := by
        have hne : ((Fin.last P.n : Fin (P.n + 1)) : ℕ) ≠ 0 := by simp [Fin.last]; omega
        rw [dif_neg hne]
        congr 1
      show C.SameFragment (P.face (Fin.last P.n)) (M.α (C.dart i))
        (if h : ((Fin.last P.n : Fin (P.n + 1)) : ℕ) = 0 then C.dart i
          else M.α (P.edge ⟨((Fin.last P.n : Fin (P.n + 1)) : ℕ) - 1, by omega⟩))
      rw [hrep]
      have hend := hcompat.end_link
      rw [dif_pos h0] at hend
      exact C.sameFragment_symm hend
    · -- n = 0: rep (last 0) = dart i; end_link (dif_neg) binds dart i ↔ α dart i
      have hn0 : P.n = 0 := by omega
      have hrep : (if h : ((Fin.last P.n : Fin (P.n + 1)) : ℕ) = 0 then C.dart i
          else M.α (P.edge ⟨((Fin.last P.n : Fin (P.n + 1)) : ℕ) - 1, by omega⟩))
          = C.dart i := by
        rw [dif_pos (by simp [Fin.last, hn0])]
      show C.SameFragment (P.face (Fin.last P.n)) (M.α (C.dart i))
        (if h : ((Fin.last P.n : Fin (P.n + 1)) : ℕ) = 0 then C.dart i
          else M.α (P.edge ⟨((Fin.last P.n : Fin (P.n + 1)) : ℕ) - 1, by omega⟩))
      rw [hrep]
      have hend := hcompat.end_link
      rw [dif_neg h0] at hend
      exact C.sameFragment_symm hend
  end_face := hcompat.end_face

/-- **Layer 2 + Layer 1 combined.**  An ordinary dual path with fragment compatibility
yields the bridge directly. -/
theorem banks_connected2_of_ordinary_dual_path (C : SimplePrimalCycle M) (i : Fin C.len)
    (P : C.OrdinaryDualPath2) (hcompat : C.FragmentCompatible2 i P) :
    C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i))) :=
  C.banks_connected2_of_fragment_dual_path
    (C.fragmentDualPath2_of_ordinary i P hcompat)

/-- **The corrected cut map is connected** from an ordinary dual path with fragment
compatibility (Layer 2) plus the Part-A core. -/
theorem cutCapMap2_connected_of_ordinary_dual_path (C : SimplePrimalCycle M)
    (i : Fin C.len) (hconn : M.Connected) (hsides : C.SidesReach2 i)
    (P : C.OrdinaryDualPath2) (hcompat : C.FragmentCompatible2 i P) :
    (C.cutCapMap2).Connected :=
  C.cutCapMap2_connected_of_reachesBank_of_bridge i
    (C.reachesBank2_of_connected i hconn hsides)
    (C.banks_connected2_of_ordinary_dual_path i P hcompat)

/-! ## Discharging the `hconn` parameter of `jordan_simple_cycle2_walk`

`jordan_simple_cycle2_walk` takes the connectivity parameter

```
hconn : ∀ i, DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
              (C.cutCapMap2).Connected
```

Per the bridge design, the bare `DualReachableAvoidingCycle` face sequence is too weak
to lift on its own (a straddling face teleports it); the honest input is a **fragment
witness** — for each cycle edge whose two faces are dual-reachable, a fragment-level
dual path between its sides and the Part-A side-coherence core.  We package this as
`CutBridgeWitness2` and discharge `hconn` from it. -/

/-- **The corrected per-edge bridge witness.**  For the cut at `e_i`: the Part-A
side-coherence core, together with a *fragment-level* dual path between the two cycle
sides whenever the two faces are dual-reachable.  This is the honest input to the
connectivity parameter (the fragment data is the no-teleport content the bare dual
path lacks). -/
structure CutBridgeWitness2 (C : SimplePrimalCycle M) (i : Fin C.len) : Prop where
  /-- Part-A side coherence. -/
  sidesReach : C.SidesReach2 i
  /-- A fragment-level dual path between the two sides of `e_i`, from any cycle-avoiding
  dual path between its faces. -/
  fragPath : DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
    Nonempty (C.FragmentDualPath2BetweenCycleSides i)

/-- **Discharge of the connectivity parameter** of `jordan_simple_cycle2_walk` from
`M.Connected` and the per-edge fragment bridge witnesses. -/
theorem cutCapMap2_connected_of_bridgeWitness (C : SimplePrimalCycle M)
    (hconn : M.Connected)
    (hwit : ∀ i : Fin C.len, C.CutBridgeWitness2 i) :
    ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected := by
  intro i hpath
  obtain ⟨P⟩ := (hwit i).fragPath hpath
  exact C.cutCapMap2_connected_of_fragment_dual_path hconn (hwit i).sidesReach P

/-! ## The final Jordan / chord-separation theorem (conditional on `NumCyclesCutPhi2`)

We feed the discharged connectivity into `jordan_simple_cycle2_walk`.  The only
remaining counting fact is the named open core `NumCyclesCutPhi2` (the per-chain
`−(k−1)` count, ground in parallel); the Euler hypotheses are the standard sphere
inputs.  This is the corrected Chapter-35 Jordan lemma, closed modulo exactly the one
face-count core. -/

/-- **The corrected Jordan lemma**, with the connectivity parameter discharged by the
fragment bridge.  Conditional only on the named face core `NumCyclesCutPhi2`, the
per-edge fragment bridge witnesses, `M.Connected`, the Euler hypothesis `hchi`, and the
sanctioned Euler inequality `chi_le`. -/
theorem jordan_simple_cycle2_bridge (C : SimplePrimalCycle M)
    (hcore : C.NumCyclesCutPhi2)
    (hconn : M.Connected)
    (hwit : ∀ i : Fin C.len, C.CutBridgeWitness2 i)
    (hchi : M.eulerChar = 2)
    (chi_le : (C.cutCapMap2).Connected → (C.cutCapMap2).eulerChar ≤ 2)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2_walk hcore
    (C.cutCapMap2_connected_of_bridgeWitness hconn hwit) hchi chi_le i

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap
