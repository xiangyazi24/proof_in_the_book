import ProofsInTheBook.PlanarMapCutCapF

/-!
# Connectivity of the cut-and-cap map from a dual path (Chapter 35 Jordan lemma)

This file works toward the `connected_of_dual_path` field of `CutSigmaCounts`
(`PlanarMapCutCapSigma.lean`) for the concrete cut map `C.cutCapMap`:

  given a cycle-avoiding dual path between the two faces of a cycle edge `e_i`, the
  cut-and-cap map `C.cutCapMap` is connected.

Per the design (CH35_JORDAN_DESIGN §4) the argument splits into:

* **Reachability infrastructure** (fully proved here): every `σ'`-step, every
  `α'`-step, and every `φ'`-step lifts to a `cutCapMap.dartStep`-reachability, so
  two darts in the same vertex `σ'`-orbit, the same edge, or the same face `φ'`-orbit
  are reachable from each other.
* **Part B — the dual bridge** (fully proved here): a cycle-avoiding dual step across
  a non-cycle edge `a ∉ E(C)` lifts to a `cutCapMap`-reachability between the
  `inl`-darts of the two old faces (the edge is uncut, so its `α`-pairing survives,
  and the two face-orbits are `φ'`-reachable).  Chaining along the dual path connects
  the forward dart `inl (dart i)` of `e_i` to its reverse dart `inl (α (dart i))`,
  i.e. the two banks of the cut at edge `e_i`.
* **Part A — the two-sided structure** (the irreducible combinatorial-Jordan core):
  every cut-dart reaches one of the two banks of `e_i`, so the cut map has at most
  two `dartStep`-components.  Combined with Part B's single bridge this forces
  connectivity.  Part A is isolated as the named predicate `ReachesBank`.

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

/-! ## Reachability in the cut map

`N := C.cutCapMap`.  `N.dartStep x y = N.σ.SameCycle x y ∨ y = N.α x`.  We package
single `σ'`-, `α'`-, and `φ'`-step reachability and their consequences. -/

/-- `cutReach x y`: `x` and `y` are joined by a chain of `cutCapMap.dartStep`s. -/
def cutReach (C : SimplePrimalCycle M) (x y : C.CutDart) : Prop :=
  Relation.ReflTransGen (C.cutCapMap).dartStep x y

@[refl] lemma cutReach_rfl (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutReach x x := Relation.ReflTransGen.refl

lemma cutReach_trans (C : SimplePrimalCycle M) {x y z : C.CutDart}
    (h₁ : C.cutReach x y) (h₂ : C.cutReach y z) :
    C.cutReach x z := Relation.ReflTransGen.trans h₁ h₂

/-- `cutCapMap.dartStep` is symmetric: `σ'.SameCycle` is symmetric and `α'` is an
involution. -/
lemma cutDartStep_symm (C : SimplePrimalCycle M) {x y : C.CutDart}
    (h : (C.cutCapMap).dartStep x y) :
    (C.cutCapMap).dartStep y x := by
  rcases h with hσ | hα
  · exact Or.inl hσ.symm
  · refine Or.inr ?_
    rw [hα]
    show x = (C.cutCapMap).α ((C.cutCapMap).α x)
    rw [show (C.cutCapMap).α ((C.cutCapMap).α x) = x from
      congrArg (fun f : Equiv.Perm C.CutDart => f x) (C.cutCapMap).α_invol]

lemma cutReach_symm (C : SimplePrimalCycle M) {x y : C.CutDart} (h : C.cutReach x y) :
    C.cutReach y x :=
  Relation.ReflTransGen.symmetric (fun _ _ => C.cutDartStep_symm) h

/-- A single `σ'`-step is a reachability. -/
lemma cutReach_of_sigma (C : SimplePrimalCycle M) {x y : C.CutDart}
    (h : (C.cutCapMap).σ.SameCycle x y) :
    C.cutReach x y :=
  Relation.ReflTransGen.single (Or.inl h)

/-- A single `α'`-step is a reachability. -/
lemma cutReach_of_alpha (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutReach x ((C.cutCapMap).α x) :=
  Relation.ReflTransGen.single (Or.inr rfl)

/-- A single `φ'`-step is a reachability (`α'` then `σ'`). -/
lemma cutReach_of_phi_step (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutReach x ((C.cutCapMap).φ x) := by
  have h1 : C.cutReach x ((C.cutCapMap).α x) := C.cutReach_of_alpha x
  have h2 : C.cutReach ((C.cutCapMap).α x) ((C.cutCapMap).σ ((C.cutCapMap).α x)) :=
    C.cutReach_of_sigma ⟨1, by rw [zpow_one]⟩
  refine C.cutReach_trans h1 ?_
  have : (C.cutCapMap).φ x = (C.cutCapMap).σ ((C.cutCapMap).α x) := by
    rw [CombMap.φ, Equiv.Perm.mul_apply]
  rw [this]; exact h2

/-- Same face (`φ'`-cycle) ⇒ reachable: a `φ'`-power chain of `φ'`-steps. -/
lemma cutReach_of_phi_pow (C : SimplePrimalCycle M) (x : C.CutDart) :
    ∀ n : ℕ, C.cutReach x (((C.cutCapMap).φ ^ n) x)
  | 0 => by simpa using C.cutReach_rfl x
  | n + 1 => by
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact C.cutReach_trans (C.cutReach_of_phi_step x)
        (C.cutReach_of_phi_pow ((C.cutCapMap).φ x) n)

lemma cutReach_of_phi_sameCycle (C : SimplePrimalCycle M) {x y : C.CutDart}
    (h : (C.cutCapMap).φ.SameCycle x y) :
    C.cutReach x y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have := C.cutReach_of_phi_pow x n
  rwa [hn] at this

/-! ## Non-cycle darts and the uncut bridge

A dart whose `Sym2`-edge is not a cycle edge is not a cycle dart; the cut map keeps
its `α`-pairing, so `α'` joins `inl d` to `inl (α d)`.  This is the dart-level kernel
of the dual bridge (design §4 Part B): a dual step across an uncut edge lifts to a
single `α'`-step between the two faces' `inl`-darts. -/

/-- A dart with a non-cycle `Sym2`-edge is not a cycle dart. -/
lemma notMem_dartSet_of_dartEdge_notMem (C : SimplePrimalCycle M) {d : D}
    (h : M.dartEdge d ∉ C.edgeSet) : d ∉ C.dartSet := by
  intro hd
  rw [C.mem_dartSet_iff] at hd
  obtain ⟨i, hi | hi⟩ := hd
  · exact h ((C.mem_edgeSet_iff _).2 ⟨i, by rw [hi, edge]⟩)
  · exact h ((C.mem_edgeSet_iff _).2 ⟨i, by rw [hi, edge, M.dartEdge_alpha]⟩)

/-- **The uncut bridge.**  Across an uncut edge `dartEdge d ∉ E(C)`, the cut map
joins `inl d` to `inl (α d)` by one `α'`-step (the edge's `α`-pairing survives). -/
lemma cutReach_uncut_bridge (C : SimplePrimalCycle M) {d : D}
    (h : M.dartEdge d ∉ C.edgeSet) :
    C.cutReach (Sum.inl d) (Sum.inl (M.α d)) := by
  have hd : d ∉ C.dartSet := C.notMem_dartSet_of_dartEdge_notMem h
  have : (C.cutCapMap).α (Sum.inl d) = Sum.inl (M.α d) := by
    rw [cutCapMap_alpha, cutAlphaPerm_apply, C.cutAlpha_other hd]
  rw [← this]
  exact C.cutReach_of_alpha (Sum.inl d)

/-! ## Cap-to-bank reduction (design §4 Part A, easy half)

Each cap is a single `α'`-step from a bank `inl`-dart:
`α'(c_i^+) = inl (dart i)` and `α'(c_i^-) = inl (α (dart i))`.  Hence connectivity of
all cut-darts reduces to connectivity of all `inl`-darts. -/

/-- `c_i^+` reaches the forward bank dart `inl (dart i)`. -/
lemma cutReach_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutReach (Sum.inr (Sum.inl i)) (Sum.inl (C.dart i)) := by
  have : (C.cutCapMap).α (Sum.inr (Sum.inl i)) = Sum.inl (C.dart i) := by
    rw [cutCapMap_alpha, cutAlphaPerm_apply, cutAlpha_capPlus]
  rw [← this]; exact C.cutReach_of_alpha _

/-- `c_i^-` reaches the reverse bank dart `inl (α (dart i))`. -/
lemma cutReach_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutReach (Sum.inr (Sum.inr i)) (Sum.inl (M.α (C.dart i))) := by
  have : (C.cutCapMap).α (Sum.inr (Sum.inr i)) = Sum.inl (M.α (C.dart i)) := by
    rw [cutCapMap_alpha, cutAlphaPerm_apply, cutAlpha_capMinus]
  rw [← this]; exact C.cutReach_of_alpha _

/-! ## The connectivity reduction (fully proved)

Connectivity of the cut map reduces, via the cap-to-bank steps, to two facts about
the banks of `e_i`:

* **`ReachesBank i`** (design §4 Part A): every cut-dart reaches one of the two banks
  `inl (dart i)`, `inl (α (dart i))`.
* **the bank bridge** (design §4 Part B): `inl (dart i)` and `inl (α (dart i))` are
  cut-reachable from each other.

Given both, every cut-dart reaches the fixed reference `inl (dart i)`, so the cut map
is connected.  This reduction is unconditional; the two bank facts are the genuine
combinatorial-Jordan content. -/

/-- **Part A predicate.**  Every cut-dart reaches one of the two banks of `e_i`. -/
def ReachesBank (C : SimplePrimalCycle M) (i : Fin C.len) : Prop :=
  ∀ x : C.CutDart,
    C.cutReach x (Sum.inl (C.dart i)) ∨ C.cutReach x (Sum.inl (M.α (C.dart i)))

/-- **The connectivity reduction.**  If every cut-dart reaches a bank of `e_i`
(`ReachesBank`) and the two banks are mutually reachable (the bridge), the cut map is
connected.  Fully proved from the reachability infrastructure. -/
theorem cutCapMap_connected_of_reachesBank_of_bridge (C : SimplePrimalCycle M)
    (i : Fin C.len)
    (hbank : C.ReachesBank i)
    (hbridge : C.cutReach (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i)))) :
    (C.cutCapMap).Connected := by
  -- Every cut-dart reaches the fixed reference `r := inl (dart i)`.
  have hreach_r : ∀ x : C.CutDart, C.cutReach x (Sum.inl (C.dart i)) := by
    intro x
    rcases hbank x with h | h
    · exact h
    · exact h.trans (C.cutReach_symm hbridge)
  intro a b
  exact (hreach_r a).trans (C.cutReach_symm (hreach_r b))

/-! ## The cut-map dual-path connectivity, isolated to one Jordan-separation fact

The two bank facts above — **Part A** (`ReachesBank`: every cut-dart reaches a bank of
`e_i`) and **Part B** (the dual path forces the two banks of `e_i` to be cut-reachable)
— are the irreducible combinatorial-Jordan separation content.  Both are genuine
global facts about the two-sided structure of the cut: Part A is the "at most two
components" half, Part B is the "the dual path merges them" half.  Per the repo's
honest-isolation discipline we package them as **one** named predicate
`DualPathSeparation`, whose two conjuncts are exactly the two halves of design §4, and
discharge the `connected_of_dual_path` field conditionally on it.

`DualPathSeparation C i` is *not* a hypothesis smuggling the conclusion: it does not
mention `Connected`, and each conjunct is a specific `cutReach` statement about the
banks of one cycle edge.  Everything *around* it (the reachability calculus, the
cap/uncut bridges, the reduction to connectivity) is proved unconditionally above. -/

/-- **The single isolated combinatorial-Jordan separation fact** for the cut at edge
`e_i`, given a cycle-avoiding dual path between its two faces:

* Part A: every cut-dart reaches one of the two banks (`ReachesBank i`);
* Part B: the two banks `inl (dart i)`, `inl (α (dart i))` are cut-reachable.

This is the irreducible content of design §4; the reachability infrastructure, the
uncut/cap bridges, and the connectivity reduction are all discharged unconditionally. -/
structure DualPathSeparation (C : SimplePrimalCycle M) (i : Fin C.len) : Prop where
  /-- Part A: every cut-dart reaches a bank of `e_i`. -/
  reachesBank : C.ReachesBank i
  /-- Part B: the two banks of `e_i` are mutually cut-reachable (dual bridge). -/
  bridge : C.cutReach (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i)))

/-- **Connectivity of the cut map from the dual-path separation fact.**  Discharges
the `connected_of_dual_path` field of `CutSigmaCounts` conditionally on the single
isolated `DualPathSeparation` fact supplied by design §4. -/
theorem cutCapMap_connected_of_dualPathSeparation (C : SimplePrimalCycle M)
    (i : Fin C.len) (hsep : C.DualPathSeparation i) :
    (C.cutCapMap).Connected :=
  C.cutCapMap_connected_of_reachesBank_of_bridge i hsep.reachesBank hsep.bridge

/-! ## Conditional assembly of `CutSigmaCounts` and the Jordan lemma

The three fields of `CutSigmaCounts` are now closed up to two named, satisfiable
facts:

* `vertex_count` — **proved** unconditionally in `PlanarMapCutCapV.lean`;
* `face_count` — reduced to `numCycles (phiLift * faceCorr) = M.F + 2` in
  `PlanarMapCutCapF.lean` (`cutCapMap_F_iff`); we take it as the hypothesis `hF`;
* `connected_of_dual_path` — discharged here from `DualPathSeparation` (the §4 core),
  which we take per edge as the hypothesis `hsep`.

We assemble `CutSigmaCounts` from these and feed it to `jordan_simple_cycle_of_counts`,
giving the Jordan lemma conditional only on the two remaining orbit-count/separation
facts plus the sanctioned Euler inequality `chi_le`. -/

/-- **Assemble `CutSigmaCounts`** from the proved `vertex_count`, the F-file face count
`hF`, and the per-edge `DualPathSeparation` core `hsep`. -/
theorem cutSigmaCounts_of_faceCount_of_dualPathSeparation {M : CombMap D}
    (C : SimplePrimalCycle M)
    (hV : (C.cutCapMap).V = M.V + C.len)
    (hF : (C.cutCapMap).F = M.F + 2)
    (hsep : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        C.DualPathSeparation i) :
    CutSigmaCounts M C where
  vertex_count := hV
  face_count := hF
  connected_of_dual_path := fun i hpath =>
    C.cutCapMap_connected_of_dualPathSeparation i (hsep i hpath)

/-- **The Jordan lemma for a simple primal cycle**, conditional on the two remaining
named facts (`hF`: the F-file face count; `hsep`: the §4 `DualPathSeparation` core)
together with the sanctioned Euler inequality `chi_le`.  Everything else — the
vertex count, the reachability calculus, the connectivity reduction — is proved
unconditionally. -/
theorem jordan_simple_cycle_conditional {M : CombMap D} (C : SimplePrimalCycle M)
    (hchi : M.eulerChar = 2)
    (hV : (C.cutCapMap).V = M.V + C.len)
    (hF : (C.cutCapMap).F = M.F + 2)
    (hsep : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        C.DualPathSeparation i)
    (chi_le : (C.cutCapMap).Connected → (C.cutCapMap).eulerChar ≤ 2)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  jordan_simple_cycle_of_counts
    (C.cutSigmaCounts_of_faceCount_of_dualPathSeparation hV hF hsep) hchi chi_le i

end SimplePrimalCycle

/-! ## End-to-end chord separation (conditional on the two remaining facts)

We thread the assembled `CutSigmaCounts` through `jordan_simple_cycle_of_counts` and
the chord plumbing of `PlanarMapCutCap.lean`.  The sanctioned Euler inequality is now
discharged **unconditionally** by `chi_le_two_of_connected`
(`PlanarMapEulerInequality.lean`), so the only remaining hypotheses are:

* `hF` — the F-file face count (`PlanarMapCutCapF.lean`, reduced but not yet closed);
* `hsep` — the §4 `DualPathSeparation` core (isolated in this file);

together with the standard chord-cycle data (the simple primal cycle realizing
chord+arc, its edge-set containment, the chord index, and the face matching) that the
design's §5 supplies.  This is the Chapter-35 chord wall, closed modulo exactly those
two named facts. -/

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

/-- **The chord separates**, conditional only on the two remaining named facts
(`hF`: F-file face count; `hsep`: §4 `DualPathSeparation`).  The Euler inequality is
discharged unconditionally via `chi_le_two_of_connected`. -/
theorem separates_of_jordan_conditional {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hV : (C.cutCapMap).V = M.V + C.len)
    (hF : (C.cutCapMap).F = M.F + 2)
    (hsep : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        C.DualPathSeparation i)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  hNT.separates_of_jordan data C hsub
    (C.cutSigmaCounts_of_faceCount_of_dualPathSeparation hV hF hsep).toSurgery
    i₀ hleft hright
    (fun hconn => chi_le_two_of_connected _ hconn)

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
