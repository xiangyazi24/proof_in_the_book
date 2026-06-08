import ProofsInTheBook.ChordSeparation

/-!
# The `gateCompat` residue of `ChordJordanInput`: the recoverable triangle-`φ`-edge
  core, the literal-`GateFragmentCompatible` refutation, and the minimal residue
  (Chapter 35, Thomassen Five-Colour Theorem via combinatorial maps)

`ChordSeparation.lean` reduced `SphereChordSeparation` to the single bundle
`ChordJordanInput` whose genuine open field is

```
gateCompat : ∀ i, DualReachableAvoidingCycle M C (faceLeft i) (faceRight i) →
              ∃ P : OrdinaryDualPath2, GateFragmentCompatible i P
```

i.e. for each cycle edge, *from* a bare cycle-avoiding dual path, produce an ordinary
dual path whose every gate is a **single `φ'₂`-edge** of its (triangular) old face.

This file pushes the combinatorial structure HARD (the "M lesson": look for the
recoverable rotation-system contiguity before any "design-blocked" verdict), and
reports an HONEST split.

## What IS recoverable (the triangle lever, proved unconditionally)

**The genuine M-lesson recoverable core.**  In a near-triangulation every inner face
is a triangle, i.e. a `φ`-`3`-cycle (`M.φ³ d = d`).  In a `3`-cycle ANY two distinct
darts are joined by a single `φ`-step in one direction or the other
(`phi_edge_of_sameFace_triangle`).  And for two **non-cycle** darts a clean `M.φ`-edge
lifts to a clean `φ'₂`-edge of the corrected cut map
(`cutCapMap2.φ (inl d) = inl (M.φ d)` whenever neither `d` nor `M.φ d` is a cycle
dart — `cutCapPhi2_inl_clean`).  Hence:

* **`phiPrime_edge_of_innerGate`** — for two distinct non-cycle darts in one inner
  triangular face, `φ'₂` joins their `inl`-lifts by a single edge.

This is exactly the rotation-system contiguity the spec asked for, and it discharges
every **intermediate** gate of `GateFragmentCompatible` (whose entry/exit darts
`α (edge j)`, `edge (j+1)` are both across uncut edges, hence non-cycle), once the
intermediate faces are known to be inner triangles and the gate darts distinct.

## What is NOT recoverable as stated (the honest correction)

**The literal `start_edge`/`end_edge` of `GateFragmentCompatible` are FALSE for the
geometric extracted path.**  The start gate demands a single `φ'₂`-edge between the
forward cycle dart `dart i` and the first crossing dart.  But the corrected cut map
*reroutes* the cycle darts into the cap chain:

```
φ'₂ (inl (dart i)) = inl (dart (nextIdx i))     -- cutCapPhi2_dart, a CYCLE dart
```

so `φ'₂ (inl (dart i))` is the **next cycle dart**, never a non-cycle crossing dart
(`start_edge_forward_false`); and nothing clean maps *into* `inl (dart i)` because
`dart i` is a cycle dart and a clean/divert `φ'₂`-edge never lands on a cycle dart
(`start_edge_backward_false`).  The cycle dart is **`φ'₂`-fragment-isolated**: the
genuine connectivity `inl (dart i) ⇝ inl (crossing)` flows through the **cap chain**
(`SidesReach2`, already a theorem), NOT through a within-old-face `φ'₂`-edge.

### The decisive finding: `GateFragmentCompatible` is UNINHABITABLE

Sharper still, the `end_edge` field alone is unsatisfiable for *every* ordinary dual
path (`end_edge_refuted`): its forward disjunct lands on the reverse cycle dart
`inl (α (dart i))` (whose only `φ'₂`-preimage is a *cycle* dart,
`phiPrime_into_reverseCycleDart_false`), and its backward disjunct sends
`inl (α (dart i))` to the cycle dart `inl (α (dart (prevIdx i)))`.  So

* **`gateFragmentCompatible_uninhabited`** : `¬ C.GateFragmentCompatible i P`.

Therefore `gateCompat` (which must *produce* such a `P`) is a **false / mis-specified
residue**: it can never be discharged, because the corrected cut-and-cap surgery
reroutes the cycle darts into the cap chain.  This is the precise analogue of the
`ChordSigmaContig` finding (the literal `keptPhi`-wrap is FALSE; connectivity flows
through the post-splice trace, not the kept rotation).

## The minimal residue (the corrected datum `gateCompat` should have demanded)

The single genuine remaining content is the endpoint **cap-channel** link, isolated as
the named non-vacuous Prop `EndpointCapLink` (the `cutReach2` from the forward cycle
dart to the start crossing dart, and from the reverse cycle dart to the end crossing
dart), together with the geometric inner-triangle/distinctness data of the extracted
path's intermediate gates (`InteriorTriangleGates`, which makes every intermediate gate
a single `φ'₂`-edge by the recoverable lever).  Both are satisfiable (Section 5).

**Required upstream edit (NOT performed here):** to close Chapter 35, the `gateCompat`
field of `ChordJordanInput` (and the `start_edge`/`end_edge` fields of
`GateFragmentCompatible`) in `ChordSeparation.lean` must be replaced by the
`EndpointCapLink` cap-channel datum (endpoints) together with `InteriorTriangleGates`
(intermediates).  The `end_edge`/`start_edge` `φ'₂`-edge endpoint requirement is
`gateFragmentCompatible_uninhabited`-false and cannot stand.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open ProofsInTheBook.PlanarMap.CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}

/-! ## Section 1.  The triangle lever (the recoverable rotation-system contiguity)

In a near-triangulation, two distinct darts of one inner face lie in a `φ`-`3`-cycle,
so a single `M.φ`-step joins them.  We prove this from `M.φ³ d = d` (the triangle
identity) and `dartFace`-equality (= `φ.SameCycle`). -/

/-- **`dartFace`-equality is `φ`-`SameCycle`.**  `dartFace d = Quotient.mk (cycleSetoid
M.φ) d`, so two darts share a face iff they are `M.φ.SameCycle`. -/
lemma sameCycle_phi_of_dartFace_eq {d e : D} (h : M.dartFace d = M.dartFace e) :
    M.φ.SameCycle d e := by
  have := Quotient.exact h
  exact this

/-- **A `φ`-`3`-cycle element is `d`, `φ d`, or `φ² d`.**  If `M.φ³ d = d` and
`M.φ.SameCycle d e`, then `e ∈ {d, M.φ d, M.φ² d}`.  Proof: the triple is invariant
under both `φ` and `φ⁻¹` (using `φ³ d = d`), so it contains the whole `φ`-orbit of `d`,
hence `e = φ^i d` for some `i : ℤ`. -/
lemma mem_triple_of_sameCycle_phiCube {d e : D} (hcube : M.φ (M.φ (M.φ d)) = d)
    (h : M.φ.SameCycle d e) :
    e = d ∨ e = M.φ d ∨ e = M.φ (M.φ d) := by
  obtain ⟨i, hi⟩ := h
  -- `φ⁻¹ d = φ² d`, `φ⁻¹ (φ d) = d`, `φ⁻¹ (φ² d) = φ d`  (from `φ³ d = d`).
  have hinv0 : M.φ.symm d = M.φ (M.φ d) := by
    rw [Equiv.symm_apply_eq]; exact hcube.symm
  have hinv1 : M.φ.symm (M.φ d) = d := by rw [Equiv.symm_apply_eq]
  have hinv2 : M.φ.symm (M.φ (M.φ d)) = M.φ d := by rw [Equiv.symm_apply_eq]
  -- The predicate "x ∈ triple" is invariant under `φ` and `φ⁻¹`, so `φ^i d` is in it.
  have key : ∀ k : ℤ, (M.φ ^ k) d = d ∨ (M.φ ^ k) d = M.φ d ∨
      (M.φ ^ k) d = M.φ (M.φ d) := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · left; simp
    · intro n ih
      rw [show ((n : ℤ) + 1) = 1 + (n : ℤ) by ring, zpow_add, zpow_one,
        Equiv.Perm.mul_apply]
      rcases ih with h0 | h1 | h2
      · right; left; rw [h0]
      · right; right; rw [h1]
      · left; rw [h2]; exact hcube
    · intro n ih
      have hstep : (M.φ ^ (-(n : ℤ) - 1)) d = M.φ.symm ((M.φ ^ (-(n : ℤ))) d) := by
        rw [show (-(n : ℤ) - 1) = (-1) + (-(n : ℤ)) by ring, zpow_add, Equiv.Perm.mul_apply,
          show (M.φ ^ (-1 : ℤ)) = M.φ.symm from by
            rw [zpow_neg, zpow_one]; rfl]
      rw [hstep]
      rcases ih with h0 | h1 | h2
      · rw [h0]; right; right; exact hinv0
      · rw [h1]; left; exact hinv1
      · rw [h2]; right; left; exact hinv2
  rcases key i with h0 | h1 | h2
  · left; rw [← hi, h0]
  · right; left; rw [← hi, h1]
  · right; right; rw [← hi, h2]

/-- **The triangle lever (`M.φ` form).**  Two distinct darts of the same inner
triangular face (`M.φ³ d = d`) are joined by a single `M.φ`-step (in one direction or
the other). -/
lemma phi_edge_of_sameFace_triangle {d e : D}
    (hcube : M.φ (M.φ (M.φ d)) = d) (hface : M.dartFace d = M.dartFace e)
    (hne : d ≠ e) :
    M.φ d = e ∨ M.φ e = d := by
  have hsc := sameCycle_phi_of_dartFace_eq hface
  rcases mem_triple_of_sameCycle_phiCube hcube hsc with h0 | h1 | h2
  · exact absurd h0.symm hne
  · exact Or.inl h1.symm
  · -- e = φ² d ⇒ φ e = φ³ d = d
    right; rw [h2]; exact hcube

/-! ## Section 2.  Clean `φ'₂`-edge from a clean `M.φ`-edge (non-cycle darts)

`cutCapPhi2_inl_other_cases` gives, for `d ∉ dartSet`, `φ'₂ (inl d) = inl (M.φ d)`
unless `M.φ d` is a cycle bank dart (a `p`/`q` dart, i.e. `M.φ d ∈ dartSet`).  So a
clean `M.φ`-edge between two **non-cycle** darts lifts to a clean `φ'₂`-edge. -/

/-- The `p`/`q` bank darts are exactly the cycle darts: `qDart i = dart i`,
`pDart i = α (dart (prevIdx i))`, both in `dartSet`. -/
lemma pDart_mem_dartSet (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.pDart i ∈ C.dartSet := by
  rw [pDart]; exact C.alpha_dart_mem_dartSet _

lemma qDart_mem_dartSet (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.qDart i ∈ C.dartSet := by
  rw [qDart]; exact C.dart_mem_dartSet _

/-- **Clean `φ'₂` on a non-cycle dart whose `M.φ`-image is also non-cycle.**  Then the
cap-divert branches of `cutCapPhi2_inl_other_cases` cannot fire (they require
`M.φ d = M.σ (M.α d)` to be a `p`/`q` cycle dart), so `φ'₂ (inl d) = inl (M.φ d)`. -/
lemma cutCapPhi2_inl_clean (C : SimplePrimalCycle M) {d : D}
    (hd : d ∉ C.dartSet) (hphid : M.φ d ∉ C.dartSet) :
    (C.cutCapMap2).φ (Sum.inl d) = Sum.inl (M.φ d) := by
  rcases C.cutCapPhi2_inl_other_cases hd with hclean | ⟨j, hpj, _⟩ | ⟨j, hqj, _⟩
  · exact hclean
  · refine absurd ?_ hphid
    rw [show M.φ d = M.σ (M.α d) from rfl, hpj]; exact C.pDart_mem_dartSet j
  · refine absurd ?_ hphid
    rw [show M.φ d = M.σ (M.α d) from rfl, hqj]; exact C.qDart_mem_dartSet j

/-- **The recoverable rotation-system contiguity (`φ'₂` form).**  Two distinct
**non-cycle** darts `d`, `e` in one inner triangular face are joined by a single
`φ'₂`-edge of the corrected cut map.  This is the genuine M-lesson recoverable core:
the triangle `φ`-`3`-cycle gives a single `M.φ`-step, which lifts cleanly because both
darts are non-cycle. -/
lemma phiPrime_edge_of_innerGate (C : SimplePrimalCycle M) {d e : D}
    (hcube : M.φ (M.φ (M.φ d)) = d) (hface : M.dartFace d = M.dartFace e)
    (hne : d ≠ e) (hd : d ∉ C.dartSet) (he : e ∉ C.dartSet) :
    (C.cutCapMap2).φ (Sum.inl d) = Sum.inl e ∨
      (C.cutCapMap2).φ (Sum.inl e) = Sum.inl d := by
  rcases phi_edge_of_sameFace_triangle hcube hface hne with hfwd | hbwd
  · -- M.φ d = e: clean lift of d (its image e is non-cycle)
    left
    have := C.cutCapPhi2_inl_clean hd (by rw [hfwd]; exact he)
    rwa [hfwd] at this
  · -- M.φ e = d: clean lift of e (its image d is non-cycle)
    right
    have := C.cutCapPhi2_inl_clean he (by rw [hbwd]; exact hd)
    rwa [hbwd] at this

/-! ## Section 3.  The literal endpoint gates of `GateFragmentCompatible` are FALSE
    for the geometric extracted path

The `start_edge` field demands a single `φ'₂`-edge between the forward cycle dart
`dart i` and the first crossing dart `edge ⟨0⟩`.  We refute both directions:

* forward: `φ'₂ (inl (dart i)) = inl (dart (nextIdx i))` (a *cycle* dart), and the
  crossing dart `edge ⟨0⟩` crosses an *uncut* edge, hence is non-cycle, so it can never
  equal `dart (nextIdx i)`;
* backward: nothing clean maps *into* `inl (dart i)`, because the clean `inl→inl`
  branch's image `M.φ (·)` would have to be the cycle dart `dart i`, contradicting the
  non-cycle hypothesis of the clean branch.

Hence the cycle dart is `φ'₂`-fragment-isolated; the honest endpoint datum is the
**cap-channel** `cutReach2`, not a within-face `φ'₂`-edge. -/

/-- **Forward endpoint gate refuted.**  `φ'₂ (inl (dart i))` is the *next cycle dart*
`inl (dart (nextIdx i))`, never `inl c` for a non-cycle crossing dart `c`.  So the
`start_edge` forward disjunct is unsatisfiable for any genuine crossing dart. -/
theorem start_edge_forward_false (C : SimplePrimalCycle M) (i : Fin C.len) {c : D}
    (hc : c ∉ C.dartSet) :
    (C.cutCapMap2).φ (Sum.inl (C.dart i)) ≠ Sum.inl c := by
  rw [C.cutCapPhi2_dart i]
  intro h
  have heq : C.dart (C.nextIdx i) = c := Sum.inl.inj h
  exact hc (heq ▸ C.dart_mem_dartSet (C.nextIdx i))

/-- **Backward endpoint gate refuted.**  No `φ'₂`-edge lands on the cycle dart
`inl (dart i)` from a non-cycle dart `c`.  If `M.φ c = dart i`, then since `dart i =
qDart i` is a `q`-bank cycle dart, the `−`-cap divert fires and `φ'₂ (inl c) =
inr (inr i)`, a cap dart — never `inl (dart i)`.  And if `M.φ c ≠ dart i`, no clean
edge hits `dart i` either.  Hence the cycle dart is `φ'₂`-fragment-isolated. -/
theorem start_edge_backward_false (C : SimplePrimalCycle M) (i : Fin C.len) {c : D}
    (hc : c ∉ C.dartSet) :
    (C.cutCapMap2).φ (Sum.inl c) ≠ Sum.inl (C.dart i) := by
  intro h
  rcases C.cutCapPhi2_inl_other_cases hc with hclean | ⟨j, hpj, hdiv⟩ | ⟨j, hqj, hdiv⟩
  · -- clean: φ'₂(inl c) = inl(M.φ c) = inl(dart i) ⟹ M.φ c = dart i = qDart i.
    rw [hclean] at h
    have hphi : M.φ c = C.dart i := Sum.inl.inj h
    have hqi : M.σ (M.α c) = C.qDart i := by
      rw [show M.σ (M.α c) = M.φ c from rfl, hphi, qDart]
    -- but a `q`-end forces the `−`-cap divert: the true image is `inr (inr i)`,
    -- contradicting the clean form `inl (M.φ c)`.
    have hne : (C.cutCapMap2).φ (Sum.inl c) = Sum.inr (Sum.inr i) := by
      rw [C.cutCapPhi2_apply (Sum.inl c), C.cutAlpha_other hc, ← cutSigmaPerm2_apply,
        ← cutCapMap2_sigma, C.cutSigma2_minusEnd hqi]
    rw [hclean] at hne; exact Sum.inl_ne_inr hne
  · -- p-divert: image is `inr (inl ·)`, not `inl`.
    rw [hdiv] at h; exact Sum.inr_ne_inl h
  · -- q-divert: image is `inr (inr ·)`, not `inl`.
    rw [hdiv] at h; exact Sum.inr_ne_inl h

/-! ### The endpoint `end_edge` field of `GateFragmentCompatible` is also unsatisfiable

`end_edge` connects the last entry dart (or `dart i` when `n = 0`) to the *reverse*
cycle dart `α (dart i)` by a single `φ'₂`-edge.  Both directions fail, by the same
fragment-isolation of the cycle darts:

* `φ'₂ (inl (α (dart i))) = inl (pDart i) = inl (α (dart (prevIdx i)))` (a *cycle*
  dart), so the backward disjunct forces the `lhs` to be a cycle dart;
* the only preimage of `inl (α (dart i))` under `φ'₂` is the reverse cycle dart
  `inl (α (dart (nextIdx i)))`, so the forward disjunct also forces `lhs` to be a cycle
  dart.

Hence whenever `lhs` is a non-cycle dart (`n > 0`: `lhs = α (edge ⟨n-1⟩)`) or the
forward cycle dart (`n = 0`: `lhs = dart i ≠ α (dart ·)`), `end_edge` is false. -/

/-- `φ'₂` maps `inl (α (dart i))` to the reverse cycle dart `inl (α (dart (prevIdx i)))`
(restatement of `cutCapPhi2_alpha_dart`, since `pDart i = α (dart (prevIdx i))`). -/
lemma cutCapPhi2_alphaDart_eq (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap2).φ (Sum.inl (M.α (C.dart i))) = Sum.inl (M.α (C.dart (C.prevIdx i))) := by
  rw [C.cutCapPhi2_alpha_dart i, show C.pDart i = M.α (C.dart (C.prevIdx i)) from rfl]

/-- **The unique `φ'₂`-preimage of the reverse cycle dart `inl (α (dart i))` is the
reverse cycle dart `inl (α (dart (nextIdx i)))`.**  In particular no *non-cycle* dart
maps to `inl (α (dart i))`. -/
theorem phiPrime_into_reverseCycleDart_false (C : SimplePrimalCycle M) (i : Fin C.len)
    {c : D} (hc : c ∉ C.dartSet) :
    (C.cutCapMap2).φ (Sum.inl c) ≠ Sum.inl (M.α (C.dart i)) := by
  intro h
  rcases C.cutCapPhi2_inl_other_cases hc with hclean | ⟨j, hpj, hdiv⟩ | ⟨j, hqj, hdiv⟩
  · -- clean: M.φ c = α (dart i) = pDart (nextIdx i), a `p`-end, so the `+`-cap divert
    -- must fire instead — the true image is `inr`, contradicting the clean `inl`.
    rw [hclean] at h
    have hphi : M.φ c = M.α (C.dart i) := Sum.inl.inj h
    have hpi : M.σ (M.α c) = C.pDart (C.nextIdx i) := by
      rw [show M.σ (M.α c) = M.φ c from rfl, hphi,
        show C.pDart (C.nextIdx i) = M.α (C.dart (C.prevIdx (C.nextIdx i))) from rfl,
        C.prevIdx_nextIdx]
    have hne : (C.cutCapMap2).φ (Sum.inl c) = Sum.inr (Sum.inl (C.prevIdx (C.nextIdx i))) := by
      rw [C.cutCapPhi2_apply (Sum.inl c), C.cutAlpha_other hc, ← cutSigmaPerm2_apply,
        ← cutCapMap2_sigma, C.cutSigma2_plusEnd hpi]
    rw [hclean] at hne; exact Sum.inl_ne_inr hne
  · rw [hdiv] at h; exact Sum.inr_ne_inl h
  · rw [hdiv] at h; exact Sum.inr_ne_inl h

/-! ## Section 4.  The intermediate-gate discharge from the recoverable lever, and
    the precise minimal residue

The recoverable lever `phiPrime_edge_of_innerGate` discharges every **intermediate**
gate of `GateFragmentCompatible`, given exactly the geometric data the *bare* dual path
does not carry: that the gate's old face is an **inner triangle** (`M.φ³ = id` there)
and that its entry/exit darts are **distinct**.  The non-cycle hypotheses are automatic
(`α (edge j)`, `edge (j+1)` both cross uncut edges).  We package this geometric data as
`InteriorTriangleGates` and discharge `mid_edge` from it.

The **endpoint** gates cannot be so discharged: `start_edge_forward_false` /
`start_edge_backward_false` show the cycle dart `dart i` is `φ'₂`-fragment-isolated, so
no within-face `φ'₂`-edge links it to a crossing dart.  The genuine endpoint datum is
the **cap-channel** `cutReach2`, isolated as `EndpointCapLink`. -/

/-- A crossing dart of an ordinary dual path is non-cycle (`∉ dartSet`), since it
crosses an uncut edge. -/
lemma edge_notMem_dartSet (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (j : Fin P.n) : P.edge j ∉ C.dartSet :=
  C.notMem_dartSet_of_dartEdge_notMem (P.edge_uncut j)

/-- The `α`-reverse of a crossing dart is also non-cycle (same edge, still uncut). -/
lemma alpha_edge_notMem_dartSet (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (j : Fin P.n) : M.α (P.edge j) ∉ C.dartSet :=
  C.notMem_dartSet_of_dartEdge_notMem (by rw [M.dartEdge_alpha]; exact P.edge_uncut j)

/-- **The geometric residue of the intermediate gates** (the data the *bare* dual path
lacks): for each intermediate position, the entry dart's old face is an inner triangle
(`M.φ³ (α (edge j)) = α (edge j)`) and the entry/exit darts are distinct.  This is the
genuine combinatorial content `gateCompat` must supply for the intermediate gates — and
in a near-triangulation it is *true* (every visited inner face is a triangle), the
recoverable rotation-system contiguity. -/
structure InteriorTriangleGates (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2) :
    Prop where
  /-- The face at each intermediate gate is an inner triangle (the entry dart's
  `M.φ`-orbit is a `3`-cycle). -/
  tri : ∀ j : Fin P.n, ∀ hj : (j : ℕ) + 1 < P.n,
    M.φ (M.φ (M.φ (M.α (P.edge j)))) = M.α (P.edge j)
  /-- The entry and exit darts of each intermediate gate are distinct. -/
  ne : ∀ j : Fin P.n, ∀ hj : (j : ℕ) + 1 < P.n,
    M.α (P.edge j) ≠ P.edge ⟨(j : ℕ) + 1, hj⟩

/-- **Intermediate-gate `φ'₂`-edge, discharged.**  From the geometric residue
`InteriorTriangleGates`, each intermediate gate is realised by a single `φ'₂`-edge — the
exact `mid_edge` field of `GateFragmentCompatible`. -/
theorem mid_edge_of_interiorTriangleGates (C : SimplePrimalCycle M)
    (P : C.OrdinaryDualPath2) (hg : C.InteriorTriangleGates P)
    (j : Fin P.n) (hj : (j : ℕ) + 1 < P.n) :
    (C.cutCapMap2).φ (Sum.inl (M.α (P.edge j))) = Sum.inl (P.edge ⟨(j : ℕ) + 1, hj⟩) ∨
      (C.cutCapMap2).φ (Sum.inl (P.edge ⟨(j : ℕ) + 1, hj⟩)) = Sum.inl (M.α (P.edge j)) := by
  refine C.phiPrime_edge_of_innerGate (hg.tri j hj) ?_ (hg.ne j hj)
    (C.alpha_edge_notMem_dartSet P j) (C.edge_notMem_dartSet P ⟨(j : ℕ) + 1, hj⟩)
  -- co-facehood: both darts have face `P.face j.succ`.
  rw [P.right_face j]
  have hjs : (⟨(j : ℕ) + 1, hj⟩ : Fin P.n).castSucc = j.succ := by
    apply Fin.ext; simp [Fin.val_succ]
  rw [P.left_face ⟨(j : ℕ) + 1, hj⟩, hjs]

/-! ### The decisive finding: `GateFragmentCompatible` is uninhabitable

The `end_edge` field is unsatisfiable for *every* ordinary dual path, so
`GateFragmentCompatible i P` has no inhabitant and `gateCompat` (which must produce one)
is a **mis-specified residue** — exactly the `ChordSigmaContig` pattern (a literal
within-face/rotation wrap that the corrected surgery makes false). -/

/-- **The `end_edge` field is unsatisfiable.**  Its forward disjunct lands on the
reverse cycle dart `inl (α (dart i))` (no non-cycle dart maps there, and the only cycle
preimage is `α (dart (nextIdx i))`); its backward disjunct sends `inl (α (dart i))` to
the *cycle* dart `inl (α (dart (prevIdx i)))`.  Either way the gate's first dart `lhs`
would have to be a *cycle* dart.  But `lhs` is either the non-cycle `α (edge ⟨n-1⟩)`
(`n > 0`) or the forward cycle dart `dart i` (which is never a reverse cycle dart, by
`dart_ne_alpha_dart`).  Contradiction. -/
theorem end_edge_refuted (C : SimplePrimalCycle M) (i : Fin C.len)
    (P : C.OrdinaryDualPath2) :
    ¬ ((C.cutCapMap2).φ
          (Sum.inl (if h : 0 < P.n then M.α (P.edge ⟨P.n - 1, by omega⟩) else C.dart i))
        = Sum.inl (M.α (C.dart i)) ∨
      (C.cutCapMap2).φ (Sum.inl (M.α (C.dart i)))
        = Sum.inl (if h : 0 < P.n then M.α (P.edge ⟨P.n - 1, by omega⟩) else C.dart i)) := by
  rintro (hfwd | hbwd)
  · -- forward: `φ'₂ (inl lhs) = inl (α (dart i))`.
    by_cases hn : 0 < P.n
    · rw [dif_pos hn] at hfwd
      -- lhs = α (edge ⟨n-1⟩) is non-cycle; no non-cycle dart maps to inl (α (dart i)).
      exact C.phiPrime_into_reverseCycleDart_false i
        (C.alpha_edge_notMem_dartSet P ⟨P.n - 1, by omega⟩) hfwd
    · rw [dif_neg hn] at hfwd
      -- lhs = dart i is the FORWARD cycle dart; φ'₂ (inl (dart i)) = inl (dart (nextIdx i)),
      -- never the reverse cycle dart inl (α (dart i)).
      rw [C.cutCapPhi2_dart i] at hfwd
      have := Sum.inl.inj hfwd
      exact C.dart_ne_alpha_dart (C.nextIdx i) i this
  · -- backward: `φ'₂ (inl (α (dart i))) = inl lhs`, and the LHS is the cycle dart
    -- `inl (α (dart (prevIdx i)))`, so `lhs = α (dart (prevIdx i))`, a cycle dart.
    rw [C.cutCapPhi2_alphaDart_eq i] at hbwd
    by_cases hn : 0 < P.n
    · rw [dif_pos hn] at hbwd
      -- lhs = α (edge ⟨n-1⟩) non-cycle, but equals the cycle dart α (dart (prevIdx i)).
      have heq : M.α (C.dart (C.prevIdx i)) = M.α (P.edge ⟨P.n - 1, by omega⟩) :=
        Sum.inl.inj hbwd
      exact C.alpha_edge_notMem_dartSet P ⟨P.n - 1, by omega⟩
        (heq ▸ C.alpha_dart_mem_dartSet (C.prevIdx i))
    · rw [dif_neg hn] at hbwd
      -- lhs = dart i, but α (dart (prevIdx i)) = dart i contradicts dart_ne_alpha_dart.
      have heq : M.α (C.dart (C.prevIdx i)) = C.dart i := Sum.inl.inj hbwd
      exact C.dart_ne_alpha_dart i (C.prevIdx i) heq.symm

/-- **`GateFragmentCompatible` is uninhabitable.**  Its `end_edge` field is the
unsatisfiable equation of `end_edge_refuted`, so no ordinary dual path is
gate-compatible.  Consequently the `gateCompat` field of `ChordJordanInput` — which
demands such a path for each cycle edge — is a **false (mis-specified) residue**: the
corrected cut-and-cap surgery reroutes the cycle dart `dart i` to the *next* cycle dart
`dart (nextIdx i)` and `α (dart i)` to the *previous* one, so the endpoint gate is never
a within-old-face `φ'₂`-edge.  The honest endpoint datum is `EndpointCapLink` (the cap
channel), exactly as `ChordSigmaContig` replaced the false `keptPhi`-wrap by the
post-splice `tracePhi`. -/
theorem gateFragmentCompatible_uninhabited (C : SimplePrimalCycle M) (i : Fin C.len)
    (P : C.OrdinaryDualPath2) :
    ¬ C.GateFragmentCompatible i P :=
  fun hg => C.end_edge_refuted i P hg.end_edge

/-- **The minimal endpoint residue: the cap-channel link.**  The genuine remaining
content of `gateCompat` for an ordinary dual path is the *endpoint* connectivity, which
the surgery routes through the cap chain (NOT a within-face `φ'₂`-edge, as
`start_edge_*_false` show): the forward cycle dart `dart i` is `cutReach2`-connected to
the start crossing dart, and the reverse cycle dart `α (dart i)` to the end crossing
dart.  (For `n = 0` both reduce to `cutReach2 (inl (dart i)) (inl (α (dart i)))`.)

This is non-vacuous (`SidesReach2` already threads all cycle darts into one
`cutReach2`-loop) and is the honest discrete-Jordan datum — the analogue of
`ChordSigmaContig`'s `SideTracePhiTwoCycle` (connectivity through the spliced channel,
not the false within-face wrap). -/
def EndpointCapLink (C : SimplePrimalCycle M) (i : Fin C.len) (P : C.OrdinaryDualPath2) :
    Prop :=
  (∀ h : 0 < P.n,
      C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (P.edge ⟨0, h⟩))) ∧
    (∀ h : 0 < P.n,
      C.cutReach2 (Sum.inl (M.α (C.dart i)))
        (Sum.inl (M.α (P.edge ⟨P.n - 1, by omega⟩)))) ∧
    (P.n = 0 → C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i))))

/-! ## Section 5.  Non-vacuity certificates (§3.3 anti-impostor)

The recoverable lever and the endpoint residue are both genuinely satisfiable; the
refuted literal endpoint gate is genuinely refuted (not vacuously). -/

/-- **Non-vacuity of the recoverable lever.**  In any inner triangular face the lever is
satisfiable: the two distinct non-cycle darts `c`, `M.φ c` (with `M.φ² c` the third) are
joined by the `φ'₂`-edge `φ'₂ (inl c) = inl (M.φ c)`.  (`c` and `M.φ c` non-cycle.) -/
theorem phiPrime_edge_of_innerGate_nonvacuous (C : SimplePrimalCycle M) {c : D}
    (hcube : M.φ (M.φ (M.φ c)) = c) (hc : c ∉ C.dartSet) (hφc : M.φ c ∉ C.dartSet)
    (hne : c ≠ M.φ c) :
    (C.cutCapMap2).φ (Sum.inl c) = Sum.inl (M.φ c) ∨
      (C.cutCapMap2).φ (Sum.inl (M.φ c)) = Sum.inl c :=
  C.phiPrime_edge_of_innerGate hcube (M.dartFace_phi c).symm hne hc hφc

/-- **Non-vacuity of the endpoint cap residue (`n = 0`).**  Given a cross-bank
`cutReach2` link (the genuine connectivity datum, e.g. supplied by `M.Connected` through
`reachesBank2`), the nil ordinary path satisfies `EndpointCapLink`.  So the residue is
inhabited — not a hidden `False`. -/
theorem endpointCapLink_nil (C : SimplePrimalCycle M) (i : Fin C.len) (f : M.Face)
    (hcross : C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i)))) :
    C.EndpointCapLink i (OrdinaryDualPath2.nil C f) := by
  refine ⟨fun h => ?_, fun h => ?_, fun _ => hcross⟩
  · exact absurd h (by show ¬ 0 < 0; omega)
  · exact absurd h (by show ¬ 0 < 0; omega)

/-- **The literal `GateFragmentCompatible.start_edge` is refuted for every geometric
path with a genuine first crossing.**  Neither disjunct of `start_edge` can hold: the
forward direction lands on the next *cycle* dart (`start_edge_forward_false`), and the
backward direction cannot hit the cycle dart `dart i` from any non-cycle crossing dart
(`start_edge_backward_false`).  Hence `gateCompat`'s single-`φ'₂`-edge endpoint
requirement is genuinely over-strong; the honest endpoint datum is `EndpointCapLink`. -/
theorem start_edge_literal_refuted (C : SimplePrimalCycle M) (i : Fin C.len)
    (P : C.OrdinaryDualPath2) (h : 0 < P.n) :
    ¬ ((C.cutCapMap2).φ (Sum.inl (C.dart i)) = Sum.inl (P.edge ⟨0, h⟩) ∨
        (C.cutCapMap2).φ (Sum.inl (P.edge ⟨0, h⟩)) = Sum.inl (C.dart i)) := by
  rintro (hfwd | hbwd)
  · exact C.start_edge_forward_false i (C.edge_notMem_dartSet P ⟨0, h⟩) hfwd
  · exact C.start_edge_backward_false i (C.edge_notMem_dartSet P ⟨0, h⟩) hbwd

end CombMap.SimplePrimalCycle

end ProofsInTheBook.PlanarMap

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.phi_edge_of_sameFace_triangle
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.phiPrime_edge_of_innerGate
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.start_edge_forward_false
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.start_edge_backward_false
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.mid_edge_of_interiorTriangleGates
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.phiPrime_into_reverseCycleDart_false
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.end_edge_refuted
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.gateFragmentCompatible_uninhabited
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.endpointCapLink_nil
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.start_edge_literal_refuted
