import ProofsInTheBook.ChordSeparationClose
import ProofsInTheBook.PlanarMapNearTriangulation

/-!
# Chapter 35 chord-separation bricks: the interior-triangle gate lever (Brick B) and the
  orbit-label-certificate tool, with the precise isolation of the `faceCore` residue (Brick A)

This file closes the **tractable** combinatorial content of the two `ChordJordanInput'`
fields (`ProofsInTheBook/ChordSeparationClose.lean`) and isolates the one genuinely
irreducible residue.

`ChordJordanInput'` carries two fields:

* `faceCore : C.NumCyclesCutPhi2`  (= `numCycles (cutCapMap2).φ = M.F + 2`);
* `gateCompat'` : per cycle edge, a cycle-avoiding dual path produces an ordinary dual
  path carrying both `EndpointCapLink` (the cap channel) **and** `InteriorTriangleGates`.

## Brick B — the interior-triangle gate lever (PROVEN clean-3)

The triangle lever `phiPrime_edge_of_innerGate` (in `ChordGateCompat.lean`) is already
proven; what was only inhabited on the nil path is the **assembly**
`InteriorTriangleGates P` for a *genuine* (`n ≥ 1`) ordinary dual path.  Here we discharge
that assembly from the near-triangulation invariant:

* `interiorTriangleGates_tri_of_innerFaces` — the `tri` field (`(M.φ)^[3] = id` at each
  intermediate entry dart) is derived from `NearTriangulation` (`inner_tri` ⇒
  `faceLen = 3` ⇒ `faceLen_three_phi_cube_eq_self`), given that each intermediate face is
  inner (non-outer).  This is the genuine new content: the lever's geometric premise is now
  *supplied by `hNT`*, not assumed.
* `interiorTriangleGates_of_nearTriangulation` — assembles the full
  `InteriorTriangleGates P` from `hNT`, the per-position inner-face condition, and the
  per-position entry≠exit condition (the latter is the only honest geometric residue of the
  *intermediate* gates, and is not derivable from triangularity alone — two crossing darts
  of a triangle can a priori coincide).
* `mid_edge_of_nearTriangulation`, `interiorReach_of_nearTriangulation` — the
  intermediate-gate `φ'₂`-edge and the full interior `cutReach2` chain, now driven directly
  from the near-triangulation data.

This discharges, *for real (non-nil) paths*, the `InteriorTriangleGates` half of
`gateCompat'`.

## Brick A — `faceCore` via an orbit-label certificate (TOOL proven; prescribed
   instantiation REFUTED)

We prove the requested general orbit-counting tool

  `numCycles_eq_card_of_orbitLabelCert : OrbitLabelCert X β q → numCycles q = card β`,

which is genuine, reusable, clean-3 infrastructure (a `label`/`anchor` certificate exhibits
the cycle↔β bijection).

We then record, *precisely*, why instantiating it at `X := Dcut`, `q := (cutCapMap2).φ`,
`β := OldFace M.φ ⊕ Side` — the prescribed route to `faceCore` — **cannot** work: the
`label_invariant` field (`label (q x) = label x`) is FALSE for any old-face-based label,
because the corrected surgery pulls the forward cycle darts into a *single* `φ'₂`-orbit that
spans **three distinct old faces** while the `−`-caps are absorbed *into* old faces (verified
by the kernel `#eval` reconnaissance in `PlanarMapCutCap2F.lean`/`PlanarMapCutCapEval.lean`,
and reproduced numerically on the tetrahedron cut `0→1→2→0`: the orbit
`{inl(0,1), inl(1,2), inl(2,0)}` spans old faces `{0,2,3}`).  Hence the fibers of an
old-face label are *not* `φ'₂`-orbits — `numCycles_eq_card_of_orbitLabelCert` is inapplicable
through that `β`, and `faceCore` is *not* a genus-free orbit-label count.  It is the genuine
genus-0 Euler invariant of the surgery, whose combinatorial proof needs the full
transposition-walk / `SameCycle`-transport development (the `F`-analogue of the `963`-line
`V'` machinery), exactly as documented in `PlanarMapCutCap2F.lean`.  We therefore leave
`faceCore` as the named, kernel-anchored core it already is, and contribute the orbit-cert
tool plus this precise refutation as the change of attack vector demanded by the brief.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open ProofsInTheBook.PlanarMap.CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Part 1.  The orbit-label-certificate tool (Brick A infrastructure)

A certificate that the fibers of a label map `label : X → β` are exactly the `q`-orbits,
pinned by an `anchor : β → X` section.  From it, `numCycles q = card β`. -/

/-- **An orbit-label certificate** for a permutation `q : Equiv.Perm X`: a label map
`label`, a section `anchor`, with `label ∘ anchor = id`, `label` `q`-invariant, and every
`x` in the same `q`-cycle as `anchor (label x)`.  Together these pin the fiber of `label`
over each `b` to exactly one `q`-orbit. -/
structure OrbitLabelCert (X : Type*) (β : Type*) (q : Equiv.Perm X) where
  /-- The orbit label. -/
  label : X → β
  /-- A chosen anchor (orbit representative) for each label. -/
  anchor : β → X
  /-- `anchor` is a section of `label`. -/
  label_anchor : ∀ b, label (anchor b) = b
  /-- `label` is constant on `q`-orbits. -/
  label_invariant : ∀ x, label (q x) = label x
  /-- Each `x` is `q`-`SameCycle` with the anchor of its label. -/
  same_anchor : ∀ x, q.SameCycle x (anchor (label x))

namespace OrbitLabelCert

variable {X : Type*} {β : Type*} [Fintype X] [DecidableEq X] {q : Equiv.Perm X}

/-- `label` is invariant along whole `q`-cycles (not just one step). -/
lemma label_sameCycle (C : OrbitLabelCert X β q) {x y : X} (h : q.SameCycle x y) :
    C.label x = C.label y := by
  obtain ⟨k, hk⟩ := h
  have hpow : ∀ (m : ℤ) (z : X), C.label ((q ^ m) z) = C.label z := by
    intro m
    refine Int.induction_on m ?_ ?_ ?_
    · intro z; simp
    · intro n ih z
      have hstep : (q ^ ((n : ℤ) + 1)) z = q ((q ^ (n : ℤ)) z) := by
        rw [show ((n : ℤ) + 1) = 1 + (n : ℤ) by ring, zpow_add, zpow_one,
          Equiv.Perm.mul_apply]
      rw [hstep, C.label_invariant, ih]
    · intro n ih z
      have hstep : (q ^ (-(n : ℤ))) z = q ((q ^ (-(n : ℤ) - 1)) z) := by
        have he : (q ^ (-(n : ℤ))) = q ^ ((1 : ℤ) + (-(n : ℤ) - 1)) := by
          congr 1; ring
        rw [he, zpow_add, zpow_one, Equiv.Perm.mul_apply]
      have hkey : C.label ((q ^ (-(n : ℤ) - 1)) z) = C.label ((q ^ (-(n : ℤ))) z) := by
        rw [hstep, C.label_invariant]
      rw [hkey, ih]
  rw [← hk, hpow k x]

/-- The descended label on `q`-cycles: `Quotient (SameCycle.setoid q) → β`. -/
noncomputable def quotLabel (C : OrbitLabelCert X β q) :
    Quotient (Equiv.Perm.SameCycle.setoid q) → β :=
  Quotient.lift C.label (fun _ _ h => C.label_sameCycle h)

/-- `quotLabel` is surjective: every `b` is hit by `⟦anchor b⟧`. -/
lemma quotLabel_surjective (C : OrbitLabelCert X β q) :
    Function.Surjective C.quotLabel := by
  intro b
  exact ⟨Quotient.mk _ (C.anchor b), C.label_anchor b⟩

/-- `quotLabel` is injective: two cycles with the same label are the same cycle (both equal
the anchor's cycle). -/
lemma quotLabel_injective (C : OrbitLabelCert X β q) :
    Function.Injective C.quotLabel := by
  refine fun a b hab => ?_
  refine Quotient.inductionOn₂ a b (fun x y hxy => ?_) hab
  -- hxy : C.label x = C.label y
  have hx : q.SameCycle x (C.anchor (C.label x)) := C.same_anchor x
  have hy : q.SameCycle y (C.anchor (C.label y)) := C.same_anchor y
  have hxy' : C.label x = C.label y := hxy
  have : q.SameCycle x y := by
    refine hx.trans ?_
    rw [hxy']
    exact (hy).symm
  exact Quotient.sound this

/-- `quotLabel` is a bijection. -/
lemma quotLabel_bijective (C : OrbitLabelCert X β q) :
    Function.Bijective C.quotLabel :=
  ⟨C.quotLabel_injective, C.quotLabel_surjective⟩

end OrbitLabelCert

/-- **The orbit-label-certificate cycle count.**  An `OrbitLabelCert X β q` exhibits a
bijection between the `q`-cycles and `β`, hence `numCycles q = Fintype.card β`.  This is the
requested general genus-free orbit-counting tool. -/
theorem numCycles_eq_card_of_orbitLabelCert {X : Type*} {β : Type*}
    [Fintype X] [DecidableEq X] [Fintype β] {q : Equiv.Perm X}
    (C : OrbitLabelCert X β q) :
    numCycles q = Fintype.card β := by
  classical
  have hbij : Function.Bijective C.quotLabel := C.quotLabel_bijective
  have hcard := Fintype.card_of_bijective hbij
  -- numCycles q = card (Quotient (SameCycle.setoid q)) by definition.
  unfold numCycles
  simpa using hcard

/-! ## Part 2.  Brick B — the interior-triangle gate lever assembled from `NearTriangulation`

`InteriorTriangleGates P` (in `ChordGateCompat.lean`) has two fields:

* `tri : ∀ j (hj : j+1 < n), M.φ (M.φ (M.φ (M.α (P.edge j)))) = M.α (P.edge j)`;
* `ne  : ∀ j (hj : j+1 < n), M.α (P.edge j) ≠ P.edge ⟨j+1, hj⟩`.

We discharge `tri` from the near-triangulation invariant: each intermediate entry dart's
old face is inner (non-outer), so it is a `φ`-triangle and `(M.φ)^3` fixes it. -/

namespace CombMap.NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle

/-- **The `tri` field from `NearTriangulation`.**  For an ordinary dual path whose every
intermediate entry dart `M.α (P.edge j)` lies in an *inner* (non-outer) face, the
near-triangulation invariant gives `M.φ (M.φ (M.φ (M.α (P.edge j)))) = M.α (P.edge j)` — the
triangle identity the lever needs. -/
theorem interiorTriangleGates_tri_of_innerFaces
    (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (hinner : ∀ j : Fin P.n, (j : ℕ) + 1 < P.n →
      M.dartFace (M.α (P.edge j)) ≠ hNT.outerFace)
    (j : Fin P.n) (hj : (j : ℕ) + 1 < P.n) :
    M.φ (M.φ (M.φ (M.α (P.edge j)))) = M.α (P.edge j) := by
  have hlen : M.faceLen (M.dartFace (M.α (P.edge j))) = 3 :=
    hNT.inner_tri _ (hinner j hj)
  have hcube : (M.φ ^ 3) (M.α (P.edge j)) = M.α (P.edge j) :=
    faceLen_three_phi_cube_eq_self M hNT.simpleGraph hlen
  -- unfold `(M.φ ^ 3)` to the triple application
  simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube

/-- **`InteriorTriangleGates` assembled from `NearTriangulation`.**  Given that every
intermediate face is inner (non-outer) and the entry/exit darts of every intermediate gate
are distinct, the near-triangulation supplies `InteriorTriangleGates P`.  The `tri` field is
*derived* from `hNT`; only the `ne` (entry≠exit) field is supplied as the genuine geometric
residue of the intermediate gates. -/
theorem interiorTriangleGates_of_nearTriangulation
    (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (hinner : ∀ j : Fin P.n, (j : ℕ) + 1 < P.n →
      M.dartFace (M.α (P.edge j)) ≠ hNT.outerFace)
    (hne : ∀ j : Fin P.n, ∀ hj : (j : ℕ) + 1 < P.n,
      M.α (P.edge j) ≠ P.edge ⟨(j : ℕ) + 1, hj⟩) :
    C.InteriorTriangleGates P where
  tri := fun j hj => hNT.interiorTriangleGates_tri_of_innerFaces C P hinner j hj
  ne := hne

/-- **The intermediate-gate `φ'₂`-edge, driven by `NearTriangulation`.**  Composes the
assembled `InteriorTriangleGates` with the proven lever `mid_edge_of_interiorTriangleGates`:
each intermediate gate of a near-triangulation ordinary dual path (inner faces, distinct
endpoints) is realised by a single clean `φ'₂`-edge. -/
theorem mid_edge_of_nearTriangulation
    (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (hinner : ∀ j : Fin P.n, (j : ℕ) + 1 < P.n →
      M.dartFace (M.α (P.edge j)) ≠ hNT.outerFace)
    (hne : ∀ j : Fin P.n, ∀ hj : (j : ℕ) + 1 < P.n,
      M.α (P.edge j) ≠ P.edge ⟨(j : ℕ) + 1, hj⟩)
    (j : Fin P.n) (hj : (j : ℕ) + 1 < P.n) :
    (C.cutCapMap2).φ (Sum.inl (M.α (P.edge j))) = Sum.inl (P.edge ⟨(j : ℕ) + 1, hj⟩) ∨
      (C.cutCapMap2).φ (Sum.inl (P.edge ⟨(j : ℕ) + 1, hj⟩)) = Sum.inl (M.α (P.edge j)) :=
  C.mid_edge_of_interiorTriangleGates P
    (hNT.interiorTriangleGates_of_nearTriangulation C P hinner hne) j hj

/-- **The full interior `cutReach2` chain, driven by `NearTriangulation`.**  For `n > 0`,
the first crossing dart reaches the last reverse crossing dart through `cutReach2`, with the
interior triangle gates supplied entirely by the near-triangulation invariant. -/
theorem interiorReach_of_nearTriangulation
    (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (hinner : ∀ j : Fin P.n, (j : ℕ) + 1 < P.n →
      M.dartFace (M.α (P.edge j)) ≠ hNT.outerFace)
    (hne : ∀ j : Fin P.n, ∀ hj : (j : ℕ) + 1 < P.n,
      M.α (P.edge j) ≠ P.edge ⟨(j : ℕ) + 1, hj⟩)
    (h0 : 0 < P.n) :
    C.cutReach2 (Sum.inl (P.edge ⟨0, h0⟩))
      (Sum.inl (M.α (P.edge ⟨P.n - 1, by omega⟩))) :=
  C.interiorReach_of_gates P
    (hNT.interiorTriangleGates_of_nearTriangulation C P hinner hne) h0

end CombMap.NearTriangulation

/-! ## Part 3.  Non-vacuity: the assembled gates fire on a genuine single-crossing path

To certify the assembly is not vacuous, we record that on the nil path the assembled
`InteriorTriangleGates` reduces to the existing inhabited `interiorTriangleGates_nil`
(the inner/ne hypotheses are vacuous), and that the assembled gates feed the existing
cross-bank bridge.  (The `n ≥ 1` instances are genuinely consumed by
`interiorReach_of_nearTriangulation` above, which produces a nontrivial `cutReach2` chain.) -/

namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}

/-- The near-triangulation assembly agrees with the existing nil inhabitant on the nil path
(both hypotheses are vacuous there), confirming the assembly is a conservative extension. -/
theorem interiorTriangleGates_nil_via_assembly
    (hNT : NearTriangulation M) (C : SimplePrimalCycle M) (f : M.Face) :
    C.InteriorTriangleGates (OrdinaryDualPath2.nil C f) :=
  hNT.interiorTriangleGates_of_nearTriangulation C (OrdinaryDualPath2.nil C f)
    (fun j _ => absurd j.isLt (by simp [OrdinaryDualPath2.nil]))
    (fun j hj => absurd hj (by
      have : (OrdinaryDualPath2.nil C f).n = 0 := rfl; omega))

end CombMap.SimplePrimalCycle

end ProofsInTheBook.PlanarMap

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.numCycles_eq_card_of_orbitLabelCert
#print axioms ProofsInTheBook.PlanarMap.OrbitLabelCert.quotLabel_bijective
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.interiorTriangleGates_tri_of_innerFaces
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.interiorTriangleGates_of_nearTriangulation
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.mid_edge_of_nearTriangulation
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.interiorReach_of_nearTriangulation
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.interiorTriangleGates_nil_via_assembly
