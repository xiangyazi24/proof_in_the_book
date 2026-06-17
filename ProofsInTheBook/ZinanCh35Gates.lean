import ProofsInTheBook.ZinanCh35Split

/-!
# Chapter 35: the connectivity gates, closed (the LAST Ch35 residue)

`ZinanCh35Split.lean` closed the whole F-side of the corrected Chapter 35 surgery and
reduced the chapter's Jordan headline (`jordan_simple_cycle2_of_gates`,
`sphereChordSeparation_of_gates`, `separates_of_gates`) to ONLY the connectivity-side
gate data

  `gateCompat' : ∀ i, DualReachableAvoidingCycle M C (faceLeft i) (faceRight i) →
      ∃ P : OrdinaryDualPath2, EndpointCapLink i P ∧ InteriorTriangleGates P`.

This file proves that gate data is a **theorem** — for every `SimplePrimalCycle` on
every `CombMap`, from the *bare* dual-reachability hypothesis alone (no triangles, no
near-triangulation, no fragment input).  Hence `ChordJordanInput'` holds outright
(`chordJordanInput'_holds`) and the chapter's chord-separation headline becomes
conditional ONLY on the hypotheses the `NearTriangulation` context itself provides
(the chord-cycle data `hsub`/`hleft`/`hright`; connectivity and `χ = 2` come from
`hNT.sphere`).

## Why the bare dual path suffices (the seam-conjugacy transport)

The bridge design (`CH35_BRIDGE_DESIGN.md` §6–§7) warned that a bare face sequence is
"too weak": a straddling old face teleports the lift, and within-face fragment
connectivity ("entry and exit fragment of one old face are connected") is FALSE.  Both
points are correct **at the `SameFragment` layer** — but the gate consumers live at the
`cutReach2` layer (global reachability of the corrected cut map), and there the seam
conjugacy of `ZinanCh35Split.lean` is decisive:

  `seamSwap_phi2_conj : e · φ'₂ · e⁻¹ = φ ⊕ (nextIdx ⊕ prevIdx)`

says φ'₂ is the *exact* conjugate of the old face permutation (plus the two seam
rotations) under the seam swap `e`.  Consequently **every old face survives as a single
φ'₂-cycle**, with each forward cycle dart `dart j` replaced by the cap `c_j⁻ = e⁻¹ (dart j)`
and each reverse cycle dart `α (dart j)` replaced by `c_j⁺` — and a single φ'₂-cycle is
`cutReach2`-connected *by definition* (`cutReach2_of_phi_sameCycle`).  The "teleport"
through a straddling face is a legitimate walk of the corrected map.  So:

* **same old face ⇒ `cutReach2`** between the seam-substituted carriers
  (`cutReach2_seamCarrier_of_dartFace_eq`);
* each dual-path crossing is one `α'`-step across an uncut edge
  (`cutReach2_across_uncut_dual_gate`);
* at the endpoints, `α'` attaches `inl (dart i)` to `c_i⁺` and `inl (α (dart i))` to
  `c_i⁻` (`cutAlpha_dart` / `cutAlpha_alpha_dart`).

Chaining these along the bare `DualReachableAvoidingCycle` face sequence yields the
cross-bank bridge `cutReach2 (inl (dart i)) (inl (α (dart i)))`
(`crossBankBridge_of_dualReachable`).  The gate data then follows by the **nil-path
instantiation**: `EndpointCapLink i (nil)` *is* the bridge (`endpointCapLink_nil`), and
`InteriorTriangleGates (nil)` is vacuous (`interiorTriangleGates_nil`).  No triangle
hypothesis is ever needed — the `InteriorTriangleGates` lever of `ChordGateCompat.lean`
was a *sufficient* route for long paths, but the corrected surgery's cap channel
short-circuits it.

## Genus sanity (why this does not prove too much)

The bridge is **conditional on the dual path** — and must be: on the sphere the cut map
has two components (kernel anchors `c = 2` in `PlanarMapCutCapEval.lean`), so the bridge
is *not* unconditionally provable; it fires exactly when the two banks' faces are
dual-connected avoiding the cycle, which on a sphere with `χ = 2` is what
`jordan_simple_cycle2_of_gates` refutes.  On the torus (`χ = 0`) an essential cycle has
dual-reachable sides and the cut map *is* connected — the bridge is then true and the
Euler contradiction correctly fails to fire.  Nothing here uses `eulerChar`.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ProofsInTheBook.PlanarMap

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

open CutCapCount

variable {M : CombMap D}

/-! ## Section 1.  The seam-conjugacy transport of `SameCycle`

`seamSwap_phi2_conj` gives `φ'₂ = e⁻¹ · seamModel · e`; conjugation transports
`SameCycle` pointwise, so a `seamModel`-orbit statement becomes a `φ'₂`-orbit statement
on the `e`-preimages. -/

/-- `φ'₂` as an explicit conjugate of the seam model (the inverted form of
`seamSwap_phi2_conj`, shaped for `conj_pow`). -/
lemma cutCapPhi2_eq_conj (C : SimplePrimalCycle M) :
    (C.cutCapMap2).φ = C.seamSwap⁻¹ * C.seamModel * C.seamSwap⁻¹⁻¹ := by
  rw [inv_inv, ← C.seamSwap_phi2_conj]
  group

/-- **`SameCycle` transport through the seam conjugacy**: a `seamModel`-orbit relation
between the `e`-images is a `φ'₂`-orbit relation. -/
lemma cutCapPhi2_sameCycle_of_seamModel (C : SimplePrimalCycle M) {x y : C.CutDart}
    (h : C.seamModel.SameCycle (C.seamSwap x) (C.seamSwap y)) :
    ((C.cutCapMap2).φ).SameCycle x y := by
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  refine ⟨(m : ℤ), ?_⟩
  rw [zpow_natCast, C.cutCapPhi2_eq_conj, conj_pow, inv_inv,
    Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hm]
  exact inv_eq_iff_eq.mpr rfl

/-- `seamModel` restricted to the `inl` (ordinary-dart) summand is the old face
permutation `φ`. -/
lemma seamModel_sameCycle_inl_iff (C : SimplePrimalCycle M) (d₁ d₂ : D) :
    C.seamModel.SameCycle (Sum.inl d₁) (Sum.inl d₂) ↔ M.φ.SameCycle d₁ d₂ := by
  unfold seamModel
  exact CutCapCount.sameCycle_sumCongr_inl_inl _ _ _ _

/-! ## Section 2.  Same old face ⇒ `cutReach2` between the seam carriers

The *seam carrier* of a dart `d` is `e⁻¹ (inl d) = seamSwapInvFun (inl d)`: the
ordinary dart itself when `d` is non-cycle, the cap `c_j⁻` when `d = dart j`, and the
cap `c_j⁺` when `d = α (dart j)`.  By the conjugacy, the carriers of one old face form
one φ'₂-cycle. -/

/-- **Same old face ⇒ same φ'₂-cycle of the seam carriers ⇒ `cutReach2`.**  This is the
within-face connectivity that the corrected surgery *does* provide at the global
reachability layer (the `SameFragment`-layer version is false; this one is a theorem). -/
lemma cutReach2_seamCarrier_of_dartFace_eq (C : SimplePrimalCycle M) {d₁ d₂ : D}
    (h : M.dartFace d₁ = M.dartFace d₂) :
    C.cutReach2 (C.seamSwapInvFun (Sum.inl d₁)) (C.seamSwapInvFun (Sum.inl d₂)) := by
  apply C.cutReach2_of_phi_sameCycle
  apply C.cutCapPhi2_sameCycle_of_seamModel
  rw [seamSwap_apply, seamSwap_apply,
    C.seamSwap_rightInverse (Sum.inl d₁), C.seamSwap_rightInverse (Sum.inl d₂)]
  exact (C.seamModel_sameCycle_inl_iff d₁ d₂).mpr (sameCycle_phi_of_dartFace_eq h)

/-- **Two non-cycle darts of one old face are `cutReach2`-connected** (the carriers are
the darts themselves).  This is the precise `cutReach2`-layer refutation of the
"no-teleport data is irreducible input" worry: for *global* reachability the bare
co-facehood is enough. -/
theorem cutReach2_of_dartFace_eq (C : SimplePrimalCycle M) {d₁ d₂ : D}
    (h₁ : d₁ ∉ C.dartSet) (h₂ : d₂ ∉ C.dartSet)
    (h : M.dartFace d₁ = M.dartFace d₂) :
    C.cutReach2 (Sum.inl d₁) (Sum.inl d₂) := by
  have := C.cutReach2_seamCarrier_of_dartFace_eq h
  rwa [C.seamSwapInvFun_other h₁, C.seamSwapInvFun_other h₂] at this

/-! ## Section 3.  The walk along the bare dual path

Induct along `DualReachableAvoidingCycle`: within each face, Section 2; across each
uncut crossing, one `α'`-step (`cutReach2_across_uncut_dual_gate`).  The carriers make
the statement uniform — no case split on whether the endpoint darts are cycle darts. -/

/-- **Carrier reach along a bare cycle-avoiding dual path.**  If `f` and `g` are
dual-reachable avoiding the cycle edges, then the seam carriers of *any* dart of `f`
and *any* dart of `g` are `cutReach2`-connected. -/
lemma cutReach2_seamCarrier_of_dualReachable (C : SimplePrimalCycle M) {f g : M.Face}
    (hpath : DualReachableAvoidingCycle M C f g) :
    ∀ {d₁ d₂ : D}, M.dartFace d₁ = f → M.dartFace d₂ = g →
      C.cutReach2 (C.seamSwapInvFun (Sum.inl d₁)) (C.seamSwapInvFun (Sum.inl d₂)) := by
  have hpath' : Relation.ReflTransGen (DualAvoidsCycleStep M C) f g := hpath
  clear hpath
  induction hpath' with
  | refl =>
      intro d₁ d₂ h₁ h₂
      exact C.cutReach2_seamCarrier_of_dartFace_eq (h₁.trans h₂.symm)
  | tail hstep hcross ih =>
      intro d₁ d₂ h₁ h₂
      obtain ⟨c, hcut, hcf, hcg⟩ := hcross
      have hc : c ∉ C.dartSet := C.notMem_dartSet_of_dartEdge_notMem hcut
      have hαc : M.α c ∉ C.dartSet := C.alpha_notMem_dartSet hc
      -- carrier d₁ ⇝ carrier c (induction hypothesis up to the previous face)
      have h1 := ih h₁ hcf
      -- inl c ⇝ inl (α c): one α'-step across the uncut crossing edge
      have h2 : C.cutReach2 (Sum.inl c) (Sum.inl (M.α c)) :=
        C.cutReach2_across_uncut_dual_gate hcut
      -- carrier (α c) ⇝ carrier d₂ (same final face)
      have h3 := C.cutReach2_seamCarrier_of_dartFace_eq (d₁ := M.α c) (d₂ := d₂)
        (hcg.trans h₂.symm)
      rw [C.seamSwapInvFun_other hc] at h1
      rw [C.seamSwapInvFun_other hαc] at h3
      exact C.cutReach2_trans (C.cutReach2_trans h1 h2) h3

/-! ## Section 4.  The cross-bank bridge from the bare dual path

At a cycle edge `e_i`: the carrier of `dart i` is `c_i⁻` and the carrier of
`α (dart i)` is `c_i⁺`; the `α'`-pairings `inl (dart i) ↔ c_i⁺` and
`inl (α (dart i)) ↔ c_i⁻` attach the two banks to the two carriers.  The dual path
between `faceLeft i` and `faceRight i` connects the carriers, hence the banks. -/

/-- **The cross-bank bridge from bare dual reachability** — the genuine connectivity
content of the Chapter 35 gates, with no triangle or fragment input.  (It is *not*
provable without `hpath`: on the sphere the cut map has two components.) -/
theorem crossBankBridge_of_dualReachable (C : SimplePrimalCycle M) (i : Fin C.len)
    (hpath : DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i)) :
    C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i))) := by
  -- carrier (dart i) = c_i⁻ ⇝ carrier (α (dart i)) = c_i⁺
  have hmid := C.cutReach2_seamCarrier_of_dualReachable hpath
    (d₁ := C.dart i) (d₂ := M.α (C.dart i)) rfl rfl
  rw [C.seamSwapInvFun_dart, C.seamSwapInvFun_alpha_dart] at hmid
  -- inl (dart i) ⇝ c_i⁺ (one α'-step)
  have h1 : C.cutReach2 (Sum.inl (C.dart i)) (Sum.inr (Sum.inl i)) := by
    have := C.cutReach2_of_alpha (Sum.inl (C.dart i))
    rwa [cutCapMap2_alpha_apply, C.cutAlpha_dart] at this
  -- c_i⁻ ⇝ inl (α (dart i)) (one α'-step, reversed)
  have h3 : C.cutReach2 (Sum.inr (Sum.inr i)) (Sum.inl (M.α (C.dart i))) := by
    have := C.cutReach2_of_alpha (Sum.inl (M.α (C.dart i)))
    rw [cutCapMap2_alpha_apply, C.cutAlpha_alpha_dart] at this
    exact C.cutReach2_symm this
  exact C.cutReach2_trans (C.cutReach2_trans h1 (C.cutReach2_symm hmid)) h3

/-! ## Section 5.  The gate data, supplied

The nil ordinary path turns the bridge into `EndpointCapLink`
(`endpointCapLink_nil`), and `InteriorTriangleGates` is vacuous on it
(`interiorTriangleGates_nil`).  So the entire `gateCompat'` field of
`ChordJordanInput'` is a theorem. -/

/-- **`EndpointCapLink`, supplied** from bare dual reachability (on the nil path). -/
theorem endpointCapLink_of_dualReachable (C : SimplePrimalCycle M) (i : Fin C.len)
    (hpath : DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i)) :
    C.EndpointCapLink i (OrdinaryDualPath2.nil C (C.faceLeft i)) :=
  C.endpointCapLink_nil i (C.faceLeft i) (C.crossBankBridge_of_dualReachable i hpath)

/-- **The connectivity gate `gateCompat'`, closed**: for every cycle edge, bare dual
reachability of its two sides yields an ordinary dual path carrying both
`EndpointCapLink` and `InteriorTriangleGates`. -/
theorem gateCompat'_of_dualReachable (C : SimplePrimalCycle M) (i : Fin C.len)
    (hpath : DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i)) :
    ∃ P : C.OrdinaryDualPath2, C.EndpointCapLink i P ∧ C.InteriorTriangleGates P :=
  ⟨OrdinaryDualPath2.nil C (C.faceLeft i),
    C.endpointCapLink_of_dualReachable i hpath,
    C.interiorTriangleGates_nil (C.faceLeft i)⟩

/-- **`ChordJordanInput'` is a theorem** for every simple primal cycle on every
combinatorial map: the face core is `numCyclesCutPhi2_holds`
(`ZinanCh35Split.lean`), the gate supplier is `gateCompat'_of_dualReachable`. -/
theorem chordJordanInput'_holds (C : SimplePrimalCycle M) : C.ChordJordanInput' :=
  ⟨C.numCyclesCutPhi2_holds, fun i hpath => C.gateCompat'_of_dualReachable i hpath⟩

/-! ## Section 6.  The discharged Jordan headline -/

/-- **The discrete Jordan separation for the corrected surgery, with all gates
discharged**: on a connected map of Euler characteristic `2`, the two sides of every
edge of a simple primal cycle are *not* dual-connected avoiding the cycle.
Conditional only on `M.Connected` and `M.eulerChar = 2`. -/
theorem jordan_simple_cycle2_unconditional (C : SimplePrimalCycle M)
    (hchi : M.eulerChar = 2) (hconn : M.Connected) (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2_of_gates hchi
    (fun j hp => C.connectivity_of_input' hconn C.chordJordanInput'_holds j hp) i

/-- The sphere-map form (`IsSphereMap` = connected + `χ = 2`). -/
theorem jordan_simple_cycle2_of_sphere (C : SimplePrimalCycle M)
    (hM : M.IsSphereMap) (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2_unconditional hM.2 hM.1 i

end SimplePrimalCycle

end CombMap

namespace CombMap.NearTriangulation

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle

/-- **`SphereChordSeparation` with the connectivity gates discharged**: conditional
only on the chord-cycle data (`hsub`, `i₀`, `hleft`, `hright`) that the chapter's own
`NearTriangulation` context supplies; the gate data of
`sphereChordSeparation_of_gates` is now the theorem `gateCompat'_of_dualReachable`. -/
theorem sphereChordSeparation_closed {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h))) :
    hNT.SphereChordSeparation h :=
  hNT.sphereChordSeparation_of_gates h C hsub
    (fun i hp => C.gateCompat'_of_dualReachable i hp) i₀ hleft hright

/-- **`Separates` with the connectivity gates discharged.** -/
theorem separates_closed {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  hNT.separates_of_gates data C hsub
    (fun i hp => C.gateCompat'_of_dualReachable i hp) i₀ hleft hright

end CombMap.NearTriangulation

/-! ## Non-vacuity / faithfulness notes (§3.3)

* The conditional theorems are not vacuous: their hypotheses are the chapter's own
  context (`M.Connected`, `χ = 2`, the chord-cycle data), all instantiated by the
  concrete chord∪arc cycle of `DartArc.lean` and the tetrahedron base anchors.
* `crossBankBridge_of_dualReachable` genuinely consumes its `hpath` input (the carrier
  walk is built by induction on it); the bridge is *known* to be unprovable without it
  (kernel anchors: the cut sphere map has `c = 2` components).
* `gateCompat'_of_dualReachable` supplies the *existential* gate data demanded
  verbatim by `ChordJordanInput'.gateCompat'` — no field is weakened: the nil path is
  a legitimate `OrdinaryDualPath2`, its `EndpointCapLink` is exactly the cross-bank
  bridge (the genuine discrete-Jordan datum), and its `InteriorTriangleGates` is
  vacuously true *on the nil path* (the structure's quantifiers range over its `n = 0`
  crossings), not weakened in general. -/

namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}

/-- The bridge construction is not discarding its input: specialised to a one-step
dual path, it produces the bridge from a single crossing dart's data. -/
example (C : CombMap.SimplePrimalCycle M) (i : Fin C.len) (c : D)
    (hcut : M.dartEdge c ∉ C.edgeSet)
    (hcf : M.dartFace c = C.faceLeft i)
    (hcg : M.dartFace (M.α c) = C.faceRight i) :
    C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i))) :=
  C.crossBankBridge_of_dualReachable i
    (Relation.ReflTransGen.single ⟨c, hcut, hcf, hcg⟩)

end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.cutCapPhi2_eq_conj
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.cutCapPhi2_sameCycle_of_seamModel
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.cutReach2_seamCarrier_of_dartFace_eq
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.cutReach2_of_dartFace_eq
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.cutReach2_seamCarrier_of_dualReachable
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.crossBankBridge_of_dualReachable
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.endpointCapLink_of_dualReachable
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.gateCompat'_of_dualReachable
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.chordJordanInput'_holds
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.jordan_simple_cycle2_unconditional
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.jordan_simple_cycle2_of_sphere
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.sphereChordSeparation_closed
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.separates_closed
