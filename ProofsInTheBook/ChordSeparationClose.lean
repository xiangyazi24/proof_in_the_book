import ProofsInTheBook.ChordGateCompat

/-!
# Closing Chapter 35's chord separation: `SphereChordSeparation` from the corrected
  combinatorial input (cap-channel endpoints + interior triangle gates)

`ChordSeparation.lean` reduced `SphereChordSeparation` to the bundle `ChordJordanInput`,
whose `gateCompat` field demanded, *per cycle edge*, an ordinary dual path every gate of
which is a single within-old-face `φ'₂`-edge (`GateFragmentCompatible`).  The prior round
(`ChordGateCompat.lean`) proved that field **uninhabitable**
(`gateFragmentCompatible_uninhabited`): the corrected cut-and-cap surgery reroutes the
cycle darts into the cap chain (`φ'₂ (inl (dart i)) = inl (dart (nextIdx i))`), so the
endpoint cycle dart is `φ'₂`-fragment-isolated and **no** within-face `φ'₂`-edge can link
it to a crossing dart.  The genuine endpoint connectivity flows through the **cap
channel** (`cutReach2`), not a `φ'₂`-edge.

This file builds the *corrected* input `ChordJordanInput'` and drives the entire chord
separation through it, **bypassing** the `FragmentDualPath2`/`FragmentCompatible2`
machinery (whose endpoint `SameFragment` links inherit the same uninhabitable
fragment-isolation).  Concretely:

* **`faceCore`** (`NumCyclesCutPhi2`) — the kernel-anchored corrected face count, reused
  verbatim from `ChordSeparation`.
* **Intermediate gates** (`InteriorTriangleGates`, the M-lesson recoverable lever from
  `ChordGateCompat.lean`) — each visited inner face is a `φ`-triangle and the entry/exit
  gate darts are non-cycle, so the corrected map joins them by a single *clean* `φ'₂`-edge
  (`mid_edge_of_interiorTriangleGates`), which lifts to a `cutReach2` step
  (`cutReach2_of_phi_step`).  We chain these into the **interior reach**
  `cutReach2 (inl (edge 0)) (inl (α (edge (n-1))))` (`interiorReach_of_gates`).
* **Endpoints** (`EndpointCapLink`, the cap channel) — the cross-bank link
  `cutReach2 (inl (dart i)) (inl (α (dart i)))`, threaded through the cap chain.  This is
  the genuine discrete-Jordan residue; it is **inhabited** (`endpointCapLink_nil`), never
  vacuous, and never the false within-face `φ'₂`-edge.

The connectivity of the corrected cut map is then assembled directly via
`cutCapMap2_connected_of_reachesBank_of_bridge` (Part-A `ReachesBank2` from
`M.Connected` + the *theorem* `sidesReach2_concrete`, plus the cross-bank bridge built
from the cap channel and the interior reach).  Feeding this connectivity supplier into the
walk-layer Euler contradiction `jordan_simple_cycle2_walk` yields
`¬ DualReachableAvoidingCycle`, hence (via `separates_of_nearTriangulation`)
`SphereChordSeparation`.

No `sorry` / `axiom` / `admit` / `native_decide`.  No vacuous conditional (the endpoint
residue is `endpointCapLink_nil`-inhabited).

## The residue

The only genuinely-irreducible discrete-Jordan content surviving is the cap-channel
cross-bank link `EndpointCapLink` (supplied per cycle edge, under the dual-reachability
hypothesis).  Everything else — `faceCore`, the Euler inequality, `SidesReach2`,
`ReachesBank2`, and *all* interior triangle gates — is discharged here.  `EndpointCapLink`
is the corrected datum that the uninhabitable `gateCompat` should have demanded.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open ProofsInTheBook.PlanarMap.CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}

/-! ## Section 1.  The interior reach from the triangle gates

Each crossing edge gives an `α'`-uncut bridge `inl (edge j) ⇝ inl (α (edge j))`; each
intermediate gate gives a clean `φ'₂`-edge `inl (α (edge j)) ⇝ inl (edge (j+1))` (lifted
to `cutReach2`).  Chaining them connects the first crossing dart to the last reverse
crossing dart, **entirely through `cutReach2`** — no `SameFragment`/`FragmentDualPath2`,
hence immune to the cycle-dart fragment isolation. -/

/-- A single intermediate gate, lifted to a `cutReach2` step.  From
`mid_edge_of_interiorTriangleGates` (a clean `φ'₂`-edge in either direction) and
`cutReach2_of_phi_step`. -/
lemma cutReach2_midGate (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (hg : C.InteriorTriangleGates P) (j : Fin P.n) (hj : (j : ℕ) + 1 < P.n) :
    C.cutReach2 (Sum.inl (M.α (P.edge j))) (Sum.inl (P.edge ⟨(j : ℕ) + 1, hj⟩)) := by
  rcases C.mid_edge_of_interiorTriangleGates P hg j hj with hphi | hphi
  · -- φ'₂ (inl (α (edge j))) = inl (edge (j+1))
    have := C.cutReach2_of_phi_step (Sum.inl (M.α (P.edge j)))
    rwa [hphi] at this
  · -- φ'₂ (inl (edge (j+1))) = inl (α (edge j)) — use the reverse step
    have := C.cutReach2_of_phi_step (Sum.inl (P.edge ⟨(j : ℕ) + 1, hj⟩))
    rw [hphi] at this
    exact C.cutReach2_symm this

/-- A single crossing, lifted to a `cutReach2` step (the `α'`-uncut bridge). -/
lemma cutReach2_cross (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2) (j : Fin P.n) :
    C.cutReach2 (Sum.inl (P.edge j)) (Sum.inl (M.α (P.edge j))) :=
  C.cutReach2_across_uncut_dual_gate (P.edge_uncut j)

/-- **The interior reach (prefix form).**  For every `k < n`, the first crossing dart
`inl (edge 0)` reaches the reverse crossing dart `inl (α (edge k))`, by chaining `k`
crossings and `k` intermediate gates. -/
lemma interiorReach_prefix (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (hg : C.InteriorTriangleGates P) (h0 : 0 < P.n) :
    ∀ k : ℕ, ∀ hk : k < P.n,
      C.cutReach2 (Sum.inl (P.edge ⟨0, h0⟩)) (Sum.inl (M.α (P.edge ⟨k, hk⟩)))
  | 0, hk => by
      -- base: just the first crossing
      have : (⟨0, hk⟩ : Fin P.n) = ⟨0, h0⟩ := rfl
      rw [this]
      exact C.cutReach2_cross P ⟨0, h0⟩
  | k + 1, hk => by
      have hk' : k < P.n := by omega
      have hkj : (k : ℕ) + 1 < P.n := by omega
      -- reach to α (edge k)
      have ih := C.interiorReach_prefix P hg h0 k hk'
      -- gate: α (edge k) ⇝ edge (k+1)
      have hgate := C.cutReach2_midGate P hg ⟨k, hk'⟩ (by simpa using hkj)
      -- crossing: edge (k+1) ⇝ α (edge (k+1))
      have hcross := C.cutReach2_cross P ⟨k + 1, hk⟩
      have hgate' :
          C.cutReach2 (Sum.inl (M.α (P.edge ⟨k, hk'⟩))) (Sum.inl (P.edge ⟨k + 1, hk⟩)) := by
        have he : (⟨(⟨k, hk'⟩ : Fin P.n) + 1, by simpa using hkj⟩ : Fin P.n)
            = ⟨k + 1, hk⟩ := by apply Fin.ext; simp
        rw [he] at hgate; exact hgate
      exact (ih.trans hgate').trans hcross

/-- **The interior reach.**  When `n > 0`, the first crossing dart reaches the last
reverse crossing dart through `cutReach2`. -/
lemma interiorReach_of_gates (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (hg : C.InteriorTriangleGates P) (h0 : 0 < P.n) :
    C.cutReach2 (Sum.inl (P.edge ⟨0, h0⟩)) (Sum.inl (M.α (P.edge ⟨P.n - 1, by omega⟩))) :=
  C.interiorReach_prefix P hg h0 (P.n - 1) (by omega)

/-! ## Section 2.  The cross-bank bridge from the cap-channel endpoints + interior reach

Combining the two endpoint cap-channel links (`EndpointCapLink`) with the interior reach
gives the cross-bank bridge `cutReach2 (inl (dart i)) (inl (α (dart i)))` — the exact
`hbridge` consumed by `cutCapMap2_connected_of_reachesBank_of_bridge`.  No `SameFragment`
ever appears; the cycle-dart fragment isolation is irrelevant because the whole walk is
at the `cutReach2` layer. -/

/-- **The cross-bank bridge.**  From the endpoint cap-channel link and the interior
triangle gates, the forward cycle bank reaches the reverse cycle bank in the corrected
cut map.  (`n = 0`: the endpoint link is the bridge directly; `n > 0`: forward dart ⇝
first crossing ⇝ [interior reach] ⇝ last reverse crossing ⇝ reverse dart.) -/
theorem crossBankBridge_of_endpointCapLink (C : SimplePrimalCycle M) (i : Fin C.len)
    (P : C.OrdinaryDualPath2) (hlink : C.EndpointCapLink i P)
    (hg : C.InteriorTriangleGates P) :
    C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i))) := by
  obtain ⟨hstart, hend, hnil⟩ := hlink
  by_cases h0 : 0 < P.n
  · -- dart i ⇝ edge 0 ⇝ α (edge (n-1)) ⇝ α (dart i)
    have hs : C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (P.edge ⟨0, h0⟩)) := hstart h0
    have hmid := C.interiorReach_of_gates P hg h0
    have he : C.cutReach2 (Sum.inl (M.α (C.dart i)))
        (Sum.inl (M.α (P.edge ⟨P.n - 1, by omega⟩))) := hend h0
    exact (hs.trans hmid).trans (C.cutReach2_symm he)
  · -- n = 0: the endpoint link is the cross-bank bridge directly
    have hn0 : P.n = 0 := by omega
    exact hnil hn0

/-! ## Section 3.  The connectivity supplier (bypassing `FragmentDualPath2`)

`cutCapMap2_connected_of_reachesBank_of_bridge` needs exactly (i) `ReachesBank2 i` —
discharged by `M.Connected` + the *theorem* `sidesReach2_concrete` — and (ii) the
cross-bank bridge, supplied by Section 2 from the corrected endpoint/interior data.  This
is the corrected connectivity parameter of `jordan_simple_cycle2_walk`, with the
uninhabitable `gateCompat`/`FragmentCompatible2` route entirely sidestepped. -/

/-- **Connectivity from the corrected gate data** (under the dual-reachability
hypothesis).  Given `M.Connected`, the endpoint cap-channel link, and the interior
triangle gates of *some* extracted ordinary path, the corrected cut map is connected. -/
theorem cutCapMap2_connected_of_corrected (C : SimplePrimalCycle M) (i : Fin C.len)
    (hconn : M.Connected)
    (P : C.OrdinaryDualPath2) (hlink : C.EndpointCapLink i P)
    (hg : C.InteriorTriangleGates P) :
    (C.cutCapMap2).Connected :=
  C.cutCapMap2_connected_of_reachesBank_of_bridge i
    (C.reachesBank2_of_connected i hconn (C.sidesReach2_concrete i))
    (C.crossBankBridge_of_endpointCapLink i P hlink hg)

/-! ## Section 4.  The corrected residue bundle `ChordJordanInput'`

Carries the kernel face core, and a per-edge supplier that — *from any cycle-avoiding
dual path between the two sides of `e_i`* — produces an ordinary dual path together with
its cap-channel endpoint link and its interior triangle gates.  This is the corrected
analogue of `ChordJordanInput`: the uninhabitable within-face `φ'₂`-edge endpoint
requirement of `GateFragmentCompatible` is replaced by the cap-channel `EndpointCapLink`,
and the intermediate gates are the recoverable `InteriorTriangleGates`. -/

/-- **The corrected minimal chord-separation residue.** -/
structure ChordJordanInput' (C : SimplePrimalCycle M) : Prop where
  /-- The corrected face count `numCycles φ'₂ = F + 2` (kernel-anchored). -/
  faceCore : C.NumCyclesCutPhi2
  /-- Per-edge supplier: from a cycle-avoiding dual path, an ordinary dual path carrying
  the **cap-channel endpoint link** (`EndpointCapLink`, the genuine discrete-Jordan datum)
  and the **interior triangle gates** (`InteriorTriangleGates`, the recoverable lever). -/
  gateCompat' : ∀ i : Fin C.len,
    DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
      ∃ P : C.OrdinaryDualPath2, C.EndpointCapLink i P ∧ C.InteriorTriangleGates P

/-- The corrected connectivity parameter of `jordan_simple_cycle2_walk`, discharged from
the corrected residue bundle. -/
theorem connectivity_of_input' (C : SimplePrimalCycle M) (hconn : M.Connected)
    (hin : C.ChordJordanInput') (i : Fin C.len)
    (hpath : DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i)) :
    (C.cutCapMap2).Connected := by
  obtain ⟨P, hlink, hg⟩ := hin.gateCompat' i hpath
  exact C.cutCapMap2_connected_of_corrected i hconn P hlink hg

end CombMap.SimplePrimalCycle

/-! ## Section 5.  The chord separation from the corrected residue bundle

We re-derive the separation chain with the corrected connectivity, running the *existing*
walk-layer Euler contradiction `jordan_simple_cycle2_walk` (which internally uses the
kernel face core, the Euler hypothesis `M.eulerChar = 2`, and the unconditional
`cutCapMap2_chi_le`), then the genus-0 reduction `separates_of_nearTriangulation`. -/

namespace CombMap.NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle

/-- **`SphereChordSeparation` from the corrected residue bundle** (cap-channel endpoints
+ interior triangle gates).  Conditional only on `ChordJordanInput'` and the chord-cycle
data; `chi_le`, `SidesReach2`, `ReachesBank2`, the interior gates, and the Euler count are
all discharged. -/
theorem sphereChordSeparation_of_input' {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hin : C.ChordJordanInput')
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h))) :
    hNT.SphereChordSeparation h := by
  intro hreach
  -- lift the chord-split adjacency path to a cycle-avoiding dual path between the sides
  have hpath : DualReachableAvoidingCycle M C
      (M.dartFace (hNT.chordDart h)) (M.dartFace (M.α (hNT.chordDart h))) :=
    hNT.reachable_dualAvoidsCycle_of_chordSplitAdj C hsub hreach
  rw [← hleft, ← hright] at hpath
  -- run the walk-layer Euler contradiction with the corrected connectivity supplier
  exact C.jordan_simple_cycle2_walk hin.faceCore
    (fun i hp => C.connectivity_of_input' hNT.sphere.1 hin i hp)
    hNT.sphere.2 C.cutCapMap2_chi_le i₀ hpath

/-- **The chord separates** (`Separates` form), from the corrected residue bundle. -/
theorem separates_of_input' {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hin : C.ChordJordanInput')
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  data.separates_of_nearTriangulation
    (hNT.sphereChordSeparation_of_input' data.chord C hsub hin i₀ hleft hright)

end CombMap.NearTriangulation

/-! ## Section 6.  Non-vacuity of the corrected residue (the §3.3 anti-impostor check)

The corrected input must not be a vacuous premise.  The endpoint datum `EndpointCapLink`
is inhabited (`endpointCapLink_nil`: the `n = 0` nil path satisfies it from a single
cross-bank `cutReach2`), and `InteriorTriangleGates` is inhabited on the nil path
(vacuously over its empty crossing set), so a `ChordJordanInput'` supplier producing the
nil path with a genuine cross-bank link is satisfiable whenever the faces coincide on a
single chord-incident triangle.  Crucially the residue is **genuine new content** relative
to the broken `gateCompat`: the latter was `gateFragmentCompatible_uninhabited`-FALSE,
whereas `EndpointCapLink` is the inhabited cap-channel datum. -/

namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}

/-- **`InteriorTriangleGates` is inhabited on the nil path** (vacuously: no intermediate
gates). -/
theorem interiorTriangleGates_nil (C : SimplePrimalCycle M) (f : M.Face) :
    C.InteriorTriangleGates (OrdinaryDualPath2.nil C f) where
  tri := fun j hj => absurd hj (by
    have : (OrdinaryDualPath2.nil C f).n = 0 := rfl; omega)
  ne := fun j hj => absurd hj (by
    have : (OrdinaryDualPath2.nil C f).n = 0 := rfl; omega)

/-- **The corrected endpoint datum is inhabited (non-vacuous).**  From a single
cross-bank `cutReach2` link, the nil ordinary path satisfies both `EndpointCapLink` and
`InteriorTriangleGates` — so `gateCompat'` is satisfiable, not a hidden `False`.  This is
the precise contrast with the uninhabitable `gateFragmentCompatible_uninhabited`. -/
theorem corrected_endpoint_nonvacuous (C : SimplePrimalCycle M) (i : Fin C.len)
    (f : M.Face)
    (hcross : C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i)))) :
    C.EndpointCapLink i (OrdinaryDualPath2.nil C f) ∧
      C.InteriorTriangleGates (OrdinaryDualPath2.nil C f) :=
  ⟨C.endpointCapLink_nil i f hcross, C.interiorTriangleGates_nil f⟩

/-- The corrected cross-bank bridge genuinely fires on the inhabited nil datum (the
construction is not discarding its input): from the nil endpoint link the bridge returns
exactly the supplied cross-bank `cutReach2`. -/
theorem crossBankBridge_nil_uses_input (C : SimplePrimalCycle M) (i : Fin C.len)
    (f : M.Face)
    (hcross : C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i)))) :
    C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i))) :=
  C.crossBankBridge_of_endpointCapLink i (OrdinaryDualPath2.nil C f)
    (C.endpointCapLink_nil i f hcross) (C.interiorTriangleGates_nil f)

end CombMap.SimplePrimalCycle

end ProofsInTheBook.PlanarMap

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.interiorReach_of_gates
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.crossBankBridge_of_endpointCapLink
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.cutCapMap2_connected_of_corrected
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.connectivity_of_input'
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.sphereChordSeparation_of_input'
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.separates_of_input'
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.corrected_endpoint_nonvacuous
