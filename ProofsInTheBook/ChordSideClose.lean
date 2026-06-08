import ProofsInTheBook.SubmapPlanar

/-!
# Closing the chord-side connectivity reduction (Chapter 35)

`SubmapPlanar.lean` proved the deepest residue of the Chapter-35 five-color route — the
genus-0 / no-handle certificate `side₁_keptMap_eulerChar_eq_two`: the kept side of a chord
split of a genus-0 near-triangulation has Euler characteristic `2` **from connectivity
alone** (`side₁IsDisk_of_connected`).  That left the kept-side *connectivity* as the one
remaining topological input.

This file **proves that connectivity unconditionally** from the chord-split structure.

## What this file proves (genuinely new, no residue)

* **Section 0 — raw primitives.**  The *raw* dart-step relation `rawStep₁` of the side-1
  chord split (`SubmapPlanar.dartStepRel M.σ (rawAlpha …)`): its two generators are the
  vertex relation `M.σ`-`SameCycle` and a `rawAlpha`-edge (the restricted involution fixing
  deleted darts and equal to `M.α` on kept darts).  The basic single-step facts, and the
  **raw face walk**: from a kept dart one `(M.σ * rawAlpha)`-step is one `M.φ`-step, so a
  `φ`-walk that stays kept is a single raw cycle, hence raw-`EqvGen`-connected.

* **Section A0 — `KeptSideRawConnected`, PROVED.**  Every two kept side-1 darts are
  connected through `rawStep₁`.  The proof is a genuine dart-graph reachability argument on
  the chord-split structure: `side₁` is the `ChordSplitAdj`-reachability closure of `face₁`;
  each adjacency step `f → g` is witnessed by a non-chord edge whose two darts are *both
  kept*, so it is a raw `α`-edge; within each face the kept darts connect by raw `φ`-walks
  (whole-face-kept away from `face₁`, and the two surviving darts of the chord triangle
  `face₁` by a single `φ`-step); and the outer-arc darts connect to their inner `α`-reverse
  by a raw `α`-edge.  Induction on the reachability closure threads it all to the reference
  dart `M.φ data.dart`.

* **Section A — descent.**  `keptSide₁_connected_of_rawConnected`: raw `EqvGen` of all kept
  side-1 darts descends (via `SubmapPlanar.raw_eqvGen_descends`) to topological `Connected`
  of the kept side map `sideKeptMap₁`.

* **Section B — assembly.**  `side₁IsDisk_unconditional`: combining the proved raw
  connectivity (A0), the descent (A), and the proved genus core
  (`SubmapPlanar.side₁IsDisk_of_connected`), the side-1 disk fact `ChordDisk.Side₁IsDisk`
  holds **with no connectivity or genus hypothesis** — only the chord-split data, the
  separation `Separates`, and a kept dart witness.

## §3.3 verdict

FAITHFUL, non-vacuous, no residue in this file.  `KeptSideRawConnected` is *proved*, not
isolated; `side₁IsDisk_unconditional` discharges `ChordDisk.Side₁IsDisk` from `Separates`
alone (plus a kept dart, which exists since `M.φ data.dart` is kept).  No `sorry` / `axiom`
/ `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordSideClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.SubmapPlanar

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## Section 0.  Raw-relation primitives

The raw relation `dartStepRel M.σ (rawAlpha …)` has two generators: `M.σ`-`SameCycle` (free
on all darts) and a `rawAlpha`-edge (which equals `M.α` on kept darts).  We record the basic
single-step facts and the **raw face walk**: from a kept dart, one `(M.σ * rawAlpha)`-step is
exactly one `M.φ`-step, so a `φ`-walk that stays in the kept set is a single
`(M.σ * rawAlpha)`-cycle, hence raw-`EqvGen`-connected. -/

section RawPrimitives

variable (M)

open scoped Classical

/-- For a kept dart `a` (`a ∉ Del`), one raw face step is one `M.φ` step:
`(M.σ * rawAlpha) a = M.φ a`. -/
lemma rawFace_step_eq_phi {Del : Finset D}
    (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {a : D} (ha : a ∉ Del) :
    (M.σ * SubmapPlanar.rawAlpha M Del hclosed) a = M.φ a := by
  rw [Equiv.Perm.mul_apply, SubmapPlanar.rawAlpha_eq_alpha_of_notMem M Del hclosed ha]
  rfl

/-- **Raw face walk.**  If `a` and the first `k` forward `M.φ`-iterates `M.φ^j a` (`0 ≤ j < k`)
are all kept, then `(M.σ * rawAlpha)^k a = M.φ^k a`. -/
lemma rawFace_walk {Del : Finset D} (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {a : D} :
    ∀ k : ℕ, (∀ j : ℕ, j < k → (M.φ ^ j) a ∉ Del) →
      ((M.σ * SubmapPlanar.rawAlpha M Del hclosed) ^ k) a = (M.φ ^ k) a := by
  classical
  set p := M.σ * SubmapPlanar.rawAlpha M Del hclosed with hp
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hkept
      have ihk : (p ^ k) a = (M.φ ^ k) a :=
        ih (fun j hj => hkept j (by omega))
      have hak : (M.φ ^ k) a ∉ Del := hkept k (by omega)
      have hstep : (p ^ (k+1)) a = p ((p ^ k) a) := by rw [pow_succ']; rfl
      rw [hstep, ihk, hp, rawFace_step_eq_phi M hclosed hak, ← Equiv.Perm.mul_apply,
        ← pow_succ']

/-- **Whole-face kept ⟹ raw face SameCycle.**  If every dart in the `M.φ`-cycle of `a` is kept
(`∉ Del`), then `M.φ.SameCycle a b` implies `(M.σ * rawAlpha).SameCycle a b`: the `φ`-walk from
`a` to `b` never leaves the kept set, so the raw face perm tracks `M.φ` along it. -/
lemma rawFace_sameCycle_of_face_kept {Del : Finset D}
    (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {a b : D}
    (hface : ∀ c : D, M.φ.SameCycle a c → c ∉ Del)
    (hab : M.φ.SameCycle a b) :
    (M.σ * SubmapPlanar.rawAlpha M Del hclosed).SameCycle a b := by
  classical
  obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
  refine ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast, rawFace_walk M hclosed k (fun j _ => hface _ ⟨(j : ℤ), by rw [zpow_natCast]⟩),
    hk]

end RawPrimitives

/-! ## Section 0b.  The raw relation and its `EqvGen` generators -/

/-- The **raw** dart-step relation at the side-1 chord split: `M.σ`-`SameCycle` or a
`rawAlpha`-edge (the restricted involution fixing deleted darts, equal to `M.α` on kept
darts).  This is `SubmapPlanar.dartStepRel M.σ (rawAlpha M keptDel₁ …)`. -/
noncomputable def rawStep₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    D → D → Prop :=
  dartStepRel M.σ (rawAlpha M data.keptDel₁ (SubmapPlanar.keptDel₁_closed data hsep))

/-- **Raw `EqvGen` from same-face whole-face-kept.**  Wrapper turning the raw face SameCycle
into raw `EqvGen` (the generator of the raw reachability). -/
lemma rawEqvGen_of_face_kept {Del : Finset D}
    (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {a b : D}
    (hface : ∀ c : D, M.φ.SameCycle a c → c ∉ Del)
    (hab : M.φ.SameCycle a b) :
    Relation.EqvGen (dartStepRel M.σ (SubmapPlanar.rawAlpha M Del hclosed)) a b :=
  eqvGen_dartStepRel_of_sameCycle_mul M.σ (SubmapPlanar.rawAlpha M Del hclosed)
    (SubmapPlanar.rawAlpha_invol M Del hclosed)
    (rawFace_sameCycle_of_face_kept M hclosed hface hab)

/-- **One kept `φ`-step is raw-connected.**  For a kept dart `a` (`a ∉ Del`), `a` and `M.φ a`
are raw-`EqvGen`-connected: one raw face-perm step `(M.σ * rawAlpha) a = M.φ a`. -/
lemma rawEqvGen_phi_step {Del : Finset D}
    (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {a : D} (ha : a ∉ Del) :
    Relation.EqvGen (dartStepRel M.σ (SubmapPlanar.rawAlpha M Del hclosed)) a (M.φ a) := by
  refine eqvGen_dartStepRel_of_sameCycle_mul M.σ (SubmapPlanar.rawAlpha M Del hclosed)
    (SubmapPlanar.rawAlpha_invol M Del hclosed) ?_
  exact ⟨(1 : ℤ), by rw [zpow_one, rawFace_step_eq_phi M hclosed ha]⟩

/-- **Raw `EqvGen` from a single `rawAlpha`-edge at a kept dart.**  For `a ∉ Del`,
`a` and `M.α a` are one raw step apart. -/
lemma rawEqvGen_of_alpha {Del : Finset D}
    (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {a : D} (ha : a ∉ Del) :
    Relation.EqvGen (dartStepRel M.σ (SubmapPlanar.rawAlpha M Del hclosed)) a (M.α a) :=
  Relation.EqvGen.rel _ _ (Or.inr (SubmapPlanar.rawAlpha_eq_alpha_of_notMem M Del hclosed ha).symm)

/-! ## Section A0.  The kept-side raw connectivity, PROVED

`side₁` is the `ChordSplitAdj`-reachability closure of `face₁`.  We prove every kept side-1
dart raw-connects to the reference dart `M.φ data.dart`, by induction on the reachability of
its face from `face₁`.  Cross-face steps are raw `α`-edges (the shared non-chord edge's two
darts are both kept); within-face steps are raw `φ`-walks. -/

section RawConnected

/-- The chord dart is deleted (removed from the side-1 kept set). -/
lemma dart_mem_keptDel₁ (data : hNT.ChordSplitData u v) :
    data.dart ∈ data.keptDel₁ := by
  classical
  by_contra hcontra
  rw [data.mem_keptDel₁_iff] at hcontra
  exact hcontra.2 rfl

/-- A dart whose face lies in side 1 and which is not the chord dart is kept. -/
lemma inner_notMem_keptDel₁ (data : hNT.ChordSplitData u v)
    {c : D} (hf : M.dartFace c ∈ data.side₁) (hne : c ≠ data.dart) :
    c ∉ data.keptDel₁ := by
  rw [data.mem_keptDel₁_iff]
  exact ⟨Or.inl hf, by simpa using hne⟩

/-- An outer-arc dart of side 1 (outer face, `α`-reverse inner) is kept; it is never the
chord dart (whose face is `face₁ ≠ outerFace`). -/
lemma outerArc_notMem_keptDel₁ (data : hNT.ChordSplitData u v)
    {c : D} (ho : M.dartFace c = hNT.outerFace)
    (hα : M.dartFace (M.α c) ∈ data.side₁) : c ∉ data.keptDel₁ := by
  rw [data.mem_keptDel₁_iff]
  refine ⟨Or.inr ⟨ho, hα⟩, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hc
  apply data.face₁_not_outer
  show M.dartFace data.dart = hNT.outerFace
  rw [← hc]; exact ho

/-- The reference kept dart of side 1: `M.φ data.dart`, a dart of the triangle `face₁` other
than the (deleted) chord dart. -/
lemma ref_kept (data : hNT.ChordSplitData u v) :
    M.φ data.dart ∉ data.keptDel₁ := by
  refine inner_notMem_keptDel₁ data ?_ ?_
  · show M.dartFace (M.φ data.dart) ∈ data.side₁
    rw [dartFace_phi]; exact data.face₁_mem_side₁
  · exact M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph data.dart

/-- **Within-face raw connectivity, away from `face₁`.**  If `M.φ.SameCycle a b` and the common
face is in side 1 but is not `face₁`, then `a` and `b` are raw-connected.  (Every dart of such
a face is kept: it is in `sideDarts₁` and is not the chord dart, which lives in `face₁`.) -/
lemma rawE_within_face_ne_face₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a b : D} (hfa : M.dartFace a ∈ data.side₁)
    (hne : M.dartFace a ≠ data.face₁) (hab : M.φ.SameCycle a b) :
    Relation.EqvGen (rawStep₁ data hsep) a b := by
  refine rawEqvGen_of_face_kept (SubmapPlanar.keptDel₁_closed data hsep)
    (fun c hac => ?_) hab
  have hfeq : M.dartFace c = M.dartFace a := Quotient.sound hac.symm
  have hfc : M.dartFace c ∈ data.side₁ := by rw [hfeq]; exact hfa
  refine inner_notMem_keptDel₁ data hfc ?_
  intro hcd
  apply hne
  rw [← hfeq, hcd]; rfl

/-- The darts of the chord triangle `face₁`: any dart `c` with `M.φ.SameCycle data.dart c` is
`data.dart`, `M.φ data.dart`, or `M.φ² data.dart`. -/
lemma face₁_dart_cases (data : hNT.ChordSplitData u v)
    {c : D} (hsc : M.φ.SameCycle data.dart c) :
    c = data.dart ∨ c = M.φ data.dart ∨ c = M.φ (M.φ data.dart) := by
  classical
  obtain ⟨h1, h2, h3⟩ := data.face₁_isFaceTriangle
  obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
  have hcube : (M.φ ^ 3) data.dart = data.dart := by
    have : (M.φ ^ 3) data.dart = M.φ (M.φ (M.φ data.dart)) := by
      simp [pow_succ, Equiv.Perm.mul_apply]
    rw [this, h3]
  have hperiodic : ∀ m : ℕ, (M.φ ^ m) data.dart = (M.φ ^ (m % 3)) data.dart := by
    intro m
    -- `φ^m dart = φ^(3*(m/3)) (φ^(m%3) dart)`; the outer factor fixes the inner point.
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, Equiv.Perm.mul_apply]
    set y := (M.φ ^ (m % 3)) data.dart with hy
    -- `φ^3` fixes `y` (it fixes `dart`, and powers commute), so `(φ^3)^(m/3)` does too.
    have hfix : (M.φ ^ 3) y = y := by
      rw [hy, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm, pow_add, Equiv.Perm.mul_apply,
        hcube]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix (m / 3)
  have hmod : c = (M.φ ^ (k % 3)) data.dart := by rw [← hk, hperiodic k]
  have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (k % 3)
  · left; rw [hmod]; simp
  · right; left; rw [hmod, pow_one]
  · right; right; rw [hmod]; simp [pow_succ, Equiv.Perm.mul_apply]

/-- **Within-`face₁` raw connectivity.**  Any kept dart of `face₁` raw-connects to the
reference dart `M.φ data.dart`. -/
lemma rawE_face₁_to_ref (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a : D} (hfa : M.dartFace a = data.face₁) (hne : a ≠ data.dart) :
    Relation.EqvGen (rawStep₁ data hsep) a (M.φ data.dart) := by
  have hsc : M.φ.SameCycle data.dart a := by
    have hf : M.dartFace a = M.dartFace data.dart := by rw [hfa]; rfl
    exact (Quotient.exact hf).symm
  rcases face₁_dart_cases data hsc with h | h | h
  · exact absurd h hne
  · subst h; exact Relation.EqvGen.refl _
  · subst h
    -- `M.φ dart → M.φ² dart` is one raw step; take its symm.
    exact Relation.EqvGen.symm _ _
      (rawEqvGen_phi_step (SubmapPlanar.keptDel₁_closed data hsep) (ref_kept data))

/-- **Any inner kept dart raw-connects to the reference, given its face does**.  Let `a` be a
kept dart whose face is in side 1, and suppose some dart `r₀` of the *same* face raw-connects
to the reference `M.φ data.dart`.  Then so does `a`.  (Within `face₁` we connect directly via
`rawE_face₁_to_ref`, ignoring `r₀`; on any other face all darts are kept, so `a` and `r₀`
share a whole-kept face and connect by a raw `φ`-walk.) -/
lemma rawE_inner_to_ref (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a r₀ : D} (hkept : a ∉ data.keptDel₁) (hfa : M.dartFace a ∈ data.side₁)
    (hsamef : M.dartFace a = M.dartFace r₀)
    (hr₀ : Relation.EqvGen (rawStep₁ data hsep) r₀ (M.φ data.dart)) :
    Relation.EqvGen (rawStep₁ data hsep) a (M.φ data.dart) := by
  classical
  by_cases hne : M.dartFace a = data.face₁
  · -- `face₁`: `a` is kept, hence `a ≠ dart`; connect directly.
    have had : a ≠ data.dart := fun h => hkept (h ▸ dart_mem_keptDel₁ data)
    exact rawE_face₁_to_ref data hsep hne had
  · -- non-`face₁` face: `a` and `r₀` share a whole-kept face.
    have hsc : M.φ.SameCycle a r₀ := Quotient.exact hsamef
    exact Relation.EqvGen.trans _ _ _ (rawE_within_face_ne_face₁ data hsep hfa hne hsc) hr₀

/-- **The chord-split adjacency step is a raw `α`-edge between kept darts.**  If `f → g` via
`ChordSplitAdj` with `f, g ∈ side₁`, the witnessing dart `d` (`dartFace d = f`,
`dartFace (α d) = g`, non-chord edge) and its reverse `M.α d` are *both kept*, and `d`,
`M.α d` are one raw `α`-step apart. -/
lemma rawE_chordSplitAdj_step (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {f g : M.Face} (hf : f ∈ data.side₁) (hg : g ∈ data.side₁)
    (hadj : hNT.ChordSplitAdj u v f g) :
    ∃ d : D, M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧
      d ∉ data.keptDel₁ ∧ M.α d ∉ data.keptDel₁ ∧
      Relation.EqvGen (rawStep₁ data hsep) d (M.α d) := by
  obtain ⟨d, hdf, hdg, _hbe, hch⟩ := hadj
  -- `d ≠ dart` (its edge is not the chord), so `d` is a kept inner dart of `f ∈ side₁`.
  have hd_ne : d ≠ data.dart := by
    intro h; apply hch; rw [h]; exact (hNT.chordDart_edge data.chord)
  have hαd_ne : M.α d ≠ data.dart := by
    intro h
    apply hch
    have : M.dartEdge d = M.dartEdge (M.α d) := (M.dartEdge_alpha d).symm
    rw [this, h]; exact (hNT.chordDart_edge data.chord)
  have hd_kept : d ∉ data.keptDel₁ :=
    inner_notMem_keptDel₁ data (by rw [hdf]; exact hf) hd_ne
  have hαd_kept : M.α d ∉ data.keptDel₁ :=
    inner_notMem_keptDel₁ data (by rw [hdg]; exact hg) hαd_ne
  exact ⟨d, hdf, hdg, hd_kept, hαd_kept,
    rawEqvGen_of_alpha (SubmapPlanar.keptDel₁_closed data hsep) hd_kept⟩

/-- **Every inner kept side-1 dart raw-connects to the reference.**  By induction on the
`ChordSplitAdj`-reachability of its face from `face₁`.  Base: `face₁` via `rawE_face₁_to_ref`.
Step: the adjacency dart joins the previous face to the current one by a raw `α`-edge between
kept darts, threading the reachability. -/
lemma rawE_inner_kept_to_ref (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {g : M.Face} (hg : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ g) :
    ∀ a : D, M.dartFace a = g → a ∉ data.keptDel₁ →
      Relation.EqvGen (rawStep₁ data hsep) a (M.φ data.dart) := by
  classical
  induction hg with
  | refl =>
      intro a hfa hkept
      have had : a ≠ data.dart := fun h => hkept (h ▸ dart_mem_keptDel₁ data)
      exact rawE_face₁_to_ref data hsep hfa had
  | @tail f g hfg hstep ih =>
      -- `f ∈ side₁` (reachable from `face₁`), `g ∈ side₁`.
      intro a hfa hkept
      have hf_side : f ∈ data.side₁ := hfg
      have hg_side : g ∈ data.side₁ := data.side₁_closed hf_side hstep
      -- the adjacency dart `d`: `dartFace d = f`, `dartFace (α d) = g`, both kept.
      obtain ⟨d, hdf, hdg, hd_kept, hαd_kept, hd_raw⟩ :=
        rawE_chordSplitAdj_step data hsep hf_side hg_side hstep
      -- `d` (in `f`) connects to the reference by the induction hypothesis.
      have hd_ref : Relation.EqvGen (rawStep₁ data hsep) d (M.φ data.dart) :=
        ih d hdf hd_kept
      -- `α d` (in `g`) connects to the reference: `α d → d → ref`.
      have hαd_ref : Relation.EqvGen (rawStep₁ data hsep) (M.α d) (M.φ data.dart) :=
        Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hd_raw) hd_ref
      -- `a` (in `g`, same face as `α d`) connects to the reference via `rawE_inner_to_ref`.
      exact rawE_inner_to_ref data hsep hkept (by rw [hfa]; exact hg_side)
        (by rw [hfa, hdg]) hαd_ref

/-- **Every kept side-1 dart raw-connects to the reference `M.φ data.dart`.**  An inner kept
dart goes through `rawE_inner_kept_to_ref`; an outer-arc kept dart connects via its raw
`α`-edge to its (inner kept) reverse, then through the inner case. -/
lemma rawE_kept_to_ref (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a : D} (hkept : a ∉ data.keptDel₁) :
    Relation.EqvGen (rawStep₁ data hsep) a (M.φ data.dart) := by
  classical
  -- `a ∈ keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`.
  have ha_in : a ∈ data.keptSet₁ := (data.mem_keptDel₁_iff a).mp hkept
  obtain ⟨haU, _⟩ := ha_in
  rcases haU with hinner | houter
  · -- inner: `dartFace a ∈ side₁`.
    have hreach : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ (M.dartFace a) :=
      hinner
    exact rawE_inner_kept_to_ref data hsep hreach a rfl hkept
  · -- outer-arc: `dartFace a = outerFace`, `dartFace (α a) ∈ side₁`.
    obtain ⟨_haouter, hαinner⟩ := houter
    -- `α a` is kept (inner side-1, not the chord dart): membership is `α`-invariant.
    have hαa_kept : M.α a ∉ data.keptDel₁ := fun h =>
      hkept ((SubmapPlanar.keptDel₁_sub data hsep a).2 h)
    -- `α a` connects to the reference (inner case).
    have hreach : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ (M.dartFace (M.α a)) :=
      hαinner
    have hαa_ref : Relation.EqvGen (rawStep₁ data hsep) (M.α a) (M.φ data.dart) :=
      rawE_inner_kept_to_ref data hsep hreach (M.α a) rfl hαa_kept
    -- `a → α a` is a raw `α`-step.
    exact Relation.EqvGen.trans _ _ _
      (rawEqvGen_of_alpha (SubmapPlanar.keptDel₁_closed data hsep) hkept) hαa_ref

/-- **The kept-side raw-reachability predicate, PROVED.**  Every two kept side-1 darts are
connected through the raw relation `rawStep₁`: each connects to the reference `M.φ data.dart`,
so they connect to each other.  This is the genuine dart-graph reachability "the side is the
closure of one Jordan region", proved unconditionally from the chord-split structure. -/
theorem keptSideRawConnected (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ x y : {d : D // d ∉ data.keptDel₁},
      Relation.EqvGen (rawStep₁ data hsep) x.1 y.1 := by
  intro x y
  exact Relation.EqvGen.trans _ _ _ (rawE_kept_to_ref data hsep x.2)
    (Relation.EqvGen.symm _ _ (rawE_kept_to_ref data hsep y.2))

end RawConnected

/-! ## Section A.  Raw reachability descends to kept-side connectivity -/

/-- **Raw reachability descends to kept-side connectivity.**  If every two kept side-1 darts
are connected through the raw relation `rawStep₁`, then the kept side-1 map `sideKeptMap₁` is
connected.  `SubmapPlanar.raw_eqvGen_descends` descends the raw `EqvGen` to a kept `EqvGen` on
the kept subtype's `keptStepRel`, which (the relation being symmetric) is the `ReflTransGen`
of the kept map's `dartStep` after identifying `sideSigma₁ = deleteSet M.σ keptDel₁` and
`sideAlpha₁ = keptAlpha`. -/
theorem keptSide₁_connected_of_rawConnected (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (hraw : ∀ x y : {d : D // d ∉ data.keptDel₁},
      Relation.EqvGen (rawStep₁ data hsep) x.1 y.1) :
    (sideKeptMap₁ data hsep).Connected := by
  classical
  set Del := data.keptDel₁ with hDel
  set hsub := SubmapPlanar.keptDel₁_sub data hsep with hhsub
  set hclosed := SubmapPlanar.keptDel₁_closed data hsep with hhclosed
  have hsymm : ∀ a b, SubmapPlanar.keptStepRel M Del hsub a b →
      SubmapPlanar.keptStepRel M Del hsub b a :=
    fun a b h => dartStepRel_symm (SubmapPlanar.keptAlpha_invol M Del hsub) h
  intro a b
  have hrawab : Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) a.1 b.1 := hraw a b
  have hkept : Relation.EqvGen (SubmapPlanar.keptStepRel M Del hsub) a b :=
    SubmapPlanar.raw_eqvGen_descends M Del hclosed hsub hrawab
  have hreach : Relation.ReflTransGen (SubmapPlanar.keptStepRel M Del hsub) a b :=
    (eqvGen_iff_reflTransGen hsymm a b).1 hkept
  refine hreach.mono ?_
  intro x y hxy
  rcases hxy with hσ | hα
  · left
    show (sideKeptMap₁ data hsep).σ.SameCycle x y
    show data.sideSigma₁.SameCycle x y
    exact hσ
  · right
    show y = (sideKeptMap₁ data hsep).α x
    show y = data.sideAlpha₁ hsep x
    rw [SubmapPlanar.sideAlpha₁_eq_keptAlpha data hsep]
    exact hα

/-- **The kept side-1 map is connected — UNCONDITIONALLY.**  Combining the proved raw
reachability `keptSideRawConnected` with the descent `keptSide₁_connected_of_rawConnected`.
This is the one remaining topological input of the Chapter-35 chord case, now discharged from
the chord-split data and the separation `Separates` alone. -/
theorem sideKeptMap₁_connected (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (sideKeptMap₁ data hsep).Connected :=
  keptSide₁_connected_of_rawConnected data hsep (keptSideRawConnected data hsep)

/-! ## Section B.  The side-1 disk fact, unconditional -/

/-- **`Side₁IsDisk`, UNCONDITIONAL.**  Side 1 of a chord split of a genus-0 near-triangulation
is a combinatorial disk (`IsSphereMap`) given the chord-split data and the separation
`Separates` alone: the genus-0 / Euler-2 half is the proved genus core
(`SubmapPlanar.side₁IsDisk_of_connected`), and the connectivity half is the proved raw
reachability (Sections A0/A).  The required kept dart witness is `M.φ data.dart` (kept by
`ref_kept`).  No connectivity or genus hypothesis is taken. -/
theorem side₁IsDisk_unconditional (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ChordDisk.Side₁IsDisk data hsep :=
  SubmapPlanar.side₁IsDisk_of_connected data hsep ⟨M.φ data.dart, ref_kept data⟩
    (sideKeptMap₁_connected data hsep)

end ProofsInTheBook.ChordSideClose

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordSideClose.keptSideRawConnected
#print axioms ProofsInTheBook.ChordSideClose.sideKeptMap₁_connected
#print axioms ProofsInTheBook.ChordSideClose.side₁IsDisk_unconditional
