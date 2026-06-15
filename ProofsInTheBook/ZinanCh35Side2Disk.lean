import ProofsInTheBook.ChordSideClose

/-!
# Closing the SIDE-2 chord-side connectivity reduction (Chapter 35) — the mirror of `ChordSideClose`

`ChordSideClose.lean` proved `sideKeptMap₁_connected` and `side₁IsDisk_unconditional`: the kept
side-1 map of a chord split of a genus-0 near-triangulation is a combinatorial disk
(`IsSphereMap`) **from the chord-split data and the separation `Separates` alone**.  The side-2
mirror — `sideKeptMap₂_connected` / `side₂IsDisk_unconditional` — was never built; `ZinanCh35Side2`
threaded `ChordDisk.Side₂IsDisk` as a named hypothesis (the one genuine asymmetry of the side-2
reconstruction tower).

This file **discharges `Side₂IsDisk` unconditionally**, as the exact mirror of the side-1 proof.

## What this file proves (the genuine side-2 mirror, no residue)

The underlying fresh-dart / raw-relation machinery (`rawAlpha`, `dartStepRel`,
`eqvGen_dartStepRel_of_sameCycle_mul`, `raw_eqvGen_descends`, `keptAlpha`, `keptStepRel`,
`keptMap_eulerChar_eq_two`, and the `rawFace_*` primitives of `ChordSideClose`) is **generic over
the abstract kept type** `{d // d ∉ Del}`, so every side-1 lemma transports verbatim with
`keptDel₁ → keptDel₂`, `keptSet₁ → keptSet₂`, `side₁ → side₂`, `face₁ → face₂`,
`sideAlpha₁ → sideAlpha₂`, `sideSigma₁ → sideSigma₂`, `sideKeptMap₁ → sideKeptMap₂`, and the
seam/reference dart `data.dart → M.α data.dart`, `M.φ data.dart → M.φ (M.α data.dart)`.  The one
honest asymmetry is geometric, not logical: side 2 deletes the chord **reverse** `M.α data.dart`
(face `face₂`), seeds its reachability from `face₂`, and uses `face₂_isFaceTriangle` (the non-outer
face `face₂` is a triangle).

* **Section T — closure/genus mirror.**  `keptDel₂_sub`/`keptDel₂_closed`/`sideAlpha₂_eq_keptAlpha`
  (the `α`-closure of the side-2 carve, mirroring `SubmapPlanar.keptDel₁_*`), the structural genus
  core `side₂_keptMap_eulerChar_eq_two`/`side₂IsDisk_of_connected` (the `eulerChar = 2` no-handle
  half, from `SubmapPlanar.keptMap_eulerChar_eq_two` against `hNT.sphere`).
* **Section 0/A0 — raw connectivity mirror.**  `rawStep₂` and `keptSideRawConnected₂`: every two
  kept side-2 darts raw-connect to the reference `M.φ (M.α data.dart)`, by the same
  `ChordSplitAdj`-reachability induction (cross-face `α`-edges between kept darts, within-face
  `φ`-walks), seeded at `face₂`.
* **Section A/B — descent + assembly.**  `sideKeptMap₂_connected` (raw `EqvGen` descends) and
  `side₂IsDisk_unconditional : ChordDisk.Side₂IsDisk data hsep` — the side-2 disk fact, discharging
  `ZinanCh35Side2.chordSideNearTriangulation₂_of_share`'s `hdisk` field unconditionally.

## §3.3 verdict

FAITHFUL, non-vacuous, no residue.  `keptSideRawConnected₂` is *proved* (genuine dart-graph
reachability on `face₂`'s side), not isolated; `side₂IsDisk_unconditional` discharges
`ChordDisk.Side₂IsDisk` from `Separates` alone (plus the kept reference dart `M.φ (M.α data.dart)`).
The fact is TRUE (side 2 of a genus-0 chord split is a disk — exact mirror of the proved side-1
fact).  No `sorry` / `axiom` / `admit` / `native_decide`; no field is `:= side₁…`.
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

/-! ## Section T.  The side-2 closure and genus core (mirror of `SubmapPlanar` ChordThreading) -/

/-- `keptDel₂` is `M.α`-closed (membership is `α`-invariant).  Mirror of
`SubmapPlanar.keptDel₁_sub`. -/
lemma keptDel₂_sub (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ d, d ∈ data.keptDel₂ ↔ M.α d ∈ data.keptDel₂ := by
  intro d
  have h1 : d ∉ data.keptDel₂ ↔ d ∈ data.keptSet₂ := data.mem_keptDel₂_iff d
  have h2 : M.α d ∉ data.keptDel₂ ↔ M.α d ∈ data.keptSet₂ := data.mem_keptDel₂_iff (M.α d)
  have hkept : M.α d ∈ data.keptSet₂ ↔ d ∈ data.keptSet₂ :=
    data.mem_keptSet₂_alpha_iff hsep d
  classical
  have h1' : d ∈ data.keptDel₂ ↔ ¬ d ∈ data.keptSet₂ := by
    rw [← h1]; exact (not_not).symm
  have h2' : M.α d ∈ data.keptDel₂ ↔ ¬ M.α d ∈ data.keptSet₂ := by
    rw [← h2]; exact (not_not).symm
  rw [h1', h2']
  exact (not_congr hkept).symm

/-- `keptDel₂` is `M.α`-closed.  Mirror of `SubmapPlanar.keptDel₁_closed`. -/
lemma keptDel₂_closed (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ d, d ∈ data.keptDel₂ → M.α d ∈ data.keptDel₂ :=
  fun d hd => (keptDel₂_sub data hsep d).1 hd

/-- `sideAlpha₂` equals the abstract `keptAlpha` of `keptDel₂`.  Mirror of
`SubmapPlanar.sideAlpha₁_eq_keptAlpha`. -/
lemma sideAlpha₂_eq_keptAlpha (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideAlpha₂ hsep
      = SubmapPlanar.keptAlpha M data.keptDel₂ (keptDel₂_sub data hsep) := by
  ext d
  rw [data.sideAlpha₂_apply_coe]
  rfl

/-- **The `≥ 2` no-handle half of the side-2 disk fact, discharged structurally.**  If the kept
side-2 map is connected and has a dart, its Euler characteristic is `2`.  Mirror of
`SubmapPlanar.side₁_keptMap_eulerChar_eq_two`. -/
theorem side₂_keptMap_eulerChar_eq_two (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₂})
    (hconn : (sideKeptMap₂ data hsep).Connected) :
    (sideKeptMap₂ data hsep).eulerChar = 2 := by
  refine SubmapPlanar.keptMap_eulerChar_eq_two M data.keptDel₂ (keptDel₂_sub data hsep)
    (keptDel₂_closed data hsep) hNT.sphere (sideKeptMap₂ data hsep) ?_ ?_ d hconn
  · -- `(sideKeptMap₂).σ = sideSigma₂ = filteredRotation M.σ keptDel₂ = deleteSet M.σ keptDel₂`.
    show data.sideSigma₂ = Equiv.Perm.deleteSet M.σ data.keptDel₂
    rfl
  · -- `(sideKeptMap₂).α = sideAlpha₂ = keptAlpha`.
    show data.sideAlpha₂ hsep = SubmapPlanar.keptAlpha M data.keptDel₂ (keptDel₂_sub data hsep)
    exact sideAlpha₂_eq_keptAlpha data hsep

/-- **`Side₂IsDisk` reduces to connectivity of the kept side.**  Mirror of
`SubmapPlanar.side₁IsDisk_of_connected`: the side-2 kept map is a disk (`IsSphereMap`) given the
structural genus-0 certificate iff its kept map is connected. -/
theorem side₂IsDisk_of_connected (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₂})
    (hconn : (sideKeptMap₂ data hsep).Connected) :
    ChordDisk.Side₂IsDisk data hsep :=
  ⟨hconn, side₂_keptMap_eulerChar_eq_two data hsep d hconn⟩

/-! ## Section 0b.  The side-2 raw relation -/

/-- The **raw** dart-step relation at the side-2 chord split.  Mirror of `rawStep₁`. -/
noncomputable def rawStep₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    D → D → Prop :=
  dartStepRel M.σ (rawAlpha M data.keptDel₂ (keptDel₂_closed data hsep))

/-! ## Section A0.  The kept-side raw connectivity, PROVED (mirror of `ChordSideClose` §A0)

The deleted seam dart of side 2 is `M.α data.dart` (face `face₂`); `side₂` is the
`ChordSplitAdj`-reachability closure of `face₂`; the reference dart is `M.φ (M.α data.dart)`. -/

section RawConnected

/-- The side-2 seam dart `M.α data.dart` is deleted (removed from the side-2 kept set). -/
lemma alphaDart_mem_keptDel₂ (data : hNT.ChordSplitData u v) :
    M.α data.dart ∈ data.keptDel₂ := by
  classical
  by_contra hcontra
  rw [data.mem_keptDel₂_iff] at hcontra
  exact hcontra.2 rfl

/-- A dart whose face lies in side 2 and which is not the side-2 seam dart `M.α data.dart` is
kept.  Mirror of `inner_notMem_keptDel₁`. -/
lemma inner_notMem_keptDel₂ (data : hNT.ChordSplitData u v)
    {c : D} (hf : M.dartFace c ∈ data.side₂) (hne : c ≠ M.α data.dart) :
    c ∉ data.keptDel₂ := by
  rw [data.mem_keptDel₂_iff]
  exact ⟨Or.inl hf, by simpa using hne⟩

/-- An outer-arc dart of side 2 is kept; it is never the side-2 seam dart `M.α data.dart` (whose
face is `face₂ ≠ outerFace`).  Mirror of `outerArc_notMem_keptDel₁`. -/
lemma outerArc_notMem_keptDel₂ (data : hNT.ChordSplitData u v)
    {c : D} (ho : M.dartFace c = hNT.outerFace)
    (hα : M.dartFace (M.α c) ∈ data.side₂) : c ∉ data.keptDel₂ := by
  rw [data.mem_keptDel₂_iff]
  refine ⟨Or.inr ⟨ho, hα⟩, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hc
  apply data.face₂_not_outer
  show M.dartFace (M.α data.dart) = hNT.outerFace
  rw [← hc]; exact ho

/-- `face₂` is a triangle: it is a non-outer face of the near-triangulation.  Mirror of
`ChordSplitData.face₁_isFaceTriangle` for the second chord-incident face. -/
lemma face₂_isFaceTriangle (data : hNT.ChordSplitData u v) :
    M.IsFaceTriangle (M.α data.dart) (M.φ (M.α data.dart)) (M.φ (M.φ (M.α data.dart))) :=
  hNT.inner_face_isFaceTriangle data.face₂_not_outer

/-- The reference kept dart of side 2: `M.φ (M.α data.dart)`, a dart of the triangle `face₂` other
than the (deleted) seam dart.  Mirror of `ref_kept`. -/
lemma ref_kept₂ (data : hNT.ChordSplitData u v) :
    M.φ (M.α data.dart) ∉ data.keptDel₂ := by
  refine inner_notMem_keptDel₂ data ?_ ?_
  · show M.dartFace (M.φ (M.α data.dart)) ∈ data.side₂
    rw [dartFace_phi]; exact data.face₂_mem_side₂
  · exact M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph (M.α data.dart)

/-- **Within-face raw connectivity, away from `face₂`.**  Mirror of `rawE_within_face_ne_face₁`. -/
lemma rawE_within_face_ne_face₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a b : D} (hfa : M.dartFace a ∈ data.side₂)
    (hne : M.dartFace a ≠ data.face₂) (hab : M.φ.SameCycle a b) :
    Relation.EqvGen (rawStep₂ data hsep) a b := by
  refine rawEqvGen_of_face_kept (keptDel₂_closed data hsep)
    (fun c hac => ?_) hab
  have hfeq : M.dartFace c = M.dartFace a := Quotient.sound hac.symm
  have hfc : M.dartFace c ∈ data.side₂ := by rw [hfeq]; exact hfa
  refine inner_notMem_keptDel₂ data hfc ?_
  intro hcd
  apply hne
  rw [← hfeq, hcd]; rfl

/-- The darts of the chord triangle `face₂`: any dart `c` with
`M.φ.SameCycle (M.α data.dart) c` is `M.α data.dart`, `M.φ (M.α data.dart)`, or
`M.φ² (M.α data.dart)`.  Mirror of `face₁_dart_cases` with seam dart `M.α data.dart`. -/
lemma face₂_dart_cases (data : hNT.ChordSplitData u v)
    {c : D} (hsc : M.φ.SameCycle (M.α data.dart) c) :
    c = M.α data.dart ∨ c = M.φ (M.α data.dart) ∨ c = M.φ (M.φ (M.α data.dart)) := by
  classical
  obtain ⟨h1, h2, h3⟩ := face₂_isFaceTriangle data
  obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
  set s := M.α data.dart with hs
  have hcube : (M.φ ^ 3) s = s := by
    have : (M.φ ^ 3) s = M.φ (M.φ (M.φ s)) := by
      simp [pow_succ, Equiv.Perm.mul_apply]
    rw [this, h3]
  have hperiodic : ∀ m : ℕ, (M.φ ^ m) s = (M.φ ^ (m % 3)) s := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, Equiv.Perm.mul_apply]
    set y := (M.φ ^ (m % 3)) s with hy
    have hfix : (M.φ ^ 3) y = y := by
      rw [hy, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm, pow_add, Equiv.Perm.mul_apply,
        hcube]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix (m / 3)
  have hmod : c = (M.φ ^ (k % 3)) s := by rw [← hk, hperiodic k]
  have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (k % 3)
  · left; rw [hmod]; simp
  · right; left; rw [hmod, pow_one]
  · right; right; rw [hmod]; simp [pow_succ, Equiv.Perm.mul_apply]

/-- **Within-`face₂` raw connectivity.**  Any kept dart of `face₂` raw-connects to the reference
dart `M.φ (M.α data.dart)`.  Mirror of `rawE_face₁_to_ref`. -/
lemma rawE_face₂_to_ref (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a : D} (hfa : M.dartFace a = data.face₂) (hne : a ≠ M.α data.dart) :
    Relation.EqvGen (rawStep₂ data hsep) a (M.φ (M.α data.dart)) := by
  have hsc : M.φ.SameCycle (M.α data.dart) a := by
    have hf : M.dartFace a = M.dartFace (M.α data.dart) := by rw [hfa]; rfl
    exact (Quotient.exact hf).symm
  rcases face₂_dart_cases data hsc with h | h | h
  · exact absurd h hne
  · subst h; exact Relation.EqvGen.refl _
  · subst h
    exact Relation.EqvGen.symm _ _
      (rawEqvGen_phi_step (keptDel₂_closed data hsep) (ref_kept₂ data))

/-- **Any inner kept dart raw-connects to the reference, given its face does.**  Mirror of
`rawE_inner_to_ref`. -/
lemma rawE_inner_to_ref₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a r₀ : D} (hkept : a ∉ data.keptDel₂) (hfa : M.dartFace a ∈ data.side₂)
    (hsamef : M.dartFace a = M.dartFace r₀)
    (hr₀ : Relation.EqvGen (rawStep₂ data hsep) r₀ (M.φ (M.α data.dart))) :
    Relation.EqvGen (rawStep₂ data hsep) a (M.φ (M.α data.dart)) := by
  classical
  by_cases hne : M.dartFace a = data.face₂
  · have had : a ≠ M.α data.dart := fun h => hkept (h ▸ alphaDart_mem_keptDel₂ data)
    exact rawE_face₂_to_ref data hsep hne had
  · have hsc : M.φ.SameCycle a r₀ := Quotient.exact hsamef
    exact Relation.EqvGen.trans _ _ _ (rawE_within_face_ne_face₂ data hsep hfa hne hsc) hr₀

/-- **The chord-split adjacency step is a raw `α`-edge between kept darts.**  Mirror of
`rawE_chordSplitAdj_step`. -/
lemma rawE_chordSplitAdj_step₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {f g : M.Face} (hf : f ∈ data.side₂) (hg : g ∈ data.side₂)
    (hadj : hNT.ChordSplitAdj u v f g) :
    ∃ d : D, M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧
      d ∉ data.keptDel₂ ∧ M.α d ∉ data.keptDel₂ ∧
      Relation.EqvGen (rawStep₂ data hsep) d (M.α d) := by
  obtain ⟨d, hdf, hdg, _hbe, hch⟩ := hadj
  -- `d ≠ α dart`: its edge is not the chord (else the `ChordSplitAdj` edge would be the chord).
  have hd_ne : d ≠ M.α data.dart := by
    intro h; apply hch
    rw [h, M.dartEdge_alpha]; exact (hNT.chordDart_edge data.chord)
  have hαd_ne : M.α d ≠ M.α data.dart := by
    intro h
    apply hch
    have : M.dartEdge d = M.dartEdge (M.α d) := (M.dartEdge_alpha d).symm
    rw [this, h, M.dartEdge_alpha]; exact (hNT.chordDart_edge data.chord)
  have hd_kept : d ∉ data.keptDel₂ :=
    inner_notMem_keptDel₂ data (by rw [hdf]; exact hf) hd_ne
  have hαd_kept : M.α d ∉ data.keptDel₂ :=
    inner_notMem_keptDel₂ data (by rw [hdg]; exact hg) hαd_ne
  exact ⟨d, hdf, hdg, hd_kept, hαd_kept,
    rawEqvGen_of_alpha (keptDel₂_closed data hsep) hd_kept⟩

/-- **Every inner kept side-2 dart raw-connects to the reference.**  By induction on the
`ChordSplitAdj`-reachability of its face from `face₂`.  Mirror of `rawE_inner_kept_to_ref`. -/
lemma rawE_inner_kept_to_ref₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {g : M.Face} (hg : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₂ g) :
    ∀ a : D, M.dartFace a = g → a ∉ data.keptDel₂ →
      Relation.EqvGen (rawStep₂ data hsep) a (M.φ (M.α data.dart)) := by
  classical
  induction hg with
  | refl =>
      intro a hfa hkept
      have had : a ≠ M.α data.dart := fun h => hkept (h ▸ alphaDart_mem_keptDel₂ data)
      exact rawE_face₂_to_ref data hsep hfa had
  | @tail f g hfg hstep ih =>
      intro a hfa hkept
      have hf_side : f ∈ data.side₂ := hfg
      have hg_side : g ∈ data.side₂ := data.side₂_closed hf_side hstep
      obtain ⟨d, hdf, hdg, hd_kept, hαd_kept, hd_raw⟩ :=
        rawE_chordSplitAdj_step₂ data hsep hf_side hg_side hstep
      have hd_ref : Relation.EqvGen (rawStep₂ data hsep) d (M.φ (M.α data.dart)) :=
        ih d hdf hd_kept
      have hαd_ref : Relation.EqvGen (rawStep₂ data hsep) (M.α d) (M.φ (M.α data.dart)) :=
        Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hd_raw) hd_ref
      exact rawE_inner_to_ref₂ data hsep hkept (by rw [hfa]; exact hg_side)
        (by rw [hfa, hdg]) hαd_ref

/-- **Every kept side-2 dart raw-connects to the reference `M.φ (M.α data.dart)`.**  Mirror of
`rawE_kept_to_ref`. -/
lemma rawE_kept_to_ref₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a : D} (hkept : a ∉ data.keptDel₂) :
    Relation.EqvGen (rawStep₂ data hsep) a (M.φ (M.α data.dart)) := by
  classical
  have ha_in : a ∈ data.keptSet₂ := (data.mem_keptDel₂_iff a).mp hkept
  obtain ⟨haU, _⟩ := ha_in
  rcases haU with hinner | houter
  · have hreach : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₂ (M.dartFace a) :=
      hinner
    exact rawE_inner_kept_to_ref₂ data hsep hreach a rfl hkept
  · obtain ⟨_haouter, hαinner⟩ := houter
    have hαa_kept : M.α a ∉ data.keptDel₂ := fun h =>
      hkept ((keptDel₂_sub data hsep a).2 h)
    have hreach : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₂ (M.dartFace (M.α a)) :=
      hαinner
    have hαa_ref : Relation.EqvGen (rawStep₂ data hsep) (M.α a) (M.φ (M.α data.dart)) :=
      rawE_inner_kept_to_ref₂ data hsep hreach (M.α a) rfl hαa_kept
    exact Relation.EqvGen.trans _ _ _
      (rawEqvGen_of_alpha (keptDel₂_closed data hsep) hkept) hαa_ref

/-- **The side-2 kept-side raw-reachability predicate, PROVED.**  Mirror of
`keptSideRawConnected`. -/
theorem keptSideRawConnected₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ x y : {d : D // d ∉ data.keptDel₂},
      Relation.EqvGen (rawStep₂ data hsep) x.1 y.1 := by
  intro x y
  exact Relation.EqvGen.trans _ _ _ (rawE_kept_to_ref₂ data hsep x.2)
    (Relation.EqvGen.symm _ _ (rawE_kept_to_ref₂ data hsep y.2))

end RawConnected

/-! ## Section A.  Raw reachability descends to side-2 kept connectivity -/

/-- **Raw reachability descends to side-2 kept connectivity.**  Mirror of
`keptSide₁_connected_of_rawConnected`. -/
theorem keptSide₂_connected_of_rawConnected (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (hraw : ∀ x y : {d : D // d ∉ data.keptDel₂},
      Relation.EqvGen (rawStep₂ data hsep) x.1 y.1) :
    (sideKeptMap₂ data hsep).Connected := by
  classical
  set Del := data.keptDel₂ with hDel
  set hsub := keptDel₂_sub data hsep with hhsub
  set hclosed := keptDel₂_closed data hsep with hhclosed
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
    show (sideKeptMap₂ data hsep).σ.SameCycle x y
    show data.sideSigma₂.SameCycle x y
    exact hσ
  · right
    show y = (sideKeptMap₂ data hsep).α x
    show y = data.sideAlpha₂ hsep x
    rw [sideAlpha₂_eq_keptAlpha data hsep]
    exact hα

/-- **The kept side-2 map is connected — UNCONDITIONALLY.**  Mirror of `sideKeptMap₁_connected`. -/
theorem sideKeptMap₂_connected (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (sideKeptMap₂ data hsep).Connected :=
  keptSide₂_connected_of_rawConnected data hsep (keptSideRawConnected₂ data hsep)

/-! ## Section B.  The side-2 disk fact, unconditional -/

/-- **`Side₂IsDisk`, UNCONDITIONAL.**  Side 2 of a chord split of a genus-0 near-triangulation is a
combinatorial disk (`IsSphereMap`) given the chord-split data and the separation `Separates` alone:
the genus-0 / Euler-2 half is the structural genus core (`side₂IsDisk_of_connected`), and the
connectivity half is the proved raw reachability (Sections A0/A).  The required kept dart witness is
`M.φ (M.α data.dart)` (kept by `ref_kept₂`).  Mirror of `side₁IsDisk_unconditional`; discharges
`ZinanCh35Side2.chordSideNearTriangulation₂_of_share`'s `hdisk` field. -/
theorem side₂IsDisk_unconditional (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ChordDisk.Side₂IsDisk data hsep :=
  side₂IsDisk_of_connected data hsep ⟨M.φ (M.α data.dart), ref_kept₂ data⟩
    (sideKeptMap₂_connected data hsep)

end ProofsInTheBook.ChordSideClose

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordSideClose.keptSideRawConnected₂
#print axioms ProofsInTheBook.ChordSideClose.sideKeptMap₂_connected
#print axioms ProofsInTheBook.ChordSideClose.side₂IsDisk_unconditional
