═══ BRIDGE life | 86f9ae3a | 21106 chars 2912 words 561 lines | 490s | prov=network | OK ═══
═══ BRIDGE life | 86f9ae3a | 21106 chars 2912 words 561 lines | 490s | prov=network | OK ═══
The reduction you landed is the right one. `ZinanCh35OuterTraceProof.lean` now isolates exactly the useful classifier: every side-1 outer-orbit dart is either the fresh root `inr 1`, carrying `v`, or an `inl`-dart whose underlying original dart is one of the `u → v` boundary-arc darts; the reduction then uses `A.head_last_ne_tail` and `A.tail_nodup` to prove `OuterTraceInjOn`. fileciteturn60file0L54-L77

The remaining classifier is **not** just a fresh-map orbit lemma. It has one new geometric bridge: the `tracePhi` orbit of the canonical kept dart `β a₁` must be identified with the concrete `DartArc` from `u` to `v`.

Below is the clean Lean route.

---

## 1. Orbit membership

Let

```lean
a₀ := side₁Anchor₀ data hsep
a₁ := side₁Anchor₁ data hsep
hne := side₁Anchors_ne data hsep
β  := data.sideAlpha₁ hsep
ρ  := data.sideSigma₁
S  := data.sideMap₁ hsep a₀ a₁ hne
τ  := tracePhi β ρ a₀ a₁
```

The generic membership statement you want is:

```lean
x ∈ S.faceDartList (Sum.inr 1)
↔ x = Sum.inr 1 ∨ ∃ k, x = Sum.inl k ∧ τ.SameCycle (β a₁) k
```

The important negative case is `x = inr 0`, whose `faceProj` is `β a₀`. You must exclude

```lean
τ.SameCycle (β a₁) (β a₀)
```

For canonical anchors, the expected already-existing lemma is the one documented in `ChordBoundaryOrbit.lean` as the genus-zero split of the shared kept face: under `Side₁AnchorsShareFace`, the swap splits the shared kept face into two distinct `tracePhi` orbits, so `β a₀` and `β a₁` are not `tracePhi`-same-cyclic. The file comments name this as `chordOrbits_distinct_of_sameFace`; the canonical producer for the hypothesis is `side₁AnchorsShareFace_canonical`. fileciteturn53file0L4-L4 fileciteturn56file0L4-L4

Use it in this shape:

```lean
lemma canonical_tracePhi_beta_a₁_not_beta_a₀
    {D : Type u} [Fintype D] [DecidableEq D]
    {M : CombMap D} {hNT : NearTriangulation M} {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ¬ (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
        ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep))
        ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) := by
  have hshare :=
    side₁AnchorsShareFace_canonical (data := data) hsep
  -- Exact lemma name expected from `ChordBoundaryOrbit.lean`.
  -- It may return the orientation `(β a₀) ~(β a₁)`, so finish by symmetry if needed.
  simpa [hshare] using
    (chordOrbits_distinct_of_sameFace
      (β := data.sideAlpha₁ hsep)
      (ρ := data.sideSigma₁)
      (a₀ := side₁Anchor₀ data hsep)
      (a₁ := side₁Anchor₁ data hsep)
      (hβinv := data.sideAlpha₁_involutive hsep)
      (hβfix := data.sideAlpha₁_no_fixed hsep)
      (hne := side₁Anchors_ne data hsep)
      hshare).symm
```

If `chordOrbits_distinct_of_sameFace` already returns the orientation with `(β a₁) (β a₀)`, remove `.symm`. If it returns a face inequality rather than a direct `¬ SameCycle`, use `chordOrbits_eq_iff_tracePhi` once to rewrite the face inequality to the `tracePhi` inequality.

Then prove the membership iff:

```lean
lemma canonical_side₁_outer_orbit_mem_iff
    {D : Type u} [Fintype D] [DecidableEq D]
    {M : CombMap D} {hNT : NearTriangulation M} {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (x :
      {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :
    let a₀ := side₁Anchor₀ data hsep
    let a₁ := side₁Anchor₁ data hsep
    let hne := side₁Anchors_ne data hsep
    let β := data.sideAlpha₁ hsep
    let ρ := data.sideSigma₁
    let τ := tracePhi β ρ a₀ a₁
    x ∈
        (data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1)
      ↔
        x = Sum.inr 1 ∨
          ∃ k : {d : D // d ∉ data.keptDel₁},
            x = Sum.inl k ∧ τ.SameCycle (β a₁) k := by
  classical
  dsimp
  set a₀ := side₁Anchor₀ data hsep
  set a₁ := side₁Anchor₁ data hsep
  set hne := side₁Anchors_ne data hsep
  set β := data.sideAlpha₁ hsep
  set ρ := data.sideSigma₁
  set τ := tracePhi β ρ a₀ a₁

  have hsplit : ¬ τ.SameCycle (β a₁) (β a₀) := by
    subst τ; subst ρ; subst β; subst hne; subst a₁; subst a₀
    exact canonical_tracePhi_beta_a₁_not_beta_a₀ data hsep

  have hroot_support :
      (Sum.inr 1 : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) ∈
        (data.sideMap₁ hsep a₀ a₁ hne).φ.support := by
    rw [Equiv.Perm.mem_support]
    rw [show data.sideMap₁ hsep a₀ a₁ hne =
        freshMap β ρ
          (data.sideAlpha₁_involutive hsep)
          (data.sideAlpha₁_no_fixed hsep)
          a₀ a₁ hne from rfl]
    rw [freshMap_phi_inr_one β ρ
      (data.sideAlpha₁_involutive hsep)
      (data.sideAlpha₁_no_fixed hsep)
      hne]
    exact Sum.inr_ne_inl

  constructor
  · intro hx
    rw [CombMap.faceDartList, Equiv.Perm.mem_toList_iff] at hx
    rcases hx with ⟨hcyc, _hsupp⟩
    have hτ :
        τ.SameCycle (faceProj β a₀ a₁ x) (β a₁) := by
      subst τ
      have h :=
        (freshFace_sameCycle_iff β ρ
          (data.sideAlpha₁_involutive hsep)
          (data.sideAlpha₁_no_fixed hsep)
          hne x (Sum.inr 1)).1
      rw [show data.sideMap₁ hsep a₀ a₁ hne =
        freshMap β ρ
          (data.sideAlpha₁_involutive hsep)
          (data.sideAlpha₁_no_fixed hsep)
          a₀ a₁ hne from rfl] at hcyc
      simpa [faceProj_inr_one] using h hcyc
    cases x with
    | inl k =>
        right
        refine ⟨k, rfl, ?_⟩
        simpa [faceProj_inl] using hτ.symm
    | inr j =>
        fin_cases j
        · -- `inr 0`, excluded by the split
          exfalso
          have hbad : τ.SameCycle (β a₁) (β a₀) := by
            simpa [faceProj_inr_zero] using hτ.symm
          exact hsplit hbad
        · left
          rfl
  · intro hx
    rw [CombMap.faceDartList, Equiv.Perm.mem_toList_iff]
    refine ⟨?_, hroot_support⟩
    rcases hx with hroot | ⟨k, rfl, hk⟩
    · subst hroot
      exact Equiv.Perm.SameCycle.refl _ _
    · rw [show data.sideMap₁ hsep a₀ a₁ hne =
        freshMap β ρ
          (data.sideAlpha₁_involutive hsep)
          (data.sideAlpha₁_no_fixed hsep)
          a₀ a₁ hne from rfl]
      refine
        (freshFace_sameCycle_iff β ρ
          (data.sideAlpha₁_involutive hsep)
          (data.sideAlpha₁_no_fixed hsep)
          hne (Sum.inl k) (Sum.inr 1)).2 ?_
      simpa [faceProj_inl, faceProj_inr_one] using hk
```

This lemma should go green modulo the exact orientation/result type of `chordOrbits_distinct_of_sameFace`.

---

## 2. Ordered trace = boundary arc

This is the one genuinely new bridge. It should not be hidden inside the classifier proof.

State it directly:

```lean
/-- The canonical `tracePhi` orbit through `β a₁` is exactly the kept copy of the
`u → v` boundary dart arc. -/
structure CanonicalTracePhiArc
    {D : Type u} [Fintype D] [DecidableEq D]
    {M : CombMap D} {hNT : NearTriangulation M} {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle u v)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁) : Prop where
  mem_iff :
    ∀ k : {d : D // d ∉ data.keptDel₁},
      (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
        ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) k
      ↔ ∃ i : Fin A.len, k = ⟨A.arcDart i, hArcKept i⟩
```

Then the classifier is immediate:

```lean
theorem canonical_arcTrace_of_tracePhiArc
    {D : Type u} [Fintype D] [DecidableEq D]
    {M : CombMap D} {hNT : NearTriangulation M} {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle u v)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hTA : CanonicalTracePhiArc data hsep A hArcKept) :
    CanonicalSide₁OuterArcTrace hNT data hsep A hArcKept := by
  intro x hx
  have hmem :=
    (canonical_side₁_outer_orbit_mem_iff data hsep x).1 hx
  rcases hmem with hroot | ⟨k, hxk, hτ⟩
  · exact Or.inl hroot
  · rcases (hTA.mem_iff k).1 hτ with ⟨i, hk⟩
    exact Or.inr ⟨i, by rw [hxk, hk]⟩
```

### The step relation you need

For `A : DartArc M hNT.outerCycle u v`, define:

```lean
def arcK (i : Fin A.len) : {d : D // d ∉ data.keptDel₁} :=
  ⟨A.arcDart i, hArcKept i⟩
```

The key forward-step lemma should be:

```lean
lemma canonical_keptPhi_arc_step
    (i : Fin A.len) (hi : (i : ℕ) + 1 < A.len) :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (arcK data hsep A hArcKept i)
      =
    arcK data hsep A hArcKept ⟨i + 1, hi⟩
```

Then the wrapping endpoint lemma should be:

```lean
lemma canonical_tracePhi_arc_wrap :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (arcK data hsep A hArcKept ⟨A.len - 1, by omega⟩)
      =
    arcK data hsep A hArcKept ⟨0, A.len_pos⟩
```

Once you have those, prove:

```lean
lemma canonical_tracePhi_arc_forward
    (i : Fin A.len) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (arcK data hsep A hArcKept i)
      =
    arcK data hsep A hArcKept
      (if h : (i : ℕ) + 1 < A.len then ⟨i + 1, h⟩ else ⟨0, A.len_pos⟩)
```

For non-last `i`, use `tracePhi_other` plus `canonical_keptPhi_arc_step`.

For last `i`, use `canonical_tracePhi_arc_wrap`.

The hard part is `canonical_keptPhi_arc_step`.

Your proposed derivation is right in spirit but **not available from `DartArc.chain` alone**. `A.chain` gives only

```lean
M.head (A.arcDart i) = M.tail (A.arcDart ⟨i+1, hi⟩)
```

The construction of `DartArc` from a boundary cycle stores chaining as head/tail equality; the `DartArc` materialization in `ZinanCh35ArcDartRun` also uses this head/tail form, not an exact `M.φ` equality. fileciteturn50file0L4-L4

Therefore, to prove the exact kept-step

```lean
ρ (β (arcK i)) = arcK (i+1)
```

you need a filtered-rotation successor lemma saying that at this boundary vertex, the filtered rotation skips only deleted darts and the next kept dart is exactly the next boundary-arc dart.

The correct new lemma is:

```lean
/-- The side-1 filtered rotation sends the reverse of the current boundary-arc dart
to the next boundary-arc dart. -/
lemma sideSigma₁_alpha_arcDart_eq_next
    (i : Fin A.len) (hi : (i : ℕ) + 1 < A.len) :
    data.sideSigma₁
        ((data.sideAlpha₁ hsep) ⟨A.arcDart i, hArcKept i⟩)
      =
    ⟨A.arcDart ⟨i + 1, hi⟩, hArcKept ⟨i + 1, hi⟩⟩
```

Then:

```lean
lemma canonical_keptPhi_arc_step
    (i : Fin A.len) (hi : (i : ℕ) + 1 < A.len) :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (arcK data hsep A hArcKept i)
      =
    arcK data hsep A hArcKept ⟨i + 1, hi⟩ := by
  unfold keptPhi arcK
  exact sideSigma₁_alpha_arcDart_eq_next
    (data := data) (hsep := hsep) (A := A) hArcKept i hi
```

`sideAlpha₁_apply_coe` and `tail_filteredRotation` help, but they do **not** by themselves identify the next kept dart. They only give:

```lean
((data.sideAlpha₁ hsep) ⟨d, hd⟩).1 = M.α d
```

and filtered rotation preserves the `M.tail` vertex. `canonicalAnchor₀_tail` is proved exactly by using `tail_filteredRotation`, so this is a vertex-level fact, not an exact successor fact. fileciteturn61file0L4-L4

So `sideSigma₁_alpha_arcDart_eq_next` is a genuine new sublemma unless you already have a stronger filtered-rotation “next kept dart” theorem.

---

## 3. Endpoint alignment

The two endpoint equations should be stated as exact dart equations, not just vertex equations:

```lean
lemma canonical_arc_first_eq_sideSigma_anchor₀ :
    data.sideSigma₁ (side₁Anchor₀ data hsep)
      =
    arcK data hsep A hArcKept ⟨0, A.len_pos⟩
```

and

```lean
lemma canonical_arc_last_eq_sideAlpha_anchor₁ :
    (data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)
      =
    arcK data hsep A hArcKept ⟨A.len - 1, by omega⟩
```

Do **not** try to prove these from `tail_first`/`head_last` alone. Those give only endpoint vertices. You also need boundary-cycle uniqueness.

A robust proof of the first lemma is:

```lean
lemma canonical_arc_first_eq_sideSigma_anchor₀
    (h_sideSigma_a₀_boundary :
      (data.sideSigma₁ (side₁Anchor₀ data hsep) : D) ∈ hNT.outerCycle.darts)
    (h_tail_data : M.tail data.dart = u) :
    data.sideSigma₁ (side₁Anchor₀ data hsep)
      =
    ⟨A.arcDart ⟨0, A.len_pos⟩, hArcKept ⟨0, A.len_pos⟩⟩ := by
  apply Subtype.ext
  apply hNT.outerCycle.tail_injective_on_darts hNT.outer_simple
  · exact h_sideSigma_a₀_boundary
  · exact A.boundary ⟨0, A.len_pos⟩
  · -- both tails are `u`
    rw [A.tail_first]
    -- left side: sideSigma a₀ has same tail as a₀, and a₀ tail is tail data.dart = u.
    have hfix : M.tail (data.sideSigma₁ (side₁Anchor₀ data hsep) : D)
        = M.tail (side₁Anchor₀ data hsep).1 := by
      rw [show data.sideSigma₁ =
          FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
        tail_filteredRotation data.keptDel₁ (side₁Anchor₀ data hsep)]
    rw [hfix, canonicalAnchor₀_tail data hsep, h_tail_data]
```

The second endpoint is analogous but usually needs head uniqueness, not tail uniqueness. The easiest way is to state and prove a helper for the `DartArc` construction:

```lean
lemma DartArc.last_eq_of_same_head_on_boundary
    (hβa₁_boundary :
      ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep) : D) ∈ hNT.outerCycle.darts)
    (hhead :
      M.head ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep) : D) = v) :
    (data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)
      =
    arcK data hsep A hArcKept ⟨A.len - 1, by omega⟩
```

If there is no `head_injective_on_darts` lemma for `BoundaryCycle`, add one:

```lean
lemma BoundaryCycle.head_injective_on_darts
    (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {d e : D} (hd : d ∈ C.darts) (he : e ∈ C.darts)
    (hhead : M.head d = M.head e) :
    d = e := ...
```

Prove it by converting `M.head d` to the tail of the cyclic successor dart in `C.darts`, then use `tail_injective_on_darts`.

Again, this is a genuine new sublemma unless already present.

---

## 4. Arc construction and `hArcKept`

The raw arc term is:

```lean
noncomputable def canonicalOuterArc
    {D : Type u} [Fintype D] [DecidableEq D]
    {M : CombMap D} {hNT : NearTriangulation M} {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v) : DartArc M hNT.outerCycle u v :=
  (hNT.outerCycle.dartArcOfNonBoundaryEdge
    hNT.outer_simple
    h.ne
    h.u_boundary
    h.v_boundary
    h.not_boundary_edge).1
```

The exact field names on `Chord` may be slightly different in your checkout, but the required four proofs are:

```lean
huv    : u ≠ v
hu_bv  : hNT.outerCycle.IsBoundaryVertex u
hv_bv  : hNT.outerCycle.IsBoundaryVertex v
hnbe   : ¬ hNT.outerCycle.IsBoundaryEdge s(u, v)
```

The `dartArcOfNonBoundaryEdge` constructor has exactly that signature: a vertex-nodup boundary cycle, distinct boundary vertices `a b`, both boundary-vertex witnesses, and a proof that `s(a,b)` is not a boundary edge. It returns a `DartArc M C a b` with length at least `2`. fileciteturn62file0L4-L4

For `hArcKept`, do **not** try to derive it from `dartArcOfNonBoundaryEdge` alone. That constructor only knows the arc lies on `hNT.outerCycle`; it does not know which side’s deletion set is `keptDel₁`.

Use the existing side-1 outer-arc producer if possible. `ZinanCh35ChordResidue.lean` explicitly says `OuterDartArc₁` is already produced unconditionally via `ZinanCh35EdgeCoreFinal.outerDartArc₁_uncond`. fileciteturn61file0L4-L4 That is the right source for:

```lean
hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁
```

If `outerDartArc₁_uncond` exposes an arc plus keptness, use that instead of rebuilding `A` raw:

```lean
noncomputable def canonicalOuterArcWithKept
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    { A : DartArc M hNT.outerCycle u v //
      ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁ } := by
  -- expected producer
  exact ZinanCh35EdgeCoreFinal.outerDartArc₁_uncond data hsep
```

If the producer returns a named structure rather than a subtype, project its fields:

```lean
let H := ZinanCh35EdgeCoreFinal.outerDartArc₁_uncond data hsep
exact ⟨H.A, H.kept⟩
```

If no such projection exists, add this small adapter theorem. The keptness itself is not small; it is the theorem that the selected `u → v` boundary arc belongs to side 1.

---

## 5. Orientation `hhv`

`ChordSplitData` should **not** be treated as inherently oriented `tail data.dart = u` and `head data.dart = v` for arbitrary data.

Your own residue file says the orientation facts

```lean
htu : M.tail data.dart = u
hhv : M.head data.dart = v
```

come from `ZinanCh35Aligned.chordDart_orientation`, and the residual supplier chooses the standard branch. fileciteturn61file0L4-L4

So there are two valid approaches:

1. Keep `hhv` and `htu` as arguments, as your reduction already does for `hhv`. This is the most local route.

2. Work only with `normalizedChordSplitData h`, where the normalized branch supplies the standard orientation.

Do not silently assume arbitrary `ChordSplitData` is oriented.

---

## Complete classifier wrapper once the two hard bridges exist

Assume these two new/adapter lemmas:

```lean
/-- New hard bridge: the canonical tracePhi orbit is exactly the side-1 boundary arc. -/
theorem canonical_tracePhiArc
    {D : Type u} [Fintype D] [DecidableEq D]
    {M : CombMap D} {hNT : NearTriangulation M} {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle u v)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁) :
    CanonicalTracePhiArc data hsep A hArcKept

/-- Adapter/producer: construct the side-1 `u → v` arc together with keptness. -/
noncomputable def canonicalSide₁ArcWithKept
    {D : Type u} [Fintype D] [DecidableEq D]
    {M : CombMap D} {hNT : NearTriangulation M} {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    { A : DartArc M hNT.outerCycle u v //
      ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁ }
```

Then the final classifier is:

```lean
theorem canonical_CanonicalSide₁OuterArcTrace
    {D : Type u} [Fintype D] [DecidableEq D]
    {M : CombMap D} {hNT : NearTriangulation M} {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle u v)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hTA : CanonicalTracePhiArc data hsep A hArcKept) :
    CanonicalSide₁OuterArcTrace hNT data hsep A hArcKept :=
  canonical_arcTrace_of_tracePhiArc
    (data := data) (hsep := hsep) (A := A)
    (hArcKept := hArcKept) hTA
```

And the fully assembled canonical theorem is:

```lean
theorem canonical_OuterTraceInjOn_closed
    {D : Type u} [Fintype D] [DecidableEq D]
    {M : CombMap D} {hNT : NearTriangulation M} {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (htu : M.tail data.dart = u)
    (hhv : M.head data.dart = v) :
    OuterTraceInjOn hNT data hsep
      (side₁Anchor₀ data hsep)
      (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep) := by
  classical
  let P := canonicalSide₁ArcWithKept (data := data) hsep
  let A : DartArc M hNT.outerCycle u v := P.1
  have hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁ := P.2
  have hTA : CanonicalTracePhiArc data hsep A hArcKept :=
    canonical_tracePhiArc data hsep A hArcKept
  have htrace : CanonicalSide₁OuterArcTrace hNT data hsep A hArcKept :=
    canonical_arcTrace_of_tracePhiArc data hsep A hArcKept hTA
  exact canonical_OuterTraceInjOn_of_arcTrace
    hNT data hsep A hArcKept hhv htrace
```

---

## Summary of what is available vs missing

Available/landed:

* `CanonicalSide₁OuterArcTrace` and `canonical_OuterTraceInjOn_of_arcTrace`; the reduction is clean and uses `canonicalAnchor₁_tail`, `A.head_last_ne_tail`, and `A.tail_nodup`. fileciteturn60file0L54-L103
* `canonicalAnchor₀_tail` / `canonicalAnchor₁_tail`, proved from `sideSigma₁_side₁Anchor₀/₁` plus `tail_filteredRotation`. fileciteturn61file0L4-L4
* The fresh-face orbit machinery: `faceProj`, `tracePhi`, `freshMap_phi_*`, and `freshFace_sameCycle_iff`. fileciteturn52file0L4-L4
* The split-orbit theorem should be `chordOrbits_distinct_of_sameFace`, fed by `side₁AnchorsShareFace_canonical`. fileciteturn53file0L4-L4
* `dartArcOfNonBoundaryEdge` constructs a concrete `DartArc` from a non-boundary edge between two distinct boundary vertices. fileciteturn62file0L4-L4

Genuinely new or adapter-level:

1. `sideSigma₁_alpha_arcDart_eq_next`: filtered rotation of the side-1 reverse boundary arc dart gives the next arc dart.
2. Endpoint exact dart alignment:
   * `data.sideSigma₁ a₀ = first arc dart`;
   * `data.sideAlpha₁ a₁ = last arc dart`.
3. `CanonicalTracePhiArc`: the `tracePhi` orbit of `β a₁` equals the kept copies of `A.arcDart`.
4. `canonicalSide₁ArcWithKept`: preferably an adapter around `outerDartArc₁_uncond`; do not reprove keptness from the raw `dartArcOfNonBoundaryEdge`.

The main risk is trying to prove exact orbit equality from endpoint vertex equalities alone. That is not enough. You need exact boundary dart identification, using boundary-cycle uniqueness and the side-1 kept/deleted structure.
