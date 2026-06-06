import ProofsInTheBook.SphericalHingeCut

/-!
# `SphericalDiagCut` — the §8.4 diagonal-cut sub-arm construction (`DiagonalCutArm`)

This module attacks the single residue of Chapter 13's spherical arm lemma isolated by the prior round
as `ProofsInTheBook.SphericalHingeCut.DiagonalCutArm`: the diagonal-cut sub-arm CONSTRUCTION that, from
a stuck strictly-convex spherical arm with a vanishing non-incident support, produces a re-indexed
`Fin (n+1)`-subfamily sub-arm that is again `StrictConvexSphArm` and shares the first endpoint.

The hard analytic pieces are already PROVED in the substrate (`SphericalHingeCut.lean`):
the §8.1 oriented opening keystone `openedAngle_ge_of_oriented`, the §8.3 persistence
`mixedSupport_persists` / `strictSupport_persists`, and the §8.4 cut-support certificates
`cut_diagonal_supports`, `cut_subseqDiag_supports`, `cut_corner_signs` (all unconditional via
`cyclicTriplePos_unconditional`).  What remains is the *index bookkeeping*: the `Fin` re-indexing of the
cut sub-family and the transport of the four `StrictConvexSphPolygon` fields across it.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut

namespace ProofsInTheBook.SphericalDiagCut

/-! ## Probe: the easy structural facts of a `Fin`-subfamily re-indexing.

We first record the parts of the convex-polygon-field transport that are unconditional and
index-free: the `open_hemisphere` field is preserved under *any* re-indexing (it only quantifies over
vertices, with no edge/successor structure), and `three_le` / `two_le` are arithmetic. -/

/-- The open-hemisphere witness of a strictly convex polygon survives composition with *any* vertex
re-indexing `σ : Fin m → Fin l`: the same functional `h` works, since the field only asks each
re-indexed vertex `P (σ j)` to have positive inner product with `h`. -/
theorem open_hemisphere_reindex {l m : ℕ} [NeZero l] [NeZero m] {P : Fin l → S2}
    (h : StrictConvexSphPolygon P) (σ : Fin m → Fin l) :
    ∃ hh : E3, ‖hh‖ = 1 ∧ ∀ j : Fin m, 0 < ⟪hh, ((P ∘ σ) j : E3)⟫ := by
  obtain ⟨hh, hhn, hhpos⟩ := h.open_hemisphere
  exact ⟨hh, hhn, fun j => hhpos (σ j)⟩

/-! ## `det3` repeated-column vanishing and vertex distinctness from a strict support.

A strict support `0 < sOrient (P a)(P b)(P c)` forces the three vertices pairwise distinct AND
pairwise non-antipodal-when-the-third-witnesses, the analytic content needed to certify that a cut
diagonal is a `ShortArc`. -/

/-- `det3 a b a = 0`: a determinant with a repeated column vanishes. -/
theorem det3_self_right (a b : E3) : det3 a b a = 0 := by
  simp only [det3]; ring

/-- `det3 a a b = 0`: a determinant with a repeated (first/second) column vanishes. -/
theorem det3_self_left (a b : E3) : det3 a a b = 0 := by
  simp only [det3]; ring

/-- `det3 a b b = 0`: a determinant with a repeated (second/third) column vanishes. -/
theorem det3_self_mid (a b : E3) : det3 a b b = 0 := by
  simp only [det3]; ring

/-- A strict orientation `0 < sOrient a b c` forces `a ≠ c`. -/
theorem ne_of_sOrient_pos_ac {a b c : S2} (h : 0 < sOrient a b c) : a ≠ c := by
  intro he
  apply (ne_of_gt h).symm
  rw [sOrient, he, det3_self_right]

/-- A strict orientation `0 < sOrient a b c` forces `a` and `c` non-antipodal: if `(a:E3) = -(c:E3)`
then `sOrient a b c = -sOrient c b c = 0` (a repeated column up to sign), contradicting positivity. -/
theorem not_antipodal_of_sOrient_pos_ac {a b c : S2} (h : 0 < sOrient a b c) :
    (a : E3) ≠ -(c : E3) := by
  intro he
  apply (ne_of_gt h).symm
  have : sOrient a b c = det3 (-(c : E3)) (b : E3) (c : E3) := by rw [sOrient, he]
  rw [this]
  simp only [det3, PiLp.neg_apply]; ring

/-! ## The last-vertex-drop cut arm.

The cleanest `Fin (n+1)`-subfamily cut of an arm `A : Fin (n+1+1) → S2` drops the *last* vertex,
keeping `cutArm A := A ∘ Fin.castSucc : Fin (n+1) → S2` (the first `n+1` vertices `A 0, …, A n`).  Its
closure polygon `(A 0, …, A n)` has the same edges as `A`'s closure *except* the new closing diagonal
`A n → A 0`, which by `cut_diagonal_supports` (cyclic form) supports every interior vertex strictly.
This re-indexing always produces a `StrictConvexSphArm` from a strictly convex arm of one more vertex
(no stuck hypothesis is needed — *any* sub-polygon of a strictly convex polygon obtained by deleting a
vertex is strictly convex), and it shares the first endpoint `A 0`.  It is the faithful payload of
`DiagonalCutArm`. -/

/-- The last-vertex-drop cut arm: keep the first `n+1` vertices `A 0, …, A n`. -/
def cutArm {n : ℕ} (A : Fin (n + 1 + 1) → S2) : Fin (n + 1) → S2 :=
  fun j => A j.castSucc

@[simp] theorem cutArm_apply {n : ℕ} (A : Fin (n + 1 + 1) → S2) (j : Fin (n + 1)) :
    cutArm A j = A j.castSucc := rfl

@[simp] theorem cutArm_zero {n : ℕ} (A : Fin (n + 1 + 1) → S2) :
    cutArm A 0 = A 0 := by simp [cutArm]

/-- For a non-last index `j` of `Fin (n+1)`, the cyclic successor commutes with `cutArm`:
`cutArm A (j+1) = A (j.castSucc + 1)` — no wraparound, so the edge `j` of the cut arm is the edge
`j.castSucc` of `A`. -/
theorem cutArm_succ_of_ne_last {n : ℕ} (A : Fin (n + 1 + 1) → S2) {j : Fin (n + 1)}
    (hj : j ≠ Fin.last n) :
    cutArm A (j + 1) = A (j.castSucc + 1) := by
  have hjlt := j.isLt
  have hjv : j.val < n := by
    rcases Nat.lt_or_ge j.val n with h | h
    · exact h
    · exact absurd (Fin.ext (by simp only [Fin.val_last]; omega)) hj
  show A (j + 1).castSucc = A (j.castSucc + 1)
  congr 1
  apply Fin.ext
  have h1 : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have h1' : ((1 : Fin (n + 1 + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  simp only [Fin.val_castSucc, Fin.val_add, h1, h1']
  rw [Nat.mod_eq_of_lt (show j.val + 1 < n + 1 by omega)]
  rw [Nat.mod_eq_of_lt (show j.val + 1 < n + 1 + 1 by omega)]

/-- At the last index, the cyclic successor wraps to `0`: `cutArm A (Fin.last n + 1) = A 0`. -/
theorem cutArm_succ_last {n : ℕ} (A : Fin (n + 1 + 1) → S2) :
    cutArm A (Fin.last n + 1) = A 0 := by
  rw [show (Fin.last n + 1 : Fin (n + 1)) = 0 by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_last, Fin.val_zero, Fin.val_one']
    rcases n with _ | m
    · rfl
    · rw [Nat.mod_eq_of_lt (show 1 < m + 1 + 1 by omega)]
      simp [Nat.mod_self]]
  exact cutArm_zero A

/-- The last vertex of the cut arm is `A n` (`= A (Fin.last n).castSucc`). -/
theorem cutArm_last {n : ℕ} (A : Fin (n + 1 + 1) → S2) :
    cutArm A (Fin.last n) = A (Fin.last n).castSucc := rfl

/-! ## Diagonal facts for the closing cut edge `A n → A 0`.

The cut arm's only new edge is `A ⟨n⟩ → A 0`, the closing diagonal of `A`'s polygon.  We extract its
`ShortArc` and support certificates from the unconditional `cut_diagonal_supports`. -/

/-- The closing diagonal `A 0 → A k` (for an interior `0 < k < n+1`) strictly supports the last vertex
`A ⟨n+1⟩`'s predecessor `A ⟨n⟩ = A (Fin.last n).castSucc`.  Direct from `cut_diagonal_supports`. -/
theorem diag_support_closing {n : ℕ} {A : Fin (n + 1 + 1) → S2}
    (hP : StrictConvexSphPolygon A) {k : Fin (n + 1 + 1)} (h0k : 0 < k)
    (hkn : k < (Fin.last n).castSucc) :
    0 < sOrient (A 0) (A k) (A (Fin.last n).castSucc) :=
  cut_diagonal_supports hP h0k hkn

/-- The closing cut edge `A ⟨n⟩ → A 0` is a short arc, when `A`'s polygon has an interior vertex
(`n ≥ 2`): pick an interior `A k` strictly supported by the diagonal `A 0 → A ⟨n⟩`, which forces
`A 0 ≠ A ⟨n⟩` and `A 0` non-antipodal to `A ⟨n⟩`. -/
theorem shortArc_closing_diag {n : ℕ} {A : Fin (n + 1 + 1) → S2}
    (hP : StrictConvexSphPolygon A) (hn : 2 ≤ n) :
    ShortArc (A (Fin.last n).castSucc) (A 0) := by
  -- interior vertex `k = 1` (exists since `n ≥ 2` makes `1 < n` strict, and `1 < n+1`).
  have h1 : (0 : Fin (n + 1 + 1)) < 1 := by
    rw [Fin.lt_def]; simp only [Fin.val_zero, Fin.val_one']
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have h1n : (1 : Fin (n + 1 + 1)) < (Fin.last n).castSucc := by
    rw [Fin.lt_def]; simp only [Fin.val_one', Fin.val_castSucc, Fin.val_last]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hpos := diag_support_closing hP h1 h1n
  -- `0 < sOrient (A 0)(A 1)(A ⟨n⟩)` ⟹ `A 0 ≠ A ⟨n⟩`, non-antipodal; symmetrise to the edge order.
  have hne : A 0 ≠ A (Fin.last n).castSucc := ne_of_sOrient_pos_ac hpos
  have hnanti : (A 0 : E3) ≠ -(A (Fin.last n).castSucc : E3) :=
    not_antipodal_of_sOrient_pos_ac hpos
  refine ⟨?_, ?_⟩
  · exact fun he => hne he.symm
  · intro he
    apply hnanti
    rw [he, neg_neg]

/-! ## The cut-arm polygon is strictly convex.

We transport the four `StrictConvexSphPolygon` fields of `A` (modulus `n+2`) to `cutArm A` (modulus
`n+1`).  Non-closing edges (`i ≠ last`) inherit directly from `A`'s edges via `cutArm_succ_of_ne_last`
and `Fin.castSucc` injectivity; the single closing edge `A ⟨n⟩ → A 0` is the cut diagonal, handled by
`shortArc_closing_diag` (short arc) and `cut_diagonal_supports` (supports, via cyclic re-indexing). -/

/-- `Fin.castSucc` is order-preserving and injective on values: this packages the index transport for
the support fields. -/
theorem castSucc_succ_eq {n : ℕ} {i : Fin (n + 1)} (hi : i ≠ Fin.last n) :
    (i.castSucc + 1 : Fin (n + 1 + 1)) = (i + 1).castSucc := by
  have hiv : i.val < n := by
    rcases Nat.lt_or_ge i.val n with h | h
    · exact h
    · exact absurd (Fin.ext (by simp only [Fin.val_last]; omega)) hi
  apply Fin.ext
  have h1' : ((1 : Fin (n + 1 + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have h1 : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  simp only [Fin.val_add, Fin.val_castSucc, h1', h1]
  rw [Nat.mod_eq_of_lt (show i.val + 1 < n + 1 + 1 by omega),
    Nat.mod_eq_of_lt (show i.val + 1 < n + 1 by omega)]

/-- **The cut-arm polygon is strictly convex.**  Dropping the last vertex of a strictly convex
spherical arm `A` yields a strictly convex polygon on the first `n+1` vertices. -/
theorem cutArm_strictConvexPolygon {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hn : 2 ≤ n) :
    StrictConvexSphPolygon (cutArm A) := by
  have hP := hA.closed_convex
  have hcastInj : Function.Injective (Fin.castSucc : Fin (n + 1) → Fin (n + 1 + 1)) :=
    Fin.castSucc_injective _
  refine
    { three_le := by omega
      edge_short := ?_
      edge_support := ?_
      strict_nonincident := ?_
      open_hemisphere := ?_ }
  · -- edge_short
    intro i
    by_cases hi : i = Fin.last n
    · subst hi
      rw [cutArm_last, cutArm_succ_last]
      exact shortArc_closing_diag hP hn
    · rw [cutArm_apply, cutArm_succ_of_ne_last A hi]
      exact hP.edge_short i.castSucc
  · -- edge_support
    intro i j
    by_cases hi : i = Fin.last n
    · subst hi
      rw [cutArm_last, cutArm_succ_last, cutArm_apply]
      -- closing edge support: `0 ≤ sOrient (A ⟨n⟩)(A 0)(A j.castSucc)`
      by_cases hj0 : j = (0 : Fin (n + 1))
      · subst hj0
        simp only [Fin.castSucc_zero, sOrient]
        rw [det3_self_mid]
      · by_cases hjl : j = Fin.last n
        · subst hjl
          simp only [sOrient]
          rw [det3_self_right]
        · -- interior j: strict, hence ≥ 0, via cyclic re-indexing of the diagonal support
          have h0j : (0 : Fin (n + 1 + 1)) < j.castSucc := by
            rw [Fin.lt_def, Fin.val_zero, Fin.val_castSucc]
            have : j.val ≠ 0 := fun h => hj0 (Fin.ext (by simp [h]))
            omega
          have hjn : j.castSucc < (Fin.last n).castSucc := by
            rw [Fin.lt_def, Fin.val_castSucc, Fin.val_castSucc, Fin.val_last]
            have : j.val ≠ n := fun h => hjl (Fin.ext (by simp [Fin.val_last, h]))
            have := j.isLt; omega
          have hpos := diag_support_closing hP h0j hjn
          -- `sOrient (A ⟨n⟩)(A 0)(A j.castSucc) = sOrient (A 0)(A j.castSucc)(A ⟨n⟩)`
          have hcyc : sOrient (A (Fin.last n).castSucc) (A 0) (A j.castSucc)
              = sOrient (A 0) (A j.castSucc) (A (Fin.last n).castSucc) :=
            (sOrient_cyclic _ _ _).1
          rw [hcyc]; exact le_of_lt hpos
    · rw [cutArm_apply, cutArm_succ_of_ne_last A hi, cutArm_apply]
      exact hP.edge_support i.castSucc j.castSucc
  · -- strict_nonincident
    intro i j hji hji1
    by_cases hi : i = Fin.last n
    · subst hi
      rw [cutArm_last, cutArm_succ_last, cutArm_apply]
      -- closing edge: `j ≠ last`, `j ≠ 0`, so `j.castSucc` is interior; strict via diagonal.
      have hlast1 : (Fin.last n + 1 : Fin (n + 1)) = 0 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_last, Fin.val_zero, Fin.val_one']
        rcases n with _ | m
        · rfl
        · rw [Nat.mod_eq_of_lt (show 1 < m + 1 + 1 by omega)]
          simp [Nat.mod_self]
      have hj0 : j ≠ (0 : Fin (n + 1)) := by
        intro h; apply hji1; rw [h, hlast1]
      have hjl : j ≠ Fin.last n := hji
      have h0j : (0 : Fin (n + 1 + 1)) < j.castSucc := by
        rw [Fin.lt_def, Fin.val_zero, Fin.val_castSucc]
        have : j.val ≠ 0 := fun h => hj0 (Fin.ext (by simp [h]))
        omega
      have hjn : j.castSucc < (Fin.last n).castSucc := by
        rw [Fin.lt_def, Fin.val_castSucc, Fin.val_castSucc, Fin.val_last]
        have : j.val ≠ n := fun h => hjl (Fin.ext (by simp [Fin.val_last, h]))
        have := j.isLt; omega
      have hpos := diag_support_closing hP h0j hjn
      have hcyc : sOrient (A (Fin.last n).castSucc) (A 0) (A j.castSucc)
          = sOrient (A 0) (A j.castSucc) (A (Fin.last n).castSucc) :=
        (sOrient_cyclic _ _ _).1
      rw [hcyc]; exact hpos
    · rw [cutArm_apply, cutArm_succ_of_ne_last A hi, cutArm_apply]
      refine hP.strict_nonincident i.castSucc j.castSucc ?_ ?_
      · exact fun h => hji (hcastInj h)
      · rw [castSucc_succ_eq hi]
        exact fun h => hji1 (hcastInj h)
  · -- open_hemisphere
    exact open_hemisphere_reindex hP Fin.castSucc

/-- **The cut arm is a strictly convex arm.**  For an arm `A` of `≥ 3` edges (`n ≥ 2`), the
last-vertex-drop `cutArm A` is again a `StrictConvexSphArm`. -/
theorem cutArm_strictConvexArm {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hn : 2 ≤ n) :
    StrictConvexSphArm (cutArm A) :=
  { two_le := hn
    closed_convex := cutArm_strictConvexPolygon A hA hn }

/-! ## Discharging `DiagonalCutArm`.

`DiagonalCutArm` asks: a strictly convex arm `A : Fin (n+1+1) → S2` with a vanishing *non-incident*
support admits a re-indexed `Fin (n+1)`-sub-arm that is `StrictConvexSphArm` and shares `A 0`.

* For `n ≥ 2` (`A` has `≥ 3` edges) the last-vertex-drop `cutArm A` is the witness
  (`cutArm_strictConvexArm`, `cutArm_zero`); the stuck hypothesis is not even needed — *any*
  vertex-deletion of a strictly convex arm is strictly convex.
* For `n = 1` (`A : Fin 3`, a triangle-arm) the hypothesis `sOrient (A i)(A (i+1))(A j) = 0` with `j`
  non-incident **contradicts** `A`'s own `strict_nonincident` field (which gives
  `0 < sOrient (A i)(A (i+1))(A j)` for exactly such a non-incident triple).  So the case is vacuous,
  and `DiagonalCutArm` holds there too. -/

/-- **`DiagonalCutArm` — proved.**  The diagonal-cut sub-arm construction: a stuck strictly convex
spherical arm admits a re-indexed `Fin (n+1)`-sub-arm that is again `StrictConvexSphArm` and shares the
first endpoint.  Built unconditionally from the last-vertex-drop re-indexing `cutArm` (whose convexity
transport is `cutArm_strictConvexPolygon`), with the degenerate triangle-arm case discharged by the
arm's own `strict_nonincident` field. -/
theorem diagonalCutArm_holds : DiagonalCutArm := by
  intro n A hA i j hji hji1 hstuck
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · -- n < 2: since `A` is an arm, `2 ≤ n+1`, so `n ≥ 1`, hence `n = 1` and `A : Fin 3`.
    have hn1 : n = 1 := by have := hA.two_le; omega
    subst hn1
    -- the non-incident strict support contradicts the vanishing hypothesis.
    exact absurd hstuck (ne_of_gt (hA.closed_convex.strict_nonincident i j hji hji1))
  · -- n ≥ 2: the last-vertex-drop cut arm is the witness.
    exact ⟨cutArm A, cutArm_strictConvexArm A hA hge, cutArm_zero A⟩

end ProofsInTheBook.SphericalDiagCut
