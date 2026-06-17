import ProofsInTheBook.ZinanFFCT12

/-!
# `ZinanFFCT13` — stage 2 bridges: the consecutive-antiparallel (`hcons`) discharge core

Per `HANDOFF/ffct12-assembly-spec.md`: instantiating `ZinanFFCT9.forward_strict_support` requires,
for each consecutive pair of apex differences, the non-antipodality `-1 < ncos (ρs t) (ρs (t+1))`.
This file proves the discharge core, abstractly in `E3` (no index plumbing):

* **`behind_witness_of_antiparallel`** — if two weakly-supported apex differences are antiparallel,
  both lie on the base line and ONE of them points strictly *backward* (`= -(t • b)`, `t > 0`).
  The indexed caller then kills that witness with `ZinanFFCT10.no_backward_collinear_kill`
  (predecessor edge, `i ≥ 1`) or the `hfirst` boundary exclusion (`i = 0`); for the backward chain
  (base `f i - f (i+1)`, apex `f (i+1)`) the SAME lemma applies verbatim and the witness is killed by
  `no_forward_collinear_kill` (successor edge) or `hlast`.
* **`hcons_of_no_behind`** — the packaged form: if no backward-pointing witness exists among the two
  differences, the consecutive turn is not antipodal (`-1 < ncos u v`), exactly the `hcons` slot.
* point/difference conversion helpers for feeding the FFCT10 kills.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT8 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12

namespace ProofsInTheBook.ZinanFFCT13

set_option maxHeartbeats 1600000

/-- If every vertex lies in the affine plane `⟪h, x⟫ = 1`, then `h ≠ 0`. -/
theorem normal_ne_zero_of_plane {n : ℕ} {h : E3} {f : Fin (n + 1) → E3}
    (hplane : ∀ i : Fin (n + 1), (⟪h, f i⟫ : ℝ) = 1)
    (i : Fin (n + 1)) : h ≠ 0 := by
  intro hz
  have hi := hplane i
  rw [hz] at hi
  simp at hi

/-- Difference form → point form for the backward-collinearity kill:
`q - p₀ = -(t • (p₁ - p₀))` rewrites to `q = p₀ - t • (p₁ - p₀)`. -/
theorem point_of_diff_behind {p0 p1 q : E3} {t : ℝ}
    (hd : q - p0 = -(t • (p1 - p0))) : q = p0 - t • (p1 - p0) := by
  linear_combination (norm := module) hd

/-- Difference form → point form for the forward-collinearity kill, at the far apex:
`q - p₁ = -(t • (p₀ - p₁))` rewrites to `q = p₁ + t • (p₁ - p₀)`. -/
theorem point_of_diff_beyond {p0 p1 q : E3} {t : ℝ}
    (hd : q - p1 = -(t • (p0 - p1))) : q = p1 + t • (p1 - p0) := by
  have h1 : -(t • (p0 - p1)) = t • (p1 - p0) := by module
  rw [h1] at hd
  linear_combination (norm := module) hd

/-- **The `hcons` discharge core.**  Two nonzero apex differences `u, v ⊥ h`, both weakly supported
by the base (`0 ≤ det3 h b u`, `0 ≤ det3 h b v`), cannot be antiparallel unless one of them points
strictly backward along the base ray: antiparallelism forces both onto the base line with opposite
parameters. -/
theorem behind_witness_of_antiparallel {h b u v : E3}
    (hb0 : (⟪h,b⟫:ℝ) = 0) (hu0 : (⟪h,u⟫:ℝ) = 0)
    (hh : h ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0)
    (hsuppu : 0 ≤ det3 h b u) (hsuppv : 0 ≤ det3 h b v)
    {s : ℝ} (hs : 0 < s) (hanti : v = -(s • u)) :
    (∃ t : ℝ, 0 < t ∧ u = -(t • b)) ∨ (∃ t : ℝ, 0 < t ∧ v = -(t • b)) := by
  -- the two supports squeeze the base support of `u` to zero
  have hvdet : det3 h b v = -s * det3 h b u := by
    rw [hanti]
    have h1 : -(s • u) = (-s) • u := by module
    rw [h1, det3_smul_right]
  have huz : det3 h b u = 0 := by nlinarith [hsuppu, hsuppv, hvdet, hs]
  -- hence `u` lies on the base line
  obtain ⟨c, hc⟩ := collinear_of_det3_zero hb0 hu0 hh hb huz
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact hu hc
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · -- `u = c • b`, `c < 0`: `u` itself is the backward witness
    exact Or.inl ⟨-c, by linarith, by rw [hc]; module⟩
  · -- `c > 0`: then `v = (-s·c) • b` with `-s·c < 0` is the backward witness
    refine Or.inr ⟨s * c, by positivity, ?_⟩
    rw [hanti, hc]
    module

/-- **`hcons` from the absence of backward witnesses.**  If neither apex difference points strictly
backward along the base ray, the consecutive turn is not antipodal: `-1 < ncos u v`. -/
theorem hcons_of_no_behind {h b u v : E3}
    (hb0 : (⟪h,b⟫:ℝ) = 0) (hu0 : (⟪h,u⟫:ℝ) = 0)
    (hh : h ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hsuppu : 0 ≤ det3 h b u) (hsuppv : 0 ≤ det3 h b v)
    (hnoU : ¬ ∃ t : ℝ, 0 < t ∧ u = -(t • b))
    (hnoV : ¬ ∃ t : ℝ, 0 < t ∧ v = -(t • b)) :
    -1 < ncos u v := by
  rcases lt_or_eq_of_le (ncos_mem hu hv).1 with hlt | heq
  · exact hlt
  · -- `ncos u v = -1`: antiparallel, contradiction with the no-witness hypotheses
    exfalso
    obtain ⟨s, hs, hvu⟩ := antiparallel_of_ncos_neg_one hu hv heq.symm
    rcases behind_witness_of_antiparallel hb0 hu0 hh hb hu hsuppu hsuppv hs hvu with hw | hw
    · exact hnoU hw
    · exact hnoV hw

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanFFCT13.behind_witness_of_antiparallel
#print axioms ProofsInTheBook.ZinanFFCT13.hcons_of_no_behind
#print axioms ProofsInTheBook.ZinanFFCT13.point_of_diff_behind
#print axioms ProofsInTheBook.ZinanFFCT13.point_of_diff_beyond

end ProofsInTheBook.ZinanFFCT13
