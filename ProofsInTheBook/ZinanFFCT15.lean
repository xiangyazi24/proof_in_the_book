import ProofsInTheBook.ZinanFFCT14

/-!
# `ZinanFFCT15` — the backward half and the headline of `PlanarWeakNoflatStrictEdgeCore`

The backward-case instantiation of `ZinanFFCT9.forward_strict_support` (normal `-h`, apex
`f (i+1)`, chain `σs t = f (i−t) − f (i+1)`), the mirror of `ZinanFFCT14.forward_case`, with
every hypothesis discharged from the corrected residue's inputs per
`HANDOFF/ffct12-assembly-spec.md`:

* `hsupp`/`hturn` from `hweak` through the plane transport `det3_plane_eq` + `det3_neg_left`
  + row rotations;
* `hcons` through `ZinanFFCT13.hcons_of_no_behind`, the backward witnesses
  (`σs t = −(s • b')`, i.e. `f (i−t) − f (i+1) = −(s • (f i − f (i+1)))`) killed by
  `ZinanFFCT14.no_beyond_vertex` (successor edge or `hlast`), with the degenerate `σs 0 = b'`
  witness killed by `(1+s) • b' = 0`;
* the first joint from `hnoflat` at `v = i`;
* `hnotanti` through `ZinanFFCT12.antiparallel_of_theta_pi` + the same beyond-witness kill at
  `w = j`.

The headline `planarWeakNoflatStrictEdgeCore_holds` glues `forward_case` (j ≥ i+2) and
`backward_case` (j ≤ i−1) by an `omega` case split on `j ≠ i`, `j ≠ i + 1`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT8 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT13 ProofsInTheBook.ZinanFFCT14

namespace ProofsInTheBook.ZinanFFCT15

set_option maxHeartbeats 3200000

/-- **The backward half of the corrected planar residue**: strict support of edge `(i, i+1)` at
every vertex `j ≤ i − 1` (the beyond-witnesses of every care-point killed internally or by
`hlast`).  Mirror of `ZinanFFCT14.forward_case` with reversed normal `-h` and apex `f (i+1)`. -/
theorem backward_case {n : ℕ} (h : E3) (f : Fin (n + 1) → E3)
    (hinj : Function.Injective f)
    (hplane : ∀ i : Fin (n + 1), (⟪h, f i⟫ : ℝ) = 1)
    (hweak : ∀ a c : ℕ, ∀ (ha1 : a + 1 < n + 1) (hc : c < n + 1),
      0 ≤ det3 (f ⟨a, by omega⟩) (f ⟨a + 1, ha1⟩) (f ⟨c, hc⟩))
    (hnoflat : ∀ v : ℕ, 1 ≤ v → ∀ (hv1 : v + 1 < n + 1),
      0 < det3 (f ⟨v - 1, by omega⟩) (f ⟨v, by omega⟩) (f ⟨v + 1, hv1⟩))
    (hlast : ∀ c : ℕ, ∀ (hc : c < n + 1), ∀ t : ℝ, 0 < t →
      f ⟨c, hc⟩ ≠ f ⟨n, by omega⟩ + t • (f ⟨n, by omega⟩ - f ⟨n - 1, by omega⟩))
    (i j : ℕ) (hji : j + 1 ≤ i) (hi1 : i + 1 < n + 1) (hj : j < n + 1) :
    0 < det3 (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) (f ⟨j, hj⟩) := by
  have hh : h ≠ 0 := normal_ne_zero_of_plane hplane ⟨0, by omega⟩
  have hhn : (0:ℝ) < ‖h‖ ^ 2 := by
    have := norm_pos_iff.mpr hh
    positivity
  have hipos : 1 ≤ i := by omega
  -- the reversed chain of apex differences (clamped; on `t ≤ N'` it is `f (i−t) − f (i+1)`)
  set N := i - j with hN_def
  have hN1 : 1 ≤ N := by omega
  set σs : ℕ → E3 :=
    fun t => f ⟨i - min t i, by omega⟩ - f ⟨i + 1, hi1⟩ with hσs_def
  have hidx : ∀ t, t ≤ N → i - min t i = i - t := by
    intro t ht
    have : min t i = t := Nat.min_eq_left (by omega)
    rw [this]
  have hσ : ∀ t, (ht : t ≤ N) →
      σs t = f ⟨i - t, by omega⟩ - f ⟨i + 1, hi1⟩ := by
    intro t ht
    simp only [hσs_def]
    congr 2
    exact Fin.ext (by simpa using hidx t ht)
  set b : E3 := f ⟨i, by omega⟩ - f ⟨i + 1, hi1⟩ with hb_def
  -- in-plane differences are perpendicular to the normal
  have hperp' : ∀ (u v : Fin (n + 1)), (⟪h, f u - f v⟫ : ℝ) = 0 := by
    intro u v
    rw [inner_sub_right, hplane u, hplane v]; ring
  -- nonzero differences from injectivity
  have hne' : ∀ (u v : Fin (n + 1)), u ≠ v → f u - f v ≠ 0 := by
    intro u v huv hz
    exact huv (hinj (by rwa [sub_eq_zero] at hz))
  -- the plane transport with reversed normal:
  -- `det3 (-h) (f u − f (i+1)) (f w − f (i+1)) = det3 (f (i+1)) (f u) (f w) · ‖h‖² · (−1)`
  have htrans : ∀ (u w : Fin (n + 1)),
      det3 (-h) (f u - f ⟨i + 1, hi1⟩) (f w - f ⟨i + 1, hi1⟩)
        = det3 (f ⟨i + 1, hi1⟩) (f u) (f w) * ‖h‖ ^ 2 * (-1) := by
    intro u w
    rw [det3_neg_left]
    rw [(det3_plane_eq (hplane ⟨i + 1, hi1⟩) (hplane u) (hplane w)).symm]
    ring
  -- the normal `-h`
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have hbh0 : (⟪-h, b⟫ : ℝ) = 0 := by rw [inner_neg_left, hperp' _ _]; ring
  have hbne : b ≠ 0 := hne' _ _ (by
    intro hcontra
    have := congrArg Fin.val hcontra
    simp at this)
  -- σs 0 = b
  have hi0eq : f ⟨i - 0, by omega⟩ = f ⟨i, by omega⟩ := by
    congr 1
  have hσ0 : σs 0 = b := by
    rw [hσ 0 (by omega), hb_def, hi0eq]
  -- the five chain hypotheses (normal `-h`, base `b`)
  have hperp : ∀ t, t ≤ N → (⟪-h, σs t⟫ : ℝ) = 0 := by
    intro t ht
    rw [hσ t ht, inner_neg_left, hperp' _ _]; ring
  have hne : ∀ t, t ≤ N → σs t ≠ 0 := by
    intro t ht
    rw [hσ t ht]
    exact hne' _ _ (by
      intro hcontra
      have := congrArg Fin.val hcontra
      simp at this; omega)
  have hsupp : ∀ t, t ≤ N → 0 ≤ det3 (-h) b (σs t) := by
    intro t ht
    rw [hσ t ht, hb_def, htrans]
    -- det3 (f (i+1)) (f i) (f (i-t)) = -det3 (f i) (f (i+1)) (f (i-t))
    have hsw : det3 (f ⟨i + 1, hi1⟩) (f ⟨i, by omega⟩) (f ⟨i - t, by omega⟩)
        = -det3 (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) (f ⟨i - t, by omega⟩) := by
      rw [det3_swap12]
    rw [hsw]
    have hwk := hweak i (i - t) hi1 (by omega)
    nlinarith [hwk, hhn]
  have hturn : ∀ t, t + 1 ≤ N → 0 ≤ det3 (-h) (σs t) (σs (t + 1)) := by
    intro t ht
    rw [hσ t (by omega), hσ (t + 1) ht, htrans]
    -- det3 (f (i+1)) (f (i-t)) (f (i-t-1)) = -det3 (f (i-t-1)) (f (i-t)) (f (i+1))
    have heqw : f ⟨i - (t + 1), by omega⟩ = f ⟨i - t - 1, by omega⟩ := by
      congr 1
    rw [heqw]
    have hcyc : det3 (f ⟨i + 1, hi1⟩) (f ⟨i - t, by omega⟩) (f ⟨i - t - 1, by omega⟩)
        = det3 (f ⟨i - t, by omega⟩) (f ⟨i - t - 1, by omega⟩) (f ⟨i + 1, hi1⟩) := by
      rw [det3_cyclic]
    rw [hcyc]
    have hsw : det3 (f ⟨i - t, by omega⟩) (f ⟨i - t - 1, by omega⟩) (f ⟨i + 1, hi1⟩)
        = -det3 (f ⟨i - t - 1, by omega⟩) (f ⟨i - t, by omega⟩) (f ⟨i + 1, hi1⟩) := by
      rw [det3_swap12]
    rw [hsw]
    -- hweak (i-t-1) (i+1): det3 (f (i-t-1)) (f (i-t-1+1)) (f (i+1)) with i-t-1+1 = i-t
    have hp1 : i - t - 1 + 1 < n + 1 := by omega
    have hwk := hweak (i - t - 1) (i + 1) hp1 (by omega)
    have heqp : f ⟨i - t - 1 + 1, hp1⟩ = f ⟨i - t, by omega⟩ := by
      congr 1; exact Fin.ext (by simp; omega)
    rw [heqp] at hwk
    nlinarith [hwk, hhn]
  -- the `hcons` discharge: no consecutive antiparallelism
  have hcons : ∀ t, t + 1 ≤ N → -1 < ncos (σs t) (σs (t + 1)) := by
    intro t ht
    refine hcons_of_no_behind hbh0 (hperp t (by omega)) hnh hbne
      (hne t (by omega)) (hne (t + 1) ht) (hsupp t (by omega)) (hsupp (t + 1) ht) ?_ ?_
    · -- no beyond witness on `σs t`
      rintro ⟨s, hs, hwit⟩
      rw [hσ t (by omega)] at hwit
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · -- `t = 0`: the witness is `b = −(s • b)`, impossible
        subst ht0
        have hbb : f ⟨i - 0, by omega⟩ - f ⟨i + 1, hi1⟩ = b := by
          rw [hb_def, hi0eq]
        rw [hbb] at hwit
        have hz : (1 + s) • b = 0 := by
          have := hwit
          linear_combination (norm := module) this
        have hb0' : b = 0 := by
          have h1s : (1 + s : ℝ) ≠ 0 := by positivity
          exact (smul_eq_zero.mp hz).resolve_left h1s
        exact hbne hb0'
      · -- `t ≥ 1`: a genuine beyond-vertex, killed
        exact no_beyond_vertex h f hweak hnoflat hlast i (i - t) hi1 (by omega) s hs hwit
    · -- no beyond witness on `σs (t+1)`
      rintro ⟨s, hs, hwit⟩
      rw [hσ (t + 1) ht] at hwit
      exact no_beyond_vertex h f hweak hnoflat hlast i (i - (t + 1)) hi1 (by omega) s hs hwit
  -- the strict first joint (hnoflat at v = i)
  have hfj : 0 < det3 (-h) b (σs 1) := by
    rw [hσ 1 hN1, hb_def, htrans]
    -- det3 (f (i+1)) (f i) (f (i-1)) cyclic→ det3 (f i) (f (i-1)) (f (i+1)) swap→ -det3 (f (i-1)) (f i) (f (i+1))
    have hcyc : det3 (f ⟨i + 1, hi1⟩) (f ⟨i, by omega⟩) (f ⟨i - 1, by omega⟩)
        = det3 (f ⟨i, by omega⟩) (f ⟨i - 1, by omega⟩) (f ⟨i + 1, hi1⟩) := by
      rw [det3_cyclic]
    rw [hcyc]
    have hsw : det3 (f ⟨i, by omega⟩) (f ⟨i - 1, by omega⟩) (f ⟨i + 1, hi1⟩)
        = -det3 (f ⟨i - 1, by omega⟩) (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) := by
      rw [det3_swap12]
    rw [hsw]
    have hjoint := hnoflat i hipos hi1
    nlinarith [hjoint, hhn]
  -- the antipodal care-point at the target vertex
  have hnotanti : theta b (σs N) ≠ Real.pi := by
    intro hpi
    obtain ⟨s, hs, hwit⟩ := antiparallel_of_theta_pi hbne (hne N le_rfl) hpi
    rw [hσ N le_rfl] at hwit
    -- σs N = f (i-N) - f (i+1) = f j - f (i+1); witness shape matches no_beyond_vertex at w = i-N
    exact no_beyond_vertex h f hweak hnoflat hlast i (i - N) hi1 (by omega) s hs hwit
  -- assemble via forward_strict_support with normal `-h`
  have hmain := forward_strict_support (h := -h) (b := b) σs N hbh0 hnh hbne
    hperp hne hsupp hturn hcons hfj hN1 N hN1 le_rfl hnotanti
  -- transport back to the points
  rw [hσ N le_rfl, hb_def, htrans] at hmain
  have hjeq : f ⟨i - N, by omega⟩ = f ⟨j, hj⟩ := by
    congr 1; exact Fin.ext (by simp; omega)
  rw [hjeq] at hmain
  -- hmain : 0 < det3 (f (i+1)) (f i) (f j) * ‖h‖² * (-1)
  -- det3 (f (i+1)) (f i) (f j) = -det3 (f i) (f (i+1)) (f j)
  have hsw : det3 (f ⟨i + 1, hi1⟩) (f ⟨i, by omega⟩) (f ⟨j, hj⟩)
      = -det3 (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) (f ⟨j, hj⟩) := by
    rw [det3_swap12]
  rw [hsw] at hmain
  nlinarith [hmain, hhn]

/-! ## §The headline: gluing the forward and backward halves. -/

/-- **The corrected planar residue holds.**  `PlanarWeakNoflatStrictEdgeCore`: for an injective
in-plane family with weak edge supports, strict interior joints, and the two boundary-collinearity
exclusions, every non-incident directed edge `(i, i+1)` strictly supports every vertex `j`.  The
forward half (`j ≥ i+2`) is `ZinanFFCT14.forward_case`; the backward half (`j ≤ i−1`) is
`backward_case`; the two are glued by `omega` on `j ≠ i`, `j ≠ i+1`.  (The carve-out hypotheses
`hhead`/`htail` are subsumed by `hfirst`/`hlast` and are not used.) -/
theorem planarWeakNoflatStrictEdgeCore_holds : PlanarWeakNoflatStrictEdgeCore := by
  intro n h f hinj hplane hweak hnoflat hfirst hlast i j hji hji1 hi1 hj _hhead _htail
  rcases Nat.lt_or_ge j i with hlt | hge
  · -- backward: j ≤ i − 1
    exact backward_case h f hinj hplane hweak hnoflat hlast i j (by omega) hi1 hj
  · -- forward: j ≥ i + 2 (since j ≠ i, j ≠ i+1, j ≥ i)
    exact forward_case h f hinj hplane hweak hnoflat hfirst i j (by omega) hi1 hj

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanFFCT15.backward_case
#print axioms ProofsInTheBook.ZinanFFCT15.planarWeakNoflatStrictEdgeCore_holds

end ProofsInTheBook.ZinanFFCT15
