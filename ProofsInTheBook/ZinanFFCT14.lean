import ProofsInTheBook.ZinanFFCT13

/-!
# `ZinanFFCT14` — the forward half of `PlanarWeakNoflatStrictEdgeCore`

The forward-case instantiation of `ZinanFFCT9.forward_strict_support` (normal `h`, apex `f i`,
chain `ρs t = f (i+1+t) − f i`), with every hypothesis discharged from the corrected residue's
inputs per `HANDOFF/ffct12-assembly-spec.md`:

* `hsupp`/`hturn` from `hweak` through the plane transport `det3_plane_eq` + row rotations;
* `hcons` through `ZinanFFCT13.hcons_of_no_behind`, the backward witnesses killed by
  `ZinanFFCT10.no_backward_collinear_kill` (predecessor edge, `i ≥ 1`) or the `hfirst` boundary
  exclusion (`i = 0`), with the degenerate `u = b` witness killed by `(1+t) • b = 0`;
* the first joint from `hnoflat` at `v = i+1`;
* `hnotanti` through `ZinanFFCT12.antiparallel_of_theta_pi` + the same backward kill.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT8 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT13

namespace ProofsInTheBook.ZinanFFCT14

set_option maxHeartbeats 3200000

/-- **The backward-collinearity master kill** (shared by `hcons`, `hnotanti`, and the
backward case's beyond-witnesses through reversal): a vertex `w ≥ i+2` cannot satisfy
`f w − f i = −(t • (f (i+1) − f i))` with `t > 0`, given the weak supports, the strict
interior joints, and (`i = 0` only) the first-edge exclusion. -/
theorem no_behind_vertex {n : ℕ} (h : E3) (f : Fin (n + 1) → E3)
    (hweak : ∀ a c : ℕ, ∀ (ha1 : a + 1 < n + 1) (hc : c < n + 1),
      0 ≤ det3 (f ⟨a, by omega⟩) (f ⟨a + 1, ha1⟩) (f ⟨c, hc⟩))
    (hnoflat : ∀ v : ℕ, 1 ≤ v → ∀ (hv1 : v + 1 < n + 1),
      0 < det3 (f ⟨v - 1, by omega⟩) (f ⟨v, by omega⟩) (f ⟨v + 1, hv1⟩))
    (hfirst : ∀ (h1 : 1 < n + 1), ∀ c : ℕ, ∀ (hc : c < n + 1), ∀ t : ℝ, 0 < t →
      f ⟨c, hc⟩ ≠ f ⟨0, by omega⟩ - t • (f ⟨1, h1⟩ - f ⟨0, by omega⟩))
    (i w : ℕ) (hi1 : i + 1 < n + 1) (hw : w < n + 1)
    (t : ℝ) (ht : 0 < t)
    (hcol : f ⟨w, hw⟩ - f ⟨i, by omega⟩
      = -(t • (f ⟨i + 1, hi1⟩ - f ⟨i, by omega⟩))) : False := by
  have hq : f ⟨w, hw⟩ = f ⟨i, by omega⟩
      - t • (f ⟨i + 1, hi1⟩ - f ⟨i, by omega⟩) := point_of_diff_behind hcol
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- `i = 0`: exactly the first-edge exclusion
    subst hi0
    exact hfirst hi1 w hw t ht (by
      have h01 : (⟨0 + 1, hi1⟩ : Fin (n + 1)) = ⟨1, hi1⟩ := rfl
      rw [← h01]; exact hq)
  · -- `i ≥ 1`: predecessor-edge kill
    have hp1 : i - 1 + 1 < n + 1 := by omega
    have hfeq : f ⟨i - 1 + 1, hp1⟩ = f ⟨i, by omega⟩ := by
      congr 1
      exact Fin.ext (by simp; omega)
    have hsupp : 0 ≤ det3 (f ⟨i - 1, by omega⟩) (f ⟨i, by omega⟩) (f ⟨w, hw⟩) := by
      have := hweak (i - 1) w hp1 hw
      rwa [hfeq] at this
    have hjoint : 0 < det3 (f ⟨i - 1, by omega⟩) (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) := by
      have := hnoflat i hipos hi1
      exact this
    exact no_backward_collinear_kill ht hq hsupp hjoint

/-- **The forward-collinearity master kill**: a vertex cannot lie beyond the far end of the
edge `(i, i+1)` on its line — `f w − f (i+1) = −(t • (f i − f (i+1)))`, `t > 0` — given the
weak supports, the strict interior joints, and (`i + 1 = n` only) the last-edge exclusion. -/
theorem no_beyond_vertex {n : ℕ} (h : E3) (f : Fin (n + 1) → E3)
    (hweak : ∀ a c : ℕ, ∀ (ha1 : a + 1 < n + 1) (hc : c < n + 1),
      0 ≤ det3 (f ⟨a, by omega⟩) (f ⟨a + 1, ha1⟩) (f ⟨c, hc⟩))
    (hnoflat : ∀ v : ℕ, 1 ≤ v → ∀ (hv1 : v + 1 < n + 1),
      0 < det3 (f ⟨v - 1, by omega⟩) (f ⟨v, by omega⟩) (f ⟨v + 1, hv1⟩))
    (hlast : ∀ c : ℕ, ∀ (hc : c < n + 1), ∀ t : ℝ, 0 < t →
      f ⟨c, hc⟩ ≠ f ⟨n, by omega⟩ + t • (f ⟨n, by omega⟩ - f ⟨n - 1, by omega⟩))
    (i w : ℕ) (hi1 : i + 1 < n + 1) (hw : w < n + 1)
    (t : ℝ) (ht : 0 < t)
    (hcol : f ⟨w, hw⟩ - f ⟨i + 1, hi1⟩
      = -(t • (f ⟨i, by omega⟩ - f ⟨i + 1, hi1⟩))) : False := by
  have hq : f ⟨w, hw⟩ = f ⟨i + 1, hi1⟩
      + t • (f ⟨i + 1, hi1⟩ - f ⟨i, by omega⟩) := point_of_diff_beyond hcol
  rcases Nat.lt_or_ge (i + 1) n with hlt | hge
  · -- successor edge `(i+1, i+2)` exists: forward kill
    have hp2 : i + 1 + 1 < n + 1 := by omega
    have hsupp : 0 ≤ det3 (f ⟨i + 1, hi1⟩) (f ⟨i + 1 + 1, hp2⟩) (f ⟨w, hw⟩) :=
      hweak (i + 1) w hp2 hw
    have hjoint : 0 < det3 (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) (f ⟨i + 1 + 1, hp2⟩) := by
      have := hnoflat (i + 1) (by omega) hp2
      have hfeq : f ⟨i + 1 - 1, by omega⟩ = f ⟨i, by omega⟩ := rfl
      rwa [hfeq] at this
    exact no_forward_collinear_kill ht hq hsupp hjoint
  · -- `i + 1 = n`: exactly the last-edge exclusion
    have hin : i + 1 = n := by omega
    refine hlast w hw t ht ?_
    have hfn : f ⟨i + 1, hi1⟩ = f ⟨n, by omega⟩ := by
      congr 1; exact Fin.ext (by simp [hin])
    have hfn1 : f ⟨i, by omega⟩ = f ⟨n - 1, by omega⟩ := by
      congr 1; exact Fin.ext (by simp; omega)
    rw [← hfn, ← hfn1]
    exact hq

/-- **The forward half of the corrected planar residue**: strict support of edge `(i, i+1)` at
every vertex `j ≥ i + 2` (the backward witnesses of every care-point killed internally or by
`hfirst`). -/
theorem forward_case {n : ℕ} (h : E3) (f : Fin (n + 1) → E3)
    (hinj : Function.Injective f)
    (hplane : ∀ i : Fin (n + 1), (⟪h, f i⟫ : ℝ) = 1)
    (hweak : ∀ a c : ℕ, ∀ (ha1 : a + 1 < n + 1) (hc : c < n + 1),
      0 ≤ det3 (f ⟨a, by omega⟩) (f ⟨a + 1, ha1⟩) (f ⟨c, hc⟩))
    (hnoflat : ∀ v : ℕ, 1 ≤ v → ∀ (hv1 : v + 1 < n + 1),
      0 < det3 (f ⟨v - 1, by omega⟩) (f ⟨v, by omega⟩) (f ⟨v + 1, hv1⟩))
    (hfirst : ∀ (h1 : 1 < n + 1), ∀ c : ℕ, ∀ (hc : c < n + 1), ∀ t : ℝ, 0 < t →
      f ⟨c, hc⟩ ≠ f ⟨0, by omega⟩ - t • (f ⟨1, h1⟩ - f ⟨0, by omega⟩))
    (i j : ℕ) (hij : i + 2 ≤ j) (hi1 : i + 1 < n + 1) (hj : j < n + 1) :
    0 < det3 (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) (f ⟨j, hj⟩) := by
  have hh : h ≠ 0 := normal_ne_zero_of_plane hplane ⟨0, by omega⟩
  have hhn : (0:ℝ) < ‖h‖ ^ 2 := by
    have := norm_pos_iff.mpr hh
    positivity
  -- the chain of apex differences (clamped; on `t ≤ N` it is `f (i+1+t) − f i`)
  set N := j - (i + 1) with hN_def
  have hN1 : 1 ≤ N := by omega
  set ρs : ℕ → E3 :=
    fun t => f ⟨min (i + 1 + t) n, by omega⟩ - f ⟨i, by omega⟩ with hρs_def
  have hidx : ∀ t, t ≤ N → min (i + 1 + t) n = i + 1 + t := by
    intro t ht
    exact Nat.min_eq_left (by omega)
  have hρ : ∀ t, (ht : t ≤ N) →
      ρs t = f ⟨i + 1 + t, by omega⟩ - f ⟨i, by omega⟩ := by
    intro t ht
    simp only [hρs_def]
    congr 2
    exact Fin.ext (by simpa using hidx t ht)
  set b : E3 := f ⟨i + 1, hi1⟩ - f ⟨i, by omega⟩ with hb_def
  -- in-plane differences are perpendicular to the normal
  have hperp' : ∀ (u v : Fin (n + 1)), (⟪h, f u - f v⟫ : ℝ) = 0 := by
    intro u v
    rw [inner_sub_right, hplane u, hplane v]; ring
  -- nonzero differences from injectivity
  have hne' : ∀ (u v : Fin (n + 1)), u ≠ v → f u - f v ≠ 0 := by
    intro u v huv hz
    exact huv (hinj (by rwa [sub_eq_zero] at hz))
  -- the plane transport: `det3 h (f u − f i) (f w − f i) = ‖h‖² · det3 (f i) (f u) (f w)`
  have htrans : ∀ (u w : Fin (n + 1)),
      det3 h (f u - f ⟨i, by omega⟩) (f w - f ⟨i, by omega⟩)
        = det3 (f ⟨i, by omega⟩) (f u) (f w) * ‖h‖ ^ 2 := by
    intro u w
    exact (det3_plane_eq (hplane ⟨i, by omega⟩) (hplane u) (hplane w)).symm
  have hb0 : (⟪h, b⟫ : ℝ) = 0 := hperp' _ _
  have hbne : b ≠ 0 := hne' _ _ (by
    intro hcontra
    have := congrArg Fin.val hcontra
    simp at this)
  -- ρs 0 = b
  have hρ0 : ρs 0 = b := by
    rw [hρ 0 (by omega), hb_def]
  -- the five chain hypotheses
  have hperp : ∀ t, t ≤ N → (⟪h, ρs t⟫ : ℝ) = 0 := by
    intro t ht
    rw [hρ t ht]; exact hperp' _ _
  have hne : ∀ t, t ≤ N → ρs t ≠ 0 := by
    intro t ht
    rw [hρ t ht]
    exact hne' _ _ (by
      intro hcontra
      have := congrArg Fin.val hcontra
      simp at this; omega)
  have hsupp : ∀ t, t ≤ N → 0 ≤ det3 h b (ρs t) := by
    intro t ht
    rw [hρ t ht, hb_def, htrans]
    have := hweak i (i + 1 + t) hi1 (by omega)
    positivity
  have hturn : ∀ t, t + 1 ≤ N → 0 ≤ det3 h (ρs t) (ρs (t + 1)) := by
    intro t ht
    rw [hρ t (by omega), hρ (t + 1) ht, htrans]
    -- det3 (f i) (f a) (f (a+1)) = det3 (f a) (f (a+1)) (f i) ≥ 0, a = i+1+t
    have ha1 : i + 1 + t + 1 < n + 1 := by omega
    have hcyc : det3 (f ⟨i, by omega⟩) (f ⟨i + 1 + t, by omega⟩) (f ⟨i + 1 + (t + 1), by omega⟩)
        = det3 (f ⟨i + 1 + t, by omega⟩) (f ⟨i + 1 + (t + 1), by omega⟩) (f ⟨i, by omega⟩) := by
      rw [det3_cyclic]
    rw [hcyc]
    have hwk := hweak (i + 1 + t) i ha1 (by omega)
    have heq2 : f ⟨i + 1 + t + 1, ha1⟩ = f ⟨i + 1 + (t + 1), by omega⟩ := rfl
    rw [heq2] at hwk
    positivity
  -- the `hcons` discharge: no consecutive antiparallelism
  have hcons : ∀ t, t + 1 ≤ N → -1 < ncos (ρs t) (ρs (t + 1)) := by
    intro t ht
    refine hcons_of_no_behind hb0 (hperp t (by omega)) hh hbne
      (hne t (by omega)) (hne (t + 1) ht) (hsupp t (by omega)) (hsupp (t + 1) ht) ?_ ?_
    · -- no backward witness on `ρs t`
      rintro ⟨s, hs, hwit⟩
      rw [hρ t (by omega)] at hwit
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · -- `t = 0`: the witness is `b = −(s • b)`, impossible
        subst ht0
        have hbb : f ⟨i + 1 + 0, by omega⟩ - f ⟨i, by omega⟩ = b := by
          rw [hb_def]
        rw [hbb] at hwit
        have : (1 + s) • b = 0 := by
          have := hwit
          linear_combination (norm := module) this
        have hb0' : b = 0 := by
          have h1s : (1 + s : ℝ) ≠ 0 := by positivity
          exact (smul_eq_zero.mp this).resolve_left h1s
        exact hbne hb0'
      · -- `t ≥ 1`: a genuine behind-vertex, killed
        exact no_behind_vertex h f hweak hnoflat hfirst i (i + 1 + t) hi1 (by omega) s hs hwit
    · -- no backward witness on `ρs (t+1)`
      rintro ⟨s, hs, hwit⟩
      rw [hρ (t + 1) ht] at hwit
      exact no_behind_vertex h f hweak hnoflat hfirst i (i + 1 + (t + 1)) hi1 (by omega) s hs hwit
  -- the strict first joint
  have hfj : 0 < det3 h b (ρs 1) := by
    rw [hρ 1 hN1, hb_def, htrans]
    have hp2 : i + 1 + 1 < n + 1 := by omega
    have hjoint : 0 < det3 (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) (f ⟨i + 1 + 1, hp2⟩) := by
      have := hnoflat (i + 1) (by omega) hp2
      have hfeq : f ⟨i + 1 - 1, by omega⟩ = f ⟨i, by omega⟩ := rfl
      rwa [hfeq] at this
    have hieq : f ⟨i + 1 + 1, by omega⟩ = f ⟨i + 1 + 1, hp2⟩ := rfl
    positivity
  -- the antipodal care-point at the target vertex
  have hnotanti : theta b (ρs N) ≠ Real.pi := by
    intro hpi
    obtain ⟨s, hs, hwit⟩ := antiparallel_of_theta_pi hbne (hne N le_rfl) hpi
    rw [hρ N le_rfl] at hwit
    exact no_behind_vertex h f hweak hnoflat hfirst i (i + 1 + N) hi1 (by omega) s hs hwit
  -- assemble
  have hmain := forward_strict_support (h := h) (b := b) ρs N hb0 hh hbne
    hperp hne hsupp hturn hcons hfj hN1 N hN1 le_rfl hnotanti
  -- transport back to the points
  rw [hρ N le_rfl, hb_def, htrans] at hmain
  have hjeq : f ⟨i + 1 + N, by omega⟩ = f ⟨j, hj⟩ := by
    congr 1; exact Fin.ext (by simp; omega)
  rw [hjeq] at hmain
  nlinarith [hmain, hhn]

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanFFCT14.no_behind_vertex
#print axioms ProofsInTheBook.ZinanFFCT14.no_beyond_vertex
#print axioms ProofsInTheBook.ZinanFFCT14.forward_case

end ProofsInTheBook.ZinanFFCT14
