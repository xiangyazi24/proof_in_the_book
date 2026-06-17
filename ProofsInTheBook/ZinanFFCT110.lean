import ProofsInTheBook.ZinanFFCT108

/-!
# `ZinanFFCT110` — the single-stuck planar bridge to discrete-Fenchel non-degeneracy

This file recovers the discrete-Fenchel non-degeneracy residue
(`ProofsInTheBook.ZinanFFCT108.core_of_nondeg`'s last argument) from a **planar
single-stuck support** structure, following the ChatGPT-designed recovery
(`HANDOFF/outbox/ch13-recovery-DIRECTION.md`).

## The idea

Build the planar vertices of the opened arm directly from the discrete-Fenchel
angle/length data as complex numbers:

  `vert n j := − chord θ ρ n j`        (so `vert n − vert j = chord j = Vₙ − Vⱼ`)

with cyclic edges (arm edges `0..n−1`, plus the closing edge `n`) and the planar
orientation `supp n i j = cross (edge i) (vert j − vert i)`.  The crux hypothesis is
**weak cyclic support** (`0 ≤ supp`) together with **at most one nonincident support
zero** (`AtMostOneZero`).  This is *much weaker* than global strict support and
matches the actual `openedWBS` structure (exactly one stuck tangency).

The two faces of the residue follow non-circularly:

* `chord k ≠ 0` — a collision `Vₖ = Vₙ` would force **two** distinct nonincident
  support zeros (edge `k` vs vertex `n`, and final edge `n−1` vs vertex `k`),
  contradicting `AtMostOneZero`.
* `bₖ ≠ π` — `bₖ = π` puts `Vₖ` beyond `Vₙ` on the final-edge ray
  (`final_ray_of_b_eq_pi`), which again forces two distinct nonincident zeros
  (final edge `n−1` at `k`, and the *closing* edge `n` at `n−1` via opposite weak
  supports), contradicting `AtMostOneZero`.

The slogan: a collision or a bad final-ray suffix is not a mere tangency — it forces
**two** nonincident support zeros; `openedWBS` has only one.

## Status

No `sorry`/`axiom`/`admit`/`native_decide`.  The whole analytic content
(`core_of_nondeg`, the suffix argument-lift) is already in `ZinanFFCT108`; this file
is the non-circular non-degeneracy bridge.  The spherical fact that `openedWBS`
actually satisfies `AtMostOneZero` is a separate next file.
-/

noncomputable section

open Complex Real ProofsInTheBook.ZinanFFCT108

namespace ProofsInTheBook.ZinanFFCT110

set_option maxHeartbeats 1600000

/-! ## §1  The planar cross product and the cyclic support family. -/

/-- The planar (oriented) cross product of two complex numbers, `Im(conj u · v)`. -/
def cross (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

lemma cross_self (u : ℂ) : cross u u = 0 := by simp only [cross]; ring

lemma cross_neg_right (u v : ℂ) : cross u (-v) = - cross u v := by
  simp only [cross, Complex.neg_re, Complex.neg_im]; ring

lemma cross_ofReal_smul_right (c : ℝ) (u v : ℂ) : cross u ((c : ℂ) * v) = c * cross u v := by
  simp only [cross, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring

lemma cross_zero_right (u : ℂ) : cross u 0 = 0 := by simp [cross]

/-- Planar vertices of the opened arm, anchored at `Vₙ = 0`:  `vert n j = − chord j`. -/
def vert (θ ρ : ℕ → ℝ) (n j : ℕ) : ℂ := - chord θ ρ n j

/-- Cyclic next vertex on `{0,…,n}`:  the closing edge sends `n ↦ 0`. -/
def nxtV (n i : ℕ) : ℕ := if i = n then 0 else i + 1

/-- Edge vector of edge `i` (arm edge for `i < n`, closing edge for `i = n`). -/
def EV (θ ρ : ℕ → ℝ) (n i : ℕ) : ℂ := vert θ ρ n (nxtV n i) - vert θ ρ n i

/-- Planar orientation of triangle `(Vᵢ, V_{nxt i}, Vⱼ)`. -/
def supp (θ ρ : ℕ → ℝ) (n i j : ℕ) : ℝ := cross (EV θ ρ n i) (vert θ ρ n j - vert θ ρ n i)

/-- `j` is not an endpoint of edge `i`. -/
def NonInc (n i j : ℕ) : Prop := j ≠ i ∧ j ≠ nxtV n i

lemma nxtV_lt (n i : ℕ) (h : i ≠ n) : nxtV n i = i + 1 := if_neg h
lemma nxtV_self (n : ℕ) : nxtV n n = 0 := if_pos rfl

lemma chord_self_zero (θ ρ : ℕ → ℝ) (n : ℕ) : chord θ ρ n n = 0 := by
  unfold chord; simp

lemma EV_arm (θ ρ : ℕ → ℝ) (n i : ℕ) (h : i < n) : EV θ ρ n i = edge θ ρ i := by
  unfold EV vert
  rw [nxtV_lt n i (by omega), chord_succ θ ρ n i h]; ring

/-- At most one nonincident support zero in the cyclic family. -/
def AtMostOneZero (θ ρ : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i₁ j₁ i₂ j₂ : ℕ, i₁ ≤ n → j₁ ≤ n → i₂ ≤ n → j₂ ≤ n →
    NonInc n i₁ j₁ → NonInc n i₂ j₂ →
    supp θ ρ n i₁ j₁ = 0 → supp θ ρ n i₂ j₂ = 0 → i₁ = i₂ ∧ j₁ = j₂

/-! ## §2  `chord k ≠ 0` from at-most-one-zero. -/

theorem chord_ne_of_atMostOne (n : ℕ) (θ ρ : ℕ → ℝ) (hn : 2 ≤ n)
    (hpos : ∀ i, 0 < ρ i) (hone : AtMostOneZero θ ρ n)
    (k : ℕ) (_hk1 : 1 ≤ k) (hkn : k ≤ n - 1) : chord θ ρ n k ≠ 0 := by
  by_cases hlast : k = n - 1
  · rw [hlast]; exact chord_last_ne θ ρ n (by omega) (hpos (n - 1))
  · have hk2 : k ≤ n - 2 := by omega
    intro h0
    -- zero #1: edge k, vertex n
    have hs1 : supp θ ρ n k n = 0 := by
      unfold supp
      have hvd : vert θ ρ n n - vert θ ρ n k = 0 := by
        unfold vert; rw [chord_self_zero, h0]; ring
      rw [hvd, cross_zero_right]
    -- zero #2: edge n-1, vertex k
    have hs2 : supp θ ρ n (n - 1) k = 0 := by
      unfold supp
      rw [EV_arm θ ρ n (n - 1) (by omega)]
      have hvd : vert θ ρ n k - vert θ ρ n (n - 1) = edge θ ρ (n - 1) := by
        unfold vert; rw [h0, chord_last θ ρ n (by omega)]; ring
      rw [hvd, cross_self]
    have ni1 : NonInc n k n := by
      refine ⟨by omega, ?_⟩; rw [nxtV_lt n k (by omega)]; omega
    have ni2 : NonInc n (n - 1) k := by
      refine ⟨by omega, ?_⟩; rw [nxtV_lt n (n - 1) (by omega)]; omega
    have heq := hone k n (n - 1) k (by omega) (le_refl n) (by omega) (by omega) ni1 ni2 hs1 hs2
    exact absurd heq.1 (by omega)

/-! ## §3  The final-ray identity from `bₖ = π`. -/

/-- The end-frame rotation of the suffix chord (extracted from `im_end_chord`'s core). -/
theorem end_rot_chord (θ ρ : ℕ → ℝ) (n j : ℕ) :
    Complex.exp (-(θ (n - 1) : ℂ) * I) * chord θ ρ n j
      = (‖chord θ ρ n j‖ : ℂ) * Complex.exp (((θ j + aang θ ρ n j - θ (n - 1) : ℝ) : ℂ) * I) := by
  have hc : chord θ ρ n j = Complex.exp ((θ j : ℂ) * I) * wrot θ ρ n j := by
    unfold wrot
    rw [← mul_assoc, ← Complex.exp_add, show (θ j : ℂ) * I + -(θ j : ℂ) * I = 0 by ring,
      Complex.exp_zero, one_mul]
  conv_lhs => rw [hc, ← chord_polar θ ρ n j]
  calc Complex.exp (-(θ (n - 1) : ℂ) * I)
          * (Complex.exp ((θ j : ℂ) * I)
            * ((‖chord θ ρ n j‖ : ℂ) * Complex.exp ((aang θ ρ n j : ℂ) * I)))
      = (‖chord θ ρ n j‖ : ℂ)
          * (Complex.exp (-(θ (n - 1) : ℂ) * I) * Complex.exp ((θ j : ℂ) * I)
            * Complex.exp ((aang θ ρ n j : ℂ) * I)) := by ring
    _ = (‖chord θ ρ n j‖ : ℂ)
          * Complex.exp (((θ j + aang θ ρ n j - θ (n - 1) : ℝ) : ℂ) * I) := by rw [exp3]

theorem final_ray_of_b_eq_pi (n : ℕ) (θ ρ : ℕ → ℝ) (hn : 1 ≤ n)
    (hpos : ∀ i, 0 < ρ i) (k : ℕ)
    (hchord : chord θ ρ n k ≠ 0)
    (hb : (θ (n - 1) - θ k) - aang θ ρ n k = π) :
    ∃ lam : ℝ, 0 < lam ∧ chord θ ρ n k = -(lam : ℂ) * edge θ ρ (n - 1) := by
  have hs : 0 < ‖chord θ ρ n k‖ := norm_pos_iff.mpr hchord
  have hkey := end_rot_chord θ ρ n k
  have hang : θ k + aang θ ρ n k - θ (n - 1) = -π := by linarith
  rw [hang] at hkey
  have hexp : Complex.exp (((-π : ℝ) : ℂ) * I) = -1 := by
    rw [show ((-π : ℝ) : ℂ) * I = -(((π : ℝ) : ℂ) * I) by push_cast; ring, Complex.exp_neg,
      show ((π : ℝ) : ℂ) * I = (π : ℂ) * I by push_cast; ring, Complex.exp_pi_mul_I]
    norm_num
  rw [hexp] at hkey
  have hchordval : chord θ ρ n k
      = -(‖chord θ ρ n k‖ : ℂ) * Complex.exp ((θ (n - 1) : ℂ) * I) := by
    have h2 : Complex.exp ((θ (n - 1) : ℂ) * I)
        * (Complex.exp (-(θ (n - 1) : ℂ) * I) * chord θ ρ n k) = chord θ ρ n k := by
      rw [← mul_assoc, ← Complex.exp_add,
        show (θ (n - 1) : ℂ) * I + -(θ (n - 1) : ℂ) * I = 0 by ring, Complex.exp_zero, one_mul]
    calc chord θ ρ n k
        = Complex.exp ((θ (n - 1) : ℂ) * I)
            * (Complex.exp (-(θ (n - 1) : ℂ) * I) * chord θ ρ n k) := h2.symm
      _ = Complex.exp ((θ (n - 1) : ℂ) * I) * ((‖chord θ ρ n k‖ : ℂ) * (-1)) := by rw [hkey]
      _ = -(‖chord θ ρ n k‖ : ℂ) * Complex.exp ((θ (n - 1) : ℂ) * I) := by ring
  have hρne : (ρ (n - 1) : ℂ) ≠ 0 := by exact_mod_cast (hpos (n - 1)).ne'
  set s := ‖chord θ ρ n k‖ with hsdef
  refine ⟨s / ρ (n - 1), div_pos hs (hpos (n - 1)), ?_⟩
  have key : ((s / ρ (n - 1) : ℝ) : ℂ) * (ρ (n - 1) : ℂ) = (s : ℂ) := by
    rw [Complex.ofReal_div, div_mul_cancel₀ _ hρne]
  rw [hchordval, edge, ← key]; ring

/-! ## §4  `bₖ ≠ π` from at-most-one-zero. -/

theorem b_ne_pi_of_atMostOne (n : ℕ) (θ ρ : ℕ → ℝ) (hn : 2 ≤ n)
    (hpos : ∀ i, 0 < ρ i)
    (hweak : ∀ i j, i ≤ n → j ≤ n → 0 ≤ supp θ ρ n i j)
    (hone : AtMostOneZero θ ρ n)
    (hchord_ne : ∀ k, 1 ≤ k → k ≤ n - 1 → chord θ ρ n k ≠ 0)
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) :
    (θ (n - 1) - θ k) - aang θ ρ n k ≠ π := by
  intro hb
  by_cases hlast : k = n - 1
  · rw [hlast, aang_last θ ρ n (by omega) (hpos (n - 1))] at hb
    simp only [sub_self, sub_zero] at hb
    linarith [Real.pi_pos]
  · have hk2 : k ≤ n - 2 := by omega
    obtain ⟨lam, hlam, hray⟩ :=
      final_ray_of_b_eq_pi n θ ρ (by omega) hpos k (hchord_ne k hk1 hkn) hb
    -- zero #1 (cFinal): final edge n-1 at vertex k
    have hs1 : supp θ ρ n (n - 1) k = 0 := by
      unfold supp
      rw [EV_arm θ ρ n (n - 1) (by omega)]
      have hvd : vert θ ρ n k - vert θ ρ n (n - 1) = ((1 + lam : ℝ) : ℂ) * edge θ ρ (n - 1) := by
        unfold vert; rw [hray, chord_last θ ρ n (by omega)]; push_cast; ring
      rw [hvd, cross_ofReal_smul_right, cross_self, mul_zero]
    -- zero #2 (cClose): closing edge n at vertex n-1, via opposite weak supports
    have e1 : supp θ ρ n n k = lam * cross (EV θ ρ n n) (edge θ ρ (n - 1)) := by
      unfold supp
      have hvd : vert θ ρ n k - vert θ ρ n n = (lam : ℂ) * edge θ ρ (n - 1) := by
        unfold vert; rw [hray, chord_self_zero]; ring
      rw [hvd, cross_ofReal_smul_right]
    have e2 : supp θ ρ n n (n - 1) = - cross (EV θ ρ n n) (edge θ ρ (n - 1)) := by
      unfold supp
      have hvd : vert θ ρ n (n - 1) - vert θ ρ n n = -(edge θ ρ (n - 1)) := by
        unfold vert; rw [chord_self_zero, chord_last θ ρ n (by omega)]; ring
      rw [hvd, cross_neg_right]
    have w1 := hweak n k (le_refl n) (by omega); rw [e1] at w1
    have w2 := hweak n (n - 1) (le_refl n) (by omega); rw [e2] at w2
    have hcross0 : cross (EV θ ρ n n) (edge θ ρ (n - 1)) = 0 := by
      rcases lt_trichotomy (cross (EV θ ρ n n) (edge θ ρ (n - 1))) 0 with h | h | h
      · nlinarith [w1, mul_pos hlam (neg_pos.mpr h)]
      · exact h
      · linarith [w2]
    have hs2 : supp θ ρ n n (n - 1) = 0 := by rw [e2, hcross0]; ring
    have ni1 : NonInc n (n - 1) k := by
      refine ⟨by omega, ?_⟩; rw [nxtV_lt n (n - 1) (by omega)]; omega
    have ni2 : NonInc n n (n - 1) := by
      refine ⟨by omega, ?_⟩; rw [nxtV_self]; omega
    have heq := hone (n - 1) k n (n - 1) (by omega) (by omega) (le_refl n) (by omega)
      ni1 ni2 hs1 hs2
    exact absurd heq.1 (by omega)

/-! ## §5  Assembled suffix non-degeneracy and the discrete-Fenchel bound. -/

theorem suffix_nondeg_of_atMostOneZero (n : ℕ) (θ ρ : ℕ → ℝ) (hn : 2 ≤ n)
    (hpos : ∀ i, 0 < ρ i)
    (hweak : ∀ i j, i ≤ n → j ≤ n → 0 ≤ supp θ ρ n i j)
    (hone : AtMostOneZero θ ρ n) :
    ∀ k, 1 ≤ k → k ≤ n - 1 →
      chord θ ρ n k ≠ 0 ∧ (θ (n - 1) - θ k) - aang θ ρ n k ≠ π := by
  have hchord_ne : ∀ k, 1 ≤ k → k ≤ n - 1 → chord θ ρ n k ≠ 0 :=
    fun k hk1 hkn => chord_ne_of_atMostOne n θ ρ hn hpos hone k hk1 hkn
  intro k hk1 hkn
  exact ⟨hchord_ne k hk1 hkn,
    b_ne_pi_of_atMostOne n θ ρ hn hpos hweak hone hchord_ne k hk1 hkn⟩

/-- **The discrete-Fenchel total-turning bound from the planar single-stuck structure.**
Weak cyclic support + at most one nonincident support zero (plus the discrete-Fenchel
angle/length premises) imply `θ(n−1) − θ 0 < 2π`. -/
theorem discreteFenchelCore_of_atMostOneZero (n : ℕ) (θ ρ : ℕ → ℝ) (hn : 2 ≤ n)
    (hmono : ∀ m, m + 1 ≤ n - 1 → θ m < θ (m + 1))
    (hgap : ∀ m, m + 2 ≤ n → θ (m + 1) - θ m < π)
    (hpos : ∀ i, 0 < ρ i)
    (hfwd : ∀ a j, a + 1 ≤ n → a ≤ j → j ≤ n →
      0 ≤ ∑ i ∈ Finset.Ico a j, ρ i * Real.sin (θ i - θ a))
    (hbwd : ∀ a j, a + 1 ≤ n → j ≤ a →
      0 ≤ - ∑ i ∈ Finset.Ico j a, ρ i * Real.sin (θ i - θ a))
    (hweak : ∀ i j, i ≤ n → j ≤ n → 0 ≤ supp θ ρ n i j)
    (hone : AtMostOneZero θ ρ n) :
    θ (n - 1) - θ 0 < 2 * π :=
  core_of_nondeg n θ ρ hn hmono hgap hpos hfwd hbwd
    (suffix_nondeg_of_atMostOneZero n θ ρ hn hpos hweak hone)

/-! ## Guards. -/
#check @cross
#check @AtMostOneZero
#check @chord_ne_of_atMostOne
#check @final_ray_of_b_eq_pi
#check @b_ne_pi_of_atMostOne
#check @suffix_nondeg_of_atMostOneZero
#check @discreteFenchelCore_of_atMostOneZero
#print axioms suffix_nondeg_of_atMostOneZero
#print axioms discreteFenchelCore_of_atMostOneZero

end ProofsInTheBook.ZinanFFCT110
