import ProofsInTheBook.PolygonWindingBound
import ProofsInTheBook.PolygonEarExterior
import ProofsInTheBook.ZinanFFCT9

/-!
# `ZinanCh36Theta` — the `mono_theta` position-vector port and the EXACT reduction of the
  Chapter-36 Jordan kernel `RayCrossingAlternation` to the ray winding dichotomy

This file executes the Ch36-theta brief (HANDOFF/task-ch36-theta.md): port the monotone
branch-cut angle technique of `ZinanFFCT9` (`theta`, `mono_ncos`, `mono_theta`,
`branch_squeeze_*`) from edge-difference vectors in `E3` onto the planar POSITION vector
`(boundary point − x)`, and aim it at the chapter's single Jordan kernel
`PolygonWindingBound.RayCrossingAlternation P ρ x` (forward-ray crossings, sorted by
`crossTau`, have alternating `eSign`).

## What is proved here UNCONDITIONALLY (axioms `{propext, Classical.choice, Quot.sound}`)

* **§0–§1 (Brick 1, the port).**  The full 2D angle layer on `Pt`: `ncos2`, `nsin2`,
  `theta2 b p := arccos (ncos2 b p)`; the Lagrange identity and the cosine/sine addition
  identities (pure coordinate `ring`, no cross-product gymnastics needed in 2D);
  `mono_ncos2` / `mono_theta2` (driven by the *same* `ZinanFFCT9.mono_abstract` crux);
  the branch-cut squeeze `branch_squeeze_theta2_ne_zero` and strict support
  `det2_pos_of_theta2_mem` — the verbatim 2D images of the FFCT9 §1–§5 chain.
* **§2 (Brick 1, position-vector form).**  `thetaPos r x p := theta2 r (p − x)`; the exact
  turning identity along one edge `det2_posVec_lineMap` (the position vector turns through
  `(t − s)·orient x a b` — monotone in the *signed* sense, strictness included), the
  single-edge monotone lemma `mono_thetaPos_edge`, and `thetaPos_eq_zero_at_forward` (the
  angle vanishes exactly at a forward ray point).
* **§3 (ray-translate structure).**  Sliding the base point out along the ray leaves every
  side coordinate unchanged (`side_translate`) and shifts every `crossTau` by `−c`
  (`crossTau_translate`); hence the crossing set at `x + c•ρ.r` is the `τ ≥ c` filter of
  the crossing set at `x` (`crossingEdges'_translate`) and
  `windCross (x + c•ρ.r) = ∑_{τ_i ≥ c} eSign i` (`windCross_translate`) — the suffix-sum
  law: **the signed winding along the ray enumerates the suffix sums of the crossing-sign
  sequence**.
* **§4 (simplicity ⟹ distinct crossing parameters).**  Under the genericity guard
  `hvert : ∀ k, side ρ.r x (P.q k) ≠ 0` (no vertex on the ray line), distinct forward
  crossings have distinct `crossTau` (`crossTau_injOn_crossingEdges`): each crossing point
  is in the open interior of its edge (`crossU_mem_Ioo`), and two distinct edges meet only
  at a shared vertex (`EdgeIntersectionCondition`), which cannot be on the ray line.  This
  is where the polygon's SIMPLICITY enters.  Off a boundary point all crossing parameters
  are nonzero (`crossTau_ne_zero_of_offBoundary`), and every cut value `c` avoiding the
  crossing parameters has `x + c•ρ.r` off the boundary (`not_onBoundary_at_cut`).
* **§5 (sorted enumeration).**  Any finite set with an injective real key admits a nodup,
  strictly-key-sorted enumeration (`exists_sorted_enum`); instantiated at `crossTau`, this
  discharges every clause of `RayCrossingAlternation` except `Alt`.
* **§6 (the combinatorial alternation engine).**  `alt_of_cut_dichotomy`: if all the
  `τ ≥ c` filtered sums of a `±1` weight lie in `{0, s}` (a fixed `s = ±1`), then any
  key-sorted enumeration has alternating weights.  Pure list/Finset combinatorics: two
  equal consecutive signs would make two suffix sums differ by `2`.
* **§7 (the headline reduction).**  `rayCrossingAlternation_of_ray_dichotomy`:

  ```
  (∀ c ≥ 0, x + c•ρ.r off the boundary →
      windCross P ρ (x + c•ρ.r) = 0 ∨ windCross P ρ (x + c•ρ.r) = s)
    →  RayCrossingAlternation P ρ x
  ```

  at every off-boundary `x` with no vertex on its ray line.  (Mathematical remark, not
  formalized here: the converse also holds — by the suffix-sum law the kernel's alternating
  signs make every along-ray winding a suffix sum of an alternating `±1` list, which lies
  in `{0, sign-of-last}` — so the reduction loses nothing; the kernel IS the two-value
  dichotomy along one ray.)
* **§9 (the full-line telescope, unconditional).**  `lineCrossing_eSign_sum_zero`: over
  the whole ray LINE the `eSign` sum of all span-crossed edges telescopes to `0` (each
  edge contributes the difference of its endpoint strict-side indicators; the cyclic sum
  vanishes) — up- and down-crossings of a generic line balance exactly, with NO Jordan
  content.  Hence `windCross_eq_neg_backwardSum`: the forward (windCross) and backward
  signed sums are exact negatives — the global budget the Jordan alternation distributes.

## The honest verdict on the brief's monotone-squeeze hope (§8, machine-checked)

The brief hoped alternation "falls out of the monotone squeeze" applied to `thetaPos`.
Two machine-checked facts pin why this cannot close the kernel unconditionally:

1. **The blanket support hypothesis of the squeeze is the refuted `allConvex` shape.**
   `mono_theta2` (like `mono_theta`) needs every consecutive turn weakly supported:
   `0 ≤ det2 (P t − x) (P t' − x)` along the boundary, i.e. `x` sees the boundary in convex
   cyclic order.  `posVec_turn_support_fails` exhibits a concrete strict simple polygon and
   an off-boundary point with a strictly NEGATIVE consecutive position-vector turn — indeed
   at every exterior point the winding `0` *forces* a negative turn somewhere, and at
   reflex polygons even interior points fail (the dead-ended `InteriorOddSeed ≡ allConvex`
   of the brief's KNOWN DEAD ENDS).  So the squeeze can serve only locally (per edge /
   per supported sub-chain, §2), never as a blanket alternation engine.
2. **The kernel as stated is FALSE without the vertex-genericity guard.**
   `rayCrossingAlternation_not_universal`: there is a strict simple triangle, an admissible
   ray direction, and an off-boundary point `x` (the ray from `x` passes through a vertex
   whose both neighbours lie strictly above the ray line) with TWO forward crossing edges
   of EQUAL `crossTau` — no strictly-`crossTau`-sorted enumeration exists at all.  So any
   unconditional supply of `RayCrossingAlternation` must first perturb `x` off the finitely
   many vertex rays (`windCross` is locally constant off the boundary, so the perturbation
   is harmless for every downstream consumer); the guard `hvert` of §7 is genuinely
   necessary, not an artifact.

## What remains (the irreducible residue, sharpened)

The §7 reduction shifts the kernel to the *ray winding dichotomy*: `windCross` takes at
most the two values `{0, s}` along a generic ray.  By the suffix-sum law this is precisely
"every ray point is inside (winding `s`) or outside (winding `0`)" — the Jordan
interior/exterior dichotomy itself, restricted to one ray.  It is NOT produced here; it is
the sharpened, named residue this route leaves, the exact two-value strengthening of the
proved three-value `windCross_mem_of_alternation` face.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36Theta

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonWinding (windCross)
open ProofsInTheBook.PolygonWindingExterior (eSign)
open ProofsInTheBook.PolygonWindingBound
  (Alt RayCrossingAlternation eSign_mem windCross_eq_sum_crossing_eSign
    windCross_mem_of_alternation)
open scoped RealInnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ## §0. Coordinate expansion: the 2D area form `det2` and the real inner product

In 2D the whole `E3` cross-product layer of `ZinanFFCT9.§0` collapses to coordinate `ring`:
`⟪·,·⟫` and `det2` are the real and imaginary parts of `conj(u)·v`, and the addition
identities are the single complex multiplication `conj(b)p · conj(p)q = |p|² conj(b)q`. -/

/-- The real inner product on `Pt` in coordinates. -/
lemma inner_expand (u v : Pt) : (⟪u, v⟫ : ℝ) = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  norm_num [RCLike.inner_apply]
  ring

/-- The squared norm on `Pt` in coordinates. -/
lemma norm_sq_expand (v : Pt) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_expand]; ring

/-- **Lagrange in 2D** (the `sin² + cos²` source identity):
`⟪u,v⟫² + det2(u,v)² = ‖u‖²‖v‖²`. -/
theorem lagrange2 (u v : Pt) :
    (⟪u, v⟫ : ℝ) ^ 2 + det2 u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [inner_expand, norm_sq_expand, norm_sq_expand]
  unfold det2; ring

/-- **Cosine addition in 2D**: `⟪b,q⟫‖p‖² = ⟪b,p⟫⟪p,q⟫ − det2(b,p)det2(p,q)`. -/
theorem cos_add_id2 (b p q : Pt) :
    (⟪b, q⟫ : ℝ) * ‖p‖ ^ 2 = (⟪b, p⟫ : ℝ) * (⟪p, q⟫ : ℝ) - det2 b p * det2 p q := by
  rw [inner_expand, inner_expand, inner_expand, norm_sq_expand]
  unfold det2; ring

/-- **Sine addition in 2D**: `‖p‖² det2(b,q) = ⟪b,p⟫ det2(p,q) + det2(b,p)⟪p,q⟫`. -/
theorem sin_add_id2 (b p q : Pt) :
    ‖p‖ ^ 2 * det2 b q = (⟪b, p⟫ : ℝ) * det2 p q + det2 b p * (⟪p, q⟫ : ℝ) := by
  rw [inner_expand, inner_expand, norm_sq_expand]
  unfold det2; ring

/-! ## §1. The 2D polar-angle layer (the verbatim port of `ZinanFFCT9.§1`)

`det2` plays the role of the `h`-oriented `det3` area form; the `h ⊥` hypotheses vanish. -/

/-- Normalised cosine of the angle from `b` to `p`. -/
def ncos2 (b p : Pt) : ℝ := (⟪b, p⟫ : ℝ) / (‖b‖ * ‖p‖)

/-- Normalised (oriented) sine of the angle from `b` to `p`. -/
def nsin2 (b p : Pt) : ℝ := det2 b p / (‖b‖ * ‖p‖)

/-- The polar angle, valued in `[0, π]` (the single branch). -/
def theta2 (b p : Pt) : ℝ := Real.arccos (ncos2 b p)

theorem ncos2_mem {b p : Pt} (hb : b ≠ 0) (hp : p ≠ 0) :
    ncos2 b p ∈ Set.Icc (-1 : ℝ) 1 := by
  have hbp : |(⟪b, p⟫ : ℝ)| ≤ ‖b‖ * ‖p‖ := abs_real_inner_le_norm b p
  have hbpos : 0 < ‖b‖ * ‖p‖ :=
    mul_pos (norm_pos_iff.mpr hb) (norm_pos_iff.mpr hp)
  rw [abs_le] at hbp
  refine ⟨?_, ?_⟩
  · rw [ncos2, le_div_iff₀ hbpos]; linarith [hbp.1]
  · rw [ncos2, div_le_iff₀ hbpos]; linarith [hbp.2]

theorem cos_theta2 {b p : Pt} (hb : b ≠ 0) (hp : p ≠ 0) :
    Real.cos (theta2 b p) = ncos2 b p := by
  rw [theta2, Real.cos_arccos (ncos2_mem hb hp).1 (ncos2_mem hb hp).2]

theorem nsin2_nonneg {b p : Pt} (hb : b ≠ 0) (hp : p ≠ 0)
    (hsupp : 0 ≤ det2 b p) : 0 ≤ nsin2 b p := by
  rw [nsin2]
  apply div_nonneg hsupp
  positivity

/-- The branch identity `ncos2² + nsin2² = 1`. -/
theorem ncos2_sq_add_nsin2_sq {b p : Pt} (hb : b ≠ 0) (hp : p ≠ 0) :
    ncos2 b p ^ 2 + nsin2 b p ^ 2 = 1 := by
  have hbn : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hpn : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  have hl : (⟪b, p⟫ : ℝ) ^ 2 + det2 b p ^ 2 = (‖b‖ * ‖p‖) ^ 2 := by
    rw [mul_pow]; exact lagrange2 b p
  rw [ncos2, nsin2, div_pow, div_pow, ← add_div, hl, div_self (by positivity)]

/-- (C) normalised: `ncos2 b q = ncos2 b p · ncos2 p q − nsin2 b p · nsin2 p q`. -/
theorem ncos2_add {b p q : Pt} (hb : b ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) :
    ncos2 b q = ncos2 b p * ncos2 p q - nsin2 b p * nsin2 p q := by
  have hbn : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hpn : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  have hqn : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq
  have h1 : ncos2 b p * ncos2 p q - nsin2 b p * nsin2 p q
      = ((⟪b, p⟫ : ℝ) * (⟪p, q⟫ : ℝ) - det2 b p * det2 p q)
        / (‖b‖ * ‖p‖ * (‖p‖ * ‖q‖)) := by
    rw [ncos2, ncos2, nsin2, nsin2, div_mul_div_comm, div_mul_div_comm,
      div_sub_div_same]
  rw [h1, ← cos_add_id2, ncos2, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- (S) normalised: `nsin2 b q = nsin2 b p · ncos2 p q + ncos2 b p · nsin2 p q`. -/
theorem nsin2_add {b p q : Pt} (hb : b ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) :
    nsin2 b q = nsin2 b p * ncos2 p q + ncos2 b p * nsin2 p q := by
  have hbn : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hpn : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  have hqn : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq
  have h1 : nsin2 b p * ncos2 p q + ncos2 b p * nsin2 p q
      = (det2 b p * (⟪p, q⟫ : ℝ) + (⟪b, p⟫ : ℝ) * det2 p q)
        / (‖b‖ * ‖p‖ * (‖p‖ * ‖q‖)) := by
    rw [nsin2, ncos2, ncos2, nsin2, div_mul_div_comm, div_mul_div_comm, ← add_div]
  have h2 : det2 b p * (⟪p, q⟫ : ℝ) + (⟪b, p⟫ : ℝ) * det2 p q = ‖p‖ ^ 2 * det2 b q := by
    rw [sin_add_id2]; ring
  rw [h1, h2, nsin2, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **Monotone angle (cos form), 2D.**  With weak supports `det2 b p ≥ 0`, `det2 b q ≥ 0`,
`det2 p q ≥ 0` and the consecutive turn not antipodal, the cosine is non-increasing.
Driven by the same `ZinanFFCT9.mono_abstract` crux as the `E3` original. -/
theorem mono_ncos2 {b p q : Pt} (hb : b ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (sbp : 0 ≤ det2 b p) (sbq : 0 ≤ det2 b q) (spq : 0 ≤ det2 p q)
    (hnotanti : -1 < ncos2 p q) :
    ncos2 b q ≤ ncos2 b p :=
  ProofsInTheBook.ZinanFFCT9.mono_abstract (ncos2 b p) (nsin2 b p) (ncos2 p q)
    (nsin2 p q) (ncos2 b q) (nsin2 b q)
    (nsin2_nonneg hb hp sbp) (nsin2_nonneg hp hq spq) (nsin2_nonneg hb hq sbq)
    (ncos2_sq_add_nsin2_sq hp hq)
    (ncos2_add hb hp hq) (nsin2_add hb hp hq) hnotanti

/-- **Monotone angle (θ form), 2D** — `mono_theta` ported to the plane. -/
theorem mono_theta2 {b p q : Pt} (hb : b ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (sbp : 0 ≤ det2 b p) (sbq : 0 ≤ det2 b q) (spq : 0 ≤ det2 p q)
    (hnotanti : -1 < ncos2 p q) :
    theta2 b p ≤ theta2 b q := by
  rw [theta2, theta2]
  exact Real.arccos_le_arccos (mono_ncos2 hb hp hq sbp sbq spq hnotanti)

/-- `theta2 = 0` forces a vanishing oriented sine. -/
theorem nsin2_eq_zero_of_theta2_zero {b p : Pt} (hb : b ≠ 0) (hp : p ≠ 0)
    (hθ : theta2 b p = 0) : nsin2 b p = 0 := by
  have hcos : ncos2 b p = 1 := by
    have := cos_theta2 hb hp
    rw [hθ, Real.cos_zero] at this
    linarith [this]
  have hpyth := ncos2_sq_add_nsin2_sq hb hp
  rw [hcos] at hpyth
  nlinarith [hpyth, sq_nonneg (nsin2 b p)]

/-- A vanishing oriented sine forces a vanishing area form. -/
theorem det2_eq_zero_of_nsin2_zero {b p : Pt} (hb : b ≠ 0) (hp : p ≠ 0)
    (hns : nsin2 b p = 0) : det2 b p = 0 := by
  have hd : (‖b‖ * ‖p‖) ≠ 0 := by positivity
  rw [nsin2, div_eq_zero_iff] at hns
  rcases hns with h1 | h2
  · exact h1
  · exact absurd h2 hd

/-- **Branch-cut squeeze, 2D** (`branch_squeeze_theta_ne_zero` ported): along a
weak-supported chain with non-antipodal turns and a strict first joint, no forward angle
returns to the base ray. -/
theorem branch_squeeze_theta2_ne_zero {b : Pt} (ρs : ℕ → Pt) (N : ℕ) (hb : b ≠ 0)
    (hne : ∀ t, t ≤ N → ρs t ≠ 0)
    (hsupp : ∀ t, t ≤ N → 0 ≤ det2 b (ρs t))
    (hturn : ∀ t, t + 1 ≤ N → 0 ≤ det2 (ρs t) (ρs (t + 1)))
    (hcons : ∀ t, t + 1 ≤ N → -1 < ncos2 (ρs t) (ρs (t + 1)))
    (hnoflat : 0 < det2 b (ρs 1)) (hN : 1 ≤ N) :
    ∀ k, 1 ≤ k → k ≤ N → theta2 b (ρs k) ≠ 0 := by
  have hmono : ∀ t, t + 1 ≤ N → theta2 b (ρs t) ≤ theta2 b (ρs (t + 1)) := by
    intro t ht
    exact mono_theta2 hb (hne t (by omega)) (hne (t + 1) (by omega))
      (hsupp t (by omega)) (hsupp (t + 1) (by omega)) (hturn t ht) (hcons t ht)
  have hchain : ∀ a c, a ≤ c → c ≤ N → theta2 b (ρs a) ≤ theta2 b (ρs c) := by
    intro a c hac hcN
    induction c with
    | zero => simp_all
    | succ d IH =>
      rcases Nat.lt_or_ge a (d + 1) with hlt | hge
      · have h1 : theta2 b (ρs a) ≤ theta2 b (ρs d) := IH (by omega) (by omega)
        have h2 : theta2 b (ρs d) ≤ theta2 b (ρs (d + 1)) := hmono d (by omega)
        linarith
      · have hae : a = d + 1 := by omega
        rw [hae]
  intro k hk1 hkN hcontra
  have h1k : theta2 b (ρs 1) ≤ theta2 b (ρs k) := hchain 1 k hk1 hkN
  have hθ1 : theta2 b (ρs 1) = 0 := by
    rw [hcontra] at h1k
    have hnn : 0 ≤ theta2 b (ρs 1) := by rw [theta2]; exact Real.arccos_nonneg _
    linarith
  have hns : nsin2 b (ρs 1) = 0 :=
    nsin2_eq_zero_of_theta2_zero hb (hne 1 hN) hθ1
  have hd0 : det2 b (ρs 1) = 0 :=
    det2_eq_zero_of_nsin2_zero hb (hne 1 hN) hns
  linarith [hnoflat, hd0]

/-- The oriented sine equals `sin (theta2 …)` under weak support. -/
theorem nsin2_eq_sin_theta2 {b p : Pt} (hb : b ≠ 0) (hp : p ≠ 0)
    (hsupp : 0 ≤ det2 b p) : nsin2 b p = Real.sin (theta2 b p) := by
  have hpyth := ncos2_sq_add_nsin2_sq hb hp
  have hcos : Real.cos (theta2 b p) = ncos2 b p := cos_theta2 hb hp
  have hsin_nonneg : 0 ≤ Real.sin (theta2 b p) := by
    rw [theta2, Real.sin_arccos]; exact Real.sqrt_nonneg _
  have hns_nonneg : 0 ≤ nsin2 b p := nsin2_nonneg hb hp hsupp
  have hsq : Real.sin (theta2 b p) ^ 2 = nsin2 b p ^ 2 := by
    have hs2 : Real.sin (theta2 b p) ^ 2 = 1 - Real.cos (theta2 b p) ^ 2 := by
      have := Real.sin_sq_add_cos_sq (theta2 b p); nlinarith [this]
    rw [hs2, hcos]; nlinarith [hpyth]
  nlinarith [hsq, hns_nonneg, hsin_nonneg, sq_nonneg (nsin2 b p - Real.sin (theta2 b p))]

/-- **Strict support from a non-degenerate angle, 2D** (`det3_pos_of_theta_mem` ported). -/
theorem det2_pos_of_theta2_mem {b p : Pt} (hb : b ≠ 0) (hp : p ≠ 0)
    (hsupp : 0 ≤ det2 b p) (hθ0 : theta2 b p ≠ 0) (hθπ : theta2 b p ≠ Real.pi) :
    0 < det2 b p := by
  have hnn : 0 ≤ theta2 b p := by rw [theta2]; exact Real.arccos_nonneg _
  have hle : theta2 b p ≤ Real.pi := by rw [theta2]; exact Real.arccos_le_pi _
  have hsinpos : 0 < Real.sin (theta2 b p) :=
    Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne hnn (Ne.symm hθ0))
      (lt_of_le_of_ne hle hθπ)
  have hns : nsin2 b p = Real.sin (theta2 b p) := nsin2_eq_sin_theta2 hb hp hsupp
  have hnspos : 0 < nsin2 b p := by rw [hns]; exact hsinpos
  rw [nsin2] at hnspos
  have hden : (0 : ℝ) < ‖b‖ * ‖p‖ := by positivity
  rw [lt_div_iff₀ hden] at hnspos
  linarith [hnspos]

/-- **Forward strict support, 2D** (`forward_strict_support` ported): packaging the squeeze
with the strict-support step, modulo the single antipodal care-point `theta2 ≠ π`. -/
theorem forward_strict_support2 {b : Pt} (ρs : ℕ → Pt) (N : ℕ) (hb : b ≠ 0)
    (hne : ∀ t, t ≤ N → ρs t ≠ 0)
    (hsupp : ∀ t, t ≤ N → 0 ≤ det2 b (ρs t))
    (hturn : ∀ t, t + 1 ≤ N → 0 ≤ det2 (ρs t) (ρs (t + 1)))
    (hcons : ∀ t, t + 1 ≤ N → -1 < ncos2 (ρs t) (ρs (t + 1)))
    (hnoflat : 0 < det2 b (ρs 1)) (hN : 1 ≤ N)
    (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (hnotanti : theta2 b (ρs k) ≠ Real.pi) :
    0 < det2 b (ρs k) := by
  have hθ0 : theta2 b (ρs k) ≠ 0 :=
    branch_squeeze_theta2_ne_zero ρs N hb hne hsupp hturn hcons hnoflat hN k hk1 hkN
  exact det2_pos_of_theta2_mem hb (hne k hkN) (hsupp k hkN) hθ0 hnotanti

/-! ## §2. `thetaPos`: the branch-cut angle of the POSITION vector (Brick 1, headline)

`thetaPos r x p` is the branch-cut angle of `p − x` against the ray direction `r`.  Along a
single edge the position vector turns monotonically in the exact signed sense
(`det2_posVec_lineMap`), and the branch-cut angle is monotone whenever the half-plane
support of the squeeze holds (`mono_thetaPos_edge`). -/

/-- **The branch-cut angle of the position vector** against the direction `r`. -/
def thetaPos (r x p : Pt) : ℝ := theta2 r (p - x)

/-- **Exact turning identity along one edge** (signed single-edge monotonicity): the
oriented area of two position vectors of edge points is `(t − s) · orient x a b`.  In
particular the position vector turns weakly/strictly monotonically along an edge, with the
rotation sense given by the sign of `orient x a b`. -/
theorem det2_posVec_lineMap (x a b : Pt) (s t : ℝ) :
    det2 (AffineMap.lineMap a b s - x) (AffineMap.lineMap a b t - x)
      = (t - s) * det2 (a - x) (b - x) := by
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
  unfold det2
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **The single-edge monotone lemma for `thetaPos`** (Brick 1): on an edge whose two
sample points are weakly supported against the ray direction and whose chord turns weakly
positively around `x`, the branch-cut position angle is monotone in the edge parameter
(modulo the antipodal care-point, exactly as in `ZinanFFCT9`). -/
theorem mono_thetaPos_edge {r x a b : Pt} {s t : ℝ} (hst : s ≤ t) (hr : r ≠ 0)
    (hp : AffineMap.lineMap a b s - x ≠ 0) (hq : AffineMap.lineMap a b t - x ≠ 0)
    (hsupp_s : 0 ≤ det2 r (AffineMap.lineMap a b s - x))
    (hsupp_t : 0 ≤ det2 r (AffineMap.lineMap a b t - x))
    (hturn : 0 ≤ det2 (a - x) (b - x))
    (hnotanti : -1 < ncos2 (AffineMap.lineMap a b s - x) (AffineMap.lineMap a b t - x)) :
    thetaPos r x (AffineMap.lineMap a b s) ≤ thetaPos r x (AffineMap.lineMap a b t) := by
  unfold thetaPos
  apply mono_theta2 hr hp hq hsupp_s hsupp_t ?_ hnotanti
  rw [det2_posVec_lineMap]
  exact mul_nonneg (by linarith) hturn

/-- **The position angle vanishes exactly at forward ray points**: at `x + τ•r` (`τ > 0`)
the branch-cut angle is `0`.  This ties `thetaPos` to the forward-crossing geometry. -/
theorem thetaPos_eq_zero_at_forward (r x : Pt) (hr : r ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    thetaPos r x (x + τ • r) = 0 := by
  have hsub : x + τ • r - x = τ • r := by abel
  have hrn : (0 : ℝ) < ‖r‖ := norm_pos_iff.mpr hr
  have hn : ncos2 r (τ • r) = 1 := by
    have hi : (⟪r, τ • r⟫ : ℝ) = τ * ‖r‖ ^ 2 := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    have hns : ‖τ • r‖ = τ * ‖r‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
    rw [ncos2, hi, hns]
    field_simp
  rw [thetaPos, theta2, hsub, hn, Real.arccos_one]

/-! ## §3. The ray-translate structure: the suffix-sum law for `windCross`

Sliding the base point out along the ray is invisible to every side coordinate and shifts
every ray parameter by `−c`; consequently the forward-crossing set at `x + c•ρ.r` is the
`τ ≥ c` filter of the one at `x`, and the signed winding along the ray enumerates the
suffix sums of the crossing-sign sequence. -/

/-- The side coordinate is invariant under sliding the base point along the ray. -/
theorem side_translate (r x v : Pt) (c : ℝ) :
    side r (x + c • r) v = side r x v := by
  unfold side det2
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The ray parameter shifts by `−c` under sliding the base point along the ray. -/
theorem crossTau_translate (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (c : ℝ) (i : Fin n) :
    crossTau P ρ (x + c • ρ.r) i = crossTau P ρ x i - c := by
  have hD := crossDen_ne_zero P ρ i
  have hnum : det2 (P.q i - (x + c • ρ.r)) (P.q (cyclicNext i) - P.q i)
      = det2 (P.q i - x) (P.q (cyclicNext i) - P.q i) - c * crossDen P ρ i := by
    unfold crossDen det2
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  unfold crossTau
  rw [hnum, sub_div, mul_div_assoc, div_self hD, mul_one]

/-- Membership transport: an edge crosses the ray from `x + c•ρ.r` (`c ≥ 0`) iff it
crosses the ray from `x` with ray parameter at least `c`. -/
theorem mem_crossingEdges'_translate (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) {c : ℝ} (hc : 0 ≤ c) (i : Fin n) :
    i ∈ CrossingEdges' P ρ (x + c • ρ.r) ↔
      i ∈ CrossingEdges' P ρ x ∧ c ≤ crossTau P ρ x i := by
  rw [mem_crossingEdges'_iff, mem_crossingEdges'_iff]
  unfold EdgeCrossesRay' SpanCrossesSide
  rw [side_translate, side_translate, crossTau_translate]
  constructor
  · rintro ⟨hspan, hτ⟩
    exact ⟨⟨hspan, by linarith⟩, by linarith⟩
  · rintro ⟨⟨hspan, _⟩, hcτ⟩
    exact ⟨hspan, by linarith⟩

/-- **The crossing set along the ray is the `τ ≥ c` suffix filter.** -/
theorem crossingEdges'_translate (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) {c : ℝ} (hc : 0 ≤ c) :
    CrossingEdges' P ρ (x + c • ρ.r)
      = (CrossingEdges' P ρ x).filter (fun i => c ≤ crossTau P ρ x i) := by
  ext i
  rw [Finset.mem_filter, mem_crossingEdges'_translate P ρ x hc]

/-- **The suffix-sum law**: the signed winding at `x + c•ρ.r` (`c ≥ 0`) is the `eSign` sum
over the crossings of `x` with ray parameter at least `c`. -/
theorem windCross_translate (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) {c : ℝ} (hc : 0 ≤ c) :
    windCross P ρ (x + c • ρ.r)
      = ∑ i ∈ (CrossingEdges' P ρ x).filter (fun i => c ≤ crossTau P ρ x i),
          eSign P ρ i := by
  rw [windCross_eq_sum_crossing_eSign, crossingEdges'_translate P ρ x hc]

/-! ## §4. Simplicity pins the crossing order: distinct crossings, distinct parameters

Under the vertex-genericity guard (no polygon vertex on the ray LINE through `x`), every
forward crossing meets its edge in the OPEN interior, so two distinct crossing edges with
equal `crossTau` would share an interior point — `EdgeIntersectionCondition` (the polygon's
simplicity) only allows a shared VERTEX, which would be on the ray line.  This section is
where the strict simple polygon's global structure enters the kernel. -/

/-- `crossU` in terms of the side coordinate: `u = −side(a) / crossDen`. -/
theorem crossU_eq_side (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i : Fin n) :
    crossU P ρ x i = -side ρ.r x (P.q i) / crossDen P ρ i := by
  rw [crossU, side_eq_neg_det2, neg_neg]

/-- **A span-crossing with both endpoint sides nonzero meets the edge in the OPEN
interior**: `crossU ∈ (0, 1)`. -/
theorem crossU_mem_Ioo (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i : Fin n) (hspan : SpanCrossesSide P ρ x i)
    (ha : side ρ.r x (P.q i) ≠ 0) (hb : side ρ.r x (P.q (cyclicNext i)) ≠ 0) :
    crossU P ρ x i ∈ Set.Ioo (0 : ℝ) 1 := by
  have hDs : crossDen P ρ i
      = side ρ.r x (P.q (cyclicNext i)) - side ρ.r x (P.q i) :=
    (side_next_sub_side P ρ x i).symm
  unfold SpanCrossesSide at hspan
  have hprod : side ρ.r x (P.q i) * side ρ.r x (P.q (cyclicNext i)) < 0 :=
    (span_iff_opp_sign ha hb).mp hspan
  set sa := side ρ.r x (P.q i) with hsa_def
  set sb := side ρ.r x (P.q (cyclicNext i)) with hsb_def
  rw [crossU_eq_side, hDs, ← hsa_def]
  rcases lt_or_gt_of_ne ha with hsa | hsa
  · have hsb' : 0 < sb := by nlinarith
    constructor
    · exact div_pos (by linarith) (by linarith)
    · rw [div_lt_one (by linarith)]; linarith
  · have hsb' : sb < 0 := by nlinarith
    have h1 : -sa / (sb - sa) = sa / (sa - sb) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [h1]
    constructor
    · exact div_pos (by linarith) (by linarith)
    · rw [div_lt_one (by linarith)]; linarith

/-- The crossing point `x + crossTau•ρ.r` lies on the (closed) edge when `crossU ∈ [0,1]`. -/
theorem crossPoint_mem_edge (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i : Fin n) (hu : crossU P ρ x i ∈ Set.Icc (0 : ℝ) 1) :
    x + crossTau P ρ x i • ρ.r ∈ Edge P.q i := by
  unfold Edge seg
  rw [segment_eq_image_lineMap]
  exact ⟨crossU P ρ x i, hu, (cross_eq P ρ x i).symm⟩

/-- **Distinct forward crossings have distinct ray parameters** (simplicity + vertex
genericity).  Equal parameters would make the two open edge interiors share the crossing
point; `EdgeIntersectionCondition` forces a shared vertex, which would lie on the ray line,
contradicting `hvert`. -/
theorem crossTau_injOn_crossingEdges (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    {i j : Fin n} (hi : i ∈ CrossingEdges' P ρ x) (hj : j ∈ CrossingEdges' P ρ x)
    (hij : i ≠ j) : crossTau P ρ x i ≠ crossTau P ρ x j := by
  intro hτ
  have hci := (mem_crossingEdges'_iff P ρ x i).mp hi
  have hcj := (mem_crossingEdges'_iff P ρ x j).mp hj
  have hui := crossU_mem_Ioo P ρ x i hci.1 (hvert i) (hvert (cyclicNext i))
  have huj := crossU_mem_Ioo P ρ x j hcj.1 (hvert j) (hvert (cyclicNext j))
  have hyi : x + crossTau P ρ x i • ρ.r ∈ Edge P.q i :=
    crossPoint_mem_edge P ρ x i ⟨hui.1.le, hui.2.le⟩
  have hyj : x + crossTau P ρ x i • ρ.r ∈ Edge P.q j := by
    rw [hτ]; exact crossPoint_mem_edge P ρ x j ⟨huj.1.le, huj.2.le⟩
  have hside_y : ∀ k : Fin n, P.q k = x + crossTau P ρ x i • ρ.r → False := by
    intro k hk
    apply hvert k
    rw [hk]
    unfold side det2
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hEC := P.edge_intersection i j
  unfold EdgeIntersectionCondition at hEC
  rw [dif_neg hij] at hEC
  by_cases hnext : cyclicNext i = j
  · rw [dif_pos hnext] at hEC
    have hmem : x + crossTau P ρ x i • ρ.r ∈ Edge P.q i ∩ Edge P.q j := ⟨hyi, hyj⟩
    rw [hEC] at hmem
    exact hside_y j (Set.mem_singleton_iff.mp hmem).symm
  · rw [dif_neg hnext] at hEC
    by_cases hprev : cyclicNext j = i
    · rw [dif_pos hprev] at hEC
      have hmem : x + crossTau P ρ x i • ρ.r ∈ Edge P.q i ∩ Edge P.q j := ⟨hyi, hyj⟩
      rw [hEC] at hmem
      exact hside_y i (Set.mem_singleton_iff.mp hmem).symm
    · rw [dif_neg hprev] at hEC
      exact Set.disjoint_left.mp hEC hyi hyj

/-- Off a boundary point, every forward crossing has a strictly positive ray parameter:
`crossTau = 0` would put `x` itself on the crossing edge. -/
theorem crossTau_ne_zero_of_offBoundary (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (hoff : ¬ OnBoundary P x) (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    {i : Fin n} (hi : i ∈ CrossingEdges' P ρ x) : crossTau P ρ x i ≠ 0 := by
  intro h0
  have hci := (mem_crossingEdges'_iff P ρ x i).mp hi
  have hui := crossU_mem_Ioo P ρ x i hci.1 (hvert i) (hvert (cyclicNext i))
  have hy := crossPoint_mem_edge P ρ x i ⟨hui.1.le, hui.2.le⟩
  rw [h0, zero_smul, add_zero] at hy
  exact hoff ⟨i, hy⟩

/-- The side coordinate is affine in the vertex along an edge. -/
theorem side_lineMap_vertex (r x a b : Pt) (u : ℝ) :
    side r x (AffineMap.lineMap a b u)
      = (1 - u) * side r x a + u * side r x b := by
  rw [AffineMap.lineMap_apply_module]
  unfold side det2
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **Cut points are off the boundary**: if `c ≥ 0` differs from every forward-crossing ray
parameter at `x` (and no vertex is on the ray line), then `x + c•ρ.r` is off the boundary.
A boundary edge through the cut point would be a forward crossing with `crossTau = c`. -/
theorem not_onBoundary_at_cut (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    {c : ℝ} (hc : 0 ≤ c)
    (hne : ∀ i ∈ CrossingEdges' P ρ x, crossTau P ρ x i ≠ c) :
    ¬ OnBoundary P (x + c • ρ.r) := by
  rintro ⟨i, hyi⟩
  unfold Edge seg at hyi
  rw [segment_eq_image_lineMap] at hyi
  obtain ⟨u, hu, huEq⟩ := hyi
  obtain ⟨huu, hτc⟩ := cross_unique P ρ x i huEq.symm
  have hzero : (1 - u) * side ρ.r x (P.q i)
      + u * side ρ.r x (P.q (cyclicNext i)) = 0 := by
    rw [← side_lineMap_vertex, huEq]
    unfold side det2
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  set sa := side ρ.r x (P.q i) with hsa_def
  set sb := side ρ.r x (P.q (cyclicNext i)) with hsb_def
  have hsa : sa ≠ 0 := hvert i
  have hsb : sb ≠ 0 := hvert (cyclicNext i)
  have hu0 : (0 : ℝ) ≤ u := hu.1
  have hu1 : u ≤ 1 := hu.2
  have hprod : sa * sb < 0 := by
    rcases lt_or_gt_of_ne hsa with h1 | h1 <;> rcases lt_or_gt_of_ne hsb with h2 | h2
    · exfalso
      have e1 : (1 - u) * sa ≤ 0 := by nlinarith
      have e2 : u * sb ≤ 0 := by nlinarith
      have e1' : (1 - u) * sa = 0 := by linarith
      have e2' : u * sb = 0 := by linarith
      rcases mul_eq_zero.mp e1' with h | h
      · rcases mul_eq_zero.mp e2' with h' | h'
        · linarith
        · exact hsb h'
      · exact hsa h
    · exact mul_neg_of_neg_of_pos h1 h2
    · exact mul_neg_of_pos_of_neg h1 h2
    · exfalso
      have e1 : 0 ≤ (1 - u) * sa := by nlinarith
      have e2 : 0 ≤ u * sb := by nlinarith
      have e1' : (1 - u) * sa = 0 := by linarith
      have e2' : u * sb = 0 := by linarith
      rcases mul_eq_zero.mp e1' with h | h
      · rcases mul_eq_zero.mp e2' with h' | h'
        · linarith
        · exact hsb h'
      · exact hsa h
  have hspan : SpanCrossesSide P ρ x i := by
    unfold SpanCrossesSide
    exact (span_iff_opp_sign hsa hsb).mpr hprod
  have hmem : i ∈ CrossingEdges' P ρ x :=
    (mem_crossingEdges'_iff P ρ x i).mpr ⟨hspan, by rw [← hτc]; exact hc⟩
  exact hne i hmem hτc.symm

/-! ## §5. Sorted enumeration of a finite set along an injective real key -/

/-- **Sorted enumeration.**  A finite set with an injective real key admits a nodup
enumeration strictly sorted by the key. -/
theorem exists_sorted_enum {α : Type*} [DecidableEq α] (f : α → ℝ) :
    ∀ S : Finset α, (∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b) →
      ∃ L : List α, L.Nodup ∧ (∀ a, a ∈ L ↔ a ∈ S) ∧
        L.Pairwise (fun a b => f a < f b) := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | _ S IH =>
    intro hinj
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], List.nodup_nil, by simp, List.Pairwise.nil⟩
    · obtain ⟨a, haS, hamin⟩ := S.exists_min_image f hne
      obtain ⟨L', hnd', hmem', hpair'⟩ := IH (S.erase a) (Finset.erase_ssubset haS)
        (fun b hb c hc h =>
          hinj b (Finset.mem_of_mem_erase hb) c (Finset.mem_of_mem_erase hc) h)
      refine ⟨a :: L', ?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        exact ⟨fun ha => (Finset.notMem_erase a S) ((hmem' a).mp ha), hnd'⟩
      · intro b
        rw [List.mem_cons, hmem' b, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨_, hb⟩)
          · exact haS
          · exact hb
        · intro hbS
          by_cases hba : b = a
          · exact Or.inl hba
          · exact Or.inr ⟨hba, hbS⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hpair'⟩
        intro b hb
        have hbe := (hmem' b).mp hb
        have hbne : b ≠ a := Finset.ne_of_mem_erase hbe
        have hle : f a ≤ f b := hamin b (Finset.mem_of_mem_erase hbe)
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exact absurd (hinj a haS b (Finset.mem_of_mem_erase hbe) h) (Ne.symm hbne)

/-! ## §6. The combinatorial alternation engine

Pure list/Finset combinatorics, no geometry: if every `τ ≥ c` filtered sum of a `±1` weight
lies in `{0, s}` for one fixed `s = ±1`, then a key-sorted enumeration has alternating
weights — two equal consecutive weights would make two of those filtered (suffix) sums
differ by `2`. -/

/-- A cut-characterised list computes its filtered sum. -/
theorem cut_sum_eq {α : Type*} [DecidableEq α] (S : Finset α) (τ : α → ℝ) (σ : α → ℤ)
    (c : ℝ) (N : List α) (hnd : N.Nodup)
    (hch : ∀ a, a ∈ N ↔ a ∈ S ∧ c ≤ τ a) :
    (∑ a ∈ S.filter (fun a => c ≤ τ a), σ a) = (N.map σ).sum := by
  have hset : S.filter (fun a => c ≤ τ a) = N.toFinset := by
    ext a
    rw [Finset.mem_filter, List.mem_toFinset, hch]
  rw [hset]
  exact List.sum_toFinset σ hnd

/-- **The alternation engine.**  If all `τ ≥ c` filtered `σ`-sums over `S` (at admissible
cuts `c ≥ 0` avoiding the key values) lie in `{0, s}` with `σ` valued in `±1` and `s = ±1`,
then any nodup, strictly-sorted, cut-characterised list over `S` has alternating `σ`. -/
theorem alt_of_cut_dichotomy {α : Type*} [DecidableEq α]
    (S : Finset α) (τ : α → ℝ) (σ : α → ℤ) (s : ℤ)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1) (hs : s = 1 ∨ s = -1)
    (HW : ∀ c : ℝ, 0 ≤ c → (∀ a ∈ S, τ a ≠ c) →
      (∑ a ∈ S.filter (fun a => c ≤ τ a), σ a) = 0 ∨
        (∑ a ∈ S.filter (fun a => c ≤ τ a), σ a) = s)
    (M : List α) (hnd : M.Nodup) (hsort : M.Pairwise (fun a b => τ a < τ b))
    (c₀ : ℝ) (hc₀0 : 0 ≤ c₀) (hc₀ne : ∀ a ∈ S, τ a ≠ c₀)
    (hcut : ∀ a, a ∈ M ↔ a ∈ S ∧ c₀ ≤ τ a) :
    Alt (M.map σ) := by
  match M, hnd, hsort, hcut with
  | [], _, _, _ => trivial
  | [a], _, _, _ => trivial
  | (a :: b :: t), hnd, hsort, hcut =>
    have haM : a ∈ a :: b :: t := List.mem_cons_self ..
    have hbM : b ∈ a :: b :: t := List.mem_cons_of_mem a (List.mem_cons_self ..)
    have haS : a ∈ S := ((hcut a).mp haM).1
    have hbS : b ∈ S := ((hcut b).mp hbM).1
    have hc₀a : c₀ ≤ τ a := ((hcut a).mp haM).2
    have hpc := List.pairwise_cons.mp hsort
    have hab : τ a < τ b := hpc.1 b (List.mem_cons_self ..)
    have hpc2 := List.pairwise_cons.mp hpc.2
    have htb : ∀ l ∈ t, τ b < τ l := hpc2.1
    -- the middle cut between `a` and `b`
    set c₁ : ℝ := (τ a + τ b) / 2 with hc₁def
    have hc₁a : τ a < c₁ := by rw [hc₁def]; linarith
    have hc₁b : c₁ < τ b := by rw [hc₁def]; linarith
    have hc₁0 : 0 ≤ c₁ := by linarith
    have hcut₁ : ∀ l, l ∈ (b :: t) ↔ l ∈ S ∧ c₁ ≤ τ l := by
      intro l
      constructor
      · intro hl
        rcases List.mem_cons.mp hl with rfl | hlt
        · exact ⟨hbS, hc₁b.le⟩
        · refine ⟨((hcut l).mp
            (List.mem_cons_of_mem a (List.mem_cons_of_mem b hlt))).1, ?_⟩
          have := htb l hlt
          linarith
      · rintro ⟨hlS, hlc⟩
        have hlM : l ∈ a :: b :: t := (hcut l).mpr ⟨hlS, by linarith⟩
        rcases List.mem_cons.mp hlM with rfl | hl'
        · exfalso; linarith
        · exact hl'
    have hc₁ne : ∀ l ∈ S, τ l ≠ c₁ := by
      intro l hlS hlc
      have hlM : l ∈ a :: b :: t := (hcut l).mpr ⟨hlS, by linarith⟩
      rcases List.mem_cons.mp hlM with rfl | hl'
      · linarith
      rcases List.mem_cons.mp hl' with rfl | hl''
      · linarith
      · have := htb l hl''; linarith
    -- the two near window sums
    have hnd₁ : (b :: t).Nodup := (List.nodup_cons.mp hnd).2
    have hnd₂ : t.Nodup := (List.nodup_cons.mp hnd₁).2
    have W₀ := HW c₀ hc₀0 hc₀ne
    have W₁ := HW c₁ hc₁0 hc₁ne
    rw [cut_sum_eq S τ σ c₀ (a :: b :: t) hnd hcut] at W₀
    rw [cut_sum_eq S τ σ c₁ (b :: t) hnd₁ hcut₁] at W₁
    simp only [List.map_cons, List.sum_cons] at W₀ W₁
    -- recurse first (structural; the far cut is only needed for the head pair)
    refine ⟨?_, alt_of_cut_dichotomy S τ σ s hpm hs HW (b :: t) hnd₁ hpc.2
      c₁ hc₁0 hc₁ne hcut₁⟩
    -- σ a ≠ σ b: equal consecutive signs would put two window sums 2 apart.
    have hσa := hpm a haS
    have hσb := hpm b hbS
    intro hEq
    rcases t with _ | ⟨d, t'⟩
    · -- t = []: W₀ = σa + σb, W₁ = σb already contradict.
      simp only [List.map_nil, List.sum_nil] at W₀ W₁
      omega
    · -- t = d :: t': build the far cut just past `b` and a third window sum.
      have hbd : τ b < τ d := htb d (List.mem_cons_self ..)
      have htd : ∀ l ∈ t', τ d < τ l := (List.pairwise_cons.mp hpc2.2).1
      set c₂ : ℝ := (τ b + τ d) / 2 with hc₂def
      have hc₂b : τ b < c₂ := by rw [hc₂def]; linarith
      have hc₂d : c₂ < τ d := by rw [hc₂def]; linarith
      have hc₂0 : 0 ≤ c₂ := by linarith
      have hc₂ne : ∀ l ∈ S, τ l ≠ c₂ := by
        intro l hlS hlc
        have hlM : l ∈ a :: b :: d :: t' := (hcut l).mpr ⟨hlS, by linarith⟩
        rcases List.mem_cons.mp hlM with rfl | hl'
        · linarith
        rcases List.mem_cons.mp hl' with rfl | hl''
        · linarith
        rcases List.mem_cons.mp hl'' with rfl | hl'''
        · linarith
        · have := htd l hl'''; linarith
      have hcut₂ : ∀ l, l ∈ (d :: t') ↔ l ∈ S ∧ c₂ ≤ τ l := by
        intro l
        constructor
        · intro hl
          rcases List.mem_cons.mp hl with rfl | hl'
          · exact ⟨((hcut l).mp (by simp)).1, hc₂d.le⟩
          · refine ⟨((hcut l).mp (by simp [hl'])).1, ?_⟩
            have := htd l hl'
            linarith
        · rintro ⟨hlS, hlc⟩
          have hlM : l ∈ a :: b :: d :: t' := (hcut l).mpr ⟨hlS, by linarith⟩
          rcases List.mem_cons.mp hlM with rfl | hl'
          · exfalso; linarith
          rcases List.mem_cons.mp hl' with rfl | hl''
          · exfalso; linarith
          · exact hl''
      have W₂ := HW c₂ hc₂0 hc₂ne
      rw [cut_sum_eq S τ σ c₂ (d :: t') hnd₂ hcut₂] at W₂
      simp only [List.map_cons, List.sum_cons] at W₀ W₁ W₂
      omega
  termination_by M.length

/-! ## §7. The headline: `RayCrossingAlternation` from the ray winding dichotomy

The kernel at a generic off-boundary base point, EXACTLY from the planar-Jordan two-value
dichotomy along its forward ray.  Everything else — the sorted enumeration, the distinct
parameters, the suffix-sum law, the alternation combinatorics — is unconditional and lives
above. -/

/-- **The Chapter-36 Jordan kernel from the ray winding dichotomy.**  Let `x` be off the
boundary with no polygon vertex on its ray line (the genericity guard — NECESSARY, see
`rayCrossingAlternation_not_universal`).  If the signed winding takes at most the two
values `{0, s}` (one fixed `s = ±1`) at every off-boundary point of the forward ray, then
the forward crossings, sorted by `crossTau`, have alternating `eSign`:
`RayCrossingAlternation P ρ x`. -/
theorem rayCrossingAlternation_of_ray_dichotomy
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hoff : ¬ OnBoundary P x)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (H : ∀ c : ℝ, 0 ≤ c → ¬ OnBoundary P (x + c • ρ.r) →
      windCross P ρ (x + c • ρ.r) = 0 ∨ windCross P ρ (x + c • ρ.r) = s) :
    RayCrossingAlternation P ρ x := by
  classical
  have hinj : ∀ a ∈ CrossingEdges' P ρ x, ∀ b ∈ CrossingEdges' P ρ x,
      crossTau P ρ x a = crossTau P ρ x b → a = b := by
    intro a ha b hb hEq
    by_contra hne
    exact crossTau_injOn_crossingEdges P ρ x hvert ha hb hne hEq
  obtain ⟨L, hnd, hmem, hsort⟩ :=
    exists_sorted_enum (crossTau P ρ x) (CrossingEdges' P ρ x) hinj
  refine ⟨L, hnd, hmem, hsort, ?_⟩
  have HW : ∀ c : ℝ, 0 ≤ c →
      (∀ a ∈ CrossingEdges' P ρ x, crossTau P ρ x a ≠ c) →
      (∑ a ∈ (CrossingEdges' P ρ x).filter (fun a => c ≤ crossTau P ρ x a),
          eSign P ρ a) = 0 ∨
        (∑ a ∈ (CrossingEdges' P ρ x).filter (fun a => c ≤ crossTau P ρ x a),
          eSign P ρ a) = s := by
    intro c hc hcne
    have hWc := windCross_translate P ρ x hc
    have hoffc := not_onBoundary_at_cut P ρ x hvert hc hcne
    rcases H c hc hoffc with h0 | h0
    · left; rw [← hWc]; exact h0
    · right; rw [← hWc]; exact h0
  have hτ0 : ∀ a ∈ CrossingEdges' P ρ x, crossTau P ρ x a ≠ 0 := fun a ha =>
    crossTau_ne_zero_of_offBoundary P ρ x hoff hvert ha
  have hcut0 : ∀ a, a ∈ L ↔ a ∈ CrossingEdges' P ρ x ∧ (0 : ℝ) ≤ crossTau P ρ x a := by
    intro a
    rw [hmem a]
    constructor
    · intro haS
      exact ⟨haS, ((mem_crossingEdges'_iff P ρ x a).mp haS).2⟩
    · exact fun h => h.1
  exact alt_of_cut_dichotomy (CrossingEdges' P ρ x) (crossTau P ρ x) (eSign P ρ) s
    (fun a _ => eSign_mem P ρ a) hs HW L hnd hsort 0 le_rfl hτ0 hcut0

/-- **The winding bound at generic points, from the dichotomy** (wiring into the proved
bridge `windCross_mem_of_alternation`): under the same hypotheses the signed winding at `x`
is `0`, `1`, or `−1`. -/
theorem windCross_mem_of_ray_dichotomy
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hoff : ¬ OnBoundary P x)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (H : ∀ c : ℝ, 0 ≤ c → ¬ OnBoundary P (x + c • ρ.r) →
      windCross P ρ (x + c • ρ.r) = 0 ∨ windCross P ρ (x + c • ρ.r) = s) :
    windCross P ρ x = 0 ∨ windCross P ρ x = 1 ∨ windCross P ρ x = -1 :=
  windCross_mem_of_alternation P ρ
    (rayCrossingAlternation_of_ray_dichotomy P ρ x hoff hvert s hs H)

/-! ## §8. The two machine refutations (concrete, on a genuine `StrictSimplePolygon`)

The witness polygon is the strict simple triangle `A = (0,0)`, `V = (2,1)`, `B = (1,3)`
(via the proved `PolygonEarExterior.earTri`), the ray direction `r = (1,0)` (parallel to no
edge), and the base point `x = (−1, 0)`: the forward ray from `x` passes through the vertex
`A`, whose both neighbours `V, B` lie strictly ABOVE the ray line. -/

/-- `mkPt` first coordinate. -/
lemma mkPt_eval0 (x y : ℝ) : (mkPt x y) 0 = x := by simp [mkPt]

/-- `mkPt` second coordinate. -/
lemma mkPt_eval1 (x y : ℝ) : (mkPt x y) 1 = y := by simp [mkPt]

/-- `lineMap` in coordinates. -/
lemma lineMap_coord (p q : Pt) (t : ℝ) (k : Fin 2) :
    (AffineMap.lineMap p q t : Pt) k = (1 - t) * p k + t * q k := by
  rw [AffineMap.lineMap_apply_module]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- Two distinct members of a `Pairwise R` list are related one way or the other. -/
lemma rel_of_pairwise_of_mem {α : Type*} {R : α → α → Prop} :
    ∀ {L : List α}, L.Pairwise R → ∀ {a b : α}, a ∈ L → b ∈ L → a ≠ b → R a b ∨ R b a := by
  intro L hL
  induction hL with
  | nil => intro a b ha _ _; simp at ha
  | @cons c l hr _ ih =>
    intro a b ha hb hne
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact Or.inl (hr b hb')
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr (hr a ha')
      · exact ih ha' hb' hne

/-- The counterexample vertices. -/
def cexA : Pt := mkPt 0 0
def cexV : Pt := mkPt 2 1
def cexB : Pt := mkPt 1 3

lemma cexO : orient cexA cexV cexB ≠ 0 := by
  unfold orient det2 cexA cexV cexB
  norm_num [mkPt, PiLp.sub_apply]

/-- The counterexample polygon: the strict simple triangle `(A, V, B)`. -/
def cexP : StrictSimplePolygon 3 := ProofsInTheBook.PolygonEarExterior.earTri cexO

/-- The counterexample base point `x = (−1, 0)`. -/
def cexX : Pt := mkPt (-1) 0

lemma cexq0 : cexP.q 0 = cexA := rfl
lemma cexq1 : cexP.q 1 = cexV := rfl
lemma cexq2 : cexP.q 2 = cexB := rfl

lemma cexNext0 : cyclicNext (0 : Fin 3) = 1 := by decide
lemma cexNext1 : cyclicNext (1 : Fin 3) = 2 := by decide
lemma cexNext2 : cyclicNext (2 : Fin 3) = 0 := by decide

/-- The counterexample ray direction `r = (1, 0)`, parallel to no edge. -/
def cexRho : RayDirection cexP where
  r := mkPt 1 0
  r_ne_zero := mkPt_one_ne_zero 0
  no_edge_parallel := by
    intro i
    fin_cases i <;>
      · simp only [cexP, ProofsInTheBook.PolygonEarExterior.earTri]
        unfold det2 ProofsInTheBook.PolygonEarExterior.earTriTuple cexA cexV cexB
        simp only [cyclicNext]
        norm_num [mkPt, PiLp.sub_apply]

lemma cexR : cexRho.r = mkPt 1 0 := rfl

/-- `x = (−1,0)` is off the boundary of the counterexample triangle. -/
lemma cexX_offBoundary : ¬ OnBoundary cexP cexX := by
  rintro ⟨i, hi⟩
  fin_cases i <;>
    · unfold Edge seg at hi
      rw [segment_eq_image_lineMap] at hi
      obtain ⟨t, ht, hEq⟩ := hi
      have h0 := congrArg (fun w : Pt => w 0) hEq
      have h1 := congrArg (fun w : Pt => w 1) hEq
      simp only [lineMap_coord] at h0 h1
      simp only [cexP, ProofsInTheBook.PolygonEarExterior.earTri] at h0 h1
      unfold ProofsInTheBook.PolygonEarExterior.earTriTuple cexA cexV cexB cexX
        at h0 h1
      simp only [cyclicNext] at h0 h1
      norm_num [mkPt] at h0 h1
      linarith [ht.1, ht.2]

/-- Side coordinates at the counterexample: the swept vertex `A` is ON the ray line,
both its neighbours strictly above. -/
lemma cexSideA : side cexRho.r cexX cexA = 0 := by
  unfold side det2 cexX cexA; rw [cexR]
  norm_num [mkPt, PiLp.sub_apply]

lemma cexSideV : side cexRho.r cexX cexV = 1 := by
  unfold side det2 cexX cexV; rw [cexR]
  norm_num [mkPt, PiLp.sub_apply]

lemma cexSideB : side cexRho.r cexX cexB = 3 := by
  unfold side det2 cexX cexB; rw [cexR]
  norm_num [mkPt, PiLp.sub_apply]

/-- Both edges incident to the swept vertex `A` are forward crossings... -/
lemma cexCross0 : EdgeCrossesRay' cexP cexRho cexX 0 := by
  constructor
  · unfold SpanCrossesSide
    rw [cexNext0, cexq0, cexq1, cexSideA, cexSideV]
    exact Or.inl ⟨le_refl 0, one_pos⟩
  · unfold crossTau crossDen
    rw [cexNext0, cexq0, cexq1]
    unfold det2 cexA cexV cexX; rw [cexR]
    norm_num [mkPt, PiLp.sub_apply]

lemma cexCross2 : EdgeCrossesRay' cexP cexRho cexX 2 := by
  constructor
  · unfold SpanCrossesSide
    rw [cexNext2, cexq2, cexq0, cexSideB, cexSideA]
    exact Or.inr ⟨le_refl 0, by norm_num⟩
  · unfold crossTau crossDen
    rw [cexNext2, cexq2, cexq0]
    unfold det2 cexA cexB cexX; rw [cexR]
    norm_num [mkPt, PiLp.sub_apply]

/-- ... and they have EQUAL ray parameter (`crossTau = 1`, the shared vertex `A`). -/
lemma cexTau0 : crossTau cexP cexRho cexX 0 = 1 := by
  unfold crossTau crossDen
  rw [cexNext0, cexq0, cexq1]
  unfold det2 cexA cexV cexX; rw [cexR]
  norm_num [mkPt, PiLp.sub_apply]

lemma cexTau2 : crossTau cexP cexRho cexX 2 = 1 := by
  unfold crossTau crossDen
  rw [cexNext2, cexq2, cexq0]
  unfold det2 cexA cexB cexX; rw [cexR]
  norm_num [mkPt, PiLp.sub_apply]

/-- **The kernel as stated is FALSE without the vertex-genericity guard** (machine
refutation): a strict simple triangle, an admissible ray direction, and an OFF-BOUNDARY
base point whose forward ray passes through a vertex with both neighbours strictly above
the ray line.  The two incident edges are BOTH forward crossings with EQUAL `crossTau`, so
no strictly-sorted enumeration exists and `RayCrossingAlternation` fails.  Hence the guard
`hvert` in `rayCrossingAlternation_of_ray_dichotomy` is necessary, and any unconditional
kernel supply must perturb `x` off the finitely many vertex rays first. -/
theorem rayCrossingAlternation_not_universal :
    ∃ (P : StrictSimplePolygon 3) (ρ : RayDirection P) (x : Pt),
      ¬ OnBoundary P x ∧ ¬ RayCrossingAlternation P ρ x := by
  refine ⟨cexP, cexRho, cexX, cexX_offBoundary, ?_⟩
  rintro ⟨L, _hnd, hmem, hsort, _halt⟩
  have h0L : (0 : Fin 3) ∈ L :=
    (hmem 0).mpr ((mem_crossingEdges'_iff cexP cexRho cexX 0).mpr cexCross0)
  have h2L : (2 : Fin 3) ∈ L :=
    (hmem 2).mpr ((mem_crossingEdges'_iff cexP cexRho cexX 2).mpr cexCross2)
  have hne : (0 : Fin 3) ≠ 2 := by decide
  rcases rel_of_pairwise_of_mem hsort h0L h2L hne with h | h
  · rw [cexTau0, cexTau2] at h; exact lt_irrefl 1 h
  · rw [cexTau0, cexTau2] at h; exact lt_irrefl 1 h

/-- **The blanket turn-support of the monotone squeeze FAILS on a genuine strict simple
polygon** (machine refutation of the brief's blanket-monotone hope): at the off-boundary
point `x` the consecutive position-vector turn across the wrap edge is strictly NEGATIVE
(`det2 (B − x) (A − x) = −3 < 0`), so the `mono_theta2` chain hypotheses cannot be supplied
along the whole boundary.  (At every exterior point winding `0` forces such a negative
turn; at reflex polygons even interior points fail — the `allConvex` dead end.) -/
theorem posVec_turn_support_fails :
    ∃ (P : StrictSimplePolygon 3) (x : Pt) (i : Fin 3),
      ¬ OnBoundary P x ∧ det2 (P.q i - x) (P.q (cyclicNext i) - x) < 0 := by
  refine ⟨cexP, cexX, 2, cexX_offBoundary, ?_⟩
  rw [cexNext2, cexq2, cexq0]
  unfold det2 cexA cexB cexX
  norm_num [mkPt, PiLp.sub_apply]

/-! ## §9. The full-line telescope: up-crossings = down-crossings (unconditional)

The ONE global crossing fact available without any Jordan content: over the whole ray LINE
(`Span` only, no forward guard), the `eSign` sum telescopes to `0` — each edge contributes
the difference of its endpoint strict-side indicators, and the cyclic sum of differences
vanishes.  Consequently the forward (`windCross`) and backward signed sums are exact
negatives.  This pins the global budget every future alternation proof must distribute. -/

/-- The strict-side indicator of a vertex (`1` strictly above the ray line, else `0`). -/
def sideInd (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n) : ℤ :=
  if 0 < side ρ.r x (P.q i) then 1 else 0

/-- **Per-edge telescope**: with no vertex on the ray line, the span-gated `eSign` of an
edge is the difference of its endpoint side indicators. -/
lemma eSign_span_eq_sideInd_sub (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) (i : Fin n) :
    (if SpanCrossesSide P ρ x i then eSign P ρ i else 0)
      = sideInd P ρ x (cyclicNext i) - sideInd P ρ x i := by
  classical
  have hD : crossDen P ρ i
      = side ρ.r x (P.q (cyclicNext i)) - side ρ.r x (P.q i) :=
    (side_next_sub_side P ρ x i).symm
  have hDdef : det2 ρ.r (P.q (cyclicNext i) - P.q i) = crossDen P ρ i := rfl
  have hsa := hvert i
  have hsb := hvert (cyclicNext i)
  have hspan := span_iff_opp_sign hsa hsb
  unfold sideInd
  unfold eSign PolygonWindingZero.edgeSign
  rw [hDdef, hD]
  rcases lt_or_gt_of_ne hsa with h1 | h1 <;> rcases lt_or_gt_of_ne hsb with h2 | h2
  · -- (−,−): no crossing, indicators 0 − 0.
    rw [if_neg (fun hs => by have := hspan.mp hs; nlinarith), if_neg (by linarith),
      if_neg (by linarith)]
    norm_num
  · -- (−,+): upward crossing, +1 = 1 − 0.
    rw [if_pos (show SpanCrossesSide P ρ x i from
        (span_iff_opp_sign hsa hsb).mpr (by nlinarith)),
      if_pos (by linarith), if_pos h2, if_neg (by linarith)]
    norm_num
  · -- (+,−): downward crossing, −1 = 0 − 1.
    rw [if_pos (show SpanCrossesSide P ρ x i from
        (span_iff_opp_sign hsa hsb).mpr (by nlinarith)),
      if_neg (by linarith), if_neg (by linarith), if_pos h1]
    norm_num
  · -- (+,+): no crossing, indicators 1 − 1.
    rw [if_neg (fun hs => by have := hspan.mp hs; nlinarith), if_pos h2, if_pos h1]
    norm_num

/-- **The full-line telescope** (unconditional, no Jordan content): with no vertex on the
ray line, the signed `eSign` sum over ALL span-crossed edges of the whole line is `0` —
up-crossings and down-crossings of a closed polygon across any generic line balance
exactly. -/
theorem lineCrossing_eSign_sum_zero (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) :
    ∑ i ∈ Finset.univ.filter (fun i => SpanCrossesSide P ρ x i), eSign P ρ i = 0 := by
  classical
  rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun i _ => eSign_span_eq_sideInd_sub P ρ x hvert i)]
  rw [Finset.sum_sub_distrib]
  have hreindex : ∑ i : Fin n, sideInd P ρ x (cyclicNext i)
      = ∑ i : Fin n, sideInd P ρ x i :=
    Function.Bijective.sum_comp
      (Finite.injective_iff_bijective.mp
        ProofsInTheBook.PolygonVertexSweep.cyclicNext_injective)
      (sideInd P ρ x)
  rw [hreindex, sub_self]

/-- **Forward/backward balance**: the signed winding (the forward-ray `eSign` sum) is the
exact negative of the backward (`crossTau < 0`) signed sum.  The global budget the Jordan
alternation must distribute along the two half-lines. -/
theorem windCross_eq_neg_backwardSum (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) :
    windCross P ρ x
      = -∑ i ∈ (Finset.univ.filter (fun i => SpanCrossesSide P ρ x i)).filter
            (fun i => crossTau P ρ x i < 0), eSign P ρ i := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun i => SpanCrossesSide P ρ x i))
    (fun i => crossTau P ρ x i < 0) (eSign P ρ)
  have hline := lineCrossing_eSign_sum_zero P ρ x hvert
  have hforward : (Finset.univ.filter (fun i => SpanCrossesSide P ρ x i)).filter
      (fun i => ¬ crossTau P ρ x i < 0) = CrossingEdges' P ρ x := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
      mem_crossingEdges'_iff]
    constructor
    · rintro ⟨hs, hτ⟩; exact ⟨hs, hτ⟩
    · rintro ⟨hs, hτ⟩; exact ⟨hs, hτ⟩
  rw [hforward, hline] at hsplit
  rw [windCross_eq_sum_crossing_eSign]
  linarith [hsplit]

end

end ProofsInTheBook.ZinanCh36Theta

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.ZinanCh36Theta.lagrange2
#print axioms ProofsInTheBook.ZinanCh36Theta.cos_add_id2
#print axioms ProofsInTheBook.ZinanCh36Theta.sin_add_id2
#print axioms ProofsInTheBook.ZinanCh36Theta.mono_ncos2
#print axioms ProofsInTheBook.ZinanCh36Theta.mono_theta2
#print axioms ProofsInTheBook.ZinanCh36Theta.branch_squeeze_theta2_ne_zero
#print axioms ProofsInTheBook.ZinanCh36Theta.det2_pos_of_theta2_mem
#print axioms ProofsInTheBook.ZinanCh36Theta.forward_strict_support2
#print axioms ProofsInTheBook.ZinanCh36Theta.det2_posVec_lineMap
#print axioms ProofsInTheBook.ZinanCh36Theta.mono_thetaPos_edge
#print axioms ProofsInTheBook.ZinanCh36Theta.thetaPos_eq_zero_at_forward
#print axioms ProofsInTheBook.ZinanCh36Theta.side_translate
#print axioms ProofsInTheBook.ZinanCh36Theta.crossTau_translate
#print axioms ProofsInTheBook.ZinanCh36Theta.crossingEdges'_translate
#print axioms ProofsInTheBook.ZinanCh36Theta.windCross_translate
#print axioms ProofsInTheBook.ZinanCh36Theta.crossU_mem_Ioo
#print axioms ProofsInTheBook.ZinanCh36Theta.crossTau_injOn_crossingEdges
#print axioms ProofsInTheBook.ZinanCh36Theta.crossTau_ne_zero_of_offBoundary
#print axioms ProofsInTheBook.ZinanCh36Theta.not_onBoundary_at_cut
#print axioms ProofsInTheBook.ZinanCh36Theta.exists_sorted_enum
#print axioms ProofsInTheBook.ZinanCh36Theta.alt_of_cut_dichotomy
#print axioms ProofsInTheBook.ZinanCh36Theta.rayCrossingAlternation_of_ray_dichotomy
#print axioms ProofsInTheBook.ZinanCh36Theta.windCross_mem_of_ray_dichotomy
#print axioms ProofsInTheBook.ZinanCh36Theta.rayCrossingAlternation_not_universal
#print axioms ProofsInTheBook.ZinanCh36Theta.posVec_turn_support_fails
#print axioms ProofsInTheBook.ZinanCh36Theta.lineCrossing_eSign_sum_zero
#print axioms ProofsInTheBook.ZinanCh36Theta.windCross_eq_neg_backwardSum
