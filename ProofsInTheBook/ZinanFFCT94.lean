import ProofsInTheBook.ZinanFFCT92

/-!
# `ZinanFFCT94` -- the pure planar lifted-turn no-repeat core (bricks A + B)

This file replaces the FALSE `ZinanFFCT92.PlanarClosedWeakStrictNoRepeat`
(refuted by the doubled triangle in `ZinanFFCT93`) with a *correct* lifted
single-wind certificate and a no-repeat theorem proved from it.

## Brick A
`PlanarLiftedTurnSpan` is a finite lifted edge-direction certificate for a
planar chain `Q : Fin N → E3` lying in the affine plane `⟨h, ·⟩ = 1`:
an orthonormal pair `(u, v) ⊥ h`, a *lifted* real turn function `θ : ℕ → ℝ`
(not taken mod `2π`), edge lengths `ρ`, with

* `edge_eq` : `Q (i+1) - Q i = ρ i • (cos (θ i) • u + sin (θ i) • v)`,
* `turn_pos`, `turn_lt_pi` : consecutive lifted turns are in `(0, π)`,
* `one_wind` : `θ N - θ 0 < 2π` (the single-wind bound).

## Brick B (what is proved here)
`planarWeakConvex_strictTurns_halfWind_noNonadjacentRepeat` :
under a *half-wind* certificate (`θ N - θ 0 < π`) the chain has no nonadjacent
repeated vertices.  This is the clean, complete, single-covector telescoping
sub-case.  It already excludes the doubled triangle, whose lifted `θ` runs
`0 → 4π`, failing even `one_wind` (let alone `half_wind`).

The general `one_wind` (`< 2π`) case is *not* a consequence of `turn_pos`,
`turn_lt_pi`, `one_wind` alone: the closed equilateral triangle
(`θ : 0, 2π/3, 4π/3`, total turn `2π`) shows that a positive combination of
directions whose lifted angles span `< 2π` can vanish.  Excluding it requires
the support hypothesis `hsupp`; see the report for the precise residual.
-/

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.ZinanFFCT94

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## Brick A: the finite lifted edge-direction certificate. -/

/-- A finite lifted edge-direction certificate for a planar chain
`Q : Fin N → E3`.  Avoids Mathlib winding numbers: the data records that every
vertex lies in the affine plane `⟨h, ·⟩ = 1`, that `(u, v)` is orthonormal and
perpendicular to `h`, and that each edge is a positive-length vector whose
*lifted* (real, not mod `2π`) direction `θ` strictly increases by less than `π`
per step, with a single-wind total bound `θ N - θ 0 < 2π`. -/
structure PlanarLiftedTurnSpan {N : ℕ} (Q : Fin N → E3) (h u v : E3) where
  in_plane : ∀ i : Fin N, (⟪h, Q i⟫ : ℝ) = 1
  u_perp_h : (⟪h, u⟫ : ℝ) = 0
  v_perp_h : (⟪h, v⟫ : ℝ) = 0
  u_unit : (⟪u, u⟫ : ℝ) = 1
  v_unit : (⟪v, v⟫ : ℝ) = 1
  uv_perp : (⟪u, v⟫ : ℝ) = 0
  θ : ℕ → ℝ
  ρ : ℕ → ℝ
  ρ_pos : ∀ i : ℕ, 0 < ρ i
  /-- Edge increment, indexed by the natural number `m < N - 1` so that the
  successor `m + 1` never wraps inside the open chain. -/
  edge_eq : ∀ (m : ℕ) (hm : m + 1 < N),
      Q ⟨m + 1, hm⟩ - Q ⟨m, by omega⟩
        = ρ m • (Real.cos (θ m) • u + Real.sin (θ m) • v)
  turn_pos : ∀ m : ℕ, 0 < θ (m + 1) - θ m
  turn_lt_pi : ∀ m : ℕ, θ (m + 1) - θ m < Real.pi
  one_wind : θ N - θ 0 < 2 * Real.pi

/-- The half-wind strengthening: the entire lifted turn-span is below `π`.
On this sub-certificate the no-repeat theorem closes by a single covector. -/
structure PlanarLiftedTurnSpanHalf {N : ℕ} (Q : Fin N → E3) (h u v : E3)
    extends PlanarLiftedTurnSpan Q h u v where
  half_wind : toPlanarLiftedTurnSpan.θ N - toPlanarLiftedTurnSpan.θ 0 < Real.pi

/-! ## The planar no-repeat predicate (planar analogue of
`SphericalKernel.NoNonadjacentRepeat`, over `E3`). -/

/-- The chain `Q : Fin N → E3` never revisits a vertex at two nonadjacent
positions `r + 2 ≤ s`. -/
def PlanarNoNonadjacentRepeat {N : ℕ} (Q : Fin N → E3) : Prop :=
  ∀ (r s : ℕ) (hr : r < N) (hs : s < N), r + 2 ≤ s →
    Q ⟨r, hr⟩ ≠ Q ⟨s, hs⟩

/-! ## Strict monotonicity of the lifted turn function. -/

/-- From `turn_pos`, the lifted turn function `θ` is strictly monotone in the
natural-number index. -/
theorem theta_strictMono {N : ℕ} {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpan Q h u v) :
    StrictMono cert.θ := by
  apply strictMono_nat_of_lt_succ
  intro m
  have := cert.turn_pos m
  linarith

/-- `θ b - θ a` is bounded by `θ N - θ 0` for `0 ≤ a ≤ b ≤ N`. -/
theorem theta_sub_le_total {N : ℕ} {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpan Q h u v) {a b : ℕ}
    (_hab : a ≤ b) (hbN : b ≤ N) :
    cert.θ b - cert.θ a ≤ cert.θ N - cert.θ 0 := by
  have hmono := theta_strictMono cert
  have h0a : cert.θ 0 ≤ cert.θ a := hmono.monotone (Nat.zero_le a)
  have hbN' : cert.θ b ≤ cert.θ N := hmono.monotone hbN
  linarith

/-! ## Brick B: the telescoping no-repeat theorem (half-wind case). -/

/-- The telescoped displacement.  For `r ≤ m ≤ N - 1`,
`Q m - Q r = ∑_{i ∈ [r, m)} ρ i • (cos (θ i) • u + sin (θ i) • v)`. -/
theorem displacement_telescope {N : ℕ} {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpan Q h u v) {r m : ℕ}
    (hrm : r ≤ m) (hmN : m < N) (hrN : r < N) :
    Q ⟨m, hmN⟩ - Q ⟨r, hrN⟩
      = ∑ i ∈ Finset.Ico r m,
          cert.ρ i • (Real.cos (cert.θ i) • u + Real.sin (cert.θ i) • v) := by
  induction m with
  | zero =>
    interval_cases r
    simp
  | succ k ih =>
    rcases Nat.lt_or_ge r (k + 1) with hr_lt | hr_ge
    · -- r ≤ k
      have hrk : r ≤ k := by omega
      have hkN : k < N := by omega
      have hstep := cert.edge_eq k hmN
      have hih := ih hrk hkN
      rw [Finset.sum_Ico_succ_top hrk]
      -- Q (k+1) - Q r = (Q (k+1) - Q k) + (Q k - Q r)
      have hsplit :
          Q ⟨k + 1, hmN⟩ - Q ⟨r, hrN⟩
            = (Q ⟨k + 1, hmN⟩ - Q ⟨k, hkN⟩) + (Q ⟨k, hkN⟩ - Q ⟨r, hrN⟩) := by
        abel
      rw [hsplit, hstep, hih]
      abel
    · -- r = k + 1 = m, empty sum
      have hr_eq : r = k + 1 := by omega
      subst hr_eq
      simp

/-- The inner product of the lifted edge direction at index `i` with the
covector `cos φ • u + sin φ • v` equals `cos (θ i - φ)`.  This is the
sum-to-product identity that turns the planar telescoping into a scalar
positivity argument. -/
theorem covector_component {N : ℕ} {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpan Q h u v) (φ : ℝ) (i : ℕ) :
    (⟪Real.cos φ • u + Real.sin φ • v,
        Real.cos (cert.θ i) • u + Real.sin (cert.θ i) • v⟫ : ℝ)
      = Real.cos (cert.θ i - φ) := by
  rw [inner_add_left, inner_add_right, inner_add_right,
    inner_smul_left, inner_smul_left, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, inner_smul_right, inner_smul_right,
    cert.u_unit, cert.v_unit, cert.uv_perp]
  have huv : (⟪v, u⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact cert.uv_perp
  rw [huv]
  simp only [conj_trivial]
  rw [Real.cos_sub]
  ring

/-- **Brick B (half-wind case).**  A planar chain carrying a *half-wind* lifted
turn certificate (`θ N - θ 0 < π`) has no nonadjacent repeated vertices.

Proof: a repeat `Q r = Q s` (`r + 2 ≤ s`) makes the telescoped displacement
`∑_{i ∈ [r, s)} ρ i • d i` vanish, where `d i` is the unit lifted direction.
Pairing with the covector `w = cos φ • u + sin φ • v` at the midpoint angle
`φ = (θ r + θ (s-1)) / 2` gives `∑_{i ∈ [r, s)} ρ i · cos (θ i - φ) = 0`.  But
half-wind forces every `θ i - φ ∈ (-π/2, π/2)`, so each cosine is positive and
each `ρ i > 0`: the sum is strictly positive.  Contradiction. -/
theorem planarWeakConvex_strictTurns_halfWind_noNonadjacentRepeat
    {N : ℕ} [NeZero N] {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpanHalf Q h u v) :
    PlanarNoNonadjacentRepeat Q := by
  intro r s hr hs hrs hrep
  -- The base certificate.
  set c := cert.toPlanarLiftedTurnSpan with hc
  -- s - 1 ≥ r + 1 > r, and the sum over [r, s) is nonempty.
  have hs1N : s - 1 < N := by omega
  have hrs1 : r ≤ s - 1 := by omega
  -- Telescoped displacement vanishes.
  have htele := displacement_telescope c (r := r) (m := s) (by omega) hs hr
  have hvanish :
      (0 : E3) = ∑ i ∈ Finset.Ico r s,
        c.ρ i • (Real.cos (c.θ i) • u + Real.sin (c.θ i) • v) := by
    rw [← htele]
    have : Q ⟨s, hs⟩ = Q ⟨r, hr⟩ := hrep.symm
    rw [this]; abel
  -- The midpoint covector angle.
  set φ : ℝ := (c.θ r + c.θ (s - 1)) / 2 with hφ
  set w : E3 := Real.cos φ • u + Real.sin φ • v with hw
  -- Pair with the covector.
  have hpair : (⟪w, (0 : E3)⟫ : ℝ)
      = ∑ i ∈ Finset.Ico r s, c.ρ i * Real.cos (c.θ i - φ) := by
    rw [hvanish, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_right]
    rw [show (Real.cos (c.θ i) • u + Real.sin (c.θ i) • v)
        = (Real.cos (c.θ i) • u + Real.sin (c.θ i) • v) from rfl]
    rw [covector_component c φ i]
  rw [inner_zero_right] at hpair
  -- The half-wind span bound.
  have hspan : c.θ (s - 1) - c.θ r < Real.pi := by
    have hle := theta_sub_le_total c (a := r) (b := s - 1) hrs1 (by omega)
    have := cert.half_wind
    calc c.θ (s - 1) - c.θ r ≤ c.θ N - c.θ 0 := hle
      _ < Real.pi := cert.half_wind
  have hmono := theta_strictMono c
  -- Each summand is strictly positive.
  have hpos_sum : 0 < ∑ i ∈ Finset.Ico r s, c.ρ i * Real.cos (c.θ i - φ) := by
    apply Finset.sum_pos
    · intro i hi
      rw [Finset.mem_Ico] at hi
      obtain ⟨hir, his⟩ := hi
      have hilo : c.θ r ≤ c.θ i := hmono.monotone hir
      have hihi : c.θ i ≤ c.θ (s - 1) := hmono.monotone (by omega)
      have hcos_pos : 0 < Real.cos (c.θ i - φ) := by
        apply Real.cos_pos_of_mem_Ioo
        rw [Set.mem_Ioo]
        constructor
        · -- -(π/2) < θ i - φ
          have : φ - c.θ i ≤ (c.θ (s - 1) - c.θ r) / 2 := by
            rw [hφ]; linarith
          have h2 : (c.θ (s - 1) - c.θ r) / 2 < Real.pi / 2 := by linarith
          linarith
        · -- θ i - φ < π/2
          have : c.θ i - φ ≤ (c.θ (s - 1) - c.θ r) / 2 := by
            rw [hφ]; linarith
          have h2 : (c.θ (s - 1) - c.θ r) / 2 < Real.pi / 2 := by linarith
          linarith
      have := c.ρ_pos i
      positivity
    · -- nonempty
      rw [Finset.nonempty_Ico]
      omega
  -- hpair : 0 = sum,  hpos_sum : 0 < sum  ⟹  0 < 0.
  rw [← hpair] at hpos_sum
  exact (lt_irrefl (0 : ℝ)) hpos_sum

/-! ## Non-vacuity: a satisfiable half-wind certificate.

We exhibit an explicit `3`-vertex strictly convex planar chain with a half-wind
lifted certificate.  This shows the hypothesis set is genuinely satisfiable
(the theorem is not vacuous) and pins the geometry: the chain turns left by
`π/8` at its single interior joint, total span `2·(π/8) = π/4 < π`. -/

/-- The orthonormal planar frame. -/
def wU : E3 := !₂[(1 : ℝ), 0, 0]
def wV : E3 := !₂[(0 : ℝ), 1, 0]
def wH : E3 := !₂[(0 : ℝ), 0, 1]

/-- An explicit half-wind chain: a corner that turns left by `π/8`. -/
def witChain : Fin 3 → E3 :=
  ![ !₂[(0 : ℝ), 0, 1],
     !₂[(1 : ℝ), 0, 1],
     !₂[(1 + Real.cos (Real.pi / 8) : ℝ), Real.sin (Real.pi / 8), 1] ]

/-- The half-wind certificate is inhabited: `witChain` carries one. -/
theorem witChain_certificate :
    Nonempty (PlanarLiftedTurnSpanHalf witChain wH wU wV) := by
  refine ⟨{
    toPlanarLiftedTurnSpan := {
      θ := fun m => (m : ℝ) * (Real.pi / 8)
      ρ := fun _ => 1
      ρ_pos := fun _ => one_pos
      in_plane := ?_
      u_perp_h := ?_
      v_perp_h := ?_
      u_unit := ?_
      v_unit := ?_
      uv_perp := ?_
      edge_eq := ?_
      turn_pos := ?_
      turn_lt_pi := ?_
      one_wind := ?_ }
    half_wind := ?_ }⟩
  · intro i
    fin_cases i
    · show (⟪wH, !₂[(0 : ℝ), 0, 1]⟫ : ℝ) = 1
      rw [wH, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
    · show (⟪wH, !₂[(1 : ℝ), 0, 1]⟫ : ℝ) = 1
      rw [wH, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
    · show (⟪wH, !₂[(1 + Real.cos (Real.pi / 8) : ℝ), Real.sin (Real.pi / 8), 1]⟫ : ℝ) = 1
      rw [wH, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
  · rw [wH, wU, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
  · rw [wH, wV, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
  · rw [wU, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
  · rw [wV, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
  · rw [wU, wV, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
  · intro m hm
    have hm2 : m < 2 := by omega
    interval_cases m
    · -- edge 0: direction θ = 0
      show witChain ⟨1, _⟩ - witChain ⟨0, _⟩
          = (1 : ℝ) • (Real.cos ((0 : ℕ) * (Real.pi / 8)) • wU
              + Real.sin ((0 : ℕ) * (Real.pi / 8)) • wV)
      simp only [Nat.cast_zero, zero_mul, Real.cos_zero, Real.sin_zero,
        one_smul, zero_smul, add_zero]
      ext k
      fin_cases k <;>
        simp [witChain, wU, PiLp.sub_apply, PiLp.smul_apply]
    · -- edge 1: direction θ = π/8, true by construction
      show witChain ⟨2, _⟩ - witChain ⟨1, _⟩
          = (1 : ℝ) • (Real.cos ((1 : ℕ) * (Real.pi / 8)) • wU
              + Real.sin ((1 : ℕ) * (Real.pi / 8)) • wV)
      simp only [Nat.cast_one, one_mul, one_smul]
      ext k
      fin_cases k <;>
        simp [witChain, wU, wV, ProofsInTheBook.ZinanFFCT10.coordE3_0,
          ProofsInTheBook.ZinanFFCT10.coordE3_1, ProofsInTheBook.ZinanFFCT10.coordE3_2,
          PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply]
  · intro m
    have hpi := Real.pi_pos
    push_cast
    ring_nf
    nlinarith [Real.pi_pos]
  · intro m
    have hpi := Real.pi_pos
    push_cast
    nlinarith [Real.pi_pos]
  · -- one_wind: θ 3 - θ 0 = 3π/8 < 2π
    push_cast
    nlinarith [Real.pi_pos]
  · -- half_wind: θ 3 - θ 0 = 3π/8 < π
    push_cast
    nlinarith [Real.pi_pos]

/-! ## Honesty guard: the doubled triangle is excluded.

The doubled equilateral triangle of `ZinanFFCT93` has lifted turn function
running `0 → 4π` (two full windings), so any certificate for it violates
`one_wind` (`θ 6 - θ 0 = 4π ≥ 2π`).  We record the abstract fact that the
half-wind certificate forces a strict span bound, which `4π` cannot satisfy. -/

/-- Any chain carrying a half-wind certificate has total lifted span `< π`;
in particular no certificate can have span `≥ π` (e.g. the doubled triangle's
`4π`).  This is the structural reason the doubled triangle no longer refutes
the no-repeat conclusion. -/
theorem halfWind_span_lt_pi {N : ℕ} {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpanHalf Q h u v) :
    cert.toPlanarLiftedTurnSpan.θ N - cert.toPlanarLiftedTurnSpan.θ 0 < Real.pi :=
  cert.half_wind

#print axioms planarWeakConvex_strictTurns_halfWind_noNonadjacentRepeat
#print axioms witChain_certificate
#print axioms halfWind_span_lt_pi

end ProofsInTheBook.ZinanFFCT94
