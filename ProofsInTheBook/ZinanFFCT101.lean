import ProofsInTheBook.ZinanFFCT94
import ProofsInTheBook.ZinanFFCT9

/-!
# `ZinanFFCT101` — a proper repeat in a globally-supported planar lifted-turn arm is a full closure

This file proves the planar convex-position no-(proper)-repeat content that
`ZinanFFCT99` showed is *not* furnished by the lifted single-wind certificate
alone: the global cyclic support hypothesis `hsupp` is the missing ingredient.

## The theorem

`planar_properRepeat_is_fullClosure` : given a `PlanarLiftedTurnSpan Q h u v`
certificate, the global cyclic edge support
`hsupp : ∀ i j, 0 ≤ det3 (Q i) (Q (i+1)) (Q j)` (with `i+1` the `Fin N` cyclic
successor — the exact shape the spherical caller `FFCT97` presents), and a
nonadjacent repeat `Q ⟨r⟩ = Q ⟨s⟩` with `r + 2 ≤ s`, the repeat is forced to be
the *full closure* `r = 0 ∧ s = N - 1`.  Equivalently: a PROPER repeat
(`0 < r ∨ s < N - 1`) is impossible.  This precisely allows the `FFCT99`
equilateral N=4 full-closure repeat and forbids only the proper ones.

## Mechanism (the STEP-3 sign clash)

Everything reduces to one fixed-normal area form.  Writing `κ := det3 h u v`
(the frame's signed area), for coplanar apex points one has the transport
`det3 a b c · ‖h‖² = det3 h (b−a) (c−a)` (`FFCT9.det3_plane_eq`), and for the
in-plane unit directions `dᵢ = cos θᵢ • u + sin θᵢ • v`,
`det3 h dᵢ dⱼ = sin (θⱼ − θᵢ) · κ`.  Hence every planar `det3` of three vertices
equals `(ρ·ρ·sin Δθ·κ)/‖h‖²`.

* `κ > 0` : `κ² = ‖h‖² > 0` (`FFCT9.det3h_sq` with the orthonormal frame), so
  `κ ≠ 0`; and a single consecutive turn `det3 (Q i)(Q (i+1))(Q (i+2)) ≥ 0`
  with `sin (θ_{i+1} − θ_i) > 0` forces `κ ≥ 0`.
* A closed sub-arc (`Q r = Q s`, so `∑_{[r,s)} ρᵢ dᵢ = 0`) has angular span
  `θ_{s-1} − θ_r ≥ π` (the covector half-plane argument, the negation of
  `FFCT94`'s half-wind positivity).
* PROPER ⟹ an external vertex exists.  If `s < N-1`, the vertex `Q_{s+1}`
  against edge `r` gives `det3 (Q r)(Q (r+1))(Q (s+1)) = κ ρ_r ρ_s
  sin(θ_s − θ_r)/‖h‖²`; strict monotonicity pushes `θ_s − θ_r > π` and one-wind
  keeps it `< 2π`, so the sine is `< 0` and the support `≥ 0` is contradicted.
  If `0 < r`, the symmetric clash at edge `s-1` against `Q_{r-1}` uses
  `θ_{s-1} − θ_{r-1} ∈ (π, 2π)`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT94

namespace ProofsInTheBook.ZinanFFCT101

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## §0. The area-form algebra for in-plane lifted directions. -/

/-- `det3 h u u = 0` (repeated argument). -/
theorem det3_self_right (a b : E3) : det3 a b b = 0 := by
  have := ProofsInTheBook.SphericalConeMembership.det3_swap_right a b b
  linarith

/-- **Bilinear area form for lifted directions.**  For the orthonormal frame
`(u, v)` perpendicular to `h`,
`det3 h (cos α • u + sin α • v) (cos β • u + sin β • v) = sin (β − α) · det3 h u v`. -/
theorem det3_h_dir_dir (h u v : E3) (α β : ℝ) :
    det3 h (Real.cos α • u + Real.sin α • v) (Real.cos β • u + Real.sin β • v)
      = Real.sin (β - α) * det3 h u v := by
  have hexpand :
      det3 h (Real.cos α • u + Real.sin α • v) (Real.cos β • u + Real.sin β • v)
        = (Real.cos α * Real.sin β - Real.sin α * Real.cos β) * det3 h u v := by
    simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hexpand, Real.sin_sub]
  ring

/-! ## §1. The planar triple reduction.

For three coplanar vertices whose two apex-differences are single scaled lifted
directions, the planar `det3` (times `‖h‖²`) is `ρ₁ ρ₂ sin(Δθ) · κ`. -/

/-- **General triple reduction.**  If `A, B, C` lie in the plane `⟪h,·⟫ = 1`,
with apex differences `B − A = a₁ • u + b₁ • v` and `C − A = a₂ • u + b₂ • v`,
then `det3 A B C · ‖h‖² = (a₁ b₂ − a₂ b₁) · det3 h u v`. -/
theorem triple_reduction_coords {h u v A B C : E3} {a₁ b₁ a₂ b₂ : ℝ}
    (hA : (⟪h, A⟫ : ℝ) = 1) (hB : (⟪h, B⟫ : ℝ) = 1) (hC : (⟪h, C⟫ : ℝ) = 1)
    (hBA : B - A = a₁ • u + b₁ • v) (hCA : C - A = a₂ • u + b₂ • v) :
    det3 A B C * ‖h‖ ^ 2 = (a₁ * b₂ - a₂ * b₁) * det3 h u v := by
  have hplane := ProofsInTheBook.ZinanFFCT9.det3_plane_eq hA hB hC
  rw [hplane, hBA, hCA]
  simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **Triple reduction (single-direction form).**  When `B − A = ρ₁ • dα` and
`C − A = ρ₂ • dβ` for lifted directions, the planar `det3` reduces to a sine. -/
theorem triple_reduction {h u v A B C : E3} {α β ρ₁ ρ₂ : ℝ}
    (hA : (⟪h, A⟫ : ℝ) = 1) (hB : (⟪h, B⟫ : ℝ) = 1) (hC : (⟪h, C⟫ : ℝ) = 1)
    (hBA : B - A = ρ₁ • (Real.cos α • u + Real.sin α • v))
    (hCA : C - A = ρ₂ • (Real.cos β • u + Real.sin β • v)) :
    det3 A B C * ‖h‖ ^ 2 = ρ₁ * ρ₂ * Real.sin (β - α) * det3 h u v := by
  have hBA' : B - A = (ρ₁ * Real.cos α) • u + (ρ₁ * Real.sin α) • v := by
    rw [hBA]; module
  have hCA' : C - A = (ρ₂ * Real.cos β) • u + (ρ₂ * Real.sin β) • v := by
    rw [hCA]; module
  rw [triple_reduction_coords hA hB hC hBA' hCA', Real.sin_sub]
  ring

/-! ## §2. `κ := det3 h u v > 0`, and the Fin/ℕ edge bridge. -/

/-- For `m + 1 < N`, the `Fin N` cyclic successor of `⟨m⟩` is the linear `⟨m+1⟩`. -/
theorem fin_edge_succ {N : ℕ} [NeZero N] {m : ℕ} (hm1 : m + 1 < N) (hm : m < N) :
    ((⟨m, hm⟩ : Fin N) + 1) = ⟨m + 1, hm1⟩ := by
  apply Fin.ext
  have := ProofsInTheBook.PlanarConvexDiag.fin_succ_val (n := N) (i := (⟨m, hm⟩ : Fin N))
    (by simpa using hm1)
  simpa using this

/-- `‖h‖ ≠ 0` from `⟪h, Q 0⟫ = 1`. -/
theorem h_ne_zero {N : ℕ} {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpan Q h u v) (i₀ : Fin N) : h ≠ 0 := by
  intro hh
  have := cert.in_plane i₀
  rw [hh] at this
  simp at this

/-- **`κ := det3 h u v` is nonzero**: `κ² = ‖h‖² > 0`. -/
theorem kappa_sq {N : ℕ} {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpan Q h u v) :
    (det3 h u v) ^ 2 = ‖h‖ ^ 2 := by
  have hsq := ProofsInTheBook.ZinanFFCT9.det3h_sq (h := h) (u := u) (v := v)
    cert.u_perp_h cert.v_perp_h
  -- ‖u‖² = 1, ‖v‖² = 1, ⟪u,v⟫ = 0
  have hu : ‖u‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]; exact cert.u_unit
  have hv : ‖v‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]; exact cert.v_unit
  rw [hsq, hu, hv, cert.uv_perp]; ring

/-- **`κ > 0`.**  The frame area form is strictly positive: nonzero (`κ² = ‖h‖²`)
and nonnegative (the first consecutive support, with positive sine). -/
theorem kappa_pos {N : ℕ} [NeZero N] {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpan Q h u v)
    (hsupp : ∀ i j : Fin N, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hN : 3 ≤ N) :
    0 < det3 h u v := by
  set κ := det3 h u v with hκ
  have hh : h ≠ 0 := h_ne_zero cert ⟨0, by omega⟩
  have hhsq : (0:ℝ) < ‖h‖ ^ 2 := by positivity
  -- κ ≠ 0
  have hκsq : κ ^ 2 = ‖h‖ ^ 2 := kappa_sq cert
  have hκne : κ ≠ 0 := by
    intro h0; rw [h0] at hκsq; simp at hκsq; nlinarith [hhsq, hκsq]
  -- the first consecutive support forces κ ≥ 0
  have h0 : (0:ℕ) < N := by omega
  have h1 : (1:ℕ) < N := by omega
  have h2 : (2:ℕ) < N := by omega
  -- edge 0 increment
  have he0 := cert.edge_eq 0 h1
  -- edge 1 increment
  have he1 := cert.edge_eq 1 h2
  -- B - A = ρ 0 • d(θ 0),  C - A : C = Q 2, A = Q 0
  -- need Q 2 - Q 0 in terms of directions? Instead use the consecutive triple (Q0,Q1,Q2):
  -- B = Q1, C = Q2: B - A = Q1 - Q0 = ρ0 d(θ0); C - A = Q2 - Q0 = (Q2-Q1)+(Q1-Q0).
  -- triple_reduction wants C - A a single direction.  Use the SHIFTED triple instead:
  -- apex A = Q1, B = Q2, C ... no.  Simplest: det3 (Q0)(Q1)(Q2). Reduce via det3_plane_eq directly.
  have hsupp012 : 0 ≤ det3 (Q ⟨0, h0⟩) (Q ⟨1, h1⟩) (Q ⟨2, h2⟩) := by
    have := hsupp ⟨0, h0⟩ ⟨2, h2⟩
    rwa [fin_edge_succ h1 h0] at this
  -- reduce det3 (Q0)(Q1)(Q2) using plane_eq + the two edge increments
  have hA := cert.in_plane ⟨0, h0⟩
  have hB := cert.in_plane ⟨1, h1⟩
  have hC := cert.in_plane ⟨2, h2⟩
  have hplane := ProofsInTheBook.ZinanFFCT9.det3_plane_eq hA hB hC
  -- Q1 - Q0 = ρ0 d(θ0)
  have hBA : Q ⟨1, h1⟩ - Q ⟨0, h0⟩
      = cert.ρ 0 • (Real.cos (cert.θ 0) • u + Real.sin (cert.θ 0) • v) := by
    have := he0
    simpa using this
  -- Q2 - Q0 = (Q2 - Q1) + (Q1 - Q0) = ρ1 d(θ1) + ρ0 d(θ0)
  have hCA : Q ⟨2, h2⟩ - Q ⟨0, h0⟩
      = cert.ρ 1 • (Real.cos (cert.θ 1) • u + Real.sin (cert.θ 1) • v)
        + cert.ρ 0 • (Real.cos (cert.θ 0) • u + Real.sin (cert.θ 0) • v) := by
    have e1 : Q ⟨2, h2⟩ - Q ⟨1, h1⟩
        = cert.ρ 1 • (Real.cos (cert.θ 1) • u + Real.sin (cert.θ 1) • v) := by
      simpa using he1
    have : Q ⟨2, h2⟩ - Q ⟨0, h0⟩
        = (Q ⟨2, h2⟩ - Q ⟨1, h1⟩) + (Q ⟨1, h1⟩ - Q ⟨0, h0⟩) := by abel
    rw [this, e1, hBA]
  -- det3 h (Q1-Q0) (Q2-Q0) = det3 h d0 (d1 + d0) (after pulling ρ) = ρ0 ρ1 det3 h d0 d1
  rw [hBA, hCA] at hplane
  -- expand: det3 h (ρ0 d0) (ρ1 d1 + ρ0 d0) = ρ0 ρ1 det3 h d0 d1 + ρ0² det3 h d0 d0
  --        = ρ0 ρ1 sin(θ1-θ0) κ   (det3 h d0 d0 = 0)
  have hd00 : det3 h (Real.cos (cert.θ 0) • u + Real.sin (cert.θ 0) • v)
      (Real.cos (cert.θ 0) • u + Real.sin (cert.θ 0) • v) = 0 := det3_self_right _ _
  have hd01 : det3 h (Real.cos (cert.θ 0) • u + Real.sin (cert.θ 0) • v)
      (Real.cos (cert.θ 1) • u + Real.sin (cert.θ 1) • v)
        = Real.sin (cert.θ 1 - cert.θ 0) * κ := det3_h_dir_dir h u v _ _
  have hexp : det3 h (cert.ρ 0 • (Real.cos (cert.θ 0) • u + Real.sin (cert.θ 0) • v))
      (cert.ρ 1 • (Real.cos (cert.θ 1) • u + Real.sin (cert.θ 1) • v)
        + cert.ρ 0 • (Real.cos (cert.θ 0) • u + Real.sin (cert.θ 0) • v))
        = cert.ρ 0 * cert.ρ 1 * Real.sin (cert.θ 1 - cert.θ 0) * κ := by
    have hlin : det3 h (cert.ρ 0 • (Real.cos (cert.θ 0) • u + Real.sin (cert.θ 0) • v))
        (cert.ρ 1 • (Real.cos (cert.θ 1) • u + Real.sin (cert.θ 1) • v)
          + cert.ρ 0 • (Real.cos (cert.θ 0) • u + Real.sin (cert.θ 0) • v))
          = cert.ρ 0 * cert.ρ 1
              * det3 h (Real.cos (cert.θ 0) • u + Real.sin (cert.θ 0) • v)
                  (Real.cos (cert.θ 1) • u + Real.sin (cert.θ 1) • v)
            + cert.ρ 0 * cert.ρ 0
              * det3 h (Real.cos (cert.θ 0) • u + Real.sin (cert.θ 0) • v)
                  (Real.cos (cert.θ 0) • u + Real.sin (cert.θ 0) • v) := by
      simp only [det3, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      ring
    rw [hlin, hd00, hd01]; ring
  rw [hexp] at hplane
  -- hplane : det3 (Q0)(Q1)(Q2) * ‖h‖² = ρ0 ρ1 sin(θ1-θ0) κ
  -- sin(θ1-θ0) > 0
  have hgap := cert.turn_pos 0
  have hgaplt := cert.turn_lt_pi 0
  have hsinpos : 0 < Real.sin (cert.θ 1 - cert.θ 0) := by
    have : cert.θ (0 + 1) - cert.θ 0 = cert.θ 1 - cert.θ 0 := by norm_num
    rw [this] at hgap hgaplt
    exact Real.sin_pos_of_pos_of_lt_pi hgap hgaplt
  have hρ0 := cert.ρ_pos 0
  have hρ1 := cert.ρ_pos 1
  -- κ ≥ 0:  det3 (Q0)(Q1)(Q2) * ‖h‖² ≥ 0 and = (pos) κ
  have hge : 0 ≤ cert.ρ 0 * cert.ρ 1 * Real.sin (cert.θ 1 - cert.θ 0) * κ := by
    rw [← hplane]; positivity
  have hκnn : 0 ≤ κ := by
    by_contra hneg
    push_neg at hneg
    have : cert.ρ 0 * cert.ρ 1 * Real.sin (cert.θ 1 - cert.θ 0) * κ < 0 := by
      have hpos : 0 < cert.ρ 0 * cert.ρ 1 * Real.sin (cert.θ 1 - cert.θ 0) := by positivity
      exact mul_neg_of_pos_of_neg hpos hneg
    linarith
  exact lt_of_le_of_ne hκnn (Ne.symm hκne)

/-! ## §3. The closed sub-arc spans at least `π`.

The negation of `FFCT94`'s half-wind covector positivity: a vanishing positive
combination of strictly-monotone lifted directions must span `≥ π`. -/

/-- **Span lemma.**  If the telescoped sum `∑_{i ∈ Ico r s} ρ i • d(θ i)` vanishes
with `r < s` and `ρ > 0`, then the angular span `θ (s-1) − θ r ≥ π`.

Contrapositive of the midpoint-covector positivity: were the span `< π`, every
`θ i − φ ∈ (−π/2, π/2)` for the midpoint covector angle `φ`, so each cosine and
hence the whole positive sum would be strictly positive, contradicting `0`. -/
theorem closed_subarc_span_ge_pi {N : ℕ} {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpan Q h u v) {r s : ℕ} (hrs : r < s)
    (hvanish : (∑ i ∈ Finset.Ico r s,
        cert.ρ i • (Real.cos (cert.θ i) • u + Real.sin (cert.θ i) • v) : E3) = 0) :
    Real.pi ≤ cert.θ (s - 1) - cert.θ r := by
  by_contra hlt
  push_neg at hlt
  -- midpoint covector angle and covector
  set φ : ℝ := (cert.θ r + cert.θ (s - 1)) / 2 with hφ
  set w : E3 := Real.cos φ • u + Real.sin φ • v with hw
  have hmono := theta_strictMono cert
  -- pairing w against the vanishing sum
  have hpair : (⟪w, (0 : E3)⟫ : ℝ)
      = ∑ i ∈ Finset.Ico r s, cert.ρ i * Real.cos (cert.θ i - φ) := by
    rw [← hvanish, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_right, ProofsInTheBook.ZinanFFCT94.covector_component cert φ i]
  rw [inner_zero_right] at hpair
  -- each summand strictly positive
  have hrs1 : r ≤ s - 1 := by omega
  have hpos_sum : 0 < ∑ i ∈ Finset.Ico r s, cert.ρ i * Real.cos (cert.θ i - φ) := by
    apply Finset.sum_pos
    · intro i hi
      rw [Finset.mem_Ico] at hi
      obtain ⟨hir, his⟩ := hi
      have hilo : cert.θ r ≤ cert.θ i := hmono.monotone hir
      have hihi : cert.θ i ≤ cert.θ (s - 1) := hmono.monotone (by omega)
      have hcos_pos : 0 < Real.cos (cert.θ i - φ) := by
        apply Real.cos_pos_of_mem_Ioo
        rw [Set.mem_Ioo]
        constructor
        · have hb : φ - cert.θ i ≤ (cert.θ (s - 1) - cert.θ r) / 2 := by rw [hφ]; linarith
          have h2 : (cert.θ (s - 1) - cert.θ r) / 2 < Real.pi / 2 := by linarith
          linarith
        · have hb : cert.θ i - φ ≤ (cert.θ (s - 1) - cert.θ r) / 2 := by rw [hφ]; linarith
          have h2 : (cert.θ (s - 1) - cert.θ r) / 2 < Real.pi / 2 := by linarith
          linarith
      have := cert.ρ_pos i
      positivity
    · rw [Finset.nonempty_Ico]; omega
  rw [← hpair] at hpos_sum
  exact (lt_irrefl (0 : ℝ)) hpos_sum

/-- `sin x < 0` for `x ∈ (π, 2π)`. -/
theorem sin_neg_of_mem_pi_two_pi {x : ℝ} (h1 : Real.pi < x) (h2 : x < 2 * Real.pi) :
    Real.sin x < 0 := by
  have hkey : Real.sin (x - Real.pi) = - Real.sin x := Real.sin_sub_pi x
  have hpos : 0 < Real.sin (x - Real.pi) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  linarith [hkey, hpos]

/-! ## §4. The headline: a proper repeat is a full closure. -/

/-- **Main theorem.**  A planar lifted-turn arm with the global cyclic edge
support `hsupp` cannot have a PROPER nonadjacent repeat: any repeat
`Q ⟨r⟩ = Q ⟨s⟩` with `r + 2 ≤ s` must be the full closure `r = 0 ∧ s = N - 1`.

The proof reduces every planar `det3` to `(ρ·ρ·sin Δθ·κ)/‖h‖²` with `κ > 0`; the
closed sub-arc forces span `≥ π`, and a proper repeat exposes an external vertex
against an interior edge whose `det3` is `κ·ρ·ρ·sin(Δθ)` with `Δθ ∈ (π, 2π)`,
hence `< 0`, contradicting `hsupp ≥ 0`. -/
theorem planar_properRepeat_is_fullClosure
    {N : ℕ} [NeZero N] {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpan Q h u v)
    (hsupp : ∀ i j : Fin N, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    {r s : ℕ} (hr : r < N) (hs : s < N) (hrs : r + 2 ≤ s)
    (hrep : Q ⟨r, hr⟩ = Q ⟨s, hs⟩) :
    r = 0 ∧ s = N - 1 := by
  have hNpos : 0 < N := by omega
  have hN3 : 3 ≤ N := by omega
  set κ := det3 h u v with hκ
  have hκpos : 0 < κ := kappa_pos cert hsupp hN3
  have hh : h ≠ 0 := h_ne_zero cert ⟨0, hNpos⟩
  have hhsq : (0:ℝ) < ‖h‖ ^ 2 := by positivity
  have hmono := theta_strictMono cert
  -- the closed sub-arc: telescoped displacement vanishes
  have hs1N : s - 1 < N := by omega
  have htele := displacement_telescope cert (r := r) (m := s) (by omega) hs hr
  have hvanish :
      (∑ i ∈ Finset.Ico r s,
        cert.ρ i • (Real.cos (cert.θ i) • u + Real.sin (cert.θ i) • v) : E3) = 0 := by
    rw [← htele, hrep]; abel
  -- span ≥ π
  have hspan : Real.pi ≤ cert.θ (s - 1) - cert.θ r :=
    closed_subarc_span_ge_pi cert (by omega) hvanish
  -- the one-wind upper bound on any θ b - θ a with a ≤ b ≤ N
  -- prove the conclusion by contradiction with properness
  by_contra hcon
  -- ¬(r = 0 ∧ s = N-1) means 0 < r ∨ s < N-1
  have hproper : 0 < r ∨ s < N - 1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨hr0, hsN⟩ := hc
    exact hcon ⟨Nat.le_zero.mp hr0, by omega⟩
  rcases hproper with hrpos | hsltN
  · -- Case 0 < r : external vertex Q (r-1), edge (s-1).
    -- det3 (Q_{s-1}) (Q_s) (Q_{r-1}) ≥ 0, but reduces to ρ ρ sin(θ_{s-1}-θ_{r-1}) κ with sin<0.
    have hr1 : r - 1 < N := by omega
    have hsm1 : s - 1 < N := hs1N
    -- hsupp at i = s-1, j = r-1; Fin successor of ⟨s-1⟩ is ⟨s⟩ (since (s-1)+1 = s < N)
    have hsupp_inst : 0 ≤ det3 (Q ⟨s - 1, hsm1⟩) (Q ⟨s, hs⟩) (Q ⟨r - 1, hr1⟩) := by
      have := hsupp ⟨s - 1, hsm1⟩ ⟨r - 1, hr1⟩
      have hsucc : ((⟨s - 1, hsm1⟩ : Fin N) + 1) = ⟨s, hs⟩ := by
        have h1 : (s - 1) + 1 < N := by omega
        have := fin_edge_succ (N := N) h1 hsm1
        rw [this]; apply Fin.ext; simp; omega
      rwa [hsucc] at this
    -- apex A = Q_{s-1}, B = Q_s, C = Q_{r-1}
    -- B - A = ρ (s-1) • d(θ (s-1))   (edge s-1, needs (s-1)+1 < N i.e. s < N ✓)
    have hedgeS := cert.edge_eq (s - 1) (by omega)
    have hBA : Q ⟨s, hs⟩ - Q ⟨s - 1, hsm1⟩
        = cert.ρ (s - 1) • (Real.cos (cert.θ (s - 1)) • u + Real.sin (cert.θ (s - 1)) • v) := by
      have hidx : (s - 1) + 1 = s := by omega
      have e := hedgeS
      -- e : Q ⟨(s-1)+1⟩ - Q ⟨s-1⟩ = ρ(s-1) • d(θ(s-1))
      rw [show (⟨(s - 1) + 1, by omega⟩ : Fin N) = (⟨s, hs⟩ : Fin N) from by
        apply Fin.ext; simp; omega] at e
      rw [show (⟨s - 1, by omega⟩ : Fin N) = (⟨s - 1, hsm1⟩ : Fin N) from rfl] at e
      convert e using 3
    -- C - A = Q_{r-1} - Q_{s-1} = -ρ(r-1) • d(θ(r-1)) + ρ(s-1) • d(θ(s-1))
    have hedgeR := cert.edge_eq (r - 1) (by omega)
    have hCA : Q ⟨r - 1, hr1⟩ - Q ⟨s - 1, hsm1⟩
        = (- cert.ρ (r - 1) * Real.cos (cert.θ (r - 1))
            + cert.ρ (s - 1) * Real.cos (cert.θ (s - 1))) • u
          + (- cert.ρ (r - 1) * Real.sin (cert.θ (r - 1))
            + cert.ρ (s - 1) * Real.sin (cert.θ (s - 1))) • v := by
      -- Q_{r-1} - Q_r = - ρ(r-1) d(θ(r-1)) ; Q_r = Q_s ; Q_s - Q_{s-1} = ρ(s-1) d(θ(s-1))
      have erm1 : Q ⟨r, hr⟩ - Q ⟨r - 1, hr1⟩
          = cert.ρ (r - 1) • (Real.cos (cert.θ (r - 1)) • u + Real.sin (cert.θ (r - 1)) • v) := by
        have e := hedgeR
        rw [show (⟨(r - 1) + 1, by omega⟩ : Fin N) = (⟨r, hr⟩ : Fin N) from by
          apply Fin.ext; simp; omega] at e
        convert e using 3
      have hQrs : Q ⟨r, hr⟩ = Q ⟨s, hs⟩ := hrep
      have hdecomp : Q ⟨r - 1, hr1⟩ - Q ⟨s - 1, hsm1⟩
          = -(Q ⟨r, hr⟩ - Q ⟨r - 1, hr1⟩) + (Q ⟨s, hs⟩ - Q ⟨s - 1, hsm1⟩) := by
        rw [hQrs]; abel
      rw [hdecomp, erm1, hBA]
      module
    have hA := cert.in_plane ⟨s - 1, hsm1⟩
    have hB := cert.in_plane ⟨s, hs⟩
    have hC := cert.in_plane ⟨r - 1, hr1⟩
    -- convert hBA to coords form
    have hBA' : Q ⟨s, hs⟩ - Q ⟨s - 1, hsm1⟩
        = (cert.ρ (s - 1) * Real.cos (cert.θ (s - 1))) • u
          + (cert.ρ (s - 1) * Real.sin (cert.θ (s - 1))) • v := by
      rw [hBA]; module
    have hred := triple_reduction_coords (h := h) (u := u) (v := v) hA hB hC hBA' hCA
    -- the coefficient (a₁ b₂ - a₂ b₁) = ρ(s-1) ρ(r-1) sin(θ(s-1) - θ(r-1))
    set a₁ := cert.ρ (s - 1) * Real.cos (cert.θ (s - 1)) with ha1
    set b₁ := cert.ρ (s - 1) * Real.sin (cert.θ (s - 1)) with hb1
    set a₂ := - cert.ρ (r - 1) * Real.cos (cert.θ (r - 1))
            + cert.ρ (s - 1) * Real.cos (cert.θ (s - 1)) with ha2
    set b₂ := - cert.ρ (r - 1) * Real.sin (cert.θ (r - 1))
            + cert.ρ (s - 1) * Real.sin (cert.θ (s - 1)) with hb2
    have hcoeff : a₁ * b₂ - a₂ * b₁
        = cert.ρ (s - 1) * cert.ρ (r - 1) * Real.sin (cert.θ (s - 1) - cert.θ (r - 1)) := by
      rw [ha1, hb1, ha2, hb2, Real.sin_sub]; ring
    rw [hcoeff] at hred
    -- the angular span θ(s-1) - θ(r-1) ∈ (π, 2π)
    have hspanLo : Real.pi < cert.θ (s - 1) - cert.θ (r - 1) := by
      have hstep : cert.θ (r - 1) < cert.θ r := by
        have := hmono (show r - 1 < r by omega); exact this
      linarith [hspan]
    have hspanHi : cert.θ (s - 1) - cert.θ (r - 1) < 2 * Real.pi := by
      have hle := theta_sub_le_total cert (a := r - 1) (b := s - 1) (by omega) (by omega)
      have := cert.one_wind
      linarith
    -- sin < 0 on (π, 2π)
    have hsinneg : Real.sin (cert.θ (s - 1) - cert.θ (r - 1)) < 0 :=
      sin_neg_of_mem_pi_two_pi hspanLo hspanHi
    -- contradiction:  det3 ≥ 0 but det3 * ‖h‖² = (neg) ρ ρ κ < 0
    have hprod_neg : det3 (Q ⟨s - 1, hsm1⟩) (Q ⟨s, hs⟩) (Q ⟨r - 1, hr1⟩) * ‖h‖ ^ 2 < 0 := by
      rw [hred]
      have hρa := cert.ρ_pos (s - 1)
      have hρb := cert.ρ_pos (r - 1)
      have : 0 < cert.ρ (s - 1) * cert.ρ (r - 1) := by positivity
      have hneg : cert.ρ (s - 1) * cert.ρ (r - 1)
          * Real.sin (cert.θ (s - 1) - cert.θ (r - 1)) < 0 :=
        mul_neg_of_pos_of_neg this hsinneg
      nlinarith [hneg, hκpos]
    nlinarith [hsupp_inst, hprod_neg, hhsq]
  · -- Case s < N - 1 : external vertex Q (s+1), edge r.
    have hrr1 : r + 1 < N := by omega
    have hs1 : s + 1 < N := by omega
    -- hsupp at i = r, j = s+1; Fin successor of ⟨r⟩ is ⟨r+1⟩
    have hsupp_inst : 0 ≤ det3 (Q ⟨r, hr⟩) (Q ⟨r + 1, hrr1⟩) (Q ⟨s + 1, hs1⟩) := by
      have := hsupp ⟨r, hr⟩ ⟨s + 1, hs1⟩
      rwa [fin_edge_succ hrr1 hr] at this
    -- B - A = ρ r • d(θ r)  (edge r)
    have hedgeR := cert.edge_eq r hrr1
    have hBA : Q ⟨r + 1, hrr1⟩ - Q ⟨r, hr⟩
        = cert.ρ r • (Real.cos (cert.θ r) • u + Real.sin (cert.θ r) • v) := by
      simpa using hedgeR
    -- C - A = Q_{s+1} - Q_r = Q_{s+1} - Q_s = ρ s • d(θ s)  (edge s, Q_r = Q_s)
    have hedgeS := cert.edge_eq s hs1
    have hCA : Q ⟨s + 1, hs1⟩ - Q ⟨r, hr⟩
        = cert.ρ s • (Real.cos (cert.θ s) • u + Real.sin (cert.θ s) • v) := by
      have e : Q ⟨s + 1, hs1⟩ - Q ⟨s, hs⟩
          = cert.ρ s • (Real.cos (cert.θ s) • u + Real.sin (cert.θ s) • v) := by
        simpa using hedgeS
      rw [show Q ⟨r, hr⟩ = Q ⟨s, hs⟩ from hrep, e]
    have hA := cert.in_plane ⟨r, hr⟩
    have hB := cert.in_plane ⟨r + 1, hrr1⟩
    have hC := cert.in_plane ⟨s + 1, hs1⟩
    have hred := triple_reduction (h := h) (u := u) (v := v) hA hB hC hBA hCA
    -- θ s - θ r ∈ (π, 2π)
    have hspanLo : Real.pi < cert.θ s - cert.θ r := by
      have hstep : cert.θ (s - 1) < cert.θ s := by
        have := hmono (show s - 1 < s by omega); exact this
      linarith [hspan]
    have hspanHi : cert.θ s - cert.θ r < 2 * Real.pi := by
      have hle := theta_sub_le_total cert (a := r) (b := s) (by omega) (by omega)
      have := cert.one_wind
      linarith
    have hsinneg : Real.sin (cert.θ s - cert.θ r) < 0 :=
      sin_neg_of_mem_pi_two_pi hspanLo hspanHi
    have hprod_neg : det3 (Q ⟨r, hr⟩) (Q ⟨r + 1, hrr1⟩) (Q ⟨s + 1, hs1⟩) * ‖h‖ ^ 2 < 0 := by
      rw [hred]
      have hρa := cert.ρ_pos r
      have hρb := cert.ρ_pos s
      have hpp : 0 < cert.ρ r * cert.ρ s := by positivity
      have hneg : cert.ρ r * cert.ρ s * Real.sin (cert.θ s - cert.θ r) < 0 :=
        mul_neg_of_pos_of_neg hpp hsinneg
      nlinarith [hneg, hκpos]
    nlinarith [hsupp_inst, hprod_neg, hhsq]

/-- **Contrapositive form.**  A PROPER nonadjacent repeat is impossible. -/
theorem no_proper_repeat
    {N : ℕ} [NeZero N] {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpan Q h u v)
    (hsupp : ∀ i j : Fin N, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    {r s : ℕ} (hr : r < N) (hs : s < N) (hrs : r + 2 ≤ s)
    (hproper : 0 < r ∨ s < N - 1)
    (hrep : Q ⟨r, hr⟩ = Q ⟨s, hs⟩) : False := by
  obtain ⟨hr0, hsN⟩ := planar_properRepeat_is_fullClosure cert hsupp hr hs hrs hrep
  rcases hproper with h1 | h2
  · omega
  · omega

#print axioms planar_properRepeat_is_fullClosure
#print axioms no_proper_repeat

end ProofsInTheBook.ZinanFFCT101
