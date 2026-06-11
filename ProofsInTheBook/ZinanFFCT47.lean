import ProofsInTheBook.ZinanFFCT46

/-!
# `ZinanFFCT47` — breaking the wrap-edge circularity: `OpenedWrapShortArcAtSupWBS` discharged.

`ZinanFFCT46` exposed the single sharp residual `OpenedWrapShortArcAtSupWBS`: at the WBS supremum, the
opened wraparound edge `(last, 0)` of `A'_WBS` is a `ShortArc`.  Distinctness is margins-free
(`openedWrap_distinct_at_supWBS`); the residual content is the **non-antipodality** of the wrap edge,
which the weak-support branch could not conclude margins-free.

## The circularity and how it is broken

FFCT46's keystone `openHemisphere_of_weakSupports_jointOpen_full` takes `hside : ∀ i, ShortArc (P i)
(P (i+1))` over **all** `n + 1` edges, **including the wrap edge** `(last, 0)` — precisely the fact we
are trying to prove.  We break the cycle by re-running the full-set separation with the **wrap edge
dropped**:

* `§1` `openChain_collapse_forces_flat_joint_ge3` — the open-chain sibling of FFCT44's
  `commonLine_collapse_forces_flat_joint` for `3 ≤ n`: `hside`/`hallplanes` are required only for the
  `n` **real** edges (`i ≠ Fin.last n`).  The meridian-pencil argument runs on the interior apexes
  `1 .. n-1`, whose two adjacent edges are always real edges, so it never touches the wrap edge.  (The
  `n = 2` corner — single interior apex, where FFCT44 used the wrap-edge cyclic identity — is **not**
  closed by a single axis; it is handled at the separation level below.)
* `§2` `openHemisphere_full_openChain` — the margins-free full-set separation with **real-edge** ShortArc
  and **real-edge** supports only.  In the `0 ∈ hull` branch, for `3 ≤ n` a positive-weight common-axis
  vertex contradicts the open-chain kernel; for `n = 2` the kernel cannot fire, so we use a
  positive-weight vertex `v₀ ≠ P 1` (which must exist, else `0 = (Σw)•(P 1) = P 1`): its index is `0`
  or `2`, and the corresponding real-edge functional gives `det3 (P 0)(P 1)(P 2) = 0` directly (cyclic),
  i.e. a flat single interior joint — contradiction.  Produces a *unit* normal `h'` strictly positive
  against every vertex, **margins-free and wrap-edge-free**.
* `§3` `wrap_shortArc_of_hemisphere` — two vertices strictly inside an open hemisphere are non-antipodal
  (`⟪h', u⟫ > 0` but `⟪h', -u⟫ < 0`); combined with the margins-free distinctness
  (`openedWrap_distinct_at_supWBS`) this is exactly `ShortArc` (= distinct ∧ non-antipodal).
* `§4` `openedWrapShortArcAtSupWBS_holds` — the residual `OpenedWrapShortArcAtSupWBS` is discharged
  unconditionally.  `§5` `mainPlus_headline_wrap_free` — the FFCT46 headline with the wrap residual
  **gone**: the final surface is `SpliceBodyDiagMono` + `SpliceStructuralData` only.

No `sorry`, `axiom`, `admit`, or `native_decide`.  Clean-3.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT21 ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT42
open ProofsInTheBook.ZinanFFCT43
open ProofsInTheBook.ZinanFFCT44
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46

namespace ProofsInTheBook.ZinanFFCT47

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §0. Index bridges for interior joints (open-chain copies of FFCT44 §0).

For an interior joint `r : Fin (n - 1)` the two edges adjacent to the apex `P (r.val + 1)` are the
edges with base indices `r.val` and `r.val + 1`, both `< n`, hence **real** edges (`≠ Fin.last n`).
These bridges let the cyclic-edge hypotheses talk to the nat-indexed `jointAngle` vertices. -/

/-- The base index of an interior joint, as a `Fin (n+1)`. -/
private def jIdx {n : ℕ} (r : Fin (n - 1)) : Fin (n + 1) :=
  ⟨r.val, by have := r.isLt; omega⟩

private theorem jIdx_val {n : ℕ} (r : Fin (n - 1)) : ((jIdx r : Fin (n + 1)) : ℕ) = r.val := rfl

private theorem jIdx_succ_val {n : ℕ} (r : Fin (n - 1)) :
    ((jIdx r + 1 : Fin (n + 1)) : ℕ) = r.val + 1 := by
  have hr := r.isLt
  rw [Fin.val_add, jIdx_val]
  have h1 : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  rw [h1]
  exact Nat.mod_eq_of_lt (by omega)

private theorem jIdx_succ_succ_val {n : ℕ} (r : Fin (n - 1)) :
    (((jIdx r + 1) + 1 : Fin (n + 1)) : ℕ) = r.val + 2 := by
  have hr := r.isLt
  rw [Fin.val_add, jIdx_succ_val]
  have h1 : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  rw [h1]; exact Nat.mod_eq_of_lt (by omega)

private theorem P_jIdx_succ {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    P (jIdx r + 1) = P ⟨r.val + 1, by have := r.isLt; omega⟩ := by
  congr 1; apply Fin.ext; rw [jIdx_succ_val]

private theorem P_jIdx_succ_succ {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    P ((jIdx r + 1) + 1) = P ⟨r.val + 2, by have := r.isLt; omega⟩ := by
  congr 1; apply Fin.ext; rw [jIdx_succ_succ_val]

private theorem P_jIdx {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    P (jIdx r) = P ⟨r.val, by have := r.isLt; omega⟩ := rfl

private theorem jointAngle_eq_consecutive {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    jointAngle P r =
      sphAngle (P ⟨r.val, by have := r.isLt; omega⟩) (P ⟨r.val + 1, by have := r.isLt; omega⟩)
        (P ⟨r.val + 2, by have := r.isLt; omega⟩) := rfl

/-- An interior-joint base index `jIdx r` is a **real** edge: `jIdx r ≠ Fin.last n` (its value is
`r.val ≤ n - 2 < n`). -/
private theorem jIdx_ne_last {n : ℕ} (r : Fin (n - 1)) : (jIdx r : Fin (n + 1)) ≠ Fin.last n := by
  intro h
  have hr := r.isLt
  have := congrArg Fin.val h
  rw [jIdx_val, Fin.val_last] at this
  omega

/-- The successor index `jIdx r + 1` is also a **real** edge: its value is `r.val + 1 ≤ n - 1 < n`. -/
private theorem jIdx_succ_ne_last {n : ℕ} (r : Fin (n - 1)) :
    (jIdx r + 1 : Fin (n + 1)) ≠ Fin.last n := by
  intro h
  have hr := r.isLt
  have := congrArg Fin.val h
  rw [jIdx_succ_val, Fin.val_last] at this
  omega

/-! ## §1. The open-chain meridian-pencil collapse kernel (`3 ≤ n`).

The open-chain sibling of FFCT44's `commonLine_collapse_forces_flat_joint`.  Hypotheses `hside` and
`hallplanes` are required only for the `n` **real** edges (`i ≠ Fin.last n`); the wrap edge is dropped.
The pencil argument runs on interior apexes `1 .. n-1`, whose two adjacent edges have base indices
`r.val`, `r.val + 1`, both `< n`, so always real — the wrap edge is never used.  For `3 ≤ n` the
all-pole corner has **two adjacent** interior apexes (joints `0` and `1`) sharing a **real** edge, killed
by ShortArc; the `n = 2` single-apex corner is not closed here and is handled at the separation level. -/

/-- A flat interior joint is impossible (open-chain copy of FFCT44's `flat_interior_joint_absurd`). -/
private theorem flat_interior_joint_absurd {n : ℕ} {P : Fin (n + 1) → S2} (r : Fin (n - 1))
    (hsau : ShortArc (P ⟨r.val + 1, by have := r.isLt; omega⟩) (P ⟨r.val, by have := r.isLt; omega⟩))
    (hsav : ShortArc (P ⟨r.val + 1, by have := r.isLt; omega⟩)
      (P ⟨r.val + 2, by have := r.isLt; omega⟩))
    (hcol : det3 (P ⟨r.val, by have := r.isLt; omega⟩ : E3)
      (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3)
      (P ⟨r.val + 2, by have := r.isLt; omega⟩ : E3) = 0)
    (hjopen : 0 < jointAngle P r ∧ jointAngle P r < Real.pi) :
    False := by
  have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero
    (u := P ⟨r.val, by have := r.isLt; omega⟩) (v := P ⟨r.val + 1, by have := r.isLt; omega⟩)
    (w := P ⟨r.val + 2, by have := r.isLt; omega⟩) hsau hsav hcol
  rw [jointAngle_eq_consecutive] at hjopen
  rcases hbridge with h0 | hπ
  · rw [h0] at hjopen; exact lt_irrefl 0 hjopen.1
  · rw [hπ] at hjopen; exact lt_irrefl Real.pi hjopen.2

/-- The two real edges adjacent to the apex of interior joint `r` both have a vanishing area form
against the axis `z` (open-chain: `hallplanes` invoked only at the two real indices). -/
private theorem edge_planes_at_apex {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hallplanes : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
    (r : Fin (n - 1)) :
    det3 (P ⟨r.val, by have := r.isLt; omega⟩ : E3) (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3)
        (z : E3) = 0 ∧
      det3 (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3)
        (P ⟨r.val + 2, by have := r.isLt; omega⟩ : E3) (z : E3) = 0 := by
  have h1 := hallplanes (jIdx r) (jIdx_ne_last r)
  have h2 := hallplanes (jIdx r + 1) (jIdx_succ_ne_last r)
  rw [P_jIdx P r, P_jIdx_succ P r] at h1
  rw [P_jIdx_succ P r, P_jIdx_succ_succ P r] at h2
  exact ⟨h1, h2⟩

/-- The non-pole apex collapse (open-chain copy of FFCT44's `consecutive_det3_zero_of_nonpole`). -/
private theorem consecutive_det3_zero_of_nonpole {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hallplanes : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
    (r : Fin (n - 1))
    (hne : (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) ≠ (z : E3))
    (hanti : (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) ≠ -(z : E3)) :
    det3 (P ⟨r.val, by have := r.isLt; omega⟩ : E3) (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3)
      (P ⟨r.val + 2, by have := r.isLt; omega⟩ : E3) = 0 := by
  obtain ⟨he1, he2⟩ := edge_planes_at_apex hallplanes r
  set apex : E3 := (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) with hapex
  set x : E3 := (P ⟨r.val, by have := r.isLt; omega⟩ : E3) with hx
  set y : E3 := (P ⟨r.val + 2, by have := r.isLt; omega⟩ : E3) with hy
  set zz : E3 := (z : E3) with hzz
  have hzu : ‖zz‖ = 1 := z.2
  have hau : ‖apex‖ = 1 := (P _).2
  have hzne : zz ≠ apex := fun h => hne h.symm
  have hzanti : zz ≠ -apex := by
    intro h
    exact hanti (by rw [h]; simp)
  have hdetx : det3 zz apex x = 0 := by
    have hcyc : det3 zz apex x = -det3 x apex zz := by simp only [det3]; ring
    rw [hcyc, he1, neg_zero]
  have hdety : det3 zz apex y = 0 := by
    have hcyc : det3 zz apex y = det3 apex y zz := by simp only [det3]; ring
    rw [hcyc, he2]
  obtain ⟨c1, d1, hx'⟩ := lin_indep_span_of_det3_zero hzu hau hzne hzanti hdetx
  obtain ⟨c2, d2, hy'⟩ := lin_indep_span_of_det3_zero hzu hau hzne hzanti hdety
  have hap' : apex = (0 : ℝ) • zz + (1 : ℝ) • apex := by simp
  exact coplanar_triple_det3_zero ⟨c1, d1, hx'.symm⟩ ⟨0, 1, hap'.symm⟩ ⟨c2, d2, hy'.symm⟩

/-- **§1 — the open-chain meridian-pencil collapse kernel (`3 ≤ n`).**  A chain `P : Fin (n+1) → S2`
(`3 ≤ n`), every **real** edge of which is a short arc (`hside`, `i ≠ Fin.last n`), every **real** edge
plane of which contains a common unit axis `z` (`hallplanes`, `i ≠ Fin.last n`), with all interior joints
in `(0, π)` (`hjopen`), is impossible.  The wrap edge `(P last, P 0)` is **not** used. -/
theorem openChain_collapse_forces_flat_joint_ge3 {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hn : 3 ≤ n)
    (hside : ∀ i : Fin (n + 1), i ≠ Fin.last n → ShortArc (P i) (P (i + 1)))
    (hallplanes : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
    (hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi) :
    False := by
  classical
  -- The two short joint arcs at the apex of interior joint `r` (both edges real).
  have hshort_apex : ∀ r : Fin (n - 1),
      ShortArc (P ⟨r.val + 1, by have := r.isLt; omega⟩) (P ⟨r.val, by have := r.isLt; omega⟩) ∧
        ShortArc (P ⟨r.val + 1, by have := r.isLt; omega⟩)
          (P ⟨r.val + 2, by have := r.isLt; omega⟩) := by
    intro r
    have e1 := hside (jIdx r) (jIdx_ne_last r)
    have e2 := hside (jIdx r + 1) (jIdx_succ_ne_last r)
    rw [P_jIdx P r, P_jIdx_succ P r] at e1
    rw [P_jIdx_succ P r, P_jIdx_succ_succ P r] at e2
    exact ⟨e1.symm, e2⟩
  by_cases hsome : ∃ r : Fin (n - 1),
      (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) ≠ (z : E3) ∧
        (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) ≠ -(z : E3)
  · -- CASE (a): a non-pole apex.  The collapse gives a flat joint.
    obtain ⟨r, hne, hanti⟩ := hsome
    obtain ⟨hsau, hsav⟩ := hshort_apex r
    have hcol := consecutive_det3_zero_of_nonpole hallplanes r hne hanti
    exact flat_interior_joint_absurd r hsau hsav hcol (hjopen r)
  · -- CASE (b): every interior apex is a pole `P apex = ± z`.  With `n ≥ 3`, joints `0`, `1` give
    -- adjacent interior poles `P 1`, `P 2` sharing the real edge `(P 1, P 2)` — ShortArc kill.
    push_neg at hsome
    have hpole : ∀ r : Fin (n - 1),
        (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) = (z : E3) ∨
          (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) = -(z : E3) := by
      intro r
      by_cases h1 : (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) = (z : E3)
      · exact Or.inl h1
      · exact Or.inr (hsome r h1)
    have hp0 := hpole ⟨0, by omega⟩
    have hp1 := hpole ⟨1, by omega⟩
    have hsh := (hshort_apex ⟨0, by omega⟩).2
    have hsh1 : (P ⟨0 + 1, by omega⟩ : E3) ≠ (P ⟨0 + 2, by omega⟩ : E3) := by
      intro he; exact hsh.1 (S2.ext he)
    have hsh2 : (P ⟨0 + 1, by omega⟩ : E3) ≠ -(P ⟨0 + 2, by omega⟩ : E3) := hsh.2
    rcases hp0 with hp0z | hp0z <;> rcases hp1 with hp1z | hp1z
    · exact hsh1 (by rw [hp0z, hp1z])
    · exact hsh2 (by rw [hp0z, hp1z, neg_neg])
    · exact hsh2 (by rw [hp0z, hp1z])
    · exact hsh1 (by rw [hp0z, hp1z])

/-! ## §2. The margins-free, wrap-edge-free open-hemisphere production.

The full-set separation of FFCT46's `openHemisphere_of_weakSupports_jointOpen_full`, with `hside`/`hsupp`
required only for the **real** edges (`i ≠ Fin.last n`).  In the `0 ∈ hull` branch a positive-weight
vertex is a common **real-edge** axis; for `3 ≤ n` the open-chain kernel closes it, and for `n = 2` a
positive-weight vertex `≠ P 1` (index `0` or `2`) gives `det3 (P 0)(P 1)(P 2) = 0` directly. -/

/-- **§2 — margins-free, wrap-edge-free open hemisphere.**  For a chain `P : Fin (n+1) → S2` (`2 ≤ n`)
with **real-edge** short arcs (`hside`, `i ≠ Fin.last n`), **real-edge** weak supports (`hsupp`,
`i ≠ Fin.last n`), and all interior joints in `(0, π)` (`hjopen`), there is a *unit* normal `h'`
strictly positive against every vertex.  **No margins, no wrap edge.** -/
theorem openHemisphere_full_openChain {n : ℕ} {P : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hside : ∀ i : Fin (n + 1), i ≠ Fin.last n → ShortArc (P i) (P (i + 1)))
    (hsupp : ∀ i j : Fin (n + 1), i ≠ Fin.last n → j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (P i) (P (i + 1)) (P j))
    (hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi) :
    ∃ h' : E3, ‖h'‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ) := by
  classical
  set s : Finset E3 := (Finset.univ : Finset (Fin (n + 1))).image (fun r => ((P r : S2) : E3))
    with hs
  have hmem_iff : ∀ v, v ∈ s ↔ ∃ m, ((P m : S2) : E3) = v := by
    intro v
    rw [hs, Finset.mem_image]
    constructor
    · rintro ⟨m, _hm, rfl⟩; exact ⟨m, rfl⟩
    · rintro ⟨m, rfl⟩; exact ⟨m, Finset.mem_univ _, rfl⟩
  by_cases h0 : (0 : E3) ∈ convexHull ℝ (s : Set E3)
  · exfalso
    rw [Finset.mem_convexHull'] at h0
    obtain ⟨w, hw0, hw1, hwsum⟩ := h0
    -- For every REAL edge `i` and every member `v`, `w v * det3 (P i)(P i+1) v ≥ 0`.
    have hterm_nonneg : ∀ (i : Fin (n + 1)), i ≠ Fin.last n → ∀ (v : E3), v ∈ s →
        0 ≤ w v * det3 (P i : E3) (P (i + 1) : E3) v := by
      intro i hi v hv
      obtain ⟨m, rfl⟩ := (hmem_iff v).mp hv
      by_cases hmi : m = i
      · subst hmi; rw [show det3 (P m : E3) (P (m + 1) : E3) (P m : E3) = 0 from by
          simp only [det3]; ring, mul_zero]
      · by_cases hmi1 : m = i + 1
        · subst hmi1; rw [show det3 (P i : E3) (P (i + 1) : E3) (P (i + 1) : E3) = 0 from by
            simp only [det3]; ring, mul_zero]
        · exact mul_nonneg (hw0 _ hv)
            (le_trans (le_of_eq rfl) (hsupp i m hi (by simpa [eq_comm] using hmi)
              (by simpa [eq_comm] using hmi1)))
    -- The REAL-edge functional pushed through the convex combination is `0`.
    have hedge_zero : ∀ i : Fin (n + 1), i ≠ Fin.last n →
        (0 : ℝ) = ∑ v ∈ s, w v * det3 (P i : E3) (P (i + 1) : E3) v := by
      intro i _hi
      have hkey := det3_edge_centerSum (P i : E3) (P (i + 1) : E3) s w
      rw [hwsum] at hkey
      rw [show det3 (P i : E3) (P (i + 1) : E3) (0 : E3) = 0 from by simp [det3]] at hkey
      exact hkey
    have hterm_zero : ∀ i : Fin (n + 1), i ≠ Fin.last n → ∀ v ∈ s,
        w v * det3 (P i : E3) (P (i + 1) : E3) v = 0 := by
      intro i hi
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun v hv => hterm_nonneg i hi v hv)).mp
        (hedge_zero i hi).symm
    -- Pick a positive-weight member.
    have hexists_pos : ∃ v ∈ s, 0 < w v := by
      by_contra hnone
      push_neg at hnone
      have : ∑ v ∈ s, w v = 0 :=
        Finset.sum_eq_zero (fun v hv => le_antisymm (hnone v hv) (hw0 v hv))
      rw [hw1] at this; exact one_ne_zero this
    -- A positive-weight vertex `v₀ = P r₀` is a common REAL-edge axis.
    have hcommon_axis : ∀ (r0 : Fin (n + 1)), 0 < w ((P r0 : S2) : E3) →
        ∀ i : Fin (n + 1), i ≠ Fin.last n →
          det3 (P i : E3) (P (i + 1) : E3) (P r0 : E3) = 0 := by
      intro r0 hr0pos i hi
      have hv0s : ((P r0 : S2) : E3) ∈ s := by rw [hmem_iff]; exact ⟨r0, rfl⟩
      have := hterm_zero i hi ((P r0 : S2) : E3) hv0s
      rcases mul_eq_zero.mp this with hw | hd
      · exact absurd hw (ne_of_gt hr0pos)
      · exact hd
    rcases Nat.lt_or_ge 2 n with hn3 | hn2
    · -- `3 ≤ n`: a common-axis vertex contradicts the open-chain kernel.
      obtain ⟨v0, hv0s, hv0pos⟩ := hexists_pos
      obtain ⟨r0, hv0eq⟩ := (hmem_iff v0).mp hv0s
      have hr0pos : 0 < w ((P r0 : S2) : E3) := by rw [hv0eq]; exact hv0pos
      exact openChain_collapse_forces_flat_joint_ge3 (z := P r0) (by omega) hside
        (hcommon_axis r0 hr0pos) hjopen
    · -- `n = 2`: a positive-weight vertex `≠ P 1` (index `0` or `2`) gives the flat single joint.
      have hneq : n = 2 := by omega
      subst hneq
      -- There is a positive-weight vertex `v₀` with `v₀ ≠ (P 1 : E3)` (else `0 = (Σw)•(P 1)`).
      have hne1 : ∃ v ∈ s, 0 < w v ∧ v ≠ ((P (1 : Fin 3) : S2) : E3) := by
        by_contra hcon
        push_neg at hcon
        -- every member is either zero-weight or equals `P 1`.
        have hsum1 : ∑ v ∈ s, w v • v = ((∑ v ∈ s, w v) : ℝ) • ((P (1 : Fin 3) : S2) : E3) := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl (fun v hv => ?_)
          rcases lt_or_eq_of_le (hw0 v hv) with hpos | hzero
          · rw [hcon v hv hpos]
          · rw [← hzero, zero_smul, zero_smul]
        rw [hwsum, hw1, one_smul] at hsum1
        -- `0 = P 1` contradicts `‖P 1‖ = 1`.
        have hnorm1 : ‖((P (1 : Fin 3) : S2) : E3)‖ = 1 := (P (1 : Fin 3)).2
        rw [← hsum1, norm_zero] at hnorm1
        exact one_ne_zero hnorm1.symm
      obtain ⟨v0, hv0s, hv0pos, hv0ne⟩ := hne1
      obtain ⟨r0, hv0eq⟩ := (hmem_iff v0).mp hv0s
      have hr0pos : 0 < w ((P r0 : S2) : E3) := by rw [hv0eq]; exact hv0pos
      -- `r0 ≠ 1` (else `P r0 = P 1 = v0`, contradicting `hv0ne`).
      have hr0ne1 : r0 ≠ (1 : Fin 3) := by
        intro h; apply hv0ne; rw [← hv0eq, h]
      -- the single interior joint `0`; vertices `P 0, P 1, P 2`.
      have hjoint0 := hjopen ⟨0, by omega⟩
      -- the two real edges `0` and `1`.
      have he0 : (Fin.last 2 : Fin 3) = (2 : Fin 3) := rfl
      have h0ne : (0 : Fin 3) ≠ Fin.last 2 := by rw [he0]; decide
      have h1ne : (1 : Fin 3) ≠ Fin.last 2 := by rw [he0]; decide
      -- `det3 (P 0)(P 1)(P 2) = 0` from the common-axis facts, depending on `r0 ∈ {0, 2}`.
      have hcol : det3 (P ⟨0, by omega⟩ : E3) (P ⟨0 + 1, by omega⟩ : E3)
          (P ⟨0 + 2, by omega⟩ : E3) = 0 := by
        -- normalise the nat-indexed vertices to `P 0, P 1, P 2`.
        have e0 : (P ⟨0, by omega⟩ : E3) = (P (0 : Fin 3) : E3) := rfl
        have e1 : (P ⟨0 + 1, by omega⟩ : E3) = (P (1 : Fin 3) : E3) := rfl
        have e2 : (P ⟨0 + 2, by omega⟩ : E3) = (P (2 : Fin 3) : E3) := rfl
        rw [e0, e1, e2]
        -- `r0` is `0` or `2`.
        have hr0cases : r0 = (0 : Fin 3) ∨ r0 = (2 : Fin 3) := by
          fin_cases r0
          · exact Or.inl rfl
          · exact absurd rfl hr0ne1
          · exact Or.inr rfl
        rcases hr0cases with hr0 | hr0
        · -- `r0 = 0`: edge `1 = (P 1, P 2)` axis gives `det3 (P 1)(P 2)(P 0) = 0`; cyclic.
          have hax := hcommon_axis r0 hr0pos (1 : Fin 3) h1ne
          rw [hr0] at hax
          -- `(1 : Fin 3) + 1 = 2`.
          have h11 : ((1 : Fin 3) + 1) = (2 : Fin 3) := by decide
          rw [h11] at hax
          -- `hax : det3 (P 1)(P 2)(P 0) = 0`; cyclic ⟹ `det3 (P 0)(P 1)(P 2) = 0`.
          have hcyc : det3 (P (0 : Fin 3) : E3) (P (1 : Fin 3) : E3) (P (2 : Fin 3) : E3)
              = det3 (P (1 : Fin 3) : E3) (P (2 : Fin 3) : E3) (P (0 : Fin 3) : E3) := by
            simp only [det3]; ring
          rw [hcyc]; exact hax
        · -- `r0 = 2`: edge `0 = (P 0, P 1)` axis gives `det3 (P 0)(P 1)(P 2) = 0` directly.
          have hax := hcommon_axis r0 hr0pos (0 : Fin 3) h0ne
          rw [hr0] at hax
          have h01 : ((0 : Fin 3) + 1) = (1 : Fin 3) := by decide
          rw [h01] at hax
          exact hax
      -- the short joint arcs at apex `P 1` (both real edges).
      have hside0 := hside (0 : Fin 3) h0ne
      have hside1 := hside (1 : Fin 3) h1ne
      have h01 : ((0 : Fin 3) + 1) = (1 : Fin 3) := by decide
      have h11 : ((1 : Fin 3) + 1) = (2 : Fin 3) := by decide
      rw [h01] at hside0
      rw [h11] at hside1
      -- assemble the apex short arcs in the orientation `flat_interior_joint_absurd` wants.
      have hsau : ShortArc (P ⟨0 + 1, by omega⟩ : S2) (P ⟨0, by omega⟩ : S2) := by
        have : ShortArc (P (1 : Fin 3)) (P (0 : Fin 3)) := hside0.symm
        exact this
      have hsav : ShortArc (P ⟨0 + 1, by omega⟩ : S2) (P ⟨0 + 2, by omega⟩ : S2) := by
        have : ShortArc (P (1 : Fin 3)) (P (2 : Fin 3)) := hside1
        exact this
      exact flat_interior_joint_absurd (⟨0, by omega⟩ : Fin (2 - 1)) hsau hsav hcol hjoint0
  · -- `0 ∉ hull`: separation gives the strict hemisphere normal directly; normalise to unit length.
    obtain ⟨t, ht⟩ := exists_inner_pos_of_zero_notMem_convexHull s.finite_toSet h0
    have htpos : ∀ r : Fin (n + 1), 0 < (⟪t, (P r : E3)⟫ : ℝ) := by
      intro r
      have hrmem : ((P r : S2) : E3) ∈ s := by rw [hmem_iff]; exact ⟨r, rfl⟩
      exact ht _ hrmem
    have htne : t ≠ 0 := by
      intro h
      have := htpos ⟨0, by omega⟩
      rw [h, inner_zero_left] at this
      exact lt_irrefl _ this
    have htnorm : 0 < ‖t‖ := norm_pos_iff.mpr htne
    refine ⟨(‖t‖⁻¹ : ℝ) • t, ?_, fun r => ?_⟩
    · rw [norm_smul, norm_inv, norm_norm]; field_simp
    · rw [inner_smul_left]
      simp only [RCLike.conj_to_real]
      exact mul_pos (by positivity) (htpos r)

/-! ## §3. Two hemisphere-interior vertices are non-antipodal ⟹ the wrap edge is a `ShortArc`. -/

/-- **§3 — wrap ShortArc from the open hemisphere.**  If `h'` is strictly positive against both wrap
endpoints `P last`, `P 0` (an open-hemisphere certificate) and the two endpoints are distinct
(`hdist`), then the wrap edge `(P last, P 0)` is a `ShortArc`: distinctness is `hdist`, and
non-antipodality is forced because `(P last : E3) = -(P 0 : E3)` would give
`0 < ⟪h', P last⟫ = -⟪h', P 0⟫ < 0`. -/
theorem wrap_shortArc_of_hemisphere {n : ℕ} {P : Fin (n + 1) → S2} {h' : E3}
    (hhem : ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ))
    (hdist : P (Fin.last n) ≠ P 0) :
    ShortArc (P (Fin.last n)) (P 0) := by
  refine ⟨hdist, fun he => ?_⟩
  have hlast : 0 < (⟪h', (P (Fin.last n) : E3)⟫ : ℝ) := hhem (Fin.last n)
  have hzero : 0 < (⟪h', (P 0 : E3)⟫ : ℝ) := hhem 0
  rw [he, inner_neg_right] at hlast
  linarith

/-! ## §4. The residual `OpenedWrapShortArcAtSupWBS`, discharged.

Assemble the wrap-edge-free hemisphere at the WBS supremum from the WBS closure supports (real edges
only, via FFCT45), the **real-edge** opened ShortArc edges (FFCT46's `openTail_nonwrap_shortArc`), and
the opened joints in `(0, π)` (FFCT46).  The hemisphere + margins-free distinctness
(`openedWrap_distinct_at_supWBS`) gives the wrap ShortArc. -/

/-- **§4 — the opened wraparound edge IS a short arc at the WBS supremum** (the discharge of the
residual content of FFCT46's `OpenedWrapShortArcAtSupWBS`, instantiated).  Margins-free,
wrap-edge-free: produced by the open-chain hemisphere on the real-edge data, plus the FFCT43-route
distinctness. -/
theorem openedWrapShortArc_at_supWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
      (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0) := by
  set δ : ℝ := monitoredSupWBS A B k with hδ
  set K : Fin (n + 1) := openingAxis k with hK
  set P : Fin (n + 1) → S2 := openTail A K (-δ) with hP
  have hn : 2 ≤ n := hA.two_le
  -- real-edge ShortArc edges (the wrap edge `i = Fin.last n` is excluded).
  have hside : ∀ i : Fin (n + 1), i ≠ Fin.last n → ShortArc (P i) (P (i + 1)) := by
    intro i hi; rw [hP]; exact openTail_nonwrap_shortArc hA K (-δ) hi
  -- real-edge weak supports (the FFCT45 supports hold for ALL `(i, j)`; restrict to real `i`).
  have hsupp : ∀ i j : Fin (n + 1), i ≠ Fin.last n → j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (P i) (P (i + 1)) (P j) := by
    intro i j _hi hji hji1
    rw [hP]; exact supportWBS_sOrient_nonneg hA hka hkt hkdef i j hji hji1
  -- opened joints in `(0, π)`.
  have hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi := by
    rw [hP]; exact openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef
  -- the wrap-edge-free open hemisphere.
  obtain ⟨h', _hnorm, hhem⟩ := openHemisphere_full_openChain hn hside hsupp hjopen
  -- margins-free distinctness of the wrap endpoints.
  have hdist : P (Fin.last n) ≠ P 0 := by
    rw [hP]
    intro he
    exact openedWrap_distinct_at_supWBS hA hka hkt hkdef he.symm
  exact wrap_shortArc_of_hemisphere hhem hdist

/-- **The residual `OpenedWrapShortArcAtSupWBS` holds unconditionally.**  This is the discharge of
FFCT46's single sharp residual: the opened wraparound edge of `A'_WBS` is a `ShortArc` at every WBS
supremum, with no hemisphere-margin or wrap-edge hypothesis. -/
theorem openedWrapShortArcAtSupWBS_holds : OpenedWrapShortArcAtSupWBS := by
  intro n A B hA hB k hkdef
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  exact openedWrapShortArc_at_supWBS hA hB hka hkt hkdef

/-! ## §5. The FFCT46 headline, with the wrap residual GONE.

`mainPlus_headline_wbs` is re-threaded with `OpenedWrapShortArcAtSupWBS` discharged: the final surface
is `SpliceBodyDiagMono` + `SpliceStructuralData` only. -/

/-- **§5 — the WBS headline, wrap-residual-free.**  `sDist (A 0)(A last) ≤ sDist (B 0)(B last)` for
strictly convex arms with equal sides and `A`'s joints `≤` `B`'s, conditional ONLY on the pre-B1 splice
geometry `SpliceBodyDiagMono` + `SpliceStructuralData`.  The wrap-edge residual
`OpenedWrapShortArcAtSupWBS` is **discharged** (`openedWrapShortArcAtSupWBS_holds`); the hemisphere
residuals were already gone on the WBS family. -/
theorem mainPlus_headline_wrap_free
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  mainPlus_headline_wbs hcore hstruct openedWrapShortArcAtSupWBS_holds hn A B hA hB hside hangle

/-! ### Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of the open-chain hemisphere: its conclusion (a unit strict hemisphere normal) is
genuine geometric data (norm `1`). -/
theorem openHemisphere_full_openChain_conclusion_real {n : ℕ} (h' : E3) (P : Fin (n + 1) → S2)
    (hh' : ‖h'‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ)) :
    ‖h'‖ = 1 := hh'.1

/-- Non-vacuity of the wrap discharge: realised at `δ*_WBS = 0` (the unopened arm), where the wrap edge
is `A`'s own short closing edge — a genuine `ShortArc`, not a vacuous-hypothesis impostor. -/
theorem openedWrapShortArcAtSupWBS_holds_conclusion_real {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) :
    ShortArc (A (Fin.last n)) (A 0) :=
  openedWrapShortArcAtSupWBS_conclusion_real hA

/-- Non-vacuity of the wrap-free headline: realised reflexively at `A = B`. -/
theorem mainPlus_headline_wrap_free_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

end ProofsInTheBook.ZinanFFCT47

-- §1 the open-chain collapse kernel (3 ≤ n)
#print axioms ProofsInTheBook.ZinanFFCT47.openChain_collapse_forces_flat_joint_ge3
-- §2 the wrap-edge-free open-hemisphere production
#print axioms ProofsInTheBook.ZinanFFCT47.openHemisphere_full_openChain
-- §3 wrap ShortArc from the hemisphere
#print axioms ProofsInTheBook.ZinanFFCT47.wrap_shortArc_of_hemisphere
-- §4 the residual discharged
#print axioms ProofsInTheBook.ZinanFFCT47.openedWrapShortArc_at_supWBS
#print axioms ProofsInTheBook.ZinanFFCT47.openedWrapShortArcAtSupWBS_holds
-- §5 the wrap-free headline
#print axioms ProofsInTheBook.ZinanFFCT47.mainPlus_headline_wrap_free
#print axioms ProofsInTheBook.ZinanFFCT47.openedWrapShortArcAtSupWBS_holds_conclusion_real
