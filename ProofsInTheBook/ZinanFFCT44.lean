import ProofsInTheBook.ZinanFFCT36

/-!
# `ZinanFFCT44` — the hemisphere-production kernel (WBS bricks 1–2)

This module delivers the *weak-support* hemisphere-production kernel of the Chapter 13 WBS family
(`HANDOFF/design-rounds/ch13-wbs-family.md`, bricks 1, §4, and brick 2 of §15.2):

* **§4 the kernel — `commonLine_collapse_forces_flat_joint`.**  A closed chain `P : Fin (n+1) → S2`
  (`hside`, cyclic short arcs including the wrap edge) every one of whose edge planes contains a
  common unit axis `z : S2` (`∀ i, det3 (P i) (P (i+1)) z = 0`), and all of whose interior joints lie
  in `(0, π)` (`hjopen`), is impossible (`False`).  This is the *meridian-pencil collapse*: the two
  edges adjacent to a non-pole interior apex `P m` both contain the linearly-independent pair
  `{z, P m}`, hence coincide as planes, forcing the consecutive triple `P (m-1), P m, P (m+1)`
  coplanar and the interior joint flat (FFCT21's `sphAngle_eq_zero_or_pi_of_det3_zero`).  The pole
  corner (`P m = ± z`) is handled honestly: consecutive interior poles are excluded by `ShortArc`
  (equal/antipodal), and the residual single-interior-joint pole case (`n = 2`) collapses via the
  wrap-edge cyclic identity `det3 (P 2) (P 0) z = det3 (P 0) (P 1) (P 2)` (pole `P 1 = ± z`).

* **§3 brick 1 — `equatorTangentExists_of_weakSupports_jointOpen`.**  Under the *weak* (`≥ 0`) edge
  supports and the same open-joint hypothesis, the equator vertices admit a common strictly-positive
  tangent: `∃ t, ∀ r, ⟪h₀, P r⟫ = 0 → 0 < ⟪t, P r⟫`.  Either the origin is outside the convex hull of
  the equator vertices (FFCT36's separation core gives `t` directly), or it is inside, and then the
  edge functional `det3 (P i)(P (i+1)) (·)` pushed through the convex combination forces every
  positive-weight equator vertex to be a common edge-plane axis — exactly the §4 kernel hypothesis,
  yielding `False`.

* **brick 2 — `openHemisphere_of_weakSupports_jointOpen`.**  Feeding the §3 tangent into FFCT30's
  tilt (`exists_unit_perturbed_normal_of_tangent`) produces a strict open-hemisphere normal:
  `∃ h', ‖h'‖ = 1 ∧ ∀ r, 0 < ⟪h', P r⟫`, from the weak hemisphere margins (`≥ 0`) and the open
  joints.  This is the §15.2 consumer shape replacing the fixed-`h₀` residual.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT21 ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT25 ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36

namespace ProofsInTheBook.ZinanFFCT44

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §0. Index bridges for interior joints.

For an interior joint `r : Fin (n - 1)` (so `r.val ≤ n - 2`), the two edges adjacent to the apex
`P (r.val + 1)` do **not** wrap: the `Fin (n+1)` additions `⟨r.val⟩ + 1` and `⟨r.val⟩ + 1 + 1` have
values `r.val + 1` and `r.val + 2`.  These bridges let the cyclic-edge hypotheses `hside`/`hallplanes`
talk to the nat-indexed `jointAngle` vertices. -/

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

/-- The apex (mid) vertex of interior joint `r` is `P (r.val + 1)` whether written via `Fin` addition
or the nat index. -/
private theorem P_jIdx_succ {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    P (jIdx r + 1) = P ⟨r.val + 1, by have := r.isLt; omega⟩ := by
  congr 1; apply Fin.ext; rw [jIdx_succ_val]

private theorem P_jIdx_succ_succ {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    P ((jIdx r + 1) + 1) = P ⟨r.val + 2, by have := r.isLt; omega⟩ := by
  congr 1; apply Fin.ext; rw [jIdx_succ_succ_val]

private theorem P_jIdx {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    P (jIdx r) = P ⟨r.val, by have := r.isLt; omega⟩ := rfl

/-- The interior joint at `r` equals the spherical angle of the three consecutive vertices
`P (r.val), P (r.val+1), P (r.val+2)`. -/
private theorem jointAngle_eq_consecutive {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    jointAngle P r =
      sphAngle (P ⟨r.val, by have := r.isLt; omega⟩) (P ⟨r.val + 1, by have := r.isLt; omega⟩)
        (P ⟨r.val + 2, by have := r.isLt; omega⟩) := rfl

/-! ## §4. The meridian-pencil collapse kernel.

The closed chain `P` with every edge plane through the common axis `z` and all interior joints in
`(0, π)` is impossible.  The single engine is: produce ONE interior joint index `r` whose consecutive
triple `det3 (P r) (P (r+1)) (P (r+2)) = 0`, then fire FFCT21's flat-joint bridge against the open
joint bound. -/

/-- **A flat interior joint is impossible** under the open-joint bound.  If the consecutive triple
`det3 (P r.val) (P (r.val+1)) (P (r.val+2)) = 0` with both joint arcs at the apex short
(`hsau`, `hsav`), the joint at `r` is in `{0, π}`, contradicting `0 < jointAngle P r < π`. -/
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

/-- The two edges adjacent to the apex of interior joint `r` both have a vanishing area form against
`z`, in the nat-indexed orientation needed for the span extraction. -/
private theorem edge_planes_at_apex {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hallplanes : ∀ i : Fin (n + 1), det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
    (r : Fin (n - 1)) :
    det3 (P ⟨r.val, by have := r.isLt; omega⟩ : E3) (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3)
        (z : E3) = 0 ∧
      det3 (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3)
        (P ⟨r.val + 2, by have := r.isLt; omega⟩ : E3) (z : E3) = 0 := by
  have h1 := hallplanes (jIdx r)
  have h2 := hallplanes (jIdx r + 1)
  rw [P_jIdx P r, P_jIdx_succ P r] at h1
  rw [P_jIdx_succ P r, P_jIdx_succ_succ P r] at h2
  exact ⟨h1, h2⟩

/-- **The non-pole apex collapse.**  If the apex `P (r.val+1)` of interior joint `r` is not a pole
(`(P apex : E3) ≠ ± z`), the two adjacent edge planes (both containing the independent pair
`{z, P apex}`) coincide, putting all three consecutive vertices in `span {z, P apex}`, so the
consecutive triple `det3 = 0`. -/
private theorem consecutive_det3_zero_of_nonpole {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hallplanes : ∀ i : Fin (n + 1), det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
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
  -- `z, apex` are unit and linearly independent (`apex ≠ ± z`).
  have hzu : ‖zz‖ = 1 := z.2
  have hau : ‖apex‖ = 1 := (P _).2
  -- after `set`, `hne : apex ≠ zz` and `hanti : apex ≠ -zz`.
  have hzne : zz ≠ apex := fun h => hne h.symm
  have hzanti : zz ≠ -apex := by
    intro h
    -- `zz = -apex ⟹ apex = -zz`.
    exact hanti (by rw [h]; simp)
  -- `det3 z apex x = 0` from `det3 x apex z = 0` (= `det3 (P r)(P r+1) z`).
  have hdetx : det3 zz apex x = 0 := by
    have hcyc : det3 zz apex x = -det3 x apex zz := by simp only [det3]; ring
    rw [hcyc, he1, neg_zero]
  -- `det3 z apex y = 0` from `det3 apex y z = 0` (= `det3 (P r+1)(P r+2) z`).
  have hdety : det3 zz apex y = 0 := by
    have hcyc : det3 zz apex y = det3 apex y zz := by simp only [det3]; ring
    rw [hcyc, he2]
  -- span extractions over the independent base pair `(z, apex)`.
  obtain ⟨c1, d1, hx'⟩ := lin_indep_span_of_det3_zero hzu hau hzne hzanti hdetx
  obtain ⟨c2, d2, hy'⟩ := lin_indep_span_of_det3_zero hzu hau hzne hzanti hdety
  -- `apex` itself is in `span {z, apex}`.
  have hap' : apex = (0 : ℝ) • zz + (1 : ℝ) • apex := by simp
  -- the consecutive triple is coplanar.
  exact coplanar_triple_det3_zero ⟨c1, d1, hx'.symm⟩ ⟨0, 1, hap'.symm⟩ ⟨c2, d2, hy'.symm⟩

/-- **§4 — the meridian-pencil collapse kernel.**  A closed chain `P : Fin (n+1) → S2` (`2 ≤ n`),
every edge of which is a short arc (`hside`, cyclic incl. wrap), every edge plane of which contains a
common unit axis `z` (`hallplanes`), with all interior joints in `(0, π)` (`hjopen`), is impossible. -/
theorem commonLine_collapse_forces_flat_joint {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hn : 2 ≤ n)
    (hside : ∀ i : Fin (n + 1), ShortArc (P i) (P (i + 1)))
    (hallplanes : ∀ i : Fin (n + 1), det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
    (hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi) :
    False := by
  classical
  -- The two short joint arcs at the apex of interior joint `r`, in the orientation FFCT21 wants.
  have hshort_apex : ∀ r : Fin (n - 1),
      ShortArc (P ⟨r.val + 1, by have := r.isLt; omega⟩) (P ⟨r.val, by have := r.isLt; omega⟩) ∧
        ShortArc (P ⟨r.val + 1, by have := r.isLt; omega⟩)
          (P ⟨r.val + 2, by have := r.isLt; omega⟩) := by
    intro r
    have e1 := hside (jIdx r)
    have e2 := hside (jIdx r + 1)
    rw [P_jIdx P r, P_jIdx_succ P r] at e1
    rw [P_jIdx_succ P r, P_jIdx_succ_succ P r] at e2
    -- `e1 : ShortArc (P r) (P r+1)`, `e2 : ShortArc (P r+1) (P r+2)`.  Symmetrize the first.
    exact ⟨e1.symm, e2⟩
  -- Decide whether some interior apex is a non-pole vertex.
  by_cases hsome : ∃ r : Fin (n - 1),
      (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) ≠ (z : E3) ∧
        (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) ≠ -(z : E3)
  · -- CASE (a): a non-pole apex.  The collapse gives a flat joint.
    obtain ⟨r, hne, hanti⟩ := hsome
    obtain ⟨hsau, hsav⟩ := hshort_apex r
    have hcol := consecutive_det3_zero_of_nonpole hallplanes r hne hanti
    exact flat_interior_joint_absurd r hsau hsav hcol (hjopen r)
  · -- CASE (b): every interior apex is a pole `P apex = ± z`.
    push_neg at hsome
    -- A uniform pole fact: each interior apex is `+z` or `-z`.
    have hpole : ∀ r : Fin (n - 1),
        (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) = (z : E3) ∨
          (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) = -(z : E3) := by
      intro r
      by_cases h1 : (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) = (z : E3)
      · exact Or.inl h1
      · exact Or.inr (hsome r h1)
    rcases Nat.lt_or_ge 2 n with hn3 | hn2
    · -- `n ≥ 3`: the interior apexes at joints `0` and `1` are vertices `P 1`, `P 2`, ADJACENT.
      -- Both poles ⟹ the edge `(P 1, P 2)` is equal or antipodal ⟹ contradicts `ShortArc`.
      have hp0 := hpole ⟨0, by omega⟩
      have hp1 := hpole ⟨1, by omega⟩
      -- `(⟨0,_⟩).val = 0` and `(⟨1,_⟩).val = 1` hold by `rfl`; the hypotheses are already
      -- about `P ⟨0+1⟩`, `P ⟨1+1⟩`.
      -- `hp0 : P 1 = ± z`, `hp1 : P 2 = ± z`.  Identify the vertices and use the edge `(P 1, P 2)`.
      have hsh := (hshort_apex ⟨0, by omega⟩).2
      -- `hsh : ShortArc (P ⟨0+1⟩) (P ⟨0+2⟩)`; expand into the E3 inequalities.
      have hsh1 : (P ⟨0 + 1, by omega⟩ : E3) ≠ (P ⟨0 + 2, by omega⟩ : E3) := by
        intro he; exact hsh.1 (S2.ext he)
      have hsh2 : (P ⟨0 + 1, by omega⟩ : E3) ≠ -(P ⟨0 + 2, by omega⟩ : E3) := hsh.2
      -- Now `P 1 ∈ {z, -z}` and `P 2 ∈ {z, -z}` give equal or antipodal — both excluded.
      rcases hp0 with hp0z | hp0z <;> rcases hp1 with hp1z | hp1z
      · exact hsh1 (by rw [hp0z, hp1z])
      · exact hsh2 (by rw [hp0z, hp1z, neg_neg])
      · exact hsh2 (by rw [hp0z, hp1z])
      · exact hsh1 (by rw [hp0z, hp1z])
    · -- `n = 2`: a single interior joint `r = 0`, apex `P 1` a pole, collapsed by the WRAP edge.
      have hneq : n = 2 := by omega
      subst hneq
      -- the single interior joint; `(⟨0,_⟩).val = 0` by `rfl`.
      have hp0 := hpole ⟨0, by omega⟩
      -- `hp0 : P 1 = ± z`.  WRAP edge `i = 2`: `det3 (P 2) (P 3) z = 0`, and `P 3 = P 0`.
      -- `(2 : Fin 3) + 1 = 0`.
      have hwrap := hallplanes 2
      have h21 : ((2 : Fin 3) + 1) = (0 : Fin 3) := by decide
      rw [h21] at hwrap
      -- `hwrap : det3 (P 2) (P 0) z = 0`.
      -- The vertices in `jointAngle 0` are `P 0, P 1, P 2` (nat-indexed).
      -- `det3 (P 0) (P 1) (P 2) = ± det3 (P 2) (P 0) z = 0` (cyclic, pole `P 1 = ± z`).
      have hP2 : (P (2 : Fin 3) : E3) = (P ⟨0 + 2, by omega⟩ : E3) := rfl
      have hP0 : (P (0 : Fin 3) : E3) = (P ⟨0, by omega⟩ : E3) := rfl
      set x : E3 := (P ⟨0, by omega⟩ : E3) with hx
      set mid : E3 := (P ⟨0 + 1, by omega⟩ : E3) with hmid
      set y : E3 := (P ⟨0 + 2, by omega⟩ : E3) with hy
      have hmidpole : mid = (z : E3) ∨ mid = -(z : E3) := by
        rw [hmid]; convert hp0 using 3
      have hwrap' : det3 y x (z : E3) = 0 := by
        rw [← hP2, ← hP0]; exact hwrap
      -- `det3 x z y = det3 y x z` (genuine cyclic) `= 0`.
      have hxzy : det3 x (z : E3) y = 0 := by
        have hcyc : det3 x (z : E3) y = det3 y x (z : E3) := by simp only [det3]; ring
        rw [hcyc]; exact hwrap'
      have hcol : det3 x mid y = 0 := by
        rcases hmidpole with hz | hz
        · rw [hz]; exact hxzy
        · -- `det3 x (-z) y = -det3 x z y = 0` (middle-slot linearity).
          rw [hz]
          have hneg : det3 x (-(z : E3)) y = -det3 x (z : E3) y := by
            simp only [det3, PiLp.neg_apply]; ring
          rw [hneg, hxzy, neg_zero]
      obtain ⟨hsau, hsav⟩ := hshort_apex ⟨0, by omega⟩
      -- `(⟨0,_⟩ : Fin (2-1)).val = 0` by rfl, so `hsau, hsav, hcol` already have the right shape.
      exact flat_interior_joint_absurd (⟨0, by omega⟩ : Fin (2 - 1)) hsau hsav hcol
        (hjopen ⟨0, by omega⟩)

/-! ## §3. The equator-tangent existence from weak supports and open joints.

By finite separation: either `0 ∉ convexHull ℝ Z` (the equator vertices), and FFCT36's separation
core gives the tangent `t` directly; or `0 ∈ convexHull ℝ Z`, and the edge functional pushed through
the convex combination forces every positive-weight equator vertex to be a common edge-plane axis —
the §4 kernel hypothesis — yielding `False`.  Either way the tangent exists. -/

/-- **§3 (brick 1) — equator tangent from weak supports + open joints.**  For a closed chain
`P : Fin (n+1) → S2` (`2 ≤ n`) with cyclic short-arc edges (`hside`), weak (`≥ 0`) edge supports
(`hsupp`), all interior joints in `(0, π)` (`hjopen`), and weak (`≥ 0`) hemisphere margins for a base
normal `h₀` (`hmargin`), there is a tangent direction `t` strictly positive against every equator
vertex (`⟪h₀, P r⟫ = 0 ⟹ 0 < ⟪t, P r⟫`). -/
theorem equatorTangentExists_of_weakSupports_jointOpen {n : ℕ} {P : Fin (n + 1) → S2} {h₀ : E3}
    (hn : 2 ≤ n)
    (hside : ∀ i : Fin (n + 1), ShortArc (P i) (P (i + 1)))
    (hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (P i) (P (i + 1)) (P j))
    (hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi)
    (_hmargin : ∀ r : Fin (n + 1), 0 ≤ (⟪h₀, (P r : E3)⟫ : ℝ)) :
    ∃ t : E3, ∀ r : Fin (n + 1),
      (⟪h₀, (P r : E3)⟫ : ℝ) = 0 → 0 < (⟪t, (P r : E3)⟫ : ℝ) := by
  classical
  -- The equator index set and its image set of vectors.
  set Zf : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun r => (⟪h₀, (P r : E3)⟫ : ℝ) = 0) with hZf
  set s : Finset E3 := Zf.image (fun r => ((P r : S2) : E3)) with hs
  have hmem_iff : ∀ v, v ∈ s ↔ ∃ m, (⟪h₀, (P m : E3)⟫ : ℝ) = 0 ∧ ((P m : S2) : E3) = v := by
    intro v
    rw [hs, Finset.mem_image]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rw [hZf, Finset.mem_filter] at hm
      exact ⟨m, hm.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, by rw [hZf, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hm⟩, rfl⟩
  by_cases h0 : (0 : E3) ∈ convexHull ℝ (s : Set E3)
  · -- `0 ∈ hull`: derive a common edge-plane axis and contradict §4.
    exfalso
    rw [Finset.mem_convexHull'] at h0
    obtain ⟨w, hw0, hw1, hwsum⟩ := h0
    -- For every edge `i` and every member `v`, `det3 (P i)(P i+1) v ≥ 0`.
    have hterm_nonneg : ∀ (i : Fin (n + 1)) (v : E3), v ∈ s →
        0 ≤ w v * det3 (P i : E3) (P (i + 1) : E3) v := by
      intro i v hv
      obtain ⟨m, _hm, rfl⟩ := (hmem_iff v).mp hv
      by_cases hmi : m = i
      · subst hmi; rw [show det3 (P m : E3) (P (m + 1) : E3) (P m : E3) = 0 from by
          simp only [det3]; ring, mul_zero]
      · by_cases hmi1 : m = i + 1
        · subst hmi1; rw [show det3 (P i : E3) (P (i + 1) : E3) (P (i + 1) : E3) = 0 from by
            simp only [det3]; ring, mul_zero]
        · exact mul_nonneg (hw0 _ hv)
            (le_trans (le_of_eq rfl) (hsupp i m (by simpa [eq_comm] using hmi)
              (by simpa [eq_comm] using hmi1)))
    -- The edge functional pushed through the convex combination is `0`.
    have hedge_zero : ∀ i : Fin (n + 1),
        (0 : ℝ) = ∑ v ∈ s, w v * det3 (P i : E3) (P (i + 1) : E3) v := by
      intro i
      have hkey := det3_edge_centerSum (P i : E3) (P (i + 1) : E3) s w
      rw [hwsum] at hkey
      rw [show det3 (P i : E3) (P (i + 1) : E3) (0 : E3) = 0 from by simp [det3]] at hkey
      exact hkey
    -- Hence every member has a vanishing edge functional for every edge.
    have hterm_zero : ∀ i : Fin (n + 1), ∀ v ∈ s,
        w v * det3 (P i : E3) (P (i + 1) : E3) v = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun v hv => hterm_nonneg i v hv)).mp
        (hedge_zero i).symm
    -- Pick a positive-weight member `v₀` (exists since the weights sum to `1`).
    have hexists_pos : ∃ v ∈ s, 0 < w v := by
      by_contra hnone
      push_neg at hnone
      have : ∑ v ∈ s, w v = 0 :=
        Finset.sum_eq_zero (fun v hv => le_antisymm (hnone v hv) (hw0 v hv))
      rw [hw1] at this; exact one_ne_zero this
    obtain ⟨v0, hv0s, hv0pos⟩ := hexists_pos
    obtain ⟨r0, _hr0, hv0eq⟩ := (hmem_iff v0).mp hv0s
    -- `z := P r0` is a common edge-plane axis.
    have hallplanes : ∀ i : Fin (n + 1), det3 (P i : E3) (P (i + 1) : E3) (P r0 : E3) = 0 := by
      intro i
      have := hterm_zero i v0 hv0s
      rcases mul_eq_zero.mp this with hw | hd
      · exact absurd hw (ne_of_gt hv0pos)
      · rw [hv0eq]; exact hd
    exact commonLine_collapse_forces_flat_joint hn hside hallplanes hjopen
  · -- `0 ∉ hull`: separation gives the tangent directly.
    obtain ⟨t, ht⟩ := exists_inner_pos_of_zero_notMem_convexHull s.finite_toSet h0
    refine ⟨t, fun r hr => ?_⟩
    have hrmem : ((P r : S2) : E3) ∈ s := by rw [hmem_iff]; exact ⟨r, hr, rfl⟩
    exact ht _ hrmem

/-! ## §15.2 brick 2 — open hemisphere from weak supports and open joints.

Feed the §3 tangent into FFCT30's tilt: with all hemisphere margins `≥ 0` as the base and the equator
tangent as the perturbation, `exists_unit_perturbed_normal_of_tangent` produces a strict open
hemisphere normal. -/

/-- **brick 2 — open hemisphere from weak supports + open joints.**  Under the same hypotheses as
§3, there is a *unit* normal `h'` strictly positive against every vertex:
`∃ h', ‖h'‖ = 1 ∧ ∀ r, 0 < ⟪h', P r⟫`.  This is the §15.2 consumer shape. -/
theorem openHemisphere_of_weakSupports_jointOpen {n : ℕ} {P : Fin (n + 1) → S2} {h₀ : E3}
    (hn : 2 ≤ n)
    (hside : ∀ i : Fin (n + 1), ShortArc (P i) (P (i + 1)))
    (hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (P i) (P (i + 1)) (P j))
    (hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi)
    (hmargin : ∀ r : Fin (n + 1), 0 ≤ (⟪h₀, (P r : E3)⟫ : ℝ)) :
    ∃ h' : E3, ‖h'‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ) := by
  obtain ⟨t, ht⟩ := equatorTangentExists_of_weakSupports_jointOpen hn hside hsupp hjopen hmargin
  -- `htan`: on the `h₀`-equator the tangent is strictly positive.
  have htan : ∀ r : Fin (n + 1), (⟪h₀, (P r : E3)⟫ : ℝ) = 0 → 0 < (⟪t, (P r : E3)⟫ : ℝ) := ht
  exact exists_unit_perturbed_normal_of_tangent (m := n + 1) (by omega)
    (fun r => ((P r : S2) : E3)) h₀ t hmargin htan

end ProofsInTheBook.ZinanFFCT44
