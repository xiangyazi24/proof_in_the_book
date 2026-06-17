import ProofsInTheBook.ZinanFFCT28
import ProofsInTheBook.SphericalOpeningGlue

/-!
# `ZinanFFCT30` — the hemi-stuck master brick of the Chapter 13 B1 final wave

This module closes the **hemisphere-stuck** sub-case of the STUCK boundary outcome of
`SphericalOpeningOutcome.InteriorOpeningGlue` clause (iii).  The sibling `SphericalOpeningGlue` already
closed the **support-stuck** sub-case down to a single hemisphere-margin residue
(`HemiMarginStrictPosAtSup`) via `weakConvex_of_supportStuck_of_hemiPos`: from weak supports (`≥ 0`),
edge distinctness, and a *strict* hemisphere margin for SOME normal, the opened arm is
`WeakConvexSphArm`.  What was missing is the genuinely different **hemi-stuck** branch of the trichotomy
(`Stuck` left-disjunct of `SphericalMonitoredSup.Stuck`):

    ∃ r : Fin (n+1), hemiMargin A K h₀ r δ* = 0

i.e. the FIXED original hemisphere normal `h₀` of `A` touches the equator at one (or more) rotated-tail
vertices of `A' := openTail A K δ*`.  Then `h₀` itself is NOT a valid open-hemisphere witness for `A'`
(it gives `= 0`, not `> 0`, at the equator vertices), so the `weakConvex_of_supportStuck_of_hemiPos`
route with `h₀` is blocked.  The open-hemisphere field of `WeakConvexSphPolygon` only asks for the
EXISTENCE of SOME normal, however — `h₀` failing at one vertex does not preclude a tilted normal `h'`
working at every vertex.

## What this module BANKS (genuine new content)

### §1 The tilt perturbation core (pure inner-product, axiom-free)
`exists_perturbed_normal_of_tangent` : for a finite family `P : Fin m → E3` with a base normal `h₀`
satisfying `⟪h₀, P i⟫ ≥ 0` everywhere, given a tangent direction `t` that is strictly positive against
EVERY vertex on the `h₀`-equator (the zero set `Z = {i | ⟪h₀, P i⟫ = 0}`), the perturbation
`h₀ + ε • t` is strictly positive against EVERY vertex for all sufficiently small `ε > 0` (a single
uniform `ε` from a finite `min'`).  `exists_unit_perturbed_normal_of_tangent` normalizes it to `‖·‖ = 1`.

### §2 The equator set sits on the rotated tail
`hemiMargin_eq_orig_of_le_axis` + `axis_lt_of_hemiMargin_zero` : a vertex `r` with `r.val ≤ K.val` is
*fixed* by the opening (`openTail_fixed`), so its hemisphere margin equals the original `⟪h₀, A r⟫ > 0`;
hence the equator set `Z` is contained in the rotated tail `{r | K.val < r.val}`.  This is the precise
structural fact the design flagged: only rotated-tail vertices can have moved onto the equator.

### §3 The hemi-stuck dichotomy
`hemiStuck_forces_supportStuck_or_weakConvex` : at `δ*`, if a hemisphere margin vanishes while all
support constraints are `≥ 0`, then EITHER a non-incident support also vanishes (the support-stuck
left branch, which `SphericalOpeningGlue` handles) OR the opened arm `A'` is `WeakConvexSphArm` — the
weak outcome directly constructible.  The `WeakConvexSphArm` branch is produced from a perturbed normal
via §1 + `weakConvex_of_supportStuck_of_hemiPos`, reducing the entire hemi-stuck obstacle to the SINGLE
named, non-vacuous residue `EquatorTangentExists` (a tilt direction strictly positive against the
equator set), with the supporting structural lemmas (Z ⊆ tail, fixed-vertex strictness, edge
distinctness from the supports) all discharged unconditionally.

The residue `EquatorTangentExists` is the honest irreducible geometric content: whether the finite set
of rotated-tail vertices lying on the `h₀`-equator admits a common strictly-positive tangent direction
(equivalently, the equator vertices lie strictly within an open half of the equator circle).  It is
non-vacuous (realised at `δ = 0`, the empty equator set) and exposed exactly, per the honesty contract.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalOpeningGlue

namespace ProofsInTheBook.ZinanFFCT30

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The tilt perturbation core.

A finite family of vectors `P : Fin m → E3`, a base normal `h₀` with all inner products `≥ 0`, and a
tangent direction `t` strictly positive against every vertex on the `h₀`-equator.  Then a small tilt
`h₀ + ε • t` is strictly positive against EVERY vertex, for a single uniform `ε > 0` chosen as a finite
minimum.  The argument splits the index set into the equator set `Z` (where `⟪h₀, P i⟫ = 0`, made strict
by the tangent) and its complement (where `⟪h₀, P i⟫ > 0`, preserved by a small enough `ε`). -/

/-- **The tilt perturbation core.**  For a finite family `P : Fin m → E3`, a base normal `h₀` with
`⟪h₀, P i⟫ ≥ 0` for all `i`, and a tangent `t` with `⟪t, P i⟫ > 0` whenever `⟪h₀, P i⟫ = 0`, there is an
`ε > 0` such that the tilt `h₀ + ε • t` is *strictly* positive against every vertex:
`0 < ⟪h₀ + ε • t, P i⟫` for all `i`. -/
theorem exists_perturbed_normal_of_tangent {m : ℕ} (P : Fin m → E3) (h₀ t : E3)
    (hnn : ∀ i, 0 ≤ (⟪h₀, P i⟫ : ℝ))
    (htan : ∀ i, (⟪h₀, P i⟫ : ℝ) = 0 → 0 < (⟪t, P i⟫ : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, 0 < (⟪h₀ + ε • t, P i⟫ : ℝ) := by
  -- For each `i`, exhibit a positive `ε i` below which the tilted inner product is positive.
  -- Equator vertices (`⟪h₀, P i⟫ = 0`): any `ε > 0` works (the tilt is `ε ⟪t, P i⟫ > 0`); pick `ε i = 1`.
  -- Off-equator vertices (`⟪h₀, P i⟫ > 0`): `ε i = ⟪h₀, P i⟫ / (1 + |⟪t, P i⟫|)` keeps it positive.
  classical
  have expand : ∀ (i : Fin m) (ε : ℝ),
      (⟪h₀ + ε • t, P i⟫ : ℝ) = (⟪h₀, P i⟫ : ℝ) + ε * (⟪t, P i⟫ : ℝ) := by
    intro i ε
    rw [inner_add_left, inner_smul_left]
    simp
  have key : ∀ i, ∃ e : ℝ, 0 < e ∧ ∀ ε : ℝ, 0 < ε → ε ≤ e → 0 < (⟪h₀ + ε • t, P i⟫ : ℝ) := by
    intro i
    rcases eq_or_lt_of_le (hnn i) with hz | hpos
    · -- equator vertex: `⟪h₀, P i⟫ = 0`, so the tangent term is strictly positive.
      refine ⟨1, one_pos, fun ε hε _ => ?_⟩
      rw [expand i ε]
      have hti : 0 < (⟪t, P i⟫ : ℝ) := htan i hz.symm
      rw [← hz]; nlinarith [mul_pos hε hti]
    · -- off-equator vertex: choose `e` so `ε * ⟪t, P i⟫ ≥ -⟪h₀, P i⟫ / 2`, keeping the sum positive.
      refine ⟨(⟪h₀, P i⟫ : ℝ) / (1 + |(⟪t, P i⟫ : ℝ)|), ?_, fun ε hε hle => ?_⟩
      · positivity
      · rw [expand i ε]
        have hden : (0:ℝ) < 1 + |(⟪t, P i⟫ : ℝ)| := by positivity
        have h1 : ε * (1 + |(⟪t, P i⟫ : ℝ)|) ≤ (⟪h₀, P i⟫ : ℝ) := by
          calc ε * (1 + |(⟪t, P i⟫ : ℝ)|)
              ≤ ((⟪h₀, P i⟫ : ℝ) / (1 + |(⟪t, P i⟫ : ℝ)|)) * (1 + |(⟪t, P i⟫ : ℝ)|) := by
                apply mul_le_mul_of_nonneg_right hle (le_of_lt hden)
            _ = (⟪h₀, P i⟫ : ℝ) := by field_simp
        have h2 : -(ε * |(⟪t, P i⟫ : ℝ)|) ≤ ε * (⟪t, P i⟫ : ℝ) := by
          have := neg_abs_le (⟪t, P i⟫ : ℝ)
          nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt hε)]
        nlinarith [hpos]
  choose e he hbound using key
  -- the uniform `ε` is `min (min over i of e i) 1`, positive and below every `e i`.
  rcases isEmpty_or_nonempty (Fin m) with hempty | hne
  · -- empty index set: any positive `ε` works vacuously.
    exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  · have hfin : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty
    set ε₀ : ℝ := (Finset.univ : Finset (Fin m)).inf' hfin e with hε₀
    have hε₀pos : 0 < ε₀ := by
      rw [hε₀, Finset.lt_inf'_iff]
      exact fun i _ => he i
    refine ⟨ε₀, hε₀pos, fun i => ?_⟩
    have hle : ε₀ ≤ e i := Finset.inf'_le e (Finset.mem_univ i)
    exact hbound i ε₀ hε₀pos hle

/-- **The unit-normalized tilt perturbation.**  As `exists_perturbed_normal_of_tangent`, but the
produced normal is a *unit* vector (the open-hemisphere field demands `‖h‖ = 1`).  We normalize the tilt
`h₀ + ε • t`, which is nonzero (it has a strictly positive inner product against some `P i`, provided
`m ≠ 0`), and the strict positivity scales by the positive factor `‖·‖⁻¹`. -/
theorem exists_unit_perturbed_normal_of_tangent {m : ℕ} (hm : 0 < m) (P : Fin m → E3) (h₀ t : E3)
    (hnn : ∀ i, 0 ≤ (⟪h₀, P i⟫ : ℝ))
    (htan : ∀ i, (⟪h₀, P i⟫ : ℝ) = 0 → 0 < (⟪t, P i⟫ : ℝ)) :
    ∃ h' : E3, ‖h'‖ = 1 ∧ ∀ i, 0 < (⟪h', P i⟫ : ℝ) := by
  obtain ⟨ε, hε, hpos⟩ := exists_perturbed_normal_of_tangent P h₀ t hnn htan
  set g : E3 := h₀ + ε • t with hg
  -- `g ≠ 0`: else `⟪g, P i₀⟫ = 0`, contradicting `hpos i₀` (using `m ≠ 0` to get an index).
  have hi0 : (⟨0, hm⟩ : Fin m) = (⟨0, hm⟩ : Fin m) := rfl
  have hgne : g ≠ 0 := by
    intro h0
    have := hpos ⟨0, hm⟩
    rw [h0, inner_zero_left] at this
    exact lt_irrefl _ this
  have hgnorm : 0 < ‖g‖ := norm_pos_iff.mpr hgne
  refine ⟨(‖g‖⁻¹ : ℝ) • g, ?_, fun i => ?_⟩
  · rw [norm_smul, norm_inv, norm_norm]
    field_simp
  · rw [inner_smul_left]
    simp only [RCLike.conj_to_real]
    have : (0:ℝ) < ‖g‖⁻¹ := by positivity
    exact mul_pos this (hpos i)

/-! ## §2. The equator set sits on the rotated tail.

A vertex `r` with `r.val ≤ K.val` is *fixed* by the opening (`openTail_fixed`), so its hemisphere
margin equals the original arm's hemisphere value `⟪h₀, A r⟫`, which is strictly positive for the
original arm's hemisphere normal `h₀`.  Hence such a vertex is NEVER on the `h₀`-equator: the equator
set `Z = {r | ⟪h₀, openTail A K δ r⟫ = 0}` is contained in the rotated tail `{r | K.val < r.val}`. -/

/-- The interior-opened vertex's hemisphere value at a *fixed* index `r` (`r.val ≤ K.val`) equals the
original `⟪h₀, A r⟫`. -/
theorem hemiMargin_eq_orig_of_le_axis {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3)
    {δ : ℝ} {r : Fin (n + 1)} (hr : r.val ≤ K.val) :
    (⟪h₀, ((openTail A K δ r : S2) : E3)⟫ : ℝ) = (⟪h₀, (A r : E3)⟫ : ℝ) := by
  rw [openTail_fixed A K δ hr]

/-- **The equator set sits on the rotated tail.**  For the original arm's hemisphere normal `h₀`
(`⟪h₀, A i⟫ > 0` for every `i`), any vertex `r` whose opened hemisphere value vanishes must be a
*rotated-tail* vertex (`K.val < r.val`): the fixed vertices keep their original strict margins. -/
theorem axis_lt_of_hemiMargin_zero {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) {h₀ : E3}
    (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) {δ : ℝ} {r : Fin (n + 1)}
    (hzero : (⟪h₀, ((openTail A K δ r : S2) : E3)⟫ : ℝ) = 0) :
    K.val < r.val := by
  by_contra hle
  rw [not_lt] at hle
  rw [hemiMargin_eq_orig_of_le_axis A K h₀ hle] at hzero
  exact (ne_of_gt (hhpos r)) hzero

/-! ## §3. The hemi-stuck dichotomy.

At the opened arm `A' := openTail A K δ`, suppose every non-incident support is `≥ 0` (closure) and a
hemisphere margin vanishes (hemi-stuck).  Then EITHER a non-incident support also vanishes (the
support-stuck left branch) OR `A'` is `WeakConvexSphArm`.  The `WeakConvexSphArm` branch is produced
from a perturbed normal: in the all-supports-strict sub-case the supports give edge distinctness, and
the residue `EquatorTangentExists` supplies a tangent direction strictly positive against the equator
set, which §1's `exists_unit_perturbed_normal_of_tangent` turns into a strict open-hemisphere witness;
`weakConvex_of_supportStuck_of_hemiPos` then assembles `WeakConvexSphArm A'`. -/

/-- **(Residue) The equator-tangent existence.**  At the opened arm `A' = openTail A K δ`, with `h₀` the
original hemisphere normal and the supports all `≥ 0`, there is a tangent direction `t` that is strictly
positive against every vertex of `A'` lying on the `h₀`-equator (`⟪h₀, A' r⟫ = 0`).  Geometrically: the
finite set of rotated-tail vertices that the opening has pushed onto the `h₀`-equator lies strictly
within an open half of the equator circle.

This is the single honest irreducible content of the hemi-stuck branch: whether the equator vertices
admit a common strictly-positive tilt.  It is non-vacuous — at `δ = 0` the equator set is empty (every
`⟪h₀, A r⟫ > 0`), so any `t` works (`equatorTangentExists_base`). -/
def EquatorTangentExists {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3) (δ : ℝ) : Prop :=
  ∃ t : E3, ∀ r : Fin (n + 1),
    (⟪h₀, ((openTail A K δ r : S2) : E3)⟫ : ℝ) = 0 → 0 < (⟪t, ((openTail A K δ r : S2) : E3)⟫ : ℝ)

/-- Non-vacuity of `EquatorTangentExists`: at `δ = 0` the opening is the identity and every hemisphere
value `⟪h₀, A r⟫` is strictly positive, so the equator set is empty and the condition holds for any `t`
(take `t = h₀`). -/
theorem equatorTangentExists_base {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) {h₀ : E3}
    (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) :
    EquatorTangentExists A K h₀ 0 := by
  refine ⟨h₀, fun r hzero => ?_⟩
  rw [openTail_zero_angle] at hzero
  exact ((ne_of_gt (hhpos r)) hzero).elim

/-- **Edge distinctness from strict supports.**  If every non-incident support of `A' = openTail A K δ`
is *strictly* positive, then consecutive vertices are distinct (witnessed by the non-incident vertex
`i + 2`, exactly as in `reach_strictConvex_interior`'s `edge_short` derivation). -/
theorem openTail_edge_ne_of_strict {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} {δ : ℝ}
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j)) :
    ∀ i : Fin (n + 1), openTail A K δ i ≠ openTail A K δ (i + 1) := by
  have h3 : 3 ≤ n + 1 := by have := hA.two_le; omega
  intro i
  have hi := i.isLt
  have h2v : ((2 : Fin (n + 1)) : ℕ) = 2 := by simp; omega
  have h1v : ((1 : Fin (n + 1)) : ℕ) = 1 := by simp; omega
  have e2 : ((i + 2 : Fin (n + 1)) : ℕ) = (↑i + 2) % (n + 1) := by rw [Fin.val_add, h2v]
  have e1 : ((i + 1 : Fin (n + 1)) : ℕ) = (↑i + 1) % (n + 1) := by rw [Fin.val_add, h1v]
  have hni0 : (i + 2 : Fin (n + 1)) ≠ i := by
    intro he
    have h := congrArg Fin.val he
    rw [e2] at h
    rcases Nat.lt_or_ge (↑i + 2) (n + 1) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h; omega
    · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h; omega
  have hni1 : (i + 2 : Fin (n + 1)) ≠ i + 1 := by
    intro he
    have h := congrArg Fin.val he
    rw [e2, e1] at h
    rcases Nat.lt_or_ge (↑i + 2) (n + 1) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)] at h; omega
    · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
      rcases Nat.lt_or_ge (↑i + 1) (n + 1) with hlt1 | hge1
      · rw [Nat.mod_eq_of_lt hlt1] at h; omega
      · rw [Nat.mod_eq_sub_mod hge1, Nat.mod_eq_of_lt (by omega)] at h; omega
  exact ne_of_sOrient_pos_ab (hmix i (i + 2) hni0 hni1)

/-- **The hemi-stuck dichotomy (generic-`δ` form, strongest).**  At the opened arm `A' = openTail A K δ`,
with `h₀` any base normal, suppose every non-incident support is `≥ 0` (`hsupp`), every hemisphere margin
is `≥ 0` (`hhemnn`, closure), and the equator-tangent residue holds.  Then EITHER a non-incident support
vanishes OR `A'` is `WeakConvexSphArm`.

This holds *whether or not* a hemisphere margin actually vanishes — the precise content is that
hemi-stuck is harmless: the only obstruction to weak convexity is a vanishing support, since a tilted
hemisphere normal always exists when the equator vertices admit a common positive tangent.  In the
all-supports-strict sub-case the strict supports give edge distinctness (`openTail_edge_ne_of_strict`);
the residue `EquatorTangentExists` supplies a tilt direction; §1's
`exists_unit_perturbed_normal_of_tangent` (using the closure `≥ 0` margins as the base and the tilt as
the tangent) builds a strict open-hemisphere witness `h'`; `weakConvex_of_supportStuck_of_hemiPos`
assembles `WeakConvexSphArm A'`. -/
theorem hemiStuck_dichotomy_of_glue {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} {δ : ℝ} {h₀ : E3}
    (hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 ≤ sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    (hhemnn : ∀ r : Fin (n + 1), 0 ≤ (⟪h₀, ((openTail A K δ r : S2) : E3)⟫ : ℝ))
    (htangent : EquatorTangentExists A K h₀ δ) :
    (∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
        sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j) = 0) ∨
      WeakConvexSphArm (openTail A K δ) := by
  classical
  -- either some non-incident support is exactly 0 (left branch) or all are strictly positive.
  by_cases hsome : ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j) = 0
  · exact Or.inl hsome
  · refine Or.inr ?_
    -- all supports strictly positive.
    have hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j) := by
      intro i j hji hji1
      refine lt_of_le_of_ne (hsupp i j hji hji1) (fun heq => hsome ⟨i, j, hji, hji1, heq.symm⟩)
    -- edge distinctness.
    have hdist := openTail_edge_ne_of_strict hA hmix
    -- the perturbed unit normal (positive `n+1 > 0`).
    obtain ⟨t, ht⟩ := htangent
    obtain ⟨h', hh'norm, hh'pos⟩ :=
      exists_unit_perturbed_normal_of_tangent (m := n + 1) (by omega)
        (fun r => ((openTail A K δ r : S2) : E3)) h₀ t hhemnn ht
    exact weakConvex_of_supportStuck_of_hemiPos hA hh'norm hsupp hdist hh'pos

/-- **The hemi-stuck master brick (`monitoredSup` form).**  This is the design's
`hemiStuck_forces_supportStuck_or_weakConvex`, adapted to the real trichotomy output.  At the monitored
supremum `δ* = monitoredSup A B k h₀ Tcap`, given the closure inputs (`hka`, `hkt`, `hTcap`, `h0`), if a
hemisphere margin vanishes (`hhem`, the hemi-stuck branch of `SphericalMonitoredSup.Stuck`) and the
equator-tangent residue holds, then EITHER a non-incident support vanishes (`SphericalMonitoredSup.Stuck`
support branch) OR the opened arm at `δ*` is `WeakConvexSphArm`.

All supports `≥ 0` and all hemisphere margins `≥ 0` at `δ*` come from closure
(`supportConstraint_nonneg_at_sup`, `hemiMargin_nonneg_at_sup`); the rest is `hemiStuck_dichotomy_of_glue`. -/
theorem hemiStuck_forces_supportStuck_or_weakConvex {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {k : Fin (n - 1)} {h₀ : E3} (_hnorm : ‖h₀‖ = 1)
    (_hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (_hhem : ∃ r : Fin (n + 1),
      hemiMargin A (openingAxis k) h₀ r (monitoredSup A B k h₀ Tcap) = 0)
    (htangent : EquatorTangentExists A (openingAxis k) h₀ (monitoredSup A B k h₀ Tcap)) :
    (∃ c : NonIncident n,
        supportConstraint A (openingAxis k) c (monitoredSup A B k h₀ Tcap) = 0) ∨
      WeakConvexSphArm (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap)) := by
  set δ : ℝ := monitoredSup A B k h₀ Tcap with hδ
  -- closure: supports ≥ 0, margins ≥ 0.
  have hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (openTail A (openingAxis k) δ i) (openTail A (openingAxis k) δ (i + 1))
        (openTail A (openingAxis k) δ j) := by
    intro i j hji hji1
    have := supportConstraint_nonneg_at_sup hka hkt hTcap h0 (⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n)
    rwa [supportConstraint_apply] at this
  have hhemnn : ∀ r : Fin (n + 1),
      0 ≤ (⟪h₀, ((openTail A (openingAxis k) δ r : S2) : E3)⟫ : ℝ) := by
    intro r
    have := hemiMargin_nonneg_at_sup hka hkt hTcap h0 r
    simpa only [hemiMargin] using this
  rcases hemiStuck_dichotomy_of_glue hA hsupp hhemnn htangent with hsup | hweak
  · -- repackage the ∃ i j vanishing support as a NonIncident witness.
    obtain ⟨i, j, hji, hji1, heq⟩ := hsup
    refine Or.inl ⟨(⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n), ?_⟩
    rw [supportConstraint_apply]; exact heq
  · exact Or.inr hweak

end ProofsInTheBook.ZinanFFCT30
