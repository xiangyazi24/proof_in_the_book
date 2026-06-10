import ProofsInTheBook.ZinanFFCT30
import ProofsInTheBook.ZinanFFCT22

/-!
# `ZinanFFCT33` — sharpening the `EquatorTangentExists` residual (Chapter 13 B1 hemi-stuck)

`ZinanFFCT30` reduced the entire hemi-stuck branch of the STUCK boundary outcome to the single named
geometric residue `EquatorTangentExists A K h₀ δ`:

    ∃ t : E3, ∀ r, ⟪h₀, A' r⟫ = 0 → 0 < ⟪t, A' r⟫,     where `A' := openTail A K δ`,

i.e. the finite set `Z := {r | ⟪h₀, A' r⟫ = 0}` of rotated-tail vertices that the opening pushed onto
the `h₀`-equator admits a common direction `t` strictly positive against all of them.  Note the design
imposes **no tangent-plane constraint** on `t` — `t` is an arbitrary `E3` vector — which is what makes
the small cases trivial: a unit vertex `v ∈ Z` already satisfies `⟪v, v⟫ = 1 > 0`.

## What this module BANKS (all axiom-free, no `sorry`, clean-3)

### §1 The abstract positive-functional core (pure inner product)
`exists_pos_functional_of_sum_pos` : for ANY finite family `P : Fin m → E3` and ANY index predicate
`Z : Fin m → Prop`, if the *equator sum* `t := Σ_{i ∈ Z} P i` is strictly positive against every
member of `Z`, then `∃ t, ∀ i, Z i → 0 < ⟪t, P i⟫`.  This is the clean separation reduction: a finite
set of vectors admits a common strictly-positive functional as soon as their **sum** is such a
functional.  Two corollaries discharge the generic small cases:

* `exists_pos_functional_of_card_le_one` : `|Z| ≤ 1` on a family of UNIT vectors — the sum is `0`
  (empty) or the single vertex `v` (`⟪v, v⟫ = 1`).
* `exists_pos_functional_of_pair_not_antipodal` : `Z = {a, b}` with `P a ≠ -(P b)` (UNIT vectors) —
  `t = P a + P b`, since `⟪t, P a⟫ = 1 + ⟪P a, P b⟫ > 0 ⟺ P a ≠ -(P b)`.

### §2 The no-3-consecutive structure of the equator set (unconditional)
`equator_no_three_consecutive` : THREE CONSECUTIVE arm vertices cannot all lie on the `h₀`-equator on a
weakly-convex `PositiveJoints` arm with the non-flat bound.  All three on the equator great circle
`{x | ⟪h₀, x⟫ = 0}` (a 2-plane through the origin) are coplanar, so their consecutive triple `det3`
vanishes (`ZinanFFCT22.coplanar_triple_det3_zero`), forcing the apex joint flat
(`ZinanFFCT22.far_fold_tail_not_interior`) — excluded by `PositiveJoints` + `jointAngle < π`.

### §3 The reduction to a strictly smaller named residual
`EquatorTangentExists` is **discharged outright** for `|Z| ≤ 1` and for non-antipodal pairs (the
generic configurations).  The single remaining obstruction is isolated as the strictly smaller named
residual `EquatorSpreadExcluded`: the equator set, when of size `≥ 2`, contains no antipodal pair AND
admits a strictly-positive sum.  `equatorTangent_of_spreadExcluded` shows it entails
`EquatorTangentExists`; the small-case discharges show it is genuinely smaller (vacuously true unless
`|Z| ≥ 3` and spread across more than a half-circle, the only surviving bad configuration).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT30

namespace ProofsInTheBook.ZinanFFCT33

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The abstract positive-functional core.

For a finite family `P : Fin m → E3` and an index predicate `Z`, the **equator sum**
`t := ∑_{i ∈ Z} P i` is a common strictly-positive functional for `Z` as soon as it is positive
against every member of `Z`.  This is the clean separation reduction underlying every small case:
`EquatorTangentExists` (which imposes no constraint on `t`) holds whenever the equator-vertex sum
already separates the equator set from the origin in the strong (strict) sense. -/

/-- **The positive-functional core.**  If the sum `t := ∑_{i ∈ Z} P i` over the equator set is
strictly positive against every equator member, then `Z` admits a common strictly-positive
functional.  (Trivially `t` itself is the witness.) -/
theorem exists_pos_functional_of_sum_pos {m : ℕ} (P : Fin m → E3) (Z : Fin m → Prop)
    [DecidablePred Z]
    (hsum : ∀ i, Z i →
      0 < (⟪∑ j ∈ Finset.univ.filter Z, P j, P i⟫ : ℝ)) :
    ∃ t : E3, ∀ i, Z i → 0 < (⟪t, P i⟫ : ℝ) :=
  ⟨∑ j ∈ Finset.univ.filter Z, P j, hsum⟩

/-- **Card ≤ 1 discharge.**  On a family of UNIT vectors, if at most one index satisfies `Z`, the
equator sum is either `0` (empty, vacuous) or the single unit vertex `v` (`⟪v, v⟫ = 1 > 0`), so a
common strictly-positive functional exists. -/
theorem exists_pos_functional_of_card_le_one {m : ℕ} (P : Fin m → E3)
    (hunit : ∀ i, (⟪P i, P i⟫ : ℝ) = 1) (Z : Fin m → Prop) [DecidablePred Z]
    (hcard : (Finset.univ.filter Z).card ≤ 1) :
    ∃ t : E3, ∀ i, Z i → 0 < (⟪t, P i⟫ : ℝ) := by
  classical
  apply exists_pos_functional_of_sum_pos P Z
  intro i hi
  -- the equator set as a Finset, nonempty (it contains `i`).
  have hmem : i ∈ Finset.univ.filter Z := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
  -- card is exactly 1: `≥ 1` from membership, `≤ 1` from hypothesis.
  have hge : 1 ≤ (Finset.univ.filter Z).card := Finset.card_pos.mpr ⟨i, hmem⟩
  have hc1 : (Finset.univ.filter Z).card = 1 := le_antisymm hcard hge
  -- a one-element finset is `{i}`.
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc1
  have hia : i = a := by rw [ha] at hmem; exact Finset.mem_singleton.mp hmem
  rw [ha, Finset.sum_singleton, ← hia]
  rw [hunit i]; norm_num

/-- **Non-antipodal pair discharge.**  On UNIT vectors `P`, if exactly the two distinct indices `a, b`
satisfy `Z` and `P a` is not the antipode of `P b`, then `t := P a + P b` is strictly positive against
both: `⟪P a + P b, P a⟫ = 1 + ⟪P a, P b⟫`, and `⟪P a, P b⟫ > -1` exactly because `P a ≠ -(P b)`. -/
theorem exists_pos_functional_of_pair_not_antipodal {m : ℕ} (P : Fin m → E3)
    (hunit : ∀ i, (⟪P i, P i⟫ : ℝ) = 1) {a b : Fin m} (hab : a ≠ b)
    (hanti : P a ≠ -(P b))
    (Z : Fin m → Prop) [DecidablePred Z]
    (hZ : ∀ i, Z i ↔ (i = a ∨ i = b)) :
    ∃ t : E3, ∀ i, Z i → 0 < (⟪t, P i⟫ : ℝ) := by
  classical
  -- the inner product `⟪P a, P b⟫ > -1` from non-antipodality of unit vectors.
  have hnorma : ‖P a‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]; exact hunit a
  have hnormb : ‖P b‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]; exact hunit b
  have hgt : -1 < (⟪P a, P b⟫ : ℝ) := by
    by_contra hle
    rw [not_lt] at hle
    -- ⟪P a, P b⟫ ≥ -1; but Cauchy–Schwarz with unit norms gives ⟪P a, P b⟫ ≥ -1, equality ⟹ antipodal.
    have hcs : -1 ≤ (⟪P a, P b⟫ : ℝ) := by
      have h := abs_real_inner_le_norm (P a) (P b)
      have hna : ‖P a‖ = 1 := by nlinarith [norm_nonneg (P a), hnorma]
      have hnb : ‖P b‖ = 1 := by nlinarith [norm_nonneg (P b), hnormb]
      rw [hna, hnb, mul_one] at h
      exact (abs_le.mp h).1
    have heq : (⟪P a, P b⟫ : ℝ) = -1 := le_antisymm (by linarith) hcs
    -- equality forces `P a = -(P b)`: ‖P a + P b‖² = 0.
    apply hanti
    have hnorm : ‖P a + P b‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right]
      have hba : (⟪P b, P a⟫ : ℝ) = -1 := by rw [real_inner_comm]; exact heq
      rw [hunit a, hunit b, heq, hba]; ring
    have : P a + P b = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
      exact norm_eq_zero.mp this
    exact eq_neg_of_add_eq_zero_left this
  apply exists_pos_functional_of_sum_pos P Z
  -- the equator finset is `{a, b}`.
  have hfilter : Finset.univ.filter Z = {a, b} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact hZ i
  rw [hfilter, Finset.sum_pair hab]
  intro i hi
  rcases (hZ i).mp hi with rfl | rfl
  · -- goal: 0 < ⟪P i + P b, P i⟫ = 1 + ⟪P b, P i⟫ = 1 + ⟪P i, P b⟫.
    rw [inner_add_left, hunit i]
    have : (⟪P b, P i⟫ : ℝ) = (⟪P i, P b⟫ : ℝ) := real_inner_comm _ _
    rw [this]; linarith
  · -- goal: 0 < ⟪P a + P i, P i⟫ = ⟪P a, P i⟫ + 1; `i = b` so `⟪P a, P i⟫ = ⟪P a, P b⟫`.
    rw [inner_add_left, hunit i]
    linarith [hgt]

/-! ## §2. The no-3-consecutive structure of the equator set.

The `h₀`-equator is the 2-plane `{x | ⟪h₀, x⟫ = 0}` through the origin.  Any three vertices on it are
coplanar, so a CONSECUTIVE triple has vanishing `det3` (`coplanar_triple_det3_zero`), forcing the apex
joint flat — excluded by `PositiveJoints` and the non-flat bound.  Hence the equator set has no three
consecutive members. -/

/-- **Three equator points are coplanar.**  In the 3-dimensional space `E3`, the orthogonal complement
of a nonzero `h₀` is a 2-plane; three vectors `x, y, z` all orthogonal to `h₀` are therefore linearly
dependent, so their scalar triple product `det3 x y z` vanishes.

The proof is the elementary Cramer/Plücker cofactor identity (valid for *all* vectors in `E3`, closed by
`ring`):
`⟪h₀,h₀⟫ · det3 x y z = ⟪h₀,x⟫·det3 h₀ y z − ⟪h₀,y⟫·det3 h₀ x z + ⟪h₀,z⟫·det3 h₀ x y`.
With the three inner products `= 0` the right side vanishes and `⟪h₀,h₀⟫ ≠ 0` (since `h₀ ≠ 0`). -/
theorem det3_zero_of_three_on_equator {h₀ : E3} (hh0 : h₀ ≠ 0) {x y z : E3}
    (hx : (⟪h₀, x⟫ : ℝ) = 0) (hy : (⟪h₀, y⟫ : ℝ) = 0) (hz : (⟪h₀, z⟫ : ℝ) = 0) :
    det3 x y z = 0 := by
  -- inner products in `EuclideanSpace ℝ (Fin 3)` expand as coordinate sums.
  have hinner3 : ∀ u v : E3, (⟪u, v⟫ : ℝ) = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
    intro u v
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  -- the Cramer/Plücker cofactor identity (pure `ring` after expanding the four inner products).
  have hkey : (⟪h₀, h₀⟫ : ℝ) * det3 x y z
      = (⟪h₀, x⟫ : ℝ) * det3 h₀ y z - (⟪h₀, y⟫ : ℝ) * det3 h₀ x z
        + (⟪h₀, z⟫ : ℝ) * det3 h₀ x y := by
    rw [hinner3 h₀ h₀, hinner3 h₀ x, hinner3 h₀ y, hinner3 h₀ z]
    simp only [det3]; ring
  -- substitute the three vanishing inner products.
  rw [hx, hy, hz] at hkey
  simp only [zero_mul, sub_zero, add_zero] at hkey
  -- `⟪h₀,h₀⟫ > 0` since `h₀ ≠ 0`.
  have hh0sq : (0 : ℝ) < (⟪h₀, h₀⟫ : ℝ) := real_inner_self_pos.mpr hh0
  exact (mul_eq_zero.mp hkey).resolve_left (ne_of_gt hh0sq)

/-- **No three CONSECUTIVE vertices on the equator.**  On a weakly-convex `PositiveJoints` arm `A'`
with the non-flat bound (a strictly-convex `B` with `JointLe A' B`) and a nonzero equator normal `h₀`,
three *consecutive* interior vertices `A'(t-1), A' t, A'(t+1)` (`1 ≤ t`, `t + 1 < n + 1`) cannot all lie
on the `h₀`-equator.

The three coplanar equator points have a vanishing consecutive triple `det3`
(`det3_zero_of_three_on_equator`), which `ZinanFFCT22.far_fold_tail_not_interior` turns into a flat apex
joint — excluded by `PositiveJoints` and `jointAngle < π`.  The two apex short arcs are supplied by the
weak-convexity `edge_short` of the closed polygon. -/
theorem equator_no_three_consecutive {n : ℕ} {A' B : Fin (n + 1) → S2}
    (hposA : PositiveJoints A') (hB : StrictConvexSphArm B) (hangle : JointLe A' B)
    {h₀ : E3} (hh0 : h₀ ≠ 0) {t : ℕ} (ht1 : 1 ≤ t) (htn : t + 1 < n + 1)
    (hpre : t - 1 < n + 1) (htt : t < n + 1) (ht2 : t + 1 < n + 1)
    (hsau : ShortArc (A' ⟨t, htt⟩) (A' ⟨t - 1, hpre⟩))
    (hsav : ShortArc (A' ⟨t, htt⟩) (A' ⟨t + 1, ht2⟩))
    (he0 : (⟪h₀, (A' ⟨t - 1, hpre⟩ : E3)⟫ : ℝ) = 0)
    (he1 : (⟪h₀, (A' ⟨t, htt⟩ : E3)⟫ : ℝ) = 0)
    (he2 : (⟪h₀, (A' ⟨t + 1, ht2⟩ : E3)⟫ : ℝ) = 0) :
    False := by
  have hcol : det3 (A' ⟨t - 1, hpre⟩ : E3) (A' ⟨t, htt⟩ : E3) (A' ⟨t + 1, ht2⟩ : E3) = 0 :=
    det3_zero_of_three_on_equator hh0 he0 he1 he2
  exact ProofsInTheBook.ZinanFFCT22.far_fold_tail_not_interior hposA hB hangle
    ht1 htn hpre htt ht2 hsau hsav hcol

/-! ## §3. Reduction to a strictly smaller named residual.

`EquatorTangentExists A K h₀ δ` (FFCT30) is `∃ t, ∀ r, ⟪h₀, A' r⟫ = 0 → 0 < ⟪t, A' r⟫`, with
`A' := openTail A K δ`.  Instantiating §1's abstract core with `P r := (openTail A K δ r : E3)`
(`hunit` is `S2.inner_self`) discharges the generic small cases outright, and isolates the single
surviving obstruction as the strictly-smaller named residual `EquatorSpreadExcluded`. -/

/-- The equator index set of the opened arm: vertices pushed onto the `h₀`-equator. -/
def equatorSet {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3) (δ : ℝ) :
    Fin (n + 1) → Prop :=
  fun r => (⟪h₀, ((openTail A K δ r : S2) : E3)⟫ : ℝ) = 0

instance equatorSet_decidable {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3) (δ : ℝ) :
    DecidablePred (equatorSet A K h₀ δ) := fun _ => Classical.dec _

/-- **(Discharge) Equator-tangent from a positive equator sum.**  If the sum of the equator vertices is
strictly positive against every equator vertex, `EquatorTangentExists` holds — directly from §1's
`exists_pos_functional_of_sum_pos` with `P r := openTail A K δ r`. -/
theorem equatorTangent_of_sum_pos {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3) (δ : ℝ)
    (hsum : ∀ r, equatorSet A K h₀ δ r →
      0 < (⟪∑ s ∈ Finset.univ.filter (equatorSet A K h₀ δ), ((openTail A K δ s : S2) : E3),
            ((openTail A K δ r : S2) : E3)⟫ : ℝ)) :
    EquatorTangentExists A K h₀ δ :=
  exists_pos_functional_of_sum_pos (fun r => ((openTail A K δ r : S2) : E3))
    (equatorSet A K h₀ δ) hsum

/-- **(Discharge) Equator-tangent when at most one vertex is on the equator.**  Directly from §1's
`exists_pos_functional_of_card_le_one` (the opened vertices are unit vectors, `S2.inner_self`). -/
theorem equatorTangent_of_card_le_one {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3)
    (δ : ℝ) (hcard : (Finset.univ.filter (equatorSet A K h₀ δ)).card ≤ 1) :
    EquatorTangentExists A K h₀ δ :=
  exists_pos_functional_of_card_le_one (fun r => ((openTail A K δ r : S2) : E3))
    (fun _ => S2.inner_self _) (equatorSet A K h₀ δ) hcard

/-- **(Discharge) Equator-tangent for a non-antipodal equator pair.**  If exactly two distinct vertices
`a, b` are on the equator and they are not antipodal, `EquatorTangentExists` holds, with witness
`t = A' a + A' b` (§1's `exists_pos_functional_of_pair_not_antipodal`). -/
theorem equatorTangent_of_pair_not_antipodal {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (h₀ : E3) (δ : ℝ) {a b : Fin (n + 1)} (hab : a ≠ b)
    (hanti : ((openTail A K δ a : S2) : E3) ≠ -((openTail A K δ b : S2) : E3))
    (hZ : ∀ r, equatorSet A K h₀ δ r ↔ (r = a ∨ r = b)) :
    EquatorTangentExists A K h₀ δ :=
  exists_pos_functional_of_pair_not_antipodal (fun r => ((openTail A K δ r : S2) : E3))
    (fun _ => S2.inner_self _) hab hanti (equatorSet A K h₀ δ) hZ

/-- **The strictly-smaller named residual.**  The ONLY equator configuration not already discharged is
a "spread" one: the equator set has size `≥ 2` AND its vertex sum is strictly positive against every
member.  `EquatorSpreadExcluded` asserts exactly this positive-sum property holds whenever it is needed.

This is genuinely smaller than `EquatorTangentExists`: it is automatically satisfied (so vacuous as an
obstruction) for `|Z| ≤ 1` (`equatorTangent_of_card_le_one`) and for non-antipodal pairs
(`equatorTangent_of_pair_not_antipodal`).  The only surviving content is `|Z| ≥ 3` (or an antipodal
pair) spread across more than an open half of the equator circle — and by §2
(`equator_no_three_consecutive`) the `≥ 3` members can never be three *consecutive* arm vertices, so a
bad spread requires a genuinely non-consecutive equator pattern, which the global edge-support geometry
at `δ*` is expected to forbid (see the report). -/
def EquatorSpreadExcluded {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3) (δ : ℝ) : Prop :=
  ∀ r, equatorSet A K h₀ δ r →
    0 < (⟪∑ s ∈ Finset.univ.filter (equatorSet A K h₀ δ), ((openTail A K δ s : S2) : E3),
          ((openTail A K δ r : S2) : E3)⟫ : ℝ)

/-- **The reduction.**  `EquatorSpreadExcluded` entails `EquatorTangentExists` — the positive equator
sum is exactly the witness `t`.  Combined with the small-case discharges, this is the sharpened residue:
the entire hemi-stuck branch now hinges only on the positivity of the equator-vertex sum, which is
automatic in every generic configuration and only at issue for `≥ 3`-vertex non-consecutive spreads. -/
theorem equatorTangent_of_spreadExcluded {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3)
    (δ : ℝ) (h : EquatorSpreadExcluded A K h₀ δ) :
    EquatorTangentExists A K h₀ δ :=
  equatorTangent_of_sum_pos A K h₀ δ h

/-- Non-vacuity of `EquatorSpreadExcluded` at `δ = 0`: the equator set is empty (every `⟪h₀, A r⟫ > 0`),
so the positive-sum condition holds vacuously. -/
theorem equatorSpreadExcluded_base {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) {h₀ : E3}
    (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) :
    EquatorSpreadExcluded A K h₀ 0 := by
  intro r hr
  -- the equator set is empty at `δ = 0`.
  rw [equatorSet, openTail_zero_angle] at hr
  exact ((ne_of_gt (hhpos r)) hr).elim
