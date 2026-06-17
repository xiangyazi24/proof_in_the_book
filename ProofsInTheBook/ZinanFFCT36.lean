import ProofsInTheBook.ZinanFFCT34
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Combination

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT33 ProofsInTheBook.ZinanFFCT34

namespace ProofsInTheBook.ZinanFFCT36

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. Abstract separation: `0 ∉ convexHull ℝ Z` gives a common strict-positive functional. -/

/-- **Separation core.**  For a *finite* set `s` of vectors in `E3`, if the origin is not in the
convex hull of `s`, then there is a direction `t` strictly positive against every member of `s`. -/
theorem exists_inner_pos_of_zero_notMem_convexHull {s : Set E3} (hfin : s.Finite)
    (h0 : (0 : E3) ∉ convexHull ℝ s) :
    ∃ t : E3, ∀ v ∈ s, 0 < (⟪t, v⟫ : ℝ) := by
  -- the convex hull of a finite set is convex and closed; `0` is outside it.
  have hconv : Convex ℝ (convexHull ℝ s) := convex_convexHull ℝ s
  have hclosed : IsClosed (convexHull ℝ s) := hfin.isClosed_convexHull ℝ
  obtain ⟨f, u, hf0, hfb⟩ :=
    geometric_hahn_banach_point_closed hconv hclosed h0
  -- `f 0 = 0 < u`, and `u < f x` for every hull point; in particular for every `v ∈ s ⊆ hull`.
  have hf0' : (0 : ℝ) < u := by simpa using hf0
  -- Riesz: realise `f` as `⟪t, ·⟫`.
  refine ⟨(InnerProductSpace.toDual ℝ E3).symm f, fun v hv => ?_⟩
  have hvhull : v ∈ convexHull ℝ s := subset_convexHull ℝ s hv
  have : u < f v := hfb v hvhull
  have hriesz : (⟪(InnerProductSpace.toDual ℝ E3).symm f, v⟫ : ℝ) = f v :=
    InnerProductSpace.toDual_symm_apply
  rw [hriesz]
  linarith

/-! ## §2. The `det3` edge functional pushed through a finite convex combination.

For a fixed oriented edge `(a, b)` the map `w ↦ det3 a b w` is linear in its third slot, hence
distributes over a weighted finite sum. -/

/-- **`det3` edge functional over a weighted Finset sum.**  For fixed `a b : E3`,
`det3 a b (∑ y ∈ t, w y • y) = ∑ y ∈ t, w y * det3 a b y`. -/
theorem det3_edge_centerSum (a b : E3) (t : Finset E3) (w : E3 → ℝ) :
    det3 a b (∑ y ∈ t, w y • y) = ∑ y ∈ t, w y * det3 a b y := by
  classical
  induction t using Finset.induction with
  | empty => simp [det3]
  | insert x t hx ih =>
      rw [Finset.sum_insert hx, ProofsInTheBook.ZinanFFCT10.det3_add_right,
        ProofsInTheBook.ZinanFFCT10.det3_smul_right, ih, Finset.sum_insert hx]

/-! ## §3. The convex-combination kill: `0 ∉ convexHull ℝ Z`.

Fix an oriented arm edge `(a, b)`.  Suppose every equator vector `y` is "incident" to the edge
(`det3 a b y = 0`, in which case `y ∈ {a, b}`) or "non-incident" (`0 < det3 a b y`, the strict
support).  Apply the edge functional `det3 a b (·)` to a convex combination `0 = ∑ w y • y`: by
multilinearity `0 = ∑ w y · det3 a b y`, a sum of nonnegatives, so every non-incident weight
vanishes.  The weight is thus supported on `{a, b}`, giving `0 = w_a • a + w_b • b` with unit `a, b`,
`w ≥ 0`, `w_a + w_b = 1` — forcing `a = b` (excluded) or `a = -b` (antipodal, excluded by the
short-arc edge).  Hence `0 ∉ convexHull ℝ Z`. -/

/-- **The edge-functional convex-combination kill (abstract).**  For a fixed oriented edge `(a, b)`
of unit vectors that is neither degenerate (`a ≠ b`) nor antipodal (`a ≠ -b`), if every member `y` of
a finite vector set `s` has `det3 a b y` either `0` (and then `y ∈ {a, b}`) or strictly positive,
then the origin is not in the convex hull of `s`. -/
theorem zero_notMem_convexHull_edge {a b : E3} (s : Finset E3)
    (hne : a ≠ b) (hanti : a ≠ -b)
    (hua : (⟪a, a⟫ : ℝ) = 1) (hub : (⟪b, b⟫ : ℝ) = 1)
    (hsign : ∀ y ∈ s, det3 a b y = 0 ∨ 0 < det3 a b y)
    (hincident : ∀ y ∈ s, det3 a b y = 0 → y = a ∨ y = b) :
    (0 : E3) ∉ convexHull ℝ (s : Set E3) := by
  classical
  intro hmem
  -- extract convex-combination weights on the vectors.
  rw [Finset.mem_convexHull'] at hmem
  obtain ⟨w, hw0, hw1, hwsum⟩ := hmem
  -- apply the edge functional to `0 = ∑ w y • y`.
  have hfun : (0 : ℝ) = ∑ y ∈ s, w y * det3 a b y := by
    have hkey := det3_edge_centerSum a b s w
    rw [hwsum] at hkey
    -- `hkey : det3 a b 0 = ∑ ...`; the LHS is `0`.
    rw [show det3 a b (0 : E3) = 0 from by simp [det3]] at hkey
    exact hkey
  -- every term is nonnegative.
  have hterm_nonneg : ∀ y ∈ s, 0 ≤ w y * det3 a b y := by
    intro y hy
    rcases hsign y hy with hz | hp
    · rw [hz, mul_zero]
    · exact mul_nonneg (hw0 y hy) (le_of_lt hp)
  -- the total being zero forces every term to vanish.
  have hterm_zero : ∀ y ∈ s, w y * det3 a b y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hfun.symm
  -- hence every non-incident weight vanishes: weight supported on `{a, b}`.
  have hsupp : ∀ y ∈ s, y ≠ a → y ≠ b → w y = 0 := by
    intro y hy hya hyb
    rcases hsign y hy with hz | hp
    · rcases hincident y hy hz with h | h
      · exact absurd h hya
      · exact absurd h hyb
    · have := hterm_zero y hy
      rcases mul_eq_zero.mp this with hw | hd
      · exact hw
      · exact absurd hd (ne_of_gt hp)
  -- the weighted sum collapses to the `{a, b}` part.
  -- Define the two coefficients.
  -- `∑_{y ∈ s} w y • y = ∑_{y ∈ s ∩ {a,b}} w y • y`.
  have hsum_restrict :
      ∑ y ∈ s, w y • y = ∑ y ∈ s.filter (fun y => y = a ∨ y = b), w y • y := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun y => y = a ∨ y = b) (fun y => w y • y)]
    have hzero_part : ∑ y ∈ s.filter (fun y => ¬ (y = a ∨ y = b)), w y • y = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨hys, hnab⟩ := hy
      obtain ⟨hya, hyb⟩ := not_or.mp hnab
      rw [hsupp y hys hya hyb, zero_smul]
    rw [hzero_part, add_zero]
  -- similarly the weight total restricts.
  have hsum1_restrict :
      ∑ y ∈ s.filter (fun y => y = a ∨ y = b), w y = 1 := by
    rw [← hw1, ← Finset.sum_filter_add_sum_filter_not s (fun y => y = a ∨ y = b) w]
    have hzero_part : ∑ y ∈ s.filter (fun y => ¬ (y = a ∨ y = b)), w y = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨hys, hnab⟩ := hy
      obtain ⟨hya, hyb⟩ := not_or.mp hnab
      exact hsupp y hys hya hyb
    rw [hzero_part, add_zero]
  -- abbreviate the restricted Finset.
  set F : Finset E3 := s.filter (fun y => y = a ∨ y = b) with hF
  -- the restricted convex combination is `0`.
  have hsum0 : ∑ y ∈ F, w y • y = 0 := by rw [← hsum_restrict, hwsum]
  -- `⟪a, b⟫ > -1` from unit vectors and non-antipodality (FFCT33's Cauchy–Schwarz pattern).
  have hnorma : ‖a‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hua
  have hnormb : ‖b‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hub
  have hgt : -1 < (⟪a, b⟫ : ℝ) := by
    by_contra hle
    rw [not_lt] at hle
    have hcs : -1 ≤ (⟪a, b⟫ : ℝ) := by
      have h := abs_real_inner_le_norm a b
      have hna : ‖a‖ = 1 := by nlinarith [norm_nonneg a, hnorma]
      have hnb : ‖b‖ = 1 := by nlinarith [norm_nonneg b, hnormb]
      rw [hna, hnb, mul_one] at h
      exact (abs_le.mp h).1
    have heq : (⟪a, b⟫ : ℝ) = -1 := le_antisymm (by linarith) hcs
    apply hanti
    have hnorm : ‖a + b‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right]
      have hba : (⟪b, a⟫ : ℝ) = -1 := by rw [real_inner_comm]; exact heq
      rw [hua, hub, heq, hba]; ring
    have hz : a + b = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
      exact norm_eq_zero.mp this
    exact eq_neg_of_add_eq_zero_left hz
  -- take inner product of `0 = ∑_F w y • y` with `a + b`: each term is `w y · ⟪y, a+b⟫ ≥ 0`,
  -- with `⟪y, a+b⟫ > 0` for `y ∈ {a, b}`, forcing `∑_F w = 0`, contradicting `∑_F w = 1`.
  have hinner0 : (0 : ℝ) = ∑ y ∈ F, w y * (⟪y, a + b⟫ : ℝ) := by
    have hexp : (⟪∑ y ∈ F, w y • y, a + b⟫ : ℝ) = ∑ y ∈ F, w y * (⟪y, a + b⟫ : ℝ) := by
      rw [sum_inner]
      exact Finset.sum_congr rfl (fun y _ => real_inner_smul_left y (a + b) (w y))
    rw [hsum0, inner_zero_left] at hexp
    exact hexp
  -- each summand is `≥ 0`, and `> 0` would force `w y = 0`; positivity of `⟪y, a+b⟫` on `F`.
  have hpos_dir : ∀ y ∈ F, 0 < (⟪y, a + b⟫ : ℝ) := by
    intro y hy
    rw [hF, Finset.mem_filter] at hy
    have hba : (⟪b, a⟫ : ℝ) = (⟪a, b⟫ : ℝ) := real_inner_comm a b
    rcases hy.2 with rfl | rfl
    · rw [inner_add_right, hua]; linarith
    · rw [inner_add_right, hub, hba]; linarith
  -- nonneg summands summing to `0` ⟹ each `w y = 0` ⟹ `∑_F w = 0`, contradicting `∑_F w = 1`.
  have hterm_nonneg2 : ∀ y ∈ F, 0 ≤ w y * (⟪y, a + b⟫ : ℝ) := by
    intro y hy
    have hwy : 0 ≤ w y := by
      have : y ∈ s := by rw [hF, Finset.mem_filter] at hy; exact hy.1
      exact hw0 y this
    exact mul_nonneg hwy (le_of_lt (hpos_dir y hy))
  have hallzero : ∀ y ∈ F, w y * (⟪y, a + b⟫ : ℝ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg2).mp hinner0.symm
  have hw_zero : ∀ y ∈ F, w y = 0 := by
    intro y hy
    rcases mul_eq_zero.mp (hallzero y hy) with h | h
    · exact h
    · exact absurd h (ne_of_gt (hpos_dir y hy))
  have hcontra : (1 : ℝ) = 0 := by
    rw [← hsum1_restrict]
    exact Finset.sum_eq_zero hw_zero
  exact one_ne_zero hcontra

/-! ## §4. The complete kill of `EquatorTangentExists` in the strict-support branch.

Specialise the abstract convex-combination kill to the opened arm `A' := openTail A K δ`.  Fix any
arm edge `(k, k+1)`.  The equator vectors form the finite image set
`s := (Z).image (fun r => (A' r : E3))`.  For each `y = A' m ∈ s` (`m` on the equator):

* if `m ≠ k` and `m ≠ k+1`, the strict support `hmix` gives `0 < det3 (A' k) (A' (k+1)) (A' m)`;
* if `m = k` or `m = k+1`, `det3 (A' k) (A' (k+1)) (A' m) = 0` (alternating, `det3_self`), and then
  `y = A' k` or `y = A' (k+1)`.

So `hsign` and `hincident` hold; with the short-arc edge supplying `A' k ≠ A' (k+1)` and
`A' k ≠ -A' (k+1)`, `zero_notMem_convexHull_edge` gives `0 ∉ convexHull ℝ s`, and the separation core
produces the tangent — `EquatorTangentExists` outright. -/

/-- **The complete equator-tangent kill (strict branch, any short-arc edge).**  In the all-supports
strict branch (`hmix`), for ANY arm edge `(k, k+1)` that is a short arc
(`ShortArc (A' k) (A' (k+1))`), `EquatorTangentExists A K h₀ δ` holds outright.  No remaining
residual: the entire hemi-stuck spread obstruction is discharged. -/
theorem equatorTangentExists_of_strictSupports {n : ℕ} {A : Fin (n + 1) → S2} {K : Fin (n + 1)}
    {h₀ : E3} {δ : ℝ}
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    {k : Fin (n + 1)} (hshort : ShortArc (openTail A K δ k) (openTail A K δ (k + 1))) :
    EquatorTangentExists A K h₀ δ := by
  classical
  set A' : Fin (n + 1) → S2 := openTail A K δ with hA'
  -- the equator index Finset and its image set of vectors.
  set Zf : Finset (Fin (n + 1)) := Finset.univ.filter (equatorSet A K h₀ δ) with hZf
  set s : Finset E3 := Zf.image (fun r => ((A' r : S2) : E3)) with hs
  -- the abbreviations `a := A' k`, `b := A' (k+1)`.
  set a : E3 := ((A' k : S2) : E3) with ha
  set b : E3 := ((A' (k + 1) : S2) : E3) with hb
  -- edge endpoints distinct and non-antipodal (from the short arc).
  have hne : a ≠ b := fun h => hshort.1 (Subtype.ext h)
  have hanti : a ≠ -b := hshort.2
  have hua : (⟪a, a⟫ : ℝ) = 1 := S2.inner_self _
  have hub : (⟪b, b⟫ : ℝ) = 1 := S2.inner_self _
  -- the two structural hypotheses on the image set.
  have hmem_iff : ∀ y, y ∈ s ↔ ∃ m, equatorSet A K h₀ δ m ∧ ((A' m : S2) : E3) = y := by
    intro y
    rw [hs, Finset.mem_image]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rw [hZf, Finset.mem_filter] at hm
      exact ⟨m, hm.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, by rw [hZf, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hm⟩, rfl⟩
  have hsign : ∀ y ∈ s, det3 a b y = 0 ∨ 0 < det3 a b y := by
    intro y hy
    obtain ⟨m, _hm, rfl⟩ := (hmem_iff y).mp hy
    by_cases hmk : m = k
    · left; rw [ha, hb, hmk]; exact ProofsInTheBook.SphericalDiagCut.det3_self_right _ _
    · by_cases hmk1 : m = k + 1
      · left; rw [ha, hb, hmk1]; exact ProofsInTheBook.SphericalDiagCut.det3_self_mid _ _
      · right
        have := hmix k m (by simpa [eq_comm] using hmk) (by simpa [eq_comm] using hmk1)
        rw [sOrient] at this
        rw [ha, hb]; exact this
  have hincident : ∀ y ∈ s, det3 a b y = 0 → y = a ∨ y = b := by
    intro y hy _hz
    obtain ⟨m, _hm, rfl⟩ := (hmem_iff y).mp hy
    by_cases hmk : m = k
    · left; rw [ha, hmk]
    · by_cases hmk1 : m = k + 1
      · right; rw [hb, hmk1]
      · -- non-incident: `det3 > 0 ≠ 0`, contradiction with the hypothesis `det3 = 0`.
        exfalso
        have hpos := hmix k m (by simpa [eq_comm] using hmk) (by simpa [eq_comm] using hmk1)
        rw [sOrient] at hpos
        rw [ha, hb] at _hz
        rw [_hz] at hpos
        exact lt_irrefl _ hpos
  -- the abstract kill: `0 ∉ convexHull ℝ s`.
  have h0 : (0 : E3) ∉ convexHull ℝ (s : Set E3) :=
    zero_notMem_convexHull_edge s hne hanti hua hub hsign hincident
  -- separation produces a strictly-positive functional against every equator vector.
  obtain ⟨t, ht⟩ := exists_inner_pos_of_zero_notMem_convexHull s.finite_toSet h0
  -- repackage as `EquatorTangentExists`.
  refine ⟨t, fun r hr => ?_⟩
  have hrmem : ((A' r : S2) : E3) ∈ s := by
    rw [hmem_iff]; exact ⟨r, hr, rfl⟩
  exact ht _ hrmem

/-! ## §5. Self-contained short-arc edge from strict supports, and the tangent-free dichotomy.

On an arm with `3 ≤ n + 1` (always true for a strictly-convex polygon, `≥ 3` vertices), the edge
`(0, 1)` is non-incident to `0` itself in BOTH the `det3`-self sense and the antipodal sense:

* `A' 0 ≠ A' 1` is `openTail_edge_ne_of_strict` (FFCT30);
* `A' 0 ≠ -A' 1` is FFCT34's antipodal exclusion (`antipodal_pair_excluded_of_strict`) with `r = 0`,
  `s = 1`, using `0 ≠ 1` and `0 ≠ 1 + 1 = 2` (valid since `3 ≤ n + 1`).

So `(0, 1)` is a short arc, and the equator-tangent residue is discharged *with no short-arc input*. -/

/-- **Short-arc edge `(0, 1)` from strict supports.**  On an arm with `3 ≤ n + 1`, in the strict
branch the edge `(0, 1)` of the opened arm is a short arc. -/
theorem shortArc_edge_zero_of_strict {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} {δ : ℝ} (hn : 3 ≤ n + 1)
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j)) :
    ShortArc (openTail A K δ 0) (openTail A K δ (0 + 1)) := by
  refine ⟨openTail_edge_ne_of_strict hA hmix 0, ?_⟩
  -- the two indices `0` and `1`, with `0 ≠ 1` and `0 ≠ 1 + 1 = 2` in `Fin (n+1)` (uses `3 ≤ n+1`).
  intro hanti
  have hval1 : (0 + 1 : Fin (n + 1)).val = 1 := by
    rw [zero_add, Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have hval2 : ((0 + 1 : Fin (n + 1)) + 1).val = 2 := by
    rw [Fin.val_add, hval1, Fin.val_one']
    rw [Nat.mod_eq_of_lt (by omega : 1 < n + 1)]
    exact Nat.mod_eq_of_lt (by omega)
  have h01 : (0 : Fin (n + 1)) ≠ (0 + 1 : Fin (n + 1)) := by
    intro h; rw [Fin.ext_iff, Fin.val_zero, hval1] at h; omega
  have h02 : (0 : Fin (n + 1)) ≠ (0 + 1 : Fin (n + 1)) + 1 := by
    intro h; rw [Fin.ext_iff, Fin.val_zero, hval2] at h; omega
  -- apply FFCT34 LEVER 1 with `r = 0`, `s = 0 + 1`.
  have hanti' : ((openTail A K δ 0 : S2) : E3) = -((openTail A K δ (0 + 1) : S2) : E3) := hanti
  exact antipodal_pair_excluded_of_strict hmix h01 h02 hanti'

/-- **The hemi-stuck dichotomy with the equator-tangent residue DISCHARGED (strict branch).**  On an
arm with `3 ≤ n + 1`, the equator-tangent input of `hemiStuck_dichotomy_of_glue` is no longer needed:
either some non-incident support vanishes, or the opened arm is `WeakConvexSphArm`.  In the
all-supports-strict case the tangent is produced internally by `equatorTangentExists_of_strictSupports`
via the short-arc edge `(0, 1)` (`shortArc_edge_zero_of_strict`). This kills the last equator residual. -/
theorem hemiStuck_dichotomy_tangentFree {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} {δ : ℝ} {h₀ : E3} (hn : 3 ≤ n + 1)
    (hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 ≤ sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    (hhemnn : ∀ r : Fin (n + 1), 0 ≤ (⟪h₀, ((openTail A K δ r : S2) : E3)⟫ : ℝ)) :
    (∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
        sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j) = 0) ∨
      WeakConvexSphArm (openTail A K δ) := by
  classical
  -- either some non-incident support vanishes (left branch) or all are strictly positive.
  by_cases hsome : ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j) = 0
  · exact Or.inl hsome
  · -- strict branch: build `hmix`, then discharge the tangent residue and apply the glue dichotomy.
    have hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j) := by
      intro i j hji hji1
      exact lt_of_le_of_ne (hsupp i j hji hji1) (fun heq => hsome ⟨i, j, hji, hji1, heq.symm⟩)
    have hshort := shortArc_edge_zero_of_strict hA hn hmix
    have htangent : EquatorTangentExists A K h₀ δ :=
      equatorTangentExists_of_strictSupports hmix hshort
    exact hemiStuck_dichotomy_of_glue hA hsupp hhemnn htangent

