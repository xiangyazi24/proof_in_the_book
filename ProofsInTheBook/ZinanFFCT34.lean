import ProofsInTheBook.ZinanFFCT33

/-!
# `ZinanFFCT34` — discharging the antipodal and consecutive-triple equator configs

`ZinanFFCT33` reduced the hemi-stuck residual `EquatorTangentExists` to the strictly smaller named
residue `EquatorSpreadExcluded` (positivity of the equator-vertex sum), and tabulated the surviving
bad configurations of the equator set `Z = {r | ⟪h₀, A' r⟫ = 0}`, `A' := openTail A K δ`:

| equator configuration | FFCT33 status |
|---|---|
| `|Z| ≤ 1`                       | proven |
| `|Z| = 2`, non-antipodal        | proven |
| `|Z| = 2`, **antipodal**        | open |
| `|Z| ≥ 3`, three consecutive    | impossible (coplanar `det3 = 0`) |
| `|Z| ≥ 3`, **spread**           | open |

This module banks the **two support-sign levers** flagged in the report's two-lever attack sketch.
Both live in the *strict-support* branch of FFCT30's hemi-stuck dichotomy
(`hemiStuck_dichotomy_of_glue`'s `by_cases hsome` right branch), where every non-incident support is
**strictly** positive (`hmix : ∀ i j, j ≠ i → j ≠ i+1 → 0 < sOrient (A' i) (A' (i+1)) (A' j)`). The
levers are def-independent of `ShortArc`: they exploit only the vanishing of the relevant `det3`.

## What this module BANKS (axiom-free, no `sorry`, clean-3)

### §1 The antipodal `det3` algebra (pure coordinate `ring`)
`det3_antipodal_third_eq_zero` : `det3 x y (-x) = 0` (a column repeated up to sign). Hence
`sOrient_antipodal_third_eq_zero` : if `(v_r : E3) = -(v_s : E3)` then
`sOrient v_s v_{s+1} v_r = 0`.

### §2 LEVER 1 — the antipodal equator pair is killed by strict supports
`antipodal_pair_excluded_of_strict` : in the strict-support branch, an antipodal equator pair
`v_r = -v_s` with `r ≠ s`, `r ≠ s+1` forces `0 < sOrient v_s v_{s+1} v_r = 0` — contradiction. (No
hypothesis on `r` vs `s` beyond non-incidence; the antipodal `det3` vanishing is identical.)

### §3 LEVER 2a — the consecutive equator pair with a third member is killed by strict supports
`equator_consecutive_triple_excluded_of_strict` : if a consecutive pair `(k, k+1)` AND a third index
`m` (`m ≠ k`, `m ≠ k+1`) all lie on the `h₀`-equator, then all three are `⟂ h₀`, so
`det3 (A' k) (A' (k+1)) (A' m) = 0` (`ZinanFFCT33.det3_zero_of_three_on_equator`); but strict supports
give `0 < sOrient (A' k) (A' (k+1)) (A' m)` — contradiction. So in the strict branch the equator set
contains **no consecutive pair together with any third member**.

### §4 The strict-branch consequence
`equator_strict_branch_structure` packages the two levers: in the strict-support branch, the equator
set has **no antipodal pair** and **no consecutive pair coexisting with a third member**. This is the
exact structural residue handed to the final 2D-convexity wave (the spread config: pairwise
non-antipodal, pairwise non-consecutive, `|Z| ≥ 3`).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT30 ProofsInTheBook.ZinanFFCT33

namespace ProofsInTheBook.ZinanFFCT34

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The antipodal `det3` algebra.

When the third argument of `det3` is the negative of the first, the determinant vanishes identically:
`det3 x y (-x) = 0` (the `3 × 3` determinant has a repeated column up to sign). This is pure coordinate
algebra closed by `ring` after `PiLp.neg_apply`, and is the def-independent core of LEVER 1. -/

/-- **Antipodal third column vanishing.**  For any `x y : E3`, `det3 x y (-x) = 0`. -/
theorem det3_antipodal_third_eq_zero (x y : E3) : det3 x y (-x) = 0 := by
  simp only [det3, PiLp.neg_apply]; ring

/-- **Antipodal support vanishing.**  If the third vertex is the antipode of the first
(`(c : E3) = -(a : E3)`), then `sOrient a b c = 0`. -/
theorem sOrient_antipodal_third_eq_zero {a b c : S2} (h : (c : E3) = -(a : E3)) :
    sOrient a b c = 0 := by
  rw [sOrient, h, det3_antipodal_third_eq_zero]

/-! ## §2. LEVER 1 — the antipodal equator pair.

In the strict-support branch every non-incident support is strictly positive. An antipodal equator pair
`v_r = -v_s` (`r ≠ s`, `r ≠ s+1`) gives the non-incident support `sOrient (A' s) (A' (s+1)) (A' r)`,
which by §1 is *identically* `0` because `A' r` is the antipode of `A' s`. Strict positivity then reads
`0 < 0` — contradiction. The antipodal pair is impossible in this branch. -/

/-- **LEVER 1 — antipodal equator pair excluded by strict supports.**  In the all-supports-strict
branch (`hmix`), if two opened-arm vertices `A' r`, `A' s` are antipodal (`(A' r : E3) = -(A' s : E3)`)
with `r ≠ s` and `r ≠ s + 1`, then `False`: the non-incident support `sOrient (A' s) (A' (s+1)) (A' r)`
vanishes identically (the antipodal `det3`), contradicting its strict positivity. -/
theorem antipodal_pair_excluded_of_strict {n : ℕ} {A : Fin (n + 1) → S2} {K : Fin (n + 1)} {δ : ℝ}
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    {r s : Fin (n + 1)} (hrs : r ≠ s) (hrs1 : r ≠ s + 1)
    (hanti : ((openTail A K δ r : S2) : E3) = -((openTail A K δ s : S2) : E3)) :
    False := by
  have hzero : sOrient (openTail A K δ s) (openTail A K δ (s + 1)) (openTail A K δ r) = 0 :=
    sOrient_antipodal_third_eq_zero hanti
  have hpos : 0 < sOrient (openTail A K δ s) (openTail A K δ (s + 1)) (openTail A K δ r) :=
    hmix s r hrs hrs1
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

/-! ## §3. LEVER 2a — the consecutive equator pair with a third member.

Three vertices all on the `h₀`-equator are coplanar (`det3 = 0`, `ZinanFFCT33`). If two of them are a
*consecutive* arm pair `(k, k+1)` — the only equator edge the no-3-consecutive structure permits — then
any third equator vertex `m` (non-incident to that edge) is the third argument of the *consecutive*
support `sOrient (A' k) (A' (k+1)) (A' m)`, whose `det3` vanishes by coplanarity; strict supports force
`0 < 0`. So the equator set contains no consecutive pair together with any third member. -/

/-- **LEVER 2a — consecutive equator pair plus a third member excluded by strict supports.**  In the
all-supports-strict branch (`hmix`), if a consecutive pair `(A' k, A' (k+1))` and a further vertex `A' m`
(`m ≠ k`, `m ≠ k + 1`) all lie on the `h₀`-equator (`h₀ ≠ 0`), then `False`: the three are coplanar so
`sOrient (A' k) (A' (k+1)) (A' m) = det3 = 0`, contradicting strict positivity. -/
theorem equator_consecutive_triple_excluded_of_strict {n : ℕ} {A : Fin (n + 1) → S2}
    {K : Fin (n + 1)} {δ : ℝ}
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    {h₀ : E3} (hh0 : h₀ ≠ 0) {k m : Fin (n + 1)} (hmk : m ≠ k) (hmk1 : m ≠ k + 1)
    (hek : (⟪h₀, ((openTail A K δ k : S2) : E3)⟫ : ℝ) = 0)
    (hek1 : (⟪h₀, ((openTail A K δ (k + 1) : S2) : E3)⟫ : ℝ) = 0)
    (hem : (⟪h₀, ((openTail A K δ m : S2) : E3)⟫ : ℝ) = 0) :
    False := by
  have hcol : det3 ((openTail A K δ k : S2) : E3) ((openTail A K δ (k + 1) : S2) : E3)
      ((openTail A K δ m : S2) : E3) = 0 :=
    det3_zero_of_three_on_equator hh0 hek hek1 hem
  have hpos : 0 < sOrient (openTail A K δ k) (openTail A K δ (k + 1)) (openTail A K δ m) :=
    hmix k m hmk hmk1
  rw [sOrient, hcol] at hpos
  exact lt_irrefl _ hpos

/-! ## §4. The strict-branch structural residue.

Packaging the two levers: in the strict-support branch of the hemi-stuck dichotomy, the equator set
`Z` (FFCT33's `equatorSet`) has

* **no antipodal pair** (LEVER 1), and
* **no consecutive pair coexisting with a third member** (LEVER 2a).

This is the exact, strictly-smaller structural residue that the final 2D-convexity wave consumes: the
only surviving spread configuration is `|Z| ≥ 3`, pairwise non-antipodal, with no consecutive pair
involved in any triple (so the equator vertices are genuinely scattered on the circle). -/

/-- **No antipodal pair in the equator set (strict branch).**  Restatement of LEVER 1 against FFCT33's
`equatorSet` membership predicate. -/
theorem equatorSet_no_antipodal_pair_of_strict {n : ℕ} {A : Fin (n + 1) → S2} {K : Fin (n + 1)}
    {h₀ : E3} {δ : ℝ}
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    {r s : Fin (n + 1)} (_hr : equatorSet A K h₀ δ r) (_hs : equatorSet A K h₀ δ s)
    (hrs : r ≠ s) (hrs1 : r ≠ s + 1)
    (hanti : ((openTail A K δ r : S2) : E3) = -((openTail A K δ s : S2) : E3)) :
    False :=
  antipodal_pair_excluded_of_strict hmix hrs hrs1 hanti

/-- **No consecutive equator pair with a third member (strict branch).**  Restatement of LEVER 2a
against FFCT33's `equatorSet`: if `k`, `k+1`, and a non-incident `m` are all in the equator set, the
strict supports are contradicted. -/
theorem equatorSet_no_consecutive_triple_of_strict {n : ℕ} {A : Fin (n + 1) → S2} {K : Fin (n + 1)}
    {h₀ : E3} (hh0 : h₀ ≠ 0) {δ : ℝ}
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    {k m : Fin (n + 1)} (hk : equatorSet A K h₀ δ k) (hk1 : equatorSet A K h₀ δ (k + 1))
    (hm : equatorSet A K h₀ δ m) (hmk : m ≠ k) (hmk1 : m ≠ k + 1) :
    False :=
  equator_consecutive_triple_excluded_of_strict hmix hh0 hmk hmk1 hk hk1 hm

end ProofsInTheBook.ZinanFFCT34
