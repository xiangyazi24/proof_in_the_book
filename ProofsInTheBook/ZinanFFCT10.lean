import ProofsInTheBook.ZinanFFCT9

/-!
# `ZinanFFCT10` — statement audit: `PlanarWeakNoflatStrictEdge` is FALSE as stated; the correction

## §3.3 finding (kernel-anchored here)

`ZinanFFCT8.PlanarWeakNoflatStrictEdge` — the isolated planar residue of the Ch13 route — is
**false** as stated.  The module header of `ZinanFFCT8` records it as "the true (numerically
verified) planar convexity fact"; the verification missed the failure because the failure set is
measure-zero (exact collinearity), invisible to generic numerical sampling.

**Counterexample (`n = 4`, rational, in the plane `⟪e₃,·⟫ = 1`):**
`f = [(0,0), (1,0), (1/2,1), (-1,0), (-1/2,0)]` (third coordinate `1`).
Every directed edge weakly supports every vertex, and all three interior joints are strict left
turns; yet `det3 (f 0) (f 1) (f 3) = 0` — vertex `3` lies on the *backward extension* of the first
edge — and `(i, j) = (0, 3) = (0, n-1)` is NOT excluded by the two carve-outs `¬(i=0 ∧ j=n)`,
`¬(i=n-1 ∧ j=0)`.  (Symmetrically `det3 (f 3) (f 4) (f 1) = 0`: vertex `1` on the *forward
extension* of the last edge.)  So the strict conclusion fails: the doubled-back chain is a genuine
planar witness, one that can never arise as the gnomonic image of a Cauchy arm — the abstraction
dropped the closure datum, and with it the truth of the statement.

## The repair (this file)

The antipodal/collinear degeneracies are *internally* excludable for every edge except the two
boundary ones:

* **`no_backward_collinear_of_pred`** (§2) — if `f j` sits on the backward extension of edge
  `(i, i+1)` with `i ≥ 1`, multilinearity gives
  `det3 (f (i-1)) (f i) (f j) = -t · det3 (f (i-1)) (f i) (f (i+1)) < 0` by the no-flat joint at
  `i`, contradicting the weak support of edge `(i-1, i)`.  So *behind*-collinearity is killed by
  the predecessor edge.
* **`no_forward_collinear_of_succ`** (§2) — if `f j` sits on the forward extension of edge
  `(i, i+1)` (beyond `f (i+1)`) with `i + 2 ≤ n`, then
  `det3 (f (i+1)) (f (i+2)) (f j) = -t · det3 (f i) (f (i+1)) (f (i+2)) < 0` by the no-flat joint
  at `i+1`, contradicting the weak support of edge `(i+1, i+2)`.  So *beyond*-collinearity is
  killed by the successor edge.

What remains genuinely underivable is exactly the boundary pair: *behind* the FIRST edge and
*beyond* the LAST edge — the two configurations realised by the counterexample.

**Second counterexample (§1b): injectivity is also required.**  The exact-retrace chain
`f = [(0,1), (0,0), (1,0), (0,1), (0,0)]` (`f 3 = f 0`, `f 4 = f 1`: the chain turns a full `2π`
and lands exactly on itself) satisfies `hweak`, `hnoflat`, AND both boundary exclusions, yet
`det3 (f 1) (f 2) (f 4) = 0` at the non-carved pair `(i, j) = (1, 4)`.  Vertex coincidence is a
distinct degeneracy from boundary collinearity, so the corrected residue must also assume the
family is injective.

§3 therefore states the corrected residue `PlanarWeakNoflatStrictEdgeCore`: the same statement
with three extra hypotheses — injectivity (`hinj`) and the two boundary-collinearity exclusions
(`hfirst`, `hlast`).  Both §1 anchors certify the extra hypotheses are individually non-removable.
The corrected residue is the one the gnomonic instance must (and, by the Cauchy-arm closure data,
can) supply.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT8 ProofsInTheBook.ZinanFFCT9

namespace ProofsInTheBook.ZinanFFCT10

set_option maxHeartbeats 1600000

/-! ## §0. Coordinate evaluation helpers for explicit `!₂[·,·,·]` vectors. -/

theorem coordE3_0 (a b c : ℝ) : (!₂[a, b, c] : E3) 0 = a := rfl
theorem coordE3_1 (a b c : ℝ) : (!₂[a, b, c] : E3) 1 = b := rfl
theorem coordE3_2 (a b c : ℝ) : (!₂[a, b, c] : E3) 2 = c := rfl

/-- Inner product of two explicit vectors. -/
theorem innerE3 (a b c x y z : ℝ) :
    (⟪(!₂[a, b, c] : E3), (!₂[x, y, z] : E3)⟫ : ℝ) = a * x + b * y + c * z := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [RCLike.inner_apply, conj_trivial,
    show (![a, b, c] : Fin 3 → ℝ) 0 = a from rfl,
    show (![a, b, c] : Fin 3 → ℝ) 1 = b from rfl,
    show (![a, b, c] : Fin 3 → ℝ) 2 = c from rfl,
    show (![x, y, z] : Fin 3 → ℝ) 0 = x from rfl,
    show (![x, y, z] : Fin 3 → ℝ) 1 = y from rfl,
    show (![x, y, z] : Fin 3 → ℝ) 2 = z from rfl]
  ring

/-- `det3` of three explicit vectors. -/
theorem det3E3 (a b c x y z u v w : ℝ) :
    det3 (!₂[a, b, c] : E3) (!₂[x, y, z] : E3) (!₂[u, v, w] : E3)
      = a * (y * w - z * v) - b * (x * w - z * u) + c * (x * v - y * u) := by
  simp only [det3,
    show (![a, b, c] : Fin 3 → ℝ) 0 = a from rfl,
    show (![a, b, c] : Fin 3 → ℝ) 1 = b from rfl,
    show (![a, b, c] : Fin 3 → ℝ) 2 = c from rfl,
    show (![x, y, z] : Fin 3 → ℝ) 0 = x from rfl,
    show (![x, y, z] : Fin 3 → ℝ) 1 = y from rfl,
    show (![x, y, z] : Fin 3 → ℝ) 2 = z from rfl,
    show (![u, v, w] : Fin 3 → ℝ) 0 = u from rfl,
    show (![u, v, w] : Fin 3 → ℝ) 1 = v from rfl,
    show (![u, v, w] : Fin 3 → ℝ) 2 = w from rfl]

/-! ## §1. The counterexample: `¬ PlanarWeakNoflatStrictEdge`. -/

/-- Counterexample vertex `f 0 = (0, 0, 1)`. -/
def cxP0 : E3 := !₂[(0 : ℝ), 0, 1]
/-- Counterexample vertex `f 1 = (1, 0, 1)`. -/
def cxP1 : E3 := !₂[(1 : ℝ), 0, 1]
/-- Counterexample vertex `f 2 = (1/2, 1, 1)`. -/
def cxP2 : E3 := !₂[(1/2 : ℝ), 1, 1]
/-- Counterexample vertex `f 3 = (-1, 0, 1)` — on the backward extension of edge `(0,1)`. -/
def cxP3 : E3 := !₂[(-1 : ℝ), 0, 1]
/-- Counterexample vertex `f 4 = (-1/2, 0, 1)`. -/
def cxP4 : E3 := !₂[(-1/2 : ℝ), 0, 1]
/-- The plane normal `h = e₃` (the family lives in the affine plane `⟪h,·⟫ = 1`). -/
def cxH : E3 := !₂[(0 : ℝ), 0, 1]

/-- The counterexample chain (`n = 4`). -/
def cxF : Fin 5 → E3 := ![cxP0, cxP1, cxP2, cxP3, cxP4]

/-- Index-eval for `cxF` on raw `Fin.mk` indices (robust under `interval_cases`). -/
theorem cxF_eval (k : ℕ) (hk : k < 5) :
    cxF ⟨k, hk⟩ = if k = 0 then cxP0 else if k = 1 then cxP1 else if k = 2 then cxP2
      else if k = 3 then cxP3 else cxP4 := by
  have h4 : k ≤ 4 := by omega
  interval_cases k <;> rfl

/-- **The planar residue of `ZinanFFCT8` is false as stated.**  The doubled-back chain `cxF`
satisfies the plane membership, all weak edge supports, and all strict interior joints, but
`det3 (f 0) (f 1) (f 3) = 0` refutes the strict non-incident conclusion at `(i, j) = (0, 3)`,
which the two boundary carve-outs do not exclude. -/
theorem planarWeakNoflatStrictEdge_false : ¬ PlanarWeakNoflatStrictEdge := by
  intro H
  have hplane : ∀ i : Fin 5, (⟪cxH, cxF i⟫ : ℝ) = 1 := by
    intro i
    fin_cases i
    · exact (innerE3 0 0 1 0 0 1).trans (by norm_num)
    · exact (innerE3 0 0 1 1 0 1).trans (by norm_num)
    · exact (innerE3 0 0 1 (1/2) 1 1).trans (by norm_num)
    · exact (innerE3 0 0 1 (-1) 0 1).trans (by norm_num)
    · exact (innerE3 0 0 1 (-1/2) 0 1).trans (by norm_num)
  have hweak : ∀ i j : ℕ, ∀ (hi1 : i + 1 < 5) (hj : j < 5),
      0 ≤ det3 (cxF ⟨i, by omega⟩) (cxF ⟨i + 1, hi1⟩) (cxF ⟨j, hj⟩) := by
    intro i j hi1 hj
    have hI : i ≤ 3 := by omega
    have hJ : j ≤ 4 := by omega
    rw [cxF_eval i (by omega), cxF_eval (i + 1) hi1, cxF_eval j hj]
    interval_cases i <;> interval_cases j <;>
      norm_num [cxP0, cxP1, cxP2, cxP3, cxP4, det3E3]
  have hnoflat : ∀ v : ℕ, 1 ≤ v → ∀ (hv1 : v + 1 < 5),
      0 < det3 (cxF ⟨v - 1, by omega⟩) (cxF ⟨v, by omega⟩) (cxF ⟨v + 1, hv1⟩) := by
    intro v hv hv1
    have hV : v ≤ 3 := by omega
    rw [cxF_eval (v - 1) (by omega), cxF_eval v (by omega), cxF_eval (v + 1) hv1]
    interval_cases v <;>
      norm_num [cxP0, cxP1, cxP2, cxP3, cxP4, det3E3]
  have hcontra :=
    H (n := 4) cxH cxF hplane hweak hnoflat 0 3
      (by omega) (by omega) (by omega) (by omega)
      (by rintro ⟨-, h3⟩; omega) (by rintro ⟨h0, -⟩; omega)
  have hzero : det3 (cxF ⟨0, by omega⟩) (cxF ⟨0 + 1, by omega⟩) (cxF ⟨3, by omega⟩) = 0 := by
    rw [cxF_eval 0 (by omega), cxF_eval (0 + 1) (by omega), cxF_eval 3 (by omega)]
    norm_num [cxP0, cxP1, cxP3, det3E3]
  rw [hzero] at hcontra
  exact lt_irrefl 0 hcontra

/-! ## §1b. The retrace counterexample: injectivity is not removable.

The exact-retrace chain (`f 3 = f 0`, `f 4 = f 1`) satisfies the weak supports, the strict interior
joints, and BOTH boundary-collinearity exclusions, yet fails the strict conclusion at `(1, 4)`.
This pins vertex coincidence as a separate, genuinely-missing hypothesis (the `2π`-wrap degeneracy:
the chain closes onto itself exactly, which no local-angle datum can see). -/

/-- Retrace vertex `g 0 = g 3 = (0, 1, 1)`. -/
def rxP0 : E3 := !₂[(0 : ℝ), 1, 1]
/-- Retrace vertex `g 1 = g 4 = (0, 0, 1)`. -/
def rxP1 : E3 := !₂[(0 : ℝ), 0, 1]
/-- Retrace vertex `g 2 = (1, 0, 1)`. -/
def rxP2 : E3 := !₂[(1 : ℝ), 0, 1]

/-- The retrace chain (`n = 4`): `[P0, P1, P2, P0, P1]`. -/
def rxF : Fin 5 → E3 := ![rxP0, rxP1, rxP2, rxP0, rxP1]

/-- Index-eval for `rxF` on raw `Fin.mk` indices. -/
theorem rxF_eval (k : ℕ) (hk : k < 5) :
    rxF ⟨k, hk⟩ = if k = 0 then rxP0 else if k = 1 then rxP1 else if k = 2 then rxP2
      else if k = 3 then rxP0 else rxP1 := by
  have h4 : k ≤ 4 := by omega
  interval_cases k <;> rfl

/-- **Without injectivity, even `hfirst`/`hlast` do not repair the residue.**  The retrace chain
satisfies plane membership, all weak edge supports, all strict interior joints, and both boundary
collinearity exclusions, yet `det3 (g 1) (g 2) (g 4) = 0` at the non-carved, non-incident pair
`(i, j) = (1, 4)`.  (Stated as the falsity of the once-repaired candidate, quantified exactly as
`PlanarWeakNoflatStrictEdgeCore` below but WITHOUT the injectivity hypothesis.) -/
theorem planarWeakNoflatStrictEdge_firstLast_insufficient :
    ¬ (∀ {n : ℕ} (h : E3) (f : Fin (n + 1) → E3),
      (∀ i : Fin (n + 1), (⟪h, f i⟫ : ℝ) = 1) →
      (∀ i j : ℕ, ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        0 ≤ det3 (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) (f ⟨j, hj⟩)) →
      (∀ v : ℕ, 1 ≤ v → ∀ (hv1 : v + 1 < n + 1),
        0 < det3 (f ⟨v - 1, by omega⟩) (f ⟨v, by omega⟩) (f ⟨v + 1, hv1⟩)) →
      (∀ (h1 : 1 < n + 1), ∀ j : ℕ, ∀ (hj : j < n + 1), ∀ t : ℝ, 0 < t →
        f ⟨j, hj⟩ ≠ f ⟨0, by omega⟩ - t • (f ⟨1, h1⟩ - f ⟨0, by omega⟩)) →
      (∀ j : ℕ, ∀ (hj : j < n + 1), ∀ t : ℝ, 0 < t →
        f ⟨j, hj⟩ ≠ f ⟨n, by omega⟩ + t • (f ⟨n, by omega⟩ - f ⟨n - 1, by omega⟩)) →
      ∀ i j : ℕ, j ≠ i → j ≠ i + 1 →
        ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        ¬ (i = 0 ∧ j = n) → ¬ (i = n - 1 ∧ j = 0) →
        0 < det3 (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) (f ⟨j, hj⟩)) := by
  intro H
  have hplane : ∀ i : Fin 5, (⟪cxH, rxF i⟫ : ℝ) = 1 := by
    intro i
    fin_cases i
    · exact (innerE3 0 0 1 0 1 1).trans (by norm_num)
    · exact (innerE3 0 0 1 0 0 1).trans (by norm_num)
    · exact (innerE3 0 0 1 1 0 1).trans (by norm_num)
    · exact (innerE3 0 0 1 0 1 1).trans (by norm_num)
    · exact (innerE3 0 0 1 0 0 1).trans (by norm_num)
  have hweak : ∀ i j : ℕ, ∀ (hi1 : i + 1 < 5) (hj : j < 5),
      0 ≤ det3 (rxF ⟨i, by omega⟩) (rxF ⟨i + 1, hi1⟩) (rxF ⟨j, hj⟩) := by
    intro i j hi1 hj
    have hI : i ≤ 3 := by omega
    have hJ : j ≤ 4 := by omega
    rw [rxF_eval i (by omega), rxF_eval (i + 1) hi1, rxF_eval j hj]
    interval_cases i <;> interval_cases j <;>
      norm_num [rxP0, rxP1, rxP2, det3E3]
  have hnoflat : ∀ v : ℕ, 1 ≤ v → ∀ (hv1 : v + 1 < 5),
      0 < det3 (rxF ⟨v - 1, by omega⟩) (rxF ⟨v, by omega⟩) (rxF ⟨v + 1, hv1⟩) := by
    intro v hv hv1
    have hV : v ≤ 3 := by omega
    rw [rxF_eval (v - 1) (by omega), rxF_eval v (by omega), rxF_eval (v + 1) hv1]
    interval_cases v <;>
      norm_num [rxP0, rxP1, rxP2, det3E3]
  -- the second-coordinate functional `w = (0, 1, 0)`: every vertex has `⟪w, ·⟫ ∈ {0, 1}`,
  -- the backward extension of the first edge has `⟪w, ·⟫ = 1 + t > 1`, and the forward
  -- extension of the last edge has `⟪w, ·⟫ = -t < 0`.
  have hwval : ∀ (k : ℕ) (hk : k < 5),
      (⟪(!₂[(0 : ℝ), 1, 0] : E3), rxF ⟨k, hk⟩⟫ : ℝ) = if k = 0 ∨ k = 3 then 1 else 0 := by
    intro k hk
    have h4 : k ≤ 4 := by omega
    rw [rxF_eval k hk]
    interval_cases k
    · norm_num; exact (innerE3 0 1 0 0 1 1).trans (by norm_num)
    · norm_num; exact (innerE3 0 1 0 0 0 1).trans (by norm_num)
    · norm_num; exact (innerE3 0 1 0 1 0 1).trans (by norm_num)
    · norm_num; exact (innerE3 0 1 0 0 1 1).trans (by norm_num)
    · norm_num; exact (innerE3 0 1 0 0 0 1).trans (by norm_num)
  have hfirst : ∀ (h1 : (1:ℕ) < 5), ∀ j : ℕ, ∀ (hj : j < 5), ∀ t : ℝ, 0 < t →
      rxF ⟨j, hj⟩ ≠ rxF ⟨0, by omega⟩ - t • (rxF ⟨1, h1⟩ - rxF ⟨0, by omega⟩) := by
    intro h1 j hj t ht heq
    have h1 := congrArg (fun v : E3 => (⟪(!₂[(0 : ℝ), 1, 0] : E3), v⟫ : ℝ)) heq
    simp only [inner_sub_right, inner_smul_right, real_inner_smul_right] at h1
    rw [hwval j hj, hwval 0 (by omega), hwval 1 (by omega)] at h1
    -- LHS ∈ {0, 1}; RHS = 1 - t·(0 - 1) = 1 + t > 1
    have : (if j = 0 ∨ j = 3 then (1:ℝ) else 0) ≤ 1 := by split <;> norm_num
    norm_num at h1
    split at h1 <;> linarith
  have hlast : ∀ j : ℕ, ∀ (hj : j < 5), ∀ t : ℝ, 0 < t →
      rxF ⟨j, hj⟩ ≠ rxF ⟨4, by omega⟩ + t • (rxF ⟨4, by omega⟩ - rxF ⟨4 - 1, by omega⟩) := by
    intro j hj t ht heq
    have h1 := congrArg (fun v : E3 => (⟪(!₂[(0 : ℝ), 1, 0] : E3), v⟫ : ℝ)) heq
    simp only [inner_add_right, inner_sub_right, inner_smul_right, real_inner_smul_right] at h1
    rw [hwval j hj, hwval 4 (by omega), hwval (4 - 1) (by omega)] at h1
    -- LHS ∈ {0, 1}; RHS = 0 + t·(0 - 1) = -t < 0
    norm_num at h1
    split at h1 <;> linarith
  have hcontra :=
    H (n := 4) cxH rxF hplane hweak hnoflat hfirst hlast 1 4
      (by omega) (by omega) (by omega) (by omega)
      (by rintro ⟨h0, -⟩; omega) (by rintro ⟨h0, -⟩; omega)
  have hzero : det3 (rxF ⟨1, by omega⟩) (rxF ⟨1 + 1, by omega⟩) (rxF ⟨4, by omega⟩) = 0 := by
    rw [rxF_eval 1 (by omega), rxF_eval (1 + 1) (by omega), rxF_eval 4 (by omega)]
    norm_num [rxP0, rxP1, rxP2, det3E3]
  rw [hzero] at hcontra
  exact lt_irrefl 0 hcontra

/-! ## §2. The interior collinearity kills (multilinearity + the no-flat joint).

`det3` is linear in each argument; for a collinear vertex `f j = f i - t • (f (i+1) - f i)`
(backward) or `f j = f (i+1) + t • (f (i+1) - f i)` (forward), the support seen by the adjacent
edge collapses to `-t` times the no-flat joint determinant — strictly negative, contradicting the
weak support.  These are the *internal* discharges of the antipodal care-point of
`ZinanFFCT9.forward_strict_support` for every non-boundary edge. -/

/-- `det3` with a third argument shifted along a vector: `det3 a b (c + w) = det3 a b c + det3 a b w`. -/
theorem det3_add_right (a b c w : E3) : det3 a b (c + w) = det3 a b c + det3 a b w := by
  simp only [det3, PiLp.add_apply]; ring

/-- `det3` with a smul third argument: `det3 a b (t • c) = t * det3 a b c`. -/
theorem det3_smul_right (a b c : E3) (t : ℝ) : det3 a b (t • c) = t * det3 a b c := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring

/-- `det3 a b (b + w) = det3 a b b + det3 a b w = det3 a b w + det3 a b b`; with `det3 a b b = 0`
this collapses shifted-along-`b` third arguments. -/
theorem det3_self_right (a b : E3) : det3 a b b = 0 := by
  simp only [det3]; ring

/-- **Backward-collinearity kill (predecessor edge).**  If `1 ≤ i` and the vertex `q` lies on the
backward extension of the edge `(p₀, p₁)` from its base `p₀` — `q = p₀ - t • (p₁ - p₀)`, `t > 0` —
while the predecessor edge `(pₚ, p₀)` weakly supports `q` and makes a strict left turn at `p₀`
(`0 < det3 pₚ p₀ p₁`), we get a contradiction. -/
theorem no_backward_collinear_kill {pp p0 p1 q : E3} {t : ℝ} (ht : 0 < t)
    (hq : q = p0 - t • (p1 - p0))
    (hsupp : 0 ≤ det3 pp p0 q) (hjoint : 0 < det3 pp p0 p1) : False := by
  have hval : det3 pp p0 q = -t * det3 pp p0 p1 := by
    subst hq
    have h1 : p0 - t • (p1 - p0) = p0 + (-t) • (p1 - p0) := by module
    rw [h1, det3_add_right, det3_smul_right]
    have h2 : det3 pp p0 (p1 - p0) = det3 pp p0 p1 - det3 pp p0 p0 := by
      have h3 : p1 - p0 + p0 = p1 := by module
      have := det3_add_right pp p0 (p1 - p0) p0
      rw [h3] at this; linarith
    rw [h2, det3_self_right]; ring
  nlinarith [hsupp, hjoint, hval]

/-- **Forward-collinearity kill (successor edge).**  If the vertex `q` lies on the forward
extension of the edge `(p₀, p₁)` beyond its far end `p₁` — `q = p₁ + t • (p₁ - p₀)`, `t > 0` —
while the successor edge `(p₁, p₂)` weakly supports `q` and the joint at `p₁` is a strict left
turn (`0 < det3 p₀ p₁ p₂`), we get a contradiction. -/
theorem no_forward_collinear_kill {p0 p1 p2 q : E3} {t : ℝ} (ht : 0 < t)
    (hq : q = p1 + t • (p1 - p0))
    (hsupp : 0 ≤ det3 p1 p2 q) (hjoint : 0 < det3 p0 p1 p2) : False := by
  -- det3 p1 p2 q = t * det3 p1 p2 (p1 - p0) = -t * det3 p1 p2 p0 = -t * det3 p0 p1 p2
  have hval : det3 p1 p2 q = -t * det3 p0 p1 p2 := by
    subst hq
    rw [det3_add_right, det3_smul_right]
    have h2 : det3 p1 p2 (p1 - p0) = det3 p1 p2 p1 - det3 p1 p2 p0 := by
      have h3 : p1 - p0 + p0 = p1 := by module
      have := det3_add_right p1 p2 (p1 - p0) p0
      rw [h3] at this; linarith
    have h4 : det3 p1 p2 p1 = 0 := by simp only [det3]; ring
    have h5 : det3 p1 p2 p0 = det3 p0 p1 p2 := by simp only [det3]; ring
    rw [h2, h4, h5]; ring
  nlinarith [hsupp, hjoint, hval]

/-! ## §3. The corrected planar residue.

The same statement as `PlanarWeakNoflatStrictEdge`, with the three genuinely-missing hypotheses
added: injectivity (`hinj`, §1b shows it is not removable), no vertex on the backward extension of
the FIRST edge (`hfirst`), and no vertex on the forward extension of the LAST edge (`hlast`) —
§1 shows the latter two are not removable.  §2 shows the boundary cases are the ONLY collinear
care-points not internally excluded.  The gnomonic instance must supply `hinj`/`hfirst`/`hlast`
from the Cauchy-arm closure data (`B`, `SameSides`, `JointLe`) — the datum the original
abstraction dropped. -/

/-- **(Corrected isolated planar residue.)**  `PlanarWeakNoflatStrictEdge` with injectivity and
the two boundary collinearity exclusions as explicit hypotheses. -/
def PlanarWeakNoflatStrictEdgeCore : Prop :=
  ∀ {n : ℕ} (h : E3) (f : Fin (n + 1) → E3),
    Function.Injective f →
    (∀ i : Fin (n + 1), (⟪h, f i⟫ : ℝ) = 1) →
    (∀ i j : ℕ, ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      0 ≤ det3 (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) (f ⟨j, hj⟩)) →
    (∀ v : ℕ, 1 ≤ v → ∀ (hv1 : v + 1 < n + 1),
      0 < det3 (f ⟨v - 1, by omega⟩) (f ⟨v, by omega⟩) (f ⟨v + 1, hv1⟩)) →
    -- `hfirst`: no vertex sits on the backward extension of the first edge
    (∀ (h1 : 1 < n + 1), ∀ j : ℕ, ∀ (hj : j < n + 1), ∀ t : ℝ, 0 < t →
      f ⟨j, hj⟩ ≠ f ⟨0, by omega⟩ - t • (f ⟨1, h1⟩ - f ⟨0, by omega⟩)) →
    -- `hlast`: no vertex sits on the forward extension of the last edge
    (∀ j : ℕ, ∀ (hj : j < n + 1), ∀ t : ℝ, 0 < t →
      f ⟨j, hj⟩ ≠ f ⟨n, by omega⟩ + t • (f ⟨n, by omega⟩ - f ⟨n - 1, by omega⟩)) →
    ∀ i j : ℕ, j ≠ i → j ≠ i + 1 →
      ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      ¬ (i = 0 ∧ j = n) → ¬ (i = n - 1 ∧ j = 0) →
      0 < det3 (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) (f ⟨j, hj⟩)

end ProofsInTheBook.ZinanFFCT10

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanFFCT10.planarWeakNoflatStrictEdge_false
#print axioms ProofsInTheBook.ZinanFFCT10.planarWeakNoflatStrictEdge_firstLast_insufficient
#print axioms ProofsInTheBook.ZinanFFCT10.no_backward_collinear_kill
#print axioms ProofsInTheBook.ZinanFFCT10.no_forward_collinear_kill
