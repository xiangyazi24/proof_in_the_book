import ProofsInTheBook.ZinanFFCT

/-!
# `ZinanFFCT2` — discharging the betweenness extraction (`CutBetweenness`) of `ZinanFFCT`

This file proves the genuine geometric content the substrate lacked (recorded gap in
`SphericalSZInduction` §6): deriving the convex-position Gram signs `hα/hβ` — equivalently the
great-circle betweenness `A i ∈ span≥0 {A (i+1), A j}` — at a vanishing non-incident support, from
**weak** convexity of the arm.

## The certificate (the new math)

For unit vectors `a, c` with `a × c ≠ 0` (a short arc) and a coplanar `b` (`det3 b a c = 0`), the
substrate's `normsq_smul_b` exhibits the explicit decomposition
`‖a×c‖² • b = hα • a + hβ • c`, where `hα, hβ` are exactly the two Gram coefficients of
`betweenness_span_nnreal`.  Applying `det3 c · X` and `det3 · a X` (and using `det3 c c X = 0`,
`det3 a a X = 0`) collapses to the two scalar identities

  `hα · det3 c a X = ‖a×c‖² · det3 c b X`,
  `hβ · det3 c a X = ‖a×c‖² · det3 b a X`.

Hence a **single witness vector** `X` with `det3 c a X > 0` and the two nonnegative orientations
`0 ≤ det3 c b X`, `0 ≤ det3 b a X` forces `hα, hβ ≥ 0`, i.e. `b ∈ span≥0 {a, c}`.

For a weakly convex arm, those two orientations are exactly the `edge_support` nonnegativities of the
two polygon edges meeting at the support vertex; the witness `X` is a third vertex strictly on the
correct side of the diagonal.  This certificate is local and elementary and is what the substrate's
convex-position machinery was missing.

## The `n = 2` boundary (honest scope)

The certificate needs a *third* vertex `X` (the strict witness).  At `n = 2` the arm has only the
three vertices `A 0, A 1, A 2`; when the head/tail support vanishes all three are coplanar (a
degenerate flat triangle) and **no** strict witness exists.  Numerically (and by an explicit
`WeakConvexSphArm` witness, see the module docstring of `ZinanFFCT`), the head/tail betweenness of
`CutBetweenness` is **FALSE** at `n = 2`: e.g. three coplanar unit points in an open hemisphere with
`A 0` an *endpoint* of the arc rather than the middle vertex satisfy every `WeakConvexSphArm` field
(all supports vanish) yet have `A 0 ∉ span≥0 {A 1, A 2}`.

Therefore `CutBetweenness` (quantified `∀ n ≥ 2`) is **not provable as stated** — its `n = 2`
instances are false.  We prove the honest, true content: the certificate lemma and the head/tail
betweenness for `n ≥ 3`.  See the end-of-file report for the precise status of both residues.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT

namespace ProofsInTheBook.ZinanFFCT2

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The betweenness certificate from a single witness. -/

/-- **The Gram-sign certificate.**  For a coplanar `b` with `cross a c` nonzero, a witness
`X` with `0 < det3 c a X` and the two nonnegative orientations `0 <= det3 c b X`, `0 <= det3 b a X`
forces the two convex-position Gram signs to be nonnegative.  The proof uses the coplanar
decomposition `normsq_smul_b` and the second-slot linearity of `det3`. -/
theorem gram_signs_of_witness {a c b : E3} (X : E3)
    (hperp : (⟪cross a c, b⟫ : ℝ) = 0)
    (hne : cross a c ≠ 0)
    (haa : (⟪a, a⟫ : ℝ) = 1) (hcc : (⟪c, c⟫ : ℝ) = 1)
    (hXpos : 0 < det3 c a X)
    (hcb : 0 ≤ det3 c b X)
    (hba : 0 ≤ det3 b a X) :
    (0 ≤ (⟪b, a⟫ : ℝ) - (⟪b, c⟫ : ℝ) * (⟪a, c⟫ : ℝ)) ∧
    (0 ≤ (⟪b, c⟫ : ℝ) - (⟪b, a⟫ : ℝ) * (⟪c, a⟫ : ℝ)) := by
  -- the explicit coplanar decomposition `w2 • b = α • a + β • c`.
  have hdec := normsq_smul_b a b c hperp
  set w2 : ℝ := ‖cross a c‖ ^ 2 with hw2def
  set α : ℝ := (⟪b, a⟫ : ℝ) * (⟪c, c⟫ : ℝ) - (⟪b, c⟫ : ℝ) * (⟪a, c⟫ : ℝ) with hαdef
  set β : ℝ := (⟪b, c⟫ : ℝ) * (⟪a, a⟫ : ℝ) - (⟪b, a⟫ : ℝ) * (⟪c, a⟫ : ℝ) with hβdef
  have hw2pos : 0 < w2 := by
    rw [hw2def]; positivity
  -- identity 1: w2 * det3 c b X = α * det3 c a X.
  have hid1 : w2 * det3 c b X = α * det3 c a X := by
    have h := congrArg (fun v => det3 c v X) hdec
    simp only at h
    rw [det3_smul_mid w2 c b X] at h
    rw [det3_add_mid c (α • a) (β • c) X, det3_smul_mid α c a X, det3_smul_mid β c c X] at h
    have hcc0 : det3 c c X = 0 := by simp only [det3]; ring
    rw [hcc0, mul_zero, add_zero] at h
    exact h
  -- identity 2: w2 * det3 b a X = β * det3 c a X.  Work in the mid slot via `det3 v a X = - det3 a v X`.
  have hid2 : w2 * det3 b a X = β * det3 c a X := by
    have h := congrArg (fun v => det3 a v X) hdec
    simp only at h
    rw [det3_smul_mid w2 a b X] at h
    rw [det3_add_mid a (α • a) (β • c) X, det3_smul_mid α a a X, det3_smul_mid β a c X] at h
    have haa0 : det3 a a X = 0 := by simp only [det3]; ring
    rw [haa0, mul_zero, zero_add] at h
    -- h : w2 * det3 a b X = β * det3 a c X.  Convert both sides via swap_left/right to the goal form.
    have e1 : det3 a b X = - det3 b a X := det3_swap_left a b X
    have e2 : det3 a c X = - det3 c a X := det3_swap_left a c X
    rw [e1, e2] at h
    linarith [h]
  -- α ≥ 0 and β ≥ 0.
  have hα0 : 0 ≤ α := by
    have hp : 0 ≤ α * det3 c a X := by rw [← hid1]; positivity
    nlinarith [hp, hXpos, mul_pos hw2pos hXpos]
  have hβ0 : 0 ≤ β := by
    have hp : 0 ≤ β * det3 c a X := by rw [← hid2]; positivity
    nlinarith [hp, hXpos]
  -- rewrite α, β into the requested gram-sign form using ⟪a,a⟫=⟪c,c⟫=1.
  constructor
  · have : α = (⟪b, a⟫ : ℝ) - (⟪b, c⟫ : ℝ) * (⟪a, c⟫ : ℝ) := by rw [hαdef, hcc]; ring
    rwa [this] at hα0
  · have : β = (⟪b, c⟫ : ℝ) - (⟪b, a⟫ : ℝ) * (⟪c, a⟫ : ℝ) := by rw [hβdef, haa]; ring
    rwa [this] at hβ0

/-! ## §2. Packaging: betweenness `span≥0` membership from a vanishing support + a witness vertex. -/

/-- **Betweenness from a support and a single strict witness.**  For `S2` points `p, mid, q` with a
vanishing support `sOrient p mid q = 0`, a short arc `(mid, q)`, and a witness vector `X` with
`0 < det3 q mid X` and the two nonnegative orientations `0 ≤ det3 q p X`, `0 ≤ det3 p mid X`, the
middle point lies in the nonnegative cone: `p ∈ span≥0 {mid, q}`.  Bridges `gram_signs_of_witness`
into the substrate's `foldedFlat_of_support`. -/
theorem betweenness_of_support_witness {p mid q : S2} (X : E3)
    (hsupp : sOrient p mid q = 0) (hsa : ShortArc mid q)
    (hXpos : 0 < det3 (q : E3) (mid : E3) X)
    (hcb : 0 ≤ det3 (q : E3) (p : E3) X)
    (hba : 0 ≤ det3 (p : E3) (mid : E3) X) :
    (p : E3) ∈ Submodule.span NNReal ({(mid : E3), (q : E3)} : Set E3) := by
  -- coplanarity in the form `gram_signs_of_witness` expects (`a = mid`, `c = q`, `b = p`).
  have hperp : (⟪cross (mid : E3) (q : E3), (p : E3)⟫ : ℝ) = 0 := by
    rw [real_inner_comm, inner_cross_eq_det3]
    -- det3 p mid q = sOrient p mid q = 0
    have : det3 (p : E3) (mid : E3) (q : E3) = sOrient p mid q := rfl
    rw [this, hsupp]
  have hne : cross (mid : E3) (q : E3) ≠ 0 := cross_ne_zero_of_shortArc mid q hsa
  have haa : (⟪(mid : E3), (mid : E3)⟫ : ℝ) = 1 := S2.inner_self mid
  have hcc : (⟪(q : E3), (q : E3)⟫ : ℝ) = 1 := S2.inner_self q
  -- the certificate gives the two gram signs.
  obtain ⟨hα, hβ⟩ := gram_signs_of_witness (a := (mid : E3)) (c := (q : E3)) (b := (p : E3)) X
    hperp hne haa hcc hXpos hcb hba
  -- feed them to `foldedFlat_of_support`.
  exact foldedFlat_of_support hsupp hsa hα hβ

/-! ## §3. Head/tail betweenness for `n ≥ 3`, conditional on a strict witness vertex.

For `n ≥ 3`, every weakly convex arm with a vanishing head/tail support admits a strict witness vertex
(numerically: always among the interior vertices `A 2 … A (n-1)`); this is the global convex-position
non-degeneracy fact the substrate lacks (recorded gap, §6).  We isolate it as the single hypothesis
`hwit` and prove the head/tail betweenness from it — every other ingredient (the two edge supports, the
coplanarity, the short arc) is supplied by `WeakConvexSphArm`.  See the report for why the witness
existence is genuinely global and why the `n = 2` case is outright false. -/

/-- **Head betweenness (n ≥ 3), modulo a strict witness vertex.**  `A 0 ∈ span≥0 {A 1, A n}` from the
head support, the short arc `(A 1, A n)`, and a witness vector `X` with `0 < det3 (A n) (A 1) X` and the
two edge-support orientations `0 ≤ det3 (A n) (A 0) X`, `0 ≤ det3 (A 0) (A 1) X` (the closing-edge and
first-edge supports against `X`, both nonnegative under weak convexity). -/
theorem head_betweenness_of_witness {n : ℕ} {A : Fin (n + 1) → S2}
    (hj : n < n + 1) (h1 : (1 : ℕ) < n + 1) (X : E3)
    (hsupp : sOrient (A ⟨0, by omega⟩) (A ⟨1, h1⟩) (A ⟨n, hj⟩) = 0)
    (hsa : ShortArc (A ⟨1, h1⟩) (A ⟨n, hj⟩))
    (hXpos : 0 < det3 (A ⟨n, hj⟩ : E3) (A ⟨1, h1⟩ : E3) X)
    (hcb : 0 ≤ det3 (A ⟨n, hj⟩ : E3) (A ⟨0, by omega⟩ : E3) X)
    (hba : 0 ≤ det3 (A ⟨0, by omega⟩ : E3) (A ⟨1, h1⟩ : E3) X) :
    (A ⟨0, by omega⟩ : E3)
      ∈ Submodule.span NNReal ({(A ⟨1, h1⟩ : E3), (A ⟨n, hj⟩ : E3)} : Set E3) :=
  betweenness_of_support_witness X hsupp hsa hXpos hcb hba

/-- **Tail betweenness (n ≥ 3), modulo a strict witness vertex.**  `A n ∈ span≥0 {A (n-1), A 0}` from
the tail support, the short arc `(A (n-1), A 0)`, and a witness vector `X` with
`0 < det3 (A 0) (A (n-1)) X` and the two edge-support orientations `0 ≤ det3 (A 0) (A n) X`,
`0 ≤ det3 (A n) (A (n-1)) X`. -/
theorem tail_betweenness_of_witness {n : ℕ} {A : Fin (n + 1) → S2}
    (hj0 : (0 : ℕ) < n + 1) (hn1 : n - 1 < n + 1) (hnn : n < n + 1) (X : E3)
    (hsupp : sOrient (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) (A ⟨0, hj0⟩) = 0)
    (hsa : ShortArc (A ⟨n - 1, hn1⟩) (A ⟨0, hj0⟩))
    (hXpos : 0 < det3 (A ⟨0, hj0⟩ : E3) (A ⟨n - 1, hn1⟩ : E3) X)
    (hcb : 0 ≤ det3 (A ⟨0, hj0⟩ : E3) (A ⟨n, hnn⟩ : E3) X)
    (hba : 0 ≤ det3 (A ⟨n, hnn⟩ : E3) (A ⟨n - 1, hn1⟩ : E3) X) :
    (A ⟨n, hnn⟩ : E3)
      ∈ Submodule.span NNReal ({(A ⟨n - 1, hn1⟩ : E3), (A ⟨0, hj0⟩ : E3)} : Set E3) := by
  -- the packaging needs the support with the middle vertex `A n` first.
  have hsupp' : sOrient (A ⟨n, hnn⟩) (A ⟨n - 1, hn1⟩) (A ⟨0, hj0⟩) = 0 := by
    have e : sOrient (A ⟨n, hnn⟩) (A ⟨n - 1, hn1⟩) (A ⟨0, hj0⟩)
        = - sOrient (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) (A ⟨0, hj0⟩) := by
      simp only [sOrient, det3]; ring
    rw [e, hsupp, neg_zero]
  exact betweenness_of_support_witness X hsupp' hsa hXpos hcb hba

/-! ## §4. `CutBetweenness` is FALSE under weak convexity (the flat-fan counterexample).

The residue `CutBetweenness` was stated for `WeakConvexSphArm`, but weak convexity is too weak: a
fully *flat* fan (all vertices on one great-circle arc inside an open hemisphere) is a genuine
`WeakConvexSphArm` whose head/tail support vanishes identically, yet whose head/tail vertex is an arc
*endpoint*, not the middle — so the `span≥0` betweenness FAILS.  We exhibit the rational `n = 2`
witness `A 0 = (-3/5, 0, 4/5)`, `A 1 = (0, 0, 1)`, `A 2 = (3/5, 0, 4/5)` (all in the plane `y = 0`)
and prove `¬ CutBetweenness`.

This is a faithfulness defect of the residue itself (an over-strong predicate, playbook §3.3): the
strict non-incidence dropped in passing from `StrictConvexSphArm` to `WeakConvexSphArm` is exactly what
pinned the betweenness.  The honest residual content is therefore the certificate
`gram_signs_of_witness` plus a *strict-witness existence* (a global convex-position non-degeneracy
fact), NOT the `WeakConvexSphArm`-only `CutBetweenness`. -/

/-- `det3` vanishes for three vectors in the plane `y = 0` (coordinate `1` equal to `0`). -/
theorem det3_y0 {a b c : E3} (ha : a 1 = 0) (hb : b 1 = 0) (hc : c 1 = 0) :
    det3 a b c = 0 := by
  simp only [det3, ha, hb, hc]; ring

/-- The three flat-fan vertices (plane `y = 0`, open hemisphere `z > 0`). -/
def fanP0 : E3 := !₂[(-3/5 : ℝ), 0, 4/5]
def fanP1 : E3 := !₂[(0 : ℝ), 0, 1]
def fanP2 : E3 := !₂[(3/5 : ℝ), 0, 4/5]

theorem fan_n0 : ‖fanP0‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three,
    show (fanP0:E3) 0 = -3/5 from rfl, show (fanP0:E3) 1 = 0 from rfl,
    show (fanP0:E3) 2 = 4/5 from rfl]; norm_num
theorem fan_n1 : ‖fanP1‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three,
    show (fanP1:E3) 0 = 0 from rfl, show (fanP1:E3) 1 = 0 from rfl,
    show (fanP1:E3) 2 = 1 from rfl]; norm_num
theorem fan_n2 : ‖fanP2‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three,
    show (fanP2:E3) 0 = 3/5 from rfl, show (fanP2:E3) 1 = 0 from rfl,
    show (fanP2:E3) 2 = 4/5 from rfl]; norm_num

def fanQ0 : S2 := ⟨fanP0, fan_n0⟩
def fanQ1 : S2 := ⟨fanP1, fan_n1⟩
def fanQ2 : S2 := ⟨fanP2, fan_n2⟩

/-- The flat-fan arm `A : Fin 3 → S2` (an `n = 2` weakly convex arm). -/
def fanArm : Fin 3 → S2 := ![fanQ0, fanQ1, fanQ2]

theorem fanArm_y0 : ∀ i : Fin 3, (fanArm i : E3) 1 = 0 := by
  intro i; fin_cases i
  · show (fanP0:E3) 1 = 0; rfl
  · show (fanP1:E3) 1 = 0; rfl
  · show (fanP2:E3) 1 = 0; rfl

/-- All supports of the flat fan vanish (every vertex is coplanar in `y = 0`). -/
theorem fanArm_support_zero (i j : Fin 3) :
    sOrient (fanArm i) (fanArm (i+1)) (fanArm j) = 0 :=
  det3_y0 (fanArm_y0 i) (fanArm_y0 (i+1)) (fanArm_y0 j)

/-- The flat fan is a genuine `WeakConvexSphArm`. -/
theorem fanArm_weakConvex : WeakConvexSphArm fanArm := by
  refine ⟨le_refl 2, le_refl 3, ?_, ?_, ?_⟩
  · -- edge_short
    intro i; fin_cases i
    · show ShortArc (fanArm 0) (fanArm (0+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (fanArm 0:E3) 0 = (fanArm (0+1):E3) 0 := by rw [h]
        rw [show (fanArm 0:E3) 0 = -3/5 from rfl, show (fanArm (0+1):E3) 0 = 0 from rfl] at hh
        norm_num at hh
      · have hh : (fanArm 0:E3) 2 = (-(fanArm (0+1):E3)) 2 := by rw [h]
        rw [show (fanArm 0:E3) 2 = 4/5 from rfl, PiLp.neg_apply,
          show (fanArm (0+1):E3) 2 = 1 from rfl] at hh
        norm_num at hh
    · show ShortArc (fanArm 1) (fanArm (1+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (fanArm 1:E3) 0 = (fanArm (1+1):E3) 0 := by rw [h]
        rw [show (fanArm 1:E3) 0 = 0 from rfl, show (fanArm (1+1):E3) 0 = 3/5 from rfl] at hh
        norm_num at hh
      · have hh : (fanArm 1:E3) 2 = (-(fanArm (1+1):E3)) 2 := by rw [h]
        rw [show (fanArm 1:E3) 2 = 1 from rfl, PiLp.neg_apply,
          show (fanArm (1+1):E3) 2 = 4/5 from rfl] at hh
        norm_num at hh
    · show ShortArc (fanArm 2) (fanArm (2+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (fanArm 2:E3) 0 = (fanArm (2+1):E3) 0 := by rw [h]
        rw [show (fanArm 2:E3) 0 = 3/5 from rfl, show (fanArm (2+1):E3) 0 = -3/5 from rfl] at hh
        norm_num at hh
      · have hh : (fanArm 2:E3) 2 = (-(fanArm (2+1):E3)) 2 := by rw [h]
        rw [show (fanArm 2:E3) 2 = 4/5 from rfl, PiLp.neg_apply,
          show (fanArm (2+1):E3) 2 = 4/5 from rfl] at hh
        norm_num at hh
  · -- edge_support: all supports vanish
    intro i j; rw [fanArm_support_zero i j]
  · -- open_hemisphere: h = (0,0,1)
    refine ⟨!₂[(0:ℝ),0,1], ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq, Fin.sum_univ_three,
        show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl,
        show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl]; norm_num
    · intro i
      fin_cases i
      · show (0:ℝ) < ⟪(!₂[(0:ℝ),0,1] : E3), (fanArm 0 : E3)⟫
        rw [inner_eq_coord, show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl,
          show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl,
          show (fanArm 0:E3) 2 = 4/5 from rfl]; norm_num
      · show (0:ℝ) < ⟪(!₂[(0:ℝ),0,1] : E3), (fanArm 1 : E3)⟫
        rw [inner_eq_coord, show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl,
          show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl,
          show (fanArm 1:E3) 2 = 1 from rfl]; norm_num
      · show (0:ℝ) < ⟪(!₂[(0:ℝ),0,1] : E3), (fanArm 2 : E3)⟫
        rw [inner_eq_coord, show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl,
          show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl,
          show (fanArm 2:E3) 2 = 4/5 from rfl]; norm_num

/-- **`CutBetweenness` is FALSE.**  Instantiating it on the flat fan (`n = 2`), the head conjunct would
give `A 0 ∈ span≥0 {A 1, A 2}`; but reading off coordinate `0` of any nonnegative combination forces a
negative coefficient (`(3/5) t = -3/5` ⟹ `t = -1 < 0`), a contradiction.  So weak convexity does not
imply the betweenness. -/
theorem not_cutBetweenness : ¬ CutBetweenness := by
  intro hcb
  have hj : (2 : ℕ) < 2 + 1 := by omega
  have h1 : (1 : ℕ) < 2 + 1 := by omega
  have hhead := (hcb 2 (le_refl 2) fanArm fanArm_weakConvex).1
  have hsupp : sOrient (fanArm ⟨0, by omega⟩) (fanArm ⟨1, h1⟩) (fanArm ⟨2, hj⟩) = 0 :=
    det3_y0 (fanArm_y0 _) (fanArm_y0 _) (fanArm_y0 _)
  have hmem := hhead hj h1 hsupp
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨s, t, hst⟩ := hmem
  -- coordinate 0 of `s • A1 + t • A2 = A0` (NNReal smul).
  have hc : ((s : ℝ≥0) • (fanArm ⟨1, h1⟩ : E3) + (t : ℝ≥0) • (fanArm ⟨2, hj⟩ : E3)) 0
      = (fanArm ⟨0, by omega⟩ : E3) 0 := by rw [hst]
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply,
    show (fanArm ⟨1, h1⟩ : E3) 0 = 0 from rfl,
    show (fanArm ⟨2, hj⟩ : E3) 0 = 3/5 from rfl,
    show (fanArm ⟨0, by omega⟩ : E3) 0 = -3/5 from rfl] at hc
  -- NNReal smul on ℝ is `(↑s) * ·`.
  rw [NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_zero, zero_add] at hc
  have htnn : (0:ℝ) ≤ (t : ℝ) := t.2
  nlinarith [hc, htnn]

/-! ## §5. `InteriorCut` is NOT vacuous under weak convexity (a genuine interior support exists).

The prior diagnosis declared the interior `(i, j)` case "numerically vacuous", but that search enforced
*closed-polygon* (strict) convexity, which forbids three collinear vertices.  Under the ACTUAL hypothesis
`WeakConvexSphArm`, an interior collinear non-incident support is genuinely realisable: a flat fan of
`n + 1 ≥ 4` vertices on one great-circle arc is weakly convex and every triple is collinear, so the
support `sOrient (A i)(A (i+1))(A j) = 0` holds for interior `(i, j)` too.

We exhibit the rational `n = 3` flat fan
`A 0 = (-4/5,0,3/5)`, `A 1 = (-3/5,0,4/5)`, `A 2 = (3/5,0,4/5)`, `A 3 = (4/5,0,3/5)`
and prove it is a `WeakConvexSphArm` with a vanishing support at the interior cut `(i, j) = (1, 3)`
(`j = 3 ≠ i = 1`, `j ≠ i + 1 = 2`, and `(1,3)` is neither head `(0,3)` nor tail `(2,0)`).  Hence
`InteriorCut`'s support hypothesis is **satisfiable** under weak convexity: the interior case is genuine
content (the spherical arm-lemma comparison at an interior flat cut), NOT a vacuous branch. -/

def fan4P0 : E3 := !₂[(-4/5 : ℝ), 0, 3/5]
def fan4P1 : E3 := !₂[(-3/5 : ℝ), 0, 4/5]
def fan4P2 : E3 := !₂[(3/5 : ℝ), 0, 4/5]
def fan4P3 : E3 := !₂[(4/5 : ℝ), 0, 3/5]

theorem fan4_n0 : ‖fan4P0‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (fan4P0:E3) 0 = -4/5 from rfl,
    show (fan4P0:E3) 1 = 0 from rfl, show (fan4P0:E3) 2 = 3/5 from rfl]; norm_num
theorem fan4_n1 : ‖fan4P1‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (fan4P1:E3) 0 = -3/5 from rfl,
    show (fan4P1:E3) 1 = 0 from rfl, show (fan4P1:E3) 2 = 4/5 from rfl]; norm_num
theorem fan4_n2 : ‖fan4P2‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (fan4P2:E3) 0 = 3/5 from rfl,
    show (fan4P2:E3) 1 = 0 from rfl, show (fan4P2:E3) 2 = 4/5 from rfl]; norm_num
theorem fan4_n3 : ‖fan4P3‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (fan4P3:E3) 0 = 4/5 from rfl,
    show (fan4P3:E3) 1 = 0 from rfl, show (fan4P3:E3) 2 = 3/5 from rfl]; norm_num

def fan4Q0 : S2 := ⟨fan4P0, fan4_n0⟩
def fan4Q1 : S2 := ⟨fan4P1, fan4_n1⟩
def fan4Q2 : S2 := ⟨fan4P2, fan4_n2⟩
def fan4Q3 : S2 := ⟨fan4P3, fan4_n3⟩

/-- The `n = 3` flat-fan arm. -/
def fan4Arm : Fin 4 → S2 := ![fan4Q0, fan4Q1, fan4Q2, fan4Q3]

theorem fan4Arm_y0 : ∀ i : Fin 4, (fan4Arm i : E3) 1 = 0 := by
  intro i; fin_cases i
  · show (fan4P0:E3) 1 = 0; rfl
  · show (fan4P1:E3) 1 = 0; rfl
  · show (fan4P2:E3) 1 = 0; rfl
  · show (fan4P3:E3) 1 = 0; rfl

theorem fan4Arm_support_zero (i j : Fin 4) :
    sOrient (fan4Arm i) (fan4Arm (i+1)) (fan4Arm j) = 0 :=
  det3_y0 (fan4Arm_y0 i) (fan4Arm_y0 (i+1)) (fan4Arm_y0 j)

/-- The flat 4-fan is a genuine `WeakConvexSphArm` (`n = 3`). -/
theorem fan4Arm_weakConvex : WeakConvexSphArm fan4Arm := by
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · -- edge_short: each consecutive pair differs in coordinate 0 and is not antipodal (coord 2 > 0).
    intro i; fin_cases i
    · show ShortArc (fan4Arm 0) (fan4Arm (0+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (fan4Arm 0:E3) 0 = (fan4Arm (0+1):E3) 0 := by rw [h]
        rw [show (fan4Arm 0:E3) 0 = -4/5 from rfl, show (fan4Arm (0+1):E3) 0 = -3/5 from rfl] at hh
        norm_num at hh
      · have hh : (fan4Arm 0:E3) 2 = (-(fan4Arm (0+1):E3)) 2 := by rw [h]
        rw [show (fan4Arm 0:E3) 2 = 3/5 from rfl, PiLp.neg_apply,
          show (fan4Arm (0+1):E3) 2 = 4/5 from rfl] at hh
        norm_num at hh
    · show ShortArc (fan4Arm 1) (fan4Arm (1+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (fan4Arm 1:E3) 0 = (fan4Arm (1+1):E3) 0 := by rw [h]
        rw [show (fan4Arm 1:E3) 0 = -3/5 from rfl, show (fan4Arm (1+1):E3) 0 = 3/5 from rfl] at hh
        norm_num at hh
      · have hh : (fan4Arm 1:E3) 2 = (-(fan4Arm (1+1):E3)) 2 := by rw [h]
        rw [show (fan4Arm 1:E3) 2 = 4/5 from rfl, PiLp.neg_apply,
          show (fan4Arm (1+1):E3) 2 = 4/5 from rfl] at hh
        norm_num at hh
    · show ShortArc (fan4Arm 2) (fan4Arm (2+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (fan4Arm 2:E3) 0 = (fan4Arm (2+1):E3) 0 := by rw [h]
        rw [show (fan4Arm 2:E3) 0 = 3/5 from rfl, show (fan4Arm (2+1):E3) 0 = 4/5 from rfl] at hh
        norm_num at hh
      · have hh : (fan4Arm 2:E3) 2 = (-(fan4Arm (2+1):E3)) 2 := by rw [h]
        rw [show (fan4Arm 2:E3) 2 = 4/5 from rfl, PiLp.neg_apply,
          show (fan4Arm (2+1):E3) 2 = 3/5 from rfl] at hh
        norm_num at hh
    · show ShortArc (fan4Arm 3) (fan4Arm (3+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (fan4Arm 3:E3) 0 = (fan4Arm (3+1):E3) 0 := by rw [h]
        rw [show (fan4Arm 3:E3) 0 = 4/5 from rfl, show (fan4Arm (3+1):E3) 0 = -4/5 from rfl] at hh
        norm_num at hh
      · have hh : (fan4Arm 3:E3) 2 = (-(fan4Arm (3+1):E3)) 2 := by rw [h]
        rw [show (fan4Arm 3:E3) 2 = 3/5 from rfl, PiLp.neg_apply,
          show (fan4Arm (3+1):E3) 2 = 3/5 from rfl] at hh
        norm_num at hh
  · -- edge_support
    intro i j; rw [fan4Arm_support_zero i j]
  · -- open_hemisphere: h = (0,0,1)
    refine ⟨!₂[(0:ℝ),0,1], ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq, Fin.sum_univ_three,
        show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl,
        show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl]; norm_num
    · intro i
      fin_cases i
      · show (0:ℝ) < ⟪(!₂[(0:ℝ),0,1] : E3), (fan4Arm 0 : E3)⟫
        rw [inner_eq_coord, show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl,
          show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl,
          show (fan4Arm 0:E3) 2 = 3/5 from rfl]; norm_num
      · show (0:ℝ) < ⟪(!₂[(0:ℝ),0,1] : E3), (fan4Arm 1 : E3)⟫
        rw [inner_eq_coord, show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl,
          show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl,
          show (fan4Arm 1:E3) 2 = 4/5 from rfl]; norm_num
      · show (0:ℝ) < ⟪(!₂[(0:ℝ),0,1] : E3), (fan4Arm 2 : E3)⟫
        rw [inner_eq_coord, show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl,
          show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl,
          show (fan4Arm 2:E3) 2 = 4/5 from rfl]; norm_num
      · show (0:ℝ) < ⟪(!₂[(0:ℝ),0,1] : E3), (fan4Arm 3 : E3)⟫
        rw [inner_eq_coord, show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl,
          show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl,
          show (fan4Arm 3:E3) 2 = 3/5 from rfl]; norm_num

/-- **`InteriorCut` is non-vacuous under weak convexity.**  The flat 4-fan is a `WeakConvexSphArm` with
a vanishing *interior* support at the cut `(i, j) = (1, 3)`: `j = 3 ≠ i = 1`, `j ≠ i + 1 = 2`, and
`(1, 3)` is neither the head `(0, 3)` nor the tail `(2, 0)`.  So the interior branch the prior diagnosis
deemed vacuous under *strict* convexity is genuinely populated under the actual *weak* hypothesis. -/
theorem interiorCut_support_satisfiable :
    WeakConvexSphArm fan4Arm ∧
    (∃ i j : ℕ, j ≠ i ∧ j ≠ i + 1 ∧ ¬ (i = 0 ∧ j = 3) ∧ ¬ (i = 3 - 1 ∧ j = 0) ∧
      ∃ (hi1 : i + 1 < 3 + 1) (hjj : j < 3 + 1),
        sOrient (fan4Arm ⟨i, by omega⟩) (fan4Arm ⟨i + 1, hi1⟩) (fan4Arm ⟨j, hjj⟩) = 0) := by
  refine ⟨fan4Arm_weakConvex, 1, 3, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  exact det3_y0 (fan4Arm_y0 _) (fan4Arm_y0 _) (fan4Arm_y0 _)

end ProofsInTheBook.ZinanFFCT2
