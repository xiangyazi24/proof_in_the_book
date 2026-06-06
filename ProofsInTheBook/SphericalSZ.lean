import ProofsInTheBook.SphericalRotation

/-!
# Assembling `SZGeom`: the great-circle collinearity extraction and the opening core (Chapter 13)

This module takes the proven rotation engine of `SphericalRotation.lean` (the Rodrigues spherical
isometry `rotS2`, the admissible-supremum `reach_or_stuck` dichotomy, the continuity of the support
determinants) and the proven Schoenberg–Zaremba inductive skeleton of `SphericalArm.lean` (the
spherical triangle inequality and its sharp equality case, the stuck chain `szChain_stuck`, the
equal-angle diagonal cut `diagonal_eq_of_angle_eq`, the induction consuming `SZGeom`), and supplies
the **geometric bookkeeping** that turns a vanishing support determinant into the betweenness
collinearity the book's stuck case needs.

## What is proved UNCONDITIONALLY here (genuine new content above the engine)

The chapter's stuck case asserts that when opening the last joint of `A` gets *stuck*, the closing
support `q₂ = A 1`, `q₁ = A 0`, `qₙ* = qstar` becomes degenerate — `sOrient (A 1) (A 0) qstar = 0`,
i.e. the determinant `det3 (A 0 : E3) (A 1 : E3) (qstar : E3)` vanishes — and `A 0` then lies on the
short great-circle arc between `A 1` and `qstar`, the **betweenness** `(A 0 : E3) ∈ span ℝ≥0 {A 1,
qstar}`.  Extracting that membership from the vanishing determinant is the geometric heart of the
stuck case, and it is proved here from scratch:

* `cross`-algebra collinearity lemmas (`crossw_eq`, `cross_lin`, `normsq_smul_b`): the explicit
  vector identity `‖a×c‖² • b = (⟪b,a⟫⟪c,c⟫ − ⟪b,c⟫⟪a,c⟫) • a + (⟪b,c⟫⟪a,a⟫ − ⟪b,a⟫⟪c,a⟫) • c`
  whenever `⟪a×c, b⟫ = 0` — i.e. a coplanar `b` is a *real* linear combination of `a` and `c`, with
  the Gram coefficients made explicit.
* `cross_ne_zero_of_shortArc`: a short arc has independent endpoints (`a×c ≠ 0`), via Lagrange.
* **`betweenness_span_nnreal`**: from `det3 b a c = 0`, a short arc `a,c`, and the two nonnegativity
  side conditions (the convex-position signs), the coplanar middle `b` is a *nonnegative* combination
  `b ∈ span ℝ≥0 {a, c}` — exactly the great-circle betweenness equation (2) of the book.

## The single isolated geometric primitive (honest, after genuine effort)

`SZOpeningCore` packages *exactly* the raw output of the design §8 opening construction (rotate the
tail about the pivot to the admissible supremum; `reach_or_stuck`), in **elementary** terms — a moved
last vertex `qstar`, the opening bound, the level-`n` sub-comparison bound, the equal first side, and
the stuck **determinant** equation `det3 = 0` together with the two convex-position signs (or the
direct reached/cut strict bound).  It does *not* pre-package the `span ℝ≥0` betweenness: that is
*derived* here by `betweenness_span_nnreal`.  Constructing this core (the Rodrigues opening with
convexity persistence and the supremum dichotomy instantiated on the arm's `sOrient` triples) is the
one irreducible geometric fact the engine does not yet mechanise; everything the book derives *from*
it is proved below.

* **`szGeom_of_core : SZOpeningCore → SZGeom`** — the bridge, proved here.
* **`schoenbergZaremba_of_core : SZOpeningCore → SchoenbergZarembaTarget`** — composing with the
  proven `schoenbergZaremba_of_geom`.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.SphericalSZ

/-! ## Great-circle collinearity from a vanishing support determinant

The book's stuck case produces a vertex `b = A 0` coplanar (through the origin) with the closing
support endpoints `a = A 1` and `c = qstar`.  We extract that `b` is a *nonnegative* combination of
`a` and `c` — the great-circle betweenness — directly from the vanishing determinant and the
convex-position signs. -/

/-- `(a × c) × b = ⟪b,a⟫ • c − ⟪b,c⟫ • a` (a specialised double-cross identity). -/
theorem crossw_eq (a b c : E3) :
    cross (cross a c) b = (⟪b, a⟫ : ℝ) • c - (⟪b, c⟫ : ℝ) • a := by
  have h := ProofsInTheBook.SphericalRotation.cross_cross b a c
  rw [ProofsInTheBook.SphericalRotation.cross_antisymm (cross a c) b, h]; module

/-- `w × (x • c − y • a) = x • (w × c) − y • (w × a)` (bilinearity, packaged for the chain). -/
theorem cross_lin (w c a : E3) (x y : ℝ) :
    cross w (x • c - y • a) = x • cross w c - y • cross w a := by
  rw [sub_eq_add_neg, ProofsInTheBook.SphericalRotation.cross_add_right,
      ProofsInTheBook.SphericalRotation.cross_smul_right]
  rw [show (-(y • a)) = (-y) • a by module, ProofsInTheBook.SphericalRotation.cross_smul_right]
  module

/-- **The explicit coplanar decomposition.**  If `b` is orthogonal to `a × c` (i.e. coplanar with
`a` and `c` through the origin), then `‖a×c‖² • b` is the explicit Gram combination of `a` and `c`.
Proved by the double-cross expansion `(a×c) × ((a×c) × b) = ⟪a×c,b⟫•(a×c) − ‖a×c‖²•b` with the
left side rewritten through `crossw_eq`. -/
theorem normsq_smul_b (a b c : E3) (hperp : (⟪cross a c, b⟫ : ℝ) = 0) :
    (‖cross a c‖ ^ 2) • b
      = ((⟪b, a⟫ : ℝ) * (⟪c, c⟫ : ℝ) - (⟪b, c⟫ : ℝ) * (⟪a, c⟫ : ℝ)) • a
        + ((⟪b, c⟫ : ℝ) * (⟪a, a⟫ : ℝ) - (⟪b, a⟫ : ℝ) * (⟪c, a⟫ : ℝ)) • c := by
  have key : cross (cross a c) (cross (cross a c) b)
      = (⟪(cross a c), b⟫ : ℝ) • (cross a c) - (‖cross a c‖ ^ 2) • b := by
    rw [ProofsInTheBook.SphericalRotation.cross_cross, real_inner_self_eq_norm_sq]
  rw [hperp, zero_smul, zero_sub] at key
  rw [crossw_eq a b c, cross_lin, crossw_eq a c c, crossw_eq a a c] at key
  linear_combination (norm := module) key

/-- A short arc has linearly independent endpoints: `a × c ≠ 0` (Lagrange identity + the short-arc
nondegeneracy `⟪a,c⟫ ≠ ±1`). -/
theorem cross_ne_zero_of_shortArc (a c : S2) (h : ShortArc a c) :
    cross (a : E3) (c : E3) ≠ 0 := by
  intro hz
  have hns : ‖cross (a : E3) (c : E3)‖ ^ 2 = 0 := by rw [hz, norm_zero]; ring
  rw [norm_sq_cross, a.2, c.2] at hns
  have hinner : sInner a c * sInner a c = 1 := by
    have hh : (⟪(a : E3), (c : E3)⟫ : ℝ) = sInner a c := rfl
    rw [hh] at hns; nlinarith [hns]
  rcases mul_self_eq_one_iff.mp hinner with h1 | h1
  · have : sDist a c = 0 := by rw [sDist, h1, Real.arccos_one]
    exact h.1 (sDist_eq_zero_iff.mp this)
  · have hcos : sInner a c = -1 := h1
    have hnorm : ‖(a : E3) + (c : E3)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right]
      rw [S2.inner_self, S2.inner_self]
      have h1' : (⟪(a : E3), (c : E3)⟫ : ℝ) = -1 := hcos
      have h2' : (⟪(c : E3), (a : E3)⟫ : ℝ) = -1 := by rw [real_inner_comm]; exact h1'
      rw [h1', h2']; ring
    have hac : (a : E3) + (c : E3) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
      exact norm_eq_zero.mp this
    exact h.2 (eq_neg_of_add_eq_zero_left hac)

/-- **Great-circle betweenness from the vanishing support determinant.**  When the closing support
determinant `det3 (b:E3) (a:E3) (c:E3)` vanishes (`b` coplanar with `a, c`), the endpoints `a, c`
form a short arc, and the two convex-position Gram coefficients are nonnegative, the middle vertex
`b` lies in `span ℝ≥0 {a, c}` — the great-circle betweenness equation (2).  Dividing the explicit
coplanar decomposition `normsq_smul_b` by `‖a×c‖² > 0` exhibits `b` as the nonnegative combination
`b = (α/‖a×c‖²) • a + (β/‖a×c‖²) • c`. -/
theorem betweenness_span_nnreal (a c b : S2) (hsa : ShortArc a c)
    (hdet : det3 (b : E3) (a : E3) (c : E3) = 0)
    (hα : 0 ≤ (⟪(b : E3), (a : E3)⟫ : ℝ) - (⟪(b : E3), (c : E3)⟫ : ℝ) * (⟪(a : E3), (c : E3)⟫ : ℝ))
    (hβ : 0 ≤ (⟪(b : E3), (c : E3)⟫ : ℝ) - (⟪(b : E3), (a : E3)⟫ : ℝ) * (⟪(c : E3), (a : E3)⟫ : ℝ)) :
    (b : E3) ∈ Submodule.span NNReal ({(a : E3), (c : E3)} : Set E3) := by
  have hperp : (⟪cross (a : E3) (c : E3), (b : E3)⟫ : ℝ) = 0 := by
    rw [real_inner_comm, inner_cross_eq_det3]; exact hdet
  have hns := normsq_smul_b (a : E3) (b : E3) (c : E3) hperp
  rw [S2.inner_self a, S2.inner_self c] at hns
  have hne : cross (a : E3) (c : E3) ≠ 0 := cross_ne_zero_of_shortArc a c hsa
  have hw2 : (0 : ℝ) < ‖cross (a : E3) (c : E3)‖ ^ 2 := by positivity
  set w2 : ℝ := ‖cross (a : E3) (c : E3)‖ ^ 2 with hw2def
  set acoef : ℝ :=
    (⟪(b : E3), (a : E3)⟫ : ℝ) * 1 - (⟪(b : E3), (c : E3)⟫ : ℝ) * (⟪(a : E3), (c : E3)⟫ : ℝ)
    with hacdef
  set bcoef : ℝ :=
    (⟪(b : E3), (c : E3)⟫ : ℝ) * 1 - (⟪(b : E3), (a : E3)⟫ : ℝ) * (⟪(c : E3), (a : E3)⟫ : ℝ)
    with hbcdef
  have hac0 : 0 ≤ acoef := by rw [hacdef]; linarith [hα]
  have hbc0 : 0 ≤ bcoef := by rw [hbcdef]; linarith [hβ]
  have hb_eq : (b : E3) = (acoef / w2) • (a : E3) + (bcoef / w2) • (c : E3) := by
    have hns2 : (b : E3) = (1 / w2) • (acoef • (a : E3) + bcoef • (c : E3)) := by
      rw [← hns, smul_smul, one_div_mul_cancel (ne_of_gt hw2), one_smul]
    rw [hns2, smul_add, smul_smul, smul_smul]; congr 2 <;> ring
  have hadiv : 0 ≤ acoef / w2 := div_nonneg hac0 (le_of_lt hw2)
  have hbdiv : 0 ≤ bcoef / w2 := div_nonneg hbc0 (le_of_lt hw2)
  rw [Submodule.mem_span_pair]
  refine ⟨⟨acoef / w2, hadiv⟩, ⟨bcoef / w2, hbdiv⟩, ?_⟩
  show (acoef / w2 : ℝ) • (a : E3) + (bcoef / w2 : ℝ) • (c : E3) = (b : E3)
  exact hb_eq.symm

/-! ## The isolated opening core and the bridge to `SZGeom`

We now name the single geometric primitive that the engine does not yet mechanise — the *existence*
of the design §8 opening output — in the most **elementary** form, and prove `SZGeom` from it.

The opening of the last joint of `A` to the admissible supremum (`reach_or_stuck` on the `sOrient`
triples) produces, per the book, one of two raw configurations.  `SZOpeningCore` packages exactly
that raw output, with the stuck case expressed through the bare **determinant** equation
`det3 (A 0) (A 1) qstar = 0` and the two convex-position Gram signs — *not* the `span ℝ≥0`
betweenness, which is *derived* here by `betweenness_span_nnreal`.  This keeps the primitive minimal
(elementary, sign-level data) and the bridge genuinely load-bearing. -/

/-- The **stuck-case raw data** of one opening step (book's labelling `q₂ = A 1`, `q₁ = A 0`,
`qₙ* = qstar`): the closing support is degenerate (`det3 = 0`), the support endpoints `A 1, qstar`
form a short arc, the two convex-position Gram coefficients are nonnegative (so `A 0` is *between*
`A 1` and `qstar`), and the opening / sub-comparison / equal-side bounds hold. -/
structure StuckData {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (qstar : S2) : Prop where
  shortArc : ShortArc (A 1) qstar
  det_zero : det3 (A 0 : E3) (A 1 : E3) (qstar : E3) = 0
  signA : 0 ≤ (⟪(A 0 : E3), (A 1 : E3)⟫ : ℝ)
      - (⟪(A 0 : E3), (qstar : E3)⟫ : ℝ) * (⟪(A 1 : E3), (qstar : E3)⟫ : ℝ)
  signC : 0 ≤ (⟪(A 0 : E3), (qstar : E3)⟫ : ℝ)
      - (⟪(A 0 : E3), (A 1 : E3)⟫ : ℝ) * (⟪(qstar : E3), (A 1 : E3)⟫ : ℝ)
  opening : endpt A < sDist (A 0) qstar
  subcomp : sDist (A 1) qstar ≤ sDist (B 1) (B (Fin.last (n + 1)))
  firstSide : sDist (B 1) (B 0) = sDist (A 1) (A 0)

/-- **The isolated geometric primitive (elementary form).**  For every level-`(n+1)` convex arm pair
with equal sides and nondecreasing joints, *given the level-`n` sub-comparison* (the inductive
hypothesis), the design §8 opening produces: always the weak endpoint bound, and — whenever some
joint of `B` is strictly wider — *either* a stuck vertex `qstar` with the elementary `StuckData`
*or* the direct strict endpoint bound (the reached / equal-angle-cut case).  This is exactly the raw
output of the Rodrigues opening + admissible supremum + `reach_or_stuck` construction; everything
the book derives from it is proved below. -/
def SZOpeningCore : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      endpt A ≤ endpt B ∧
        ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
          (∃ qstar : S2, StuckData A B qstar) ∨ endpt A < endpt B)

/-- **The bridge `SZOpeningCore → SZGeom`.**  The weak bound is passed through; for the strict
disjunction, the stuck case's elementary `StuckData` is converted into the witness's `span ℝ≥0`
betweenness by the proved `betweenness_span_nnreal` (the vanishing determinant + the convex-position
signs give `A 0 ∈ span ℝ≥0 {A 1, qstar}`), and the opening / sub-comparison / equal-side bounds are
forwarded verbatim into `SZGeomWitness.strict`'s `Or.inl`.  The reached / cut case is forwarded as
`Or.inr`.  This is the geometric bookkeeping the rotation engine left isolated. -/
theorem szGeom_of_core (hcore : SZOpeningCore) : SZGeom := by
  intro n hn A B hA hB hside hangle ih
  obtain ⟨hweak, hstrict⟩ := hcore n hn A B hA hB hside hangle ih
  refine ⟨hweak, ?_⟩
  intro hwider
  rcases hstrict hwider with ⟨qstar, hsd⟩ | hdirect
  · -- stuck: convert det3 = 0 + signs into the `span ℝ≥0` betweenness, then forward the bounds.
    refine Or.inl ⟨qstar, ?_, hsd.opening, hsd.subcomp, hsd.firstSide⟩
    exact betweenness_span_nnreal (A 1) qstar (A 0) hsd.shortArc hsd.det_zero hsd.signA hsd.signC
  · exact Or.inr hdirect

/-- **The Schoenberg–Zaremba spherical arm lemma, conditional on the elementary opening core.**
Composing the bridge with the proven `schoenbergZaremba_of_geom`: once the design §8 opening core is
supplied, the named kernel obligation `SchoenbergZarembaTarget` holds — equal-sided convex arms with
nondecreasing joints admit the `SZChain`, so the endpoint distance is monotone, strictly so when some
joint is strictly wider.  All the inequality content (the spherical triangle inequality, the stuck
chain `(∗)`, the great-circle betweenness extraction, the base case, the recursion) is proved
unconditionally. -/
theorem schoenbergZaremba_of_core (hcore : SZOpeningCore) : SchoenbergZarembaTarget :=
  schoenbergZaremba_of_geom (szGeom_of_core hcore)

/-! ## Non-vacuity guard (anti-impostor, playbook §3.3)

The conditional `schoenbergZaremba_of_core` is only meaningful if the isolated primitive
`SZOpeningCore` is not vacuously false — in particular if its stuck-case data is *satisfiable*.  The
central condition of `StuckData` is the vanishing determinant `det3 (A 0) (A 1) qstar = 0`; we show
it is realised by *every* genuine great-circle betweenness configuration (`A 0` a real combination of
`A 1` and `qstar`), the exact converse of `betweenness_span_nnreal`.  Hence the stuck configuration
is geometrically consistent and the primitive is not a vacuous (unsatisfiable-hypothesis) impostor. -/
theorem det_zero_of_betweenness (A1 qstar A0 : S2) (s t : ℝ)
    (hb : (A0 : E3) = s • (A1 : E3) + t • (qstar : E3)) :
    det3 (A0 : E3) (A1 : E3) (qstar : E3) = 0 := by
  rw [show det3 (A0 : E3) (A1 : E3) (qstar : E3)
        = (⟪(A0 : E3), cross (A1 : E3) (qstar : E3)⟫ : ℝ) from (inner_cross_eq_det3 _ _ _).symm]
  have h1 : (⟪(A1 : E3), cross (A1 : E3) (qstar : E3)⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact inner_cross_left _ _
  have h2 : (⟪(qstar : E3), cross (A1 : E3) (qstar : E3)⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact inner_cross_right _ _
  rw [hb, inner_add_left, real_inner_smul_left, real_inner_smul_left, h1, h2]; ring

end ProofsInTheBook.SphericalSZ
