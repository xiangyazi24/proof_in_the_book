import ProofsInTheBook.BricardConcrete

/-!
# The cube side of the Chapter 9 headline: the Kuhn decomposition of the unit cube

`BricardConcrete.lean` discharged the *regular-tetrahedron* side of the Chapter 9 headline
(`regularTet_cube_no_equidecomp_concreteP`), leaving the **cube side** as the honest residue: a
`SolidWithAngles` packaging a genuine tetrahedral subdivision of the cube, together with its
`EdgeSourceFaithful` faithfulness bridge.  The faithfulness bridge was flagged there as the *single
truly-resistant concrete fact*, because a generic simplicial subdivision has collinear-overlapping
raw edges, defeating the single-tetrahedron `EdgesNonOverlapping` route.

This module supplies that cube side **concretely and unconditionally**, using the **Kuhn
decomposition** (the canonical splitting of a cube into `6` order-simplices, one per permutation of
the coordinate axes).  The key geometric facts, all verified coordinate-by-coordinate:

* **The six Kuhn tetrahedra are affinely independent.**  Each is the orthoscheme chain
  `0 → e_{σ0} → e_{σ0}+e_{σ1} → (1,1,1)`; affine independence follows from an explicit triangular
  coordinate extraction.
* **Their interiors are pairwise disjoint.**  Each carrier lies in an order region
  `{x_{σ0} ≥ x_{σ1} ≥ x_{σ2}}`; two distinct permutations disagree on some coordinate pair, and the
  separating coordinate-difference functional confines the two interiors to opposite *open* halfspaces.
* **The raw edges do not overlap** (`EdgesNonOverlapping`).  Despite adjacent tetrahedra sharing
  edges, *every* raw edge of the Kuhn decomposition is a full segment between two cube vertices, and
  **no three distinct cube vertices are collinear** — so two distinct raw edges sharing two distinct
  points would exhibit three collinear cube vertices, a contradiction.  This is *exactly* why the
  single-tetrahedron `EdgesNonOverlapping` proof of `BricardConcrete.lean` extends to the whole Kuhn
  solid: the obstruction (collinear overlap) simply does not occur here.

Consequently the cube-side `EdgeSourceFaithful` bridge is discharged by
`edgeSourceFaithful_of_nonOverlapping` with **no remaining hypothesis**, and we assemble the
`SolidWithAngles` whose twelve external (cube) edges carry the dihedral angle `π/2`.

What this leaves for the Chapter 9 headline is *exactly* the two design-sanctioned isolated residues:
the `LocationData`/`PearlSectorModel` cross-section certificates (one per side) and the two
external-angle normalizations — nothing geometric remains undischarged on either solid.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped BigOperators Classical RealInnerProductSpace
open Set
open ProofsInTheBook.TetPearls
open ProofsInTheBook.TetDihedral
open ProofsInTheBook.PearlClassification
open ProofsInTheBook.Chapter09
open ProofsInTheBook.Bricard

namespace ProofsInTheBook.BricardCube

/-! ## Cube vertices and the "no three collinear" fact -/

/-- A point of `Pt3` is a **cube vertex** if each coordinate is `0` or `1`. -/
def IsCubeVertex (x : Pt3) : Prop := ∀ i : Fin 3, x i = 0 ∨ x i = 1

/-- **No three distinct cube vertices are collinear.**  If three pairwise-distinct cube vertices were
collinear, then (writing `v, w` as affine combinations `u + s • d`) the ratio `r = sw/sv` would have
to be `0`, `1`, or `-1` at the coordinate where `v` and `u` differ; the first two force `w = u` or
`w = v`, and `r = -1` forces a coordinate value `2` or `-1`, impossible for a cube vertex. -/
theorem no_three_cubeVerts_collinear {u v w : Pt3}
    (hu : IsCubeVertex u) (hv : IsCubeVertex v) (hw : IsCubeVertex w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ¬ Collinear ℝ ({u, v, w} : Set Pt3) := by
  intro hcol
  rw [collinear_iff_of_mem (show u ∈ ({u, v, w} : Set Pt3) by simp)] at hcol
  obtain ⟨d, hd⟩ := hcol
  obtain ⟨sv, hsv⟩ := hd v (by simp)
  obtain ⟨sw, hsw⟩ := hd w (by simp)
  have hvc : ∀ i, v i = sv * d i + u i := by
    intro i
    have := congrFun (congrArg (fun z : Pt3 => z.ofLp) hsv) i
    simpa only [vadd_eq_add, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] using this
  have hwc : ∀ i, w i = sw * d i + u i := by
    intro i
    have := congrFun (congrArg (fun z : Pt3 => z.ofLp) hsw) i
    simpa only [vadd_eq_add, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] using this
  have hex : ∃ a, v a ≠ u a := by
    by_contra hc; push_neg at hc; exact huv (by ext i; exact (hc i).symm)
  obtain ⟨a, ha⟩ := hex
  have hsvda : sv * d a ≠ 0 := by intro h; apply ha; rw [hvc a, h, zero_add]
  have hsv0 : sv ≠ 0 := fun h => hsvda (by rw [h]; ring)
  set r := sw / sv with hr
  have hwr : ∀ i, w i = u i + r * (v i - u i) := by
    intro i; rw [hwc i, hvc i, hr]; field_simp; ring
  have hva := hv a; have hua := hu a; have hwa := hwr a; have hwa1 := hw a
  rcases hua with hua0 | hua1 <;> rcases hva with hva0 | hva1
  · exact ha (by rw [hua0, hva0])
  · rw [hua0, hva1] at hwa
    rcases hwa1 with h0 | h1
    · have : r = 0 := by linarith [hwa, h0]
      apply huw; ext i; rw [hwr i, this]; ring
    · have : r = 1 := by linarith [hwa, h1]
      apply hvw; ext i; rw [hwr i, hvc i, this]; ring
  · rw [hua1, hva0] at hwa
    rcases hwa1 with h0 | h1
    · have : r = 1 := by linarith [hwa, h0]
      apply hvw; ext i; rw [hwr i, hvc i, this]; ring
    · have : r = 0 := by linarith [hwa, h1]
      apply huw; ext i; rw [hwr i, this]; ring
  · exact ha (by rw [hua1, hva1])

/-! ## Separating coordinate-difference functionals and disjoint interiors

For two distinct Kuhn order-simplices, some coordinate pair `(p, q)` is ordered oppositely on the
two carriers.  The coordinate-difference functional `coordDiff p q x = x p - x q` then confines one
carrier to `{f ≤ 0}` and the other to `{f ≥ 0}`; the *interiors* land in the *open* halfspaces
`{f < 0}` / `{f > 0}`, which are disjoint. -/

/-- The coordinate-difference functional `x ↦ x p - x q`. -/
def coordDiff (p q : Fin 3) (x : Pt3) : ℝ := x p - x q

theorem continuous_coordDiff (p q : Fin 3) : Continuous (coordDiff p q) := by
  unfold coordDiff; fun_prop

/-- The witness direction `e_p - e_q`, on which `coordDiff p q` evaluates to `2`. -/
def dirVec (p q : Fin 3) : Pt3 := EuclideanSpace.single p (1 : ℝ) - EuclideanSpace.single q (1 : ℝ)

theorem coordDiff_dirVec {p q : Fin 3} (hpq : p ≠ q) : coordDiff p q (dirVec p q) = 2 := by
  simp only [coordDiff, dirVec, PiLp.sub_apply, PiLp.single_apply]
  rw [if_neg hpq, if_neg (Ne.symm hpq)]; norm_num

/-- **Interior of a closed coordinate-difference halfspace lands in the open halfspace.**  If `x` is
in the topological interior of `{y | coordDiff p q y ≤ 0}`, then in fact `coordDiff p q x < 0`:
pushing `x` along `dirVec p q` (on which the functional increases) would otherwise exit the set. -/
theorem interior_coordDiff_le_subset_lt {p q : Fin 3} (hpq : p ≠ q) {x : Pt3}
    (hx : x ∈ interior {y : Pt3 | coordDiff p q y ≤ 0}) : coordDiff p q x < 0 := by
  have hmem : x ∈ {y : Pt3 | coordDiff p q y ≤ 0} := interior_subset hx
  have hx0 : coordDiff p q x ≤ 0 := hmem
  rcases lt_or_eq_of_le hx0 with h | h
  · exact h
  · exfalso
    have hnhds := isOpen_interior.mem_nhds hx
    set d := dirVec p q with hd
    have hg : Continuous (fun t : ℝ => x + t • d) := by fun_prop
    have hg0 : (fun t : ℝ => x + t • d) 0 = x := by simp
    have hpre : (fun t : ℝ => x + t • d) ⁻¹' (interior {y : Pt3 | coordDiff p q y ≤ 0}) ∈ nhds (0 : ℝ) := by
      apply hg.continuousAt.preimage_mem_nhds; simpa using hnhds
    rw [Metric.mem_nhds_iff] at hpre
    obtain ⟨ε, hε, hball⟩ := hpre
    have htmem : (ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]; simp only [sub_zero]
      rw [abs_of_pos (by linarith)]; linarith
    have hin0 := hball htmem
    rw [Set.mem_preimage] at hin0
    have hle := interior_subset hin0
    rw [Set.mem_setOf_eq] at hle
    have hcomp : coordDiff p q (x + (ε / 2) • d) = coordDiff p q x + (ε / 2) * coordDiff p q d := by
      simp only [coordDiff, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hcomp, ← h, coordDiff_dirVec hpq] at hle
    norm_num at hle; linarith

/-- **Disjoint interiors from a separating coordinate-difference functional.**  If carrier `CA` lies
in `{coordDiff p q ≤ 0}` and carrier `CB` lies in `{coordDiff p q ≥ 0}` (i.e. `{coordDiff q p ≤ 0}`),
then the interiors of `CA` and `CB` are disjoint. -/
theorem disjoint_interior_of_separating {p q : Fin 3} (hpq : p ≠ q) {CA CB : Set Pt3}
    (hA : CA ⊆ {y : Pt3 | coordDiff p q y ≤ 0}) (hB : CB ⊆ {y : Pt3 | coordDiff q p y ≤ 0}) :
    Disjoint (interior CA) (interior CB) := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  have hsubA : interior CA ⊆ interior {y : Pt3 | coordDiff p q y ≤ 0} := interior_mono hA
  have hsubB : interior CB ⊆ interior {y : Pt3 | coordDiff q p y ≤ 0} := interior_mono hB
  have h1 : coordDiff p q x < 0 := interior_coordDiff_le_subset_lt hpq (hsubA hxA)
  have h2 : coordDiff q p x < 0 := interior_coordDiff_le_subset_lt (Ne.symm hpq) (hsubB hxB)
  -- coordDiff p q x = - coordDiff q p x, so both < 0 is impossible.
  have : coordDiff p q x = - coordDiff q p x := by simp only [coordDiff]; ring
  rw [this] at h1; linarith

/-! ## The six Kuhn order-simplices

The Kuhn decomposition splits the unit cube `[0,1]³` into the six order-simplices, one for each
permutation `σ` of the coordinate axes: the orthoscheme chain
`0 → e_{σ0} → e_{σ0}+e_{σ1} → (1,1,1)`. We record the six explicit vertex maps and prove affine
independence of each by the (triangular) coordinate extraction. -/

/-- Vertex map of the Kuhn tetrahedron for permutation `(0,1,2)`. -/
def kv012 : Fin 4 → Pt3 := ![!₂[(0:ℝ),0,0], !₂[(1:ℝ),0,0], !₂[(1:ℝ),1,0], !₂[(1:ℝ),1,1]]
def kv021 : Fin 4 → Pt3 := ![!₂[(0:ℝ),0,0], !₂[(1:ℝ),0,0], !₂[(1:ℝ),0,1], !₂[(1:ℝ),1,1]]
def kv102 : Fin 4 → Pt3 := ![!₂[(0:ℝ),0,0], !₂[(0:ℝ),1,0], !₂[(1:ℝ),1,0], !₂[(1:ℝ),1,1]]
def kv120 : Fin 4 → Pt3 := ![!₂[(0:ℝ),0,0], !₂[(0:ℝ),1,0], !₂[(0:ℝ),1,1], !₂[(1:ℝ),1,1]]
def kv201 : Fin 4 → Pt3 := ![!₂[(0:ℝ),0,0], !₂[(0:ℝ),0,1], !₂[(1:ℝ),0,1], !₂[(1:ℝ),1,1]]
def kv210 : Fin 4 → Pt3 := ![!₂[(0:ℝ),0,0], !₂[(0:ℝ),0,1], !₂[(0:ℝ),1,1], !₂[(1:ℝ),1,1]]

theorem kv012_ai : AffineIndependent ℝ kv012 := by
  rw [affineIndependent_iff_of_fintype]
  intro w hsum hvec i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hvec
  have h0 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 0
  have h1 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 1
  have h2 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 2
  rw [Fin.sum_univ_four] at hsum
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_four, kv012, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val, Matrix.cons_val_fin_one, WithLp.ofLp_toLp] at h0 h1 h2
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    at h0 h1 h2
  have e0 : w 0 = 0 := by linarith
  have e1 : w 1 = 0 := by linarith
  have e2 : w 2 = 0 := by linarith
  have e3 : w 3 = 0 := by linarith
  fin_cases i <;> assumption

theorem kv021_ai : AffineIndependent ℝ kv021 := by
  rw [affineIndependent_iff_of_fintype]
  intro w hsum hvec i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hvec
  have h0 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 0
  have h1 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 1
  have h2 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 2
  rw [Fin.sum_univ_four] at hsum
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_four, kv021, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val, Matrix.cons_val_fin_one, WithLp.ofLp_toLp] at h0 h1 h2
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    at h0 h1 h2
  have e0 : w 0 = 0 := by linarith
  have e1 : w 1 = 0 := by linarith
  have e2 : w 2 = 0 := by linarith
  have e3 : w 3 = 0 := by linarith
  fin_cases i <;> assumption

theorem kv102_ai : AffineIndependent ℝ kv102 := by
  rw [affineIndependent_iff_of_fintype]
  intro w hsum hvec i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hvec
  have h0 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 0
  have h1 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 1
  have h2 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 2
  rw [Fin.sum_univ_four] at hsum
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_four, kv102, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val, Matrix.cons_val_fin_one, WithLp.ofLp_toLp] at h0 h1 h2
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    at h0 h1 h2
  have e0 : w 0 = 0 := by linarith
  have e1 : w 1 = 0 := by linarith
  have e2 : w 2 = 0 := by linarith
  have e3 : w 3 = 0 := by linarith
  fin_cases i <;> assumption

theorem kv120_ai : AffineIndependent ℝ kv120 := by
  rw [affineIndependent_iff_of_fintype]
  intro w hsum hvec i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hvec
  have h0 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 0
  have h1 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 1
  have h2 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 2
  rw [Fin.sum_univ_four] at hsum
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_four, kv120, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val, Matrix.cons_val_fin_one, WithLp.ofLp_toLp] at h0 h1 h2
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    at h0 h1 h2
  have e0 : w 0 = 0 := by linarith
  have e1 : w 1 = 0 := by linarith
  have e2 : w 2 = 0 := by linarith
  have e3 : w 3 = 0 := by linarith
  fin_cases i <;> assumption

theorem kv201_ai : AffineIndependent ℝ kv201 := by
  rw [affineIndependent_iff_of_fintype]
  intro w hsum hvec i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hvec
  have h0 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 0
  have h1 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 1
  have h2 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 2
  rw [Fin.sum_univ_four] at hsum
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_four, kv201, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val, Matrix.cons_val_fin_one, WithLp.ofLp_toLp] at h0 h1 h2
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    at h0 h1 h2
  have e0 : w 0 = 0 := by linarith
  have e1 : w 1 = 0 := by linarith
  have e2 : w 2 = 0 := by linarith
  have e3 : w 3 = 0 := by linarith
  fin_cases i <;> assumption

theorem kv210_ai : AffineIndependent ℝ kv210 := by
  rw [affineIndependent_iff_of_fintype]
  intro w hsum hvec i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hvec
  have h0 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 0
  have h1 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 1
  have h2 := congrFun (congrArg (fun x : Pt3 => x.ofLp) hvec) 2
  rw [Fin.sum_univ_four] at hsum
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_four, kv210, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val, Matrix.cons_val_fin_one, WithLp.ofLp_toLp] at h0 h1 h2
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    at h0 h1 h2
  have e0 : w 0 = 0 := by linarith
  have e1 : w 1 = 0 := by linarith
  have e2 : w 2 = 0 := by linarith
  have e3 : w 3 = 0 := by linarith
  fin_cases i <;> assumption

/-- The six Kuhn tetrahedra as `Tet` structures. -/
def kt012 : Tet := ⟨kv012, kv012_ai⟩
def kt021 : Tet := ⟨kv021, kv021_ai⟩
def kt102 : Tet := ⟨kv102, kv102_ai⟩
def kt120 : Tet := ⟨kv120, kv120_ai⟩
def kt201 : Tet := ⟨kv201, kv201_ai⟩
def kt210 : Tet := ⟨kv210, kv210_ai⟩

/-! ## Carrier confinement to order halfspaces -/

/-- The closed coordinate-difference halfspace `{coordDiff p q ≤ 0}` is convex. -/
theorem convex_coordDiff_le (p q : Fin 3) : Convex ℝ {y : Pt3 | coordDiff p q y ≤ 0} := by
  have : {y : Pt3 | coordDiff p q y ≤ 0} = {y : Pt3 | coordDiff p q y ≤ (0:ℝ)} := rfl
  -- coordDiff is linear; a sublevel set of a linear functional is convex.
  intro x hx z hz s t hs ht hst
  simp only [Set.mem_setOf_eq, coordDiff] at hx hz ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hxx : x p - x q ≤ 0 := hx
  have hzz : z p - z q ≤ 0 := hz
  nlinarith [hs, ht, hxx, hzz]

/-- A tetrahedron whose four vertices all satisfy `coordDiff p q · ≤ 0` has its whole carrier in that
halfspace. -/
theorem carrier_subset_coordDiff_le {T : Tet} {p q : Fin 3}
    (hv : ∀ i, coordDiff p q (T.v i) ≤ 0) :
    T.carrier ⊆ {y : Pt3 | coordDiff p q y ≤ 0} := by
  apply convexHull_min _ (convex_coordDiff_le p q)
  rintro y ⟨i, rfl⟩
  exact hv i

/-! ## Pairwise disjoint interiors of the six Kuhn tetrahedra

For each of the 15 unordered pairs, a coordinate-difference functional separates the two order
regions; the interiors land in opposite open halfspaces. -/

theorem disj_012_102 : Disjoint kt012.interior kt102.interior := by
  apply disjoint_interior_of_separating (p := 1) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt012, kv012, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt102, kv102, coordDiff]

theorem disj_012_021 : Disjoint kt012.interior kt021.interior := by
  apply disjoint_interior_of_separating (p := 2) (q := 1) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt012, kv012, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt021, kv021, coordDiff]

theorem disj_012_120 : Disjoint kt012.interior kt120.interior := by
  apply disjoint_interior_of_separating (p := 1) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt012, kv012, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt120, kv120, coordDiff]

theorem disj_012_201 : Disjoint kt012.interior kt201.interior := by
  apply disjoint_interior_of_separating (p := 2) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt012, kv012, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt201, kv201, coordDiff]

theorem disj_012_210 : Disjoint kt012.interior kt210.interior := by
  apply disjoint_interior_of_separating (p := 1) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt012, kv012, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt210, kv210, coordDiff]

theorem disj_021_102 : Disjoint kt021.interior kt102.interior := by
  apply disjoint_interior_of_separating (p := 1) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt021, kv021, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt102, kv102, coordDiff]

theorem disj_021_120 : Disjoint kt021.interior kt120.interior := by
  apply disjoint_interior_of_separating (p := 1) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt021, kv021, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt120, kv120, coordDiff]

theorem disj_021_201 : Disjoint kt021.interior kt201.interior := by
  apply disjoint_interior_of_separating (p := 2) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt021, kv021, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt201, kv201, coordDiff]

theorem disj_021_210 : Disjoint kt021.interior kt210.interior := by
  apply disjoint_interior_of_separating (p := 1) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt021, kv021, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt210, kv210, coordDiff]

theorem disj_102_120 : Disjoint kt102.interior kt120.interior := by
  apply disjoint_interior_of_separating (p := 2) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt102, kv102, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt120, kv120, coordDiff]

theorem disj_102_201 : Disjoint kt102.interior kt201.interior := by
  apply disjoint_interior_of_separating (p := 2) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt102, kv102, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt201, kv201, coordDiff]

theorem disj_102_210 : Disjoint kt102.interior kt210.interior := by
  apply disjoint_interior_of_separating (p := 2) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt102, kv102, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt210, kv210, coordDiff]

theorem disj_120_201 : Disjoint kt120.interior kt201.interior := by
  apply disjoint_interior_of_separating (p := 0) (q := 1) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt120, kv120, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt201, kv201, coordDiff]

theorem disj_120_210 : Disjoint kt120.interior kt210.interior := by
  apply disjoint_interior_of_separating (p := 2) (q := 1) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt120, kv120, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt210, kv210, coordDiff]

theorem disj_201_210 : Disjoint kt201.interior kt210.interior := by
  apply disjoint_interior_of_separating (p := 1) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt201, kv201, coordDiff]
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;> simp [kt210, kv210, coordDiff]

/-! ## The Kuhn solid -/

/-! ## Pairwise distinctness of the six Kuhn tetrahedra -/

theorem kt012_ne_kt021 : kt012 ≠ kt021 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (2 : Fin 4))) (1 : Fin 3)
  simp only [kt012, kt021, kv012, kv021, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt012_ne_kt102 : kt012 ≠ kt102 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (1 : Fin 4))) (0 : Fin 3)
  simp only [kt012, kt102, kv012, kv102, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt012_ne_kt120 : kt012 ≠ kt120 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (1 : Fin 4))) (0 : Fin 3)
  simp only [kt012, kt120, kv012, kv120, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt012_ne_kt201 : kt012 ≠ kt201 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (1 : Fin 4))) (0 : Fin 3)
  simp only [kt012, kt201, kv012, kv201, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt012_ne_kt210 : kt012 ≠ kt210 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (1 : Fin 4))) (0 : Fin 3)
  simp only [kt012, kt210, kv012, kv210, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt021_ne_kt102 : kt021 ≠ kt102 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (1 : Fin 4))) (0 : Fin 3)
  simp only [kt021, kt102, kv021, kv102, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt021_ne_kt120 : kt021 ≠ kt120 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (1 : Fin 4))) (0 : Fin 3)
  simp only [kt021, kt120, kv021, kv120, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt021_ne_kt201 : kt021 ≠ kt201 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (1 : Fin 4))) (0 : Fin 3)
  simp only [kt021, kt201, kv021, kv201, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt021_ne_kt210 : kt021 ≠ kt210 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (1 : Fin 4))) (0 : Fin 3)
  simp only [kt021, kt210, kv021, kv210, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt102_ne_kt120 : kt102 ≠ kt120 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (2 : Fin 4))) (0 : Fin 3)
  simp only [kt102, kt120, kv102, kv120, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt102_ne_kt201 : kt102 ≠ kt201 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (1 : Fin 4))) (1 : Fin 3)
  simp only [kt102, kt201, kv102, kv201, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt102_ne_kt210 : kt102 ≠ kt210 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (1 : Fin 4))) (1 : Fin 3)
  simp only [kt102, kt210, kv102, kv210, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt120_ne_kt201 : kt120 ≠ kt201 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (1 : Fin 4))) (1 : Fin 3)
  simp only [kt120, kt201, kv120, kv201, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt120_ne_kt210 : kt120 ≠ kt210 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (1 : Fin 4))) (1 : Fin 3)
  simp only [kt120, kt210, kv120, kv210, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

theorem kt201_ne_kt210 : kt201 ≠ kt210 := by
  intro h
  have hc := congrFun (congrArg (fun z : Pt3 => z.ofLp) (congrFun (congrArg Tet.v h) (2 : Fin 4))) (0 : Fin 3)
  simp only [kt201, kt210, kv201, kv210, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] at hc
  norm_num at hc

/-- The unit-cube **Kuhn solid**: the six order-simplices as a `TetSolid` with pairwise disjoint
interiors. -/
def kuhnSolid : TetSolid where
  pieces := {kt012, kt021, kt102, kt120, kt201, kt210}
  interior_disjoint := by
    intro A hA B hB hAB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hAB
        | exact disj_012_021 | exact disj_012_021.symm
        | exact disj_012_102 | exact disj_012_102.symm
        | exact disj_012_120 | exact disj_012_120.symm
        | exact disj_012_201 | exact disj_012_201.symm
        | exact disj_012_210 | exact disj_012_210.symm
        | exact disj_021_102 | exact disj_021_102.symm
        | exact disj_021_120 | exact disj_021_120.symm
        | exact disj_021_201 | exact disj_021_201.symm
        | exact disj_021_210 | exact disj_021_210.symm
        | exact disj_102_120 | exact disj_102_120.symm
        | exact disj_102_201 | exact disj_102_201.symm
        | exact disj_102_210 | exact disj_102_210.symm
        | exact disj_120_201 | exact disj_120_201.symm
        | exact disj_120_210 | exact disj_120_210.symm
        | exact disj_201_210 | exact disj_201_210.symm

@[simp] theorem kuhnSolid_pieces :
    kuhnSolid.pieces = {kt012, kt021, kt102, kt120, kt201, kt210} := rfl

theorem kuhnSolid_pieces_nonempty : kuhnSolid.pieces.Nonempty :=
  ⟨kt012, by simp⟩

/-! ## Every Kuhn vertex is a cube vertex; the edges do not overlap -/

/-- Every vertex of every Kuhn piece is a cube vertex (each coordinate is `0` or `1`). -/
theorem kuhn_vertex_isCubeVertex {T : Tet} (hT : T ∈ kuhnSolid.pieces) (i : Fin 4) :
    IsCubeVertex (T.v i) := by
  simp only [kuhnSolid_pieces, Finset.mem_insert, Finset.mem_singleton] at hT
  intro c
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases i <;> fin_cases c <;>
    simp only [kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102, kv120, kv201,
      kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, WithLp.ofLp_toLp] <;>
    norm_num

/-- The endpoints of any raw edge of the Kuhn solid are cube vertices. -/
theorem pieceEdges_endpoints_isCubeVertex {f : Segment3} (hf : f ∈ PieceEdges kuhnSolid) :
    IsCubeVertex f.a ∧ IsCubeVertex f.b := by
  rw [PieceEdges, Finset.mem_biUnion] at hf
  obtain ⟨T, hT, hfT⟩ := hf
  obtain ⟨i, j, _, hfa, hfb⟩ := mem_edges_endpoints hfT
  rw [hfa, hfb]
  exact ⟨kuhn_vertex_isCubeVertex hT i, kuhn_vertex_isCubeVertex hT j⟩

/-- The two endpoints of any raw edge of the Kuhn solid are distinct. -/
theorem pieceEdges_endpoints_ne {f : Segment3} (_hf : f ∈ PieceEdges kuhnSolid) : f.a ≠ f.b :=
  f.hne

/-- The coordinate sum of a point. -/
def coordSum (x : Pt3) : ℝ := x 0 + x 1 + x 2

/-- Within a Kuhn piece the vertex coordinate-sums are strictly increasing with the index, so each
raw edge `(T.v i, T.v j)` with `i < j` has `coordSum (T.v i) < coordSum (T.v j)`: the orientation is
canonical (low sum to high sum), and no edge is the reverse of another. -/
theorem kuhn_edge_coordSum_lt {f : Segment3} (hf : f ∈ PieceEdges kuhnSolid) :
    coordSum f.a < coordSum f.b := by
  rw [PieceEdges, Finset.mem_biUnion] at hf
  obtain ⟨T, hT, hfT⟩ := hf
  obtain ⟨i, j, hij, hfa, hfb⟩ := mem_edges_endpoints hfT
  rw [hfa, hfb]
  simp only [kuhnSolid_pieces, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (fin_cases i <;> fin_cases j <;>
      first
        | (exact absurd hij (by decide))
        | (simp [kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102, kv120,
            kv201, kv210, Tet.v, coordSum] <;> norm_num))

/-- **No Kuhn edge is the orientation-reverse of another.**  If `g.a = f.b` and `g.b = f.a` for two
raw edges, the canonical (increasing coordinate-sum) orientation is violated. -/
theorem kuhn_edges_no_reverse {f g : Segment3} (hf : f ∈ PieceEdges kuhnSolid)
    (hg : g ∈ PieceEdges kuhnSolid) (h1 : g.a = f.b) (h2 : g.b = f.a) : f = g := by
  exfalso
  have hf' := kuhn_edge_coordSum_lt hf
  have hg' := kuhn_edge_coordSum_lt hg
  rw [h1, h2] at hg'
  linarith

/-- **The Kuhn solid has non-overlapping edges.**  Two distinct raw edges sharing two distinct points
would have all four (cube-vertex) endpoints on the line through those points; among the four there
are then three distinct cube vertices, all collinear — contradicting `no_three_cubeVerts_collinear`. -/
theorem edgesNonOverlapping_kuhnSolid : EdgesNonOverlapping kuhnSolid := by
  intro f g hf hg x y hxy hxf hyf hxg hyg
  by_contra hne
  -- all four endpoints lie on line[x,y]
  obtain ⟨hfaL, hfbL⟩ := endpoints_mem_line_of_two_mem hxy hxf hyf
  obtain ⟨hgaL, hgbL⟩ := endpoints_mem_line_of_two_mem hxy hxg hyg
  obtain ⟨hfaC, hfbC⟩ := pieceEdges_endpoints_isCubeVertex hf
  obtain ⟨hgaC, hgbC⟩ := pieceEdges_endpoints_isCubeVertex hg
  have hfab : f.a ≠ f.b := f.hne
  have hgab : g.a ≠ g.b := g.hne
  -- a helper: three distinct collinear cube vertices on line[x,y] give a contradiction.
  have hcol3 : ∀ {p q s : Pt3}, IsCubeVertex p → IsCubeVertex q → IsCubeVertex s →
      p ≠ q → p ≠ s → q ≠ s → p ∈ line[ℝ, x, y] → q ∈ line[ℝ, x, y] → s ∈ line[ℝ, x, y] → False := by
    intro p q s hp hq hs hpq hps hqs hpL hqL hsL
    apply no_three_cubeVerts_collinear hp hq hs hpq hps hqs
    have h4 : Collinear ℝ ({p, q, x, y} : Set Pt3) :=
      collinear_insert_insert_of_mem_affineSpan_pair hpL hqL
    have hsin : s ∈ affineSpan ℝ ({p, q, x, y} : Set Pt3) := by
      refine (AffineSubspace.le_def' _ _).1 ?_ _ hsL
      refine affineSpan_mono ℝ ?_
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> simp
    have h5 : Collinear ℝ (insert s ({p, q, x, y} : Set Pt3)) :=
      (collinear_insert_iff_of_mem_affineSpan hsin).mpr h4
    exact h5.subset (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;> simp)
  -- since f ≠ g, the unordered endpoint pairs differ; find a 3rd distinct vertex.
  -- case on whether g.a ∈ {f.a, f.b} and g.b ∈ {f.a, f.b}.
  by_cases hga_fa : g.a = f.a
  · by_cases hgb_fb : g.b = f.b
    · -- both match ⇒ f = g (same endpoints), contradicting hne
      exact hne (by cases f; cases g; simp_all)
    · -- g.a = f.a, g.b ≠ f.b : vertices f.a, f.b, g.b. distinct? g.b ≠ f.a (= g.a) since g.a≠g.b.
      have hgb_fa : g.b ≠ f.a := by rw [← hga_fa]; exact (Ne.symm hgab)
      exact hcol3 hfaC hfbC hgbC hfab (Ne.symm hgb_fa) (Ne.symm hgb_fb) hfaL hfbL hgbL
  · -- g.a ≠ f.a.  vertices f.a, f.b, g.a need 3 distinct.
    by_cases hga_fb : g.a = f.b
    · -- g.a = f.b.  then g.b: g.b ≠ f.b (=g.a). consider f.a, f.b, g.b.
      have hgb_fb' : g.b ≠ f.b := by rw [← hga_fb]; exact (Ne.symm hgab)
      by_cases hgb_fa : g.b = f.a
      · -- g = (f.b, f.a) reversed.  But check: g.a=f.b, g.b=f.a.  carriers equal; need f=g false.
        -- f.a, f.b distinct on line; this is the swapped edge.  Distinct vertices: only f.a,f.b.
        -- Show contradiction differently: g.a=f.b, g.b=f.a means same carrier but we still need 3 verts.
        -- Use x,y on both; but x≠y are interior. Instead: this case means {g.a,g.b}={f.a,f.b}.
        -- A reversed Kuhn edge cannot occur (orientation canonical), so derive via a third point?
        -- We must rule it out: show no Kuhn edge is the reverse of another.
        exact absurd (kuhn_edges_no_reverse hf hg hga_fb hgb_fa) hne
      · exact hcol3 hfaC hfbC hgbC hfab (Ne.symm hgb_fa) (Ne.symm hgb_fb') hfaL hfbL hgbL
    · -- g.a ∉ {f.a, f.b}: f.a, f.b, g.a distinct.
      exact hcol3 hfaC hfbC hgaC hfab (Ne.symm hga_fa) (Ne.symm hga_fb) hfaL hfbL hgaL

/-! ## The cube solid as a `SolidWithAngles`

The twelve edges of the unit cube are the external edges, each carrying the cube's dihedral angle
`π/2`.  The `LocalDihedralModel` validation is simply `0 < π/2 < π`. -/

/-- Two points of `Pt3` that differ at coordinate `k` are distinct. -/
theorem euclid3_ne_of_coord {a b : Pt3} (k : Fin 3) (h : a k ≠ b k) : a ≠ b := by
  intro hab; exact h (by rw [hab])

/-- A cube edge between two given cube-corner points (nondegeneracy supplied by the caller). -/
def cubeEdge (a b : Pt3) (h : a ≠ b) : Segment3 := ⟨a, b, h⟩

/-- The twelve edges of the unit cube `[0,1]³`, as `Segment3` values between adjacent cube vertices.
Nondegeneracy is by the differing coordinate (`0` for the `x`-edges, `1` for the `y`-edges, `2` for
the `z`-edges). -/
def cubeExtEdges : Finset Segment3 :=
  { cubeEdge !₂[(0:ℝ),0,0] !₂[(1:ℝ),0,0] (euclid3_ne_of_coord 0 (by simp)),
    cubeEdge !₂[(0:ℝ),1,0] !₂[(1:ℝ),1,0] (euclid3_ne_of_coord 0 (by simp)),
    cubeEdge !₂[(0:ℝ),0,1] !₂[(1:ℝ),0,1] (euclid3_ne_of_coord 0 (by simp)),
    cubeEdge !₂[(0:ℝ),1,1] !₂[(1:ℝ),1,1] (euclid3_ne_of_coord 0 (by simp)),
    cubeEdge !₂[(0:ℝ),0,0] !₂[(0:ℝ),1,0] (euclid3_ne_of_coord 1 (by simp)),
    cubeEdge !₂[(1:ℝ),0,0] !₂[(1:ℝ),1,0] (euclid3_ne_of_coord 1 (by simp)),
    cubeEdge !₂[(0:ℝ),0,1] !₂[(0:ℝ),1,1] (euclid3_ne_of_coord 1 (by simp)),
    cubeEdge !₂[(1:ℝ),0,1] !₂[(1:ℝ),1,1] (euclid3_ne_of_coord 1 (by simp)),
    cubeEdge !₂[(0:ℝ),0,0] !₂[(0:ℝ),0,1] (euclid3_ne_of_coord 2 (by simp)),
    cubeEdge !₂[(1:ℝ),0,0] !₂[(1:ℝ),0,1] (euclid3_ne_of_coord 2 (by simp)),
    cubeEdge !₂[(0:ℝ),1,0] !₂[(0:ℝ),1,1] (euclid3_ne_of_coord 2 (by simp)),
    cubeEdge !₂[(1:ℝ),1,0] !₂[(1:ℝ),1,1] (euclid3_ne_of_coord 2 (by simp)) }

/-- `π/2` is a valid dihedral angle: `0 < π/2 < π`. -/
theorem pi_div_two_mem_Ioo : Real.pi / 2 ∈ Set.Ioo (0 : ℝ) Real.pi := by
  constructor
  · positivity
  · linarith [Real.pi_pos]

/-- **The unit cube as a `SolidWithAngles`.**  The six Kuhn order-simplices, with the twelve cube
edges declared external and each carrying the cube dihedral angle `π/2`. -/
def cubeSolid : SolidWithAngles where
  toTetSolid := kuhnSolid
  extEdges := cubeExtEdges
  angleOfExtEdge := fun _ => Real.pi / 2
  extEdge_local_model := by
    intro e _
    exact ⟨pi_div_two_mem_Ioo.1, pi_div_two_mem_Ioo.2⟩

@[simp] theorem cubeSolid_toTetSolid : cubeSolid.toTetSolid = kuhnSolid := rfl

/-- `EdgeSourceFaithful` for the cube solid — discharged with **no remaining hypothesis** via the
proven `edgesNonOverlapping_kuhnSolid` and the unconditional converse
`edgeSourceFaithful_of_nonOverlapping` of `BricardConcrete.lean`. -/
theorem edgeSourceFaithful_cubeSolid : EdgeSourceFaithful cubeSolid.toTetSolid :=
  edgeSourceFaithful_of_nonOverlapping edgesNonOverlapping_kuhnSolid

theorem cubeSolid_pieces_nonempty : cubeSolid.toTetSolid.pieces.Nonempty :=
  kuhnSolid_pieces_nonempty

/-! ## The fully concrete Chapter 9 headline (both solids discharged)

Specializing `regularTet_cube_no_equidecomp_concreteP` (which already has the regular-tet side fully
concrete) to `SQ := cubeSolid`, the **cube-side faithfulness bridge `hFQ` is discharged** by the
proven `edgeSourceFaithful_cubeSolid` — it is no longer a hypothesis.

Both solids are now concrete (`regularTetSolid` and `cubeSolid`), both faithfulness bridges and both
nonemptiness facts are proven, and the only remaining inputs are exactly the two design-sanctioned
isolated residues — the `LocationData`/`PearlSectorModel` cross-section certificates (`Ldata`,
`Rdata`) — together with the putative equidecomposition `decomp` (the object refuted) and the two
external-angle normalizations `hP_arccos`/`hQ_pi2` (properties of those certificates).  **No
geometric input remains undischarged on either side.** -/

/-- **The fully concrete Chapter 9 headline.**  A regular tetrahedron is not equidecomposable with
the Kuhn-decomposed unit cube realizing the `π/2` external-angle normalization, with **both** solids
concrete: the regular-tet side's faithfulness/nonemptiness are the proven
`edgeSourceFaithful_regularTetSolid` / `regularTetSolid_pieces_nonempty`, and the cube side's
faithfulness is the proven `edgeSourceFaithful_cubeSolid` (via the Kuhn `EdgesNonOverlapping`).

Remaining honest inputs (the isolated residues, identical to the parent minus the cube faithfulness
bridge): the two `LocationData`/`PearlSectorModel` certificates `Ldata`/`Rdata`, the equidecomposition
`decomp`, and the two angle normalizations `hP_arccos`/`hQ_pi2`. -/
theorem regularTet_cube_no_equidecomp_concrete
    (Ldata : LocationData regularTetSolid (Pearls (PieceEdges regularTetSolid.toTetSolid)))
    (Rdata : LocationData cubeSolid (Pearls (PieceEdges cubeSolid.toTetSolid)))
    (decomp : TetEquidecomp regularTetSolid.toTetSolid cubeSolid.toTetSolid)
    (hP_arccos : ∀ p, (hp : p ∈ Pearls (PieceEdges regularTetSolid.toTetSolid)) →
      pearlExtAngle (Ldata.cert p hp) = Real.arccos (1 / 3))
    (hQ_pi2 : ∀ p, (hp : p ∈ Pearls (PieceEdges cubeSolid.toTetSolid)) →
      pearlExtAngle (Rdata.cert p hp) = Real.pi / 2) : False :=
  regularTet_cube_no_equidecomp_concreteP Ldata Rdata decomp hP_arccos hQ_pi2
    edgeSourceFaithful_cubeSolid

end ProofsInTheBook.BricardCube

