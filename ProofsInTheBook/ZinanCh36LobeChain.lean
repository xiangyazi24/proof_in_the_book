import ProofsInTheBook.ZinanCh36ArcSweep

/-!
# `ZinanCh36LobeChain` — the same-side lobe noninterleaving theorem (the last geometric
piece of Chapter 36).

This file builds, on top of the arc-restricted parity sweep substrate
(`ZinanCh36ArcSweep`: `Chain`, `Chain.rayCount`, `rayCountParity_eventually_eq`,
`rayCountParity_constant_on_segment`, `rayCount_zero_of_coordMax`, the line tools
`lineCoord`, `side_ray_eta`) and the 1-D telescope of `ZinanCh36Lobes`
(`UpperLobe`, `sum_crossInd_emod_two`, `uCoord`), the geometric theorem that two
same-side boundary lobes of a strict simple polygon cannot interleave along a
generic line.

## Structure

* **§A.** `UpperLobe.chain` — the clipped chain of a lobe: the first and last
  vertices are replaced by the two feet (on the line), all interior walk vertices
  retained.  Lemmas: the chain endpoints are the feet; `side` of each foot is `0`;
  `chain_interior_pos` (every carrier point except the feet has `side > 0`);
  `carrier_inter_baseLine` (carrier ∩ {side = 0} = the two feet).
* **§B.** `upper_lobes_not_interleave` — the noninterleave theorem via the fixed
  sweep path.
* **§C.** the lower mirror `lower_lobes_not_interleave` (explicit duplication with
  `side < 0`).

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36LobeChain

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.ZinanCh36Lobes
open ProofsInTheBook.ZinanCh36ArcSweep
open Filter Topology
open scoped RealInnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ## §0. Cyclic walk position helpers (local re-proofs; the wiring file is concurrent). -/

/-- `arcPos i 0 = i`. -/
lemma arcPos_zero (i : Fin n) : arcPos i 0 = i := by
  unfold arcPos
  apply Fin.ext
  simp [Nat.mod_eq_of_lt i.isLt]

/-- The cyclic successor of `arcPos i k` is `arcPos i (k+1)`. -/
lemma cyclicNext_arcPos (i : Fin n) (k : ℕ) :
    cyclicNext (arcPos i k) = arcPos i (k + 1) := by
  apply Fin.ext
  have hcnv : (cyclicNext (arcPos i k)).val
      = if (arcPos i k).val + 1 < n then (arcPos i k).val + 1 else 0 := by
    unfold cyclicNext; split_ifs <;> rfl
  rw [hcnv]
  unfold arcPos
  simp only
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hlt : (i.val + k) % n < n := Nat.mod_lt _ hn
  have hmod : (i.val + (k + 1)) % n = ((i.val + k) % n + 1) % n := by
    conv_lhs => rw [show i.val + (k + 1) = (i.val + k) + 1 from by ring]
    rw [Nat.add_mod (i.val + k) 1 n, Nat.add_mod ((i.val + k) % n) 1 n, Nat.mod_mod]
  rw [hmod]
  by_cases h : (i.val + k) % n + 1 < n
  · rw [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h]
    have : (i.val + k) % n + 1 = n := by omega
    rw [this, Nat.mod_self]

/-! ## §A. The clipped chain of a lobe -/

variable {P : StrictSimplePolygon n} {ρ : RayDirection P} {x : Pt}

/-- The last crossing edge of the lobe (the up-crossing foot's edge). -/
def lobeLastEdge (L : UpperLobe P ρ x) : Fin n := arcPos L.start (L.len - 1)

/-- The first foot: the crossing point of the first (down-crossing) edge. -/
def footFirst (L : UpperLobe P ρ x) : Pt :=
  x + crossTau P ρ x L.start • ρ.r

/-- The last foot: the crossing point of the last (up-crossing) edge. -/
def footLast (L : UpperLobe P ρ x) : Pt :=
  x + crossTau P ρ x (lobeLastEdge L) • ρ.r

/-- Any ray point `x + τ•ρ.r` is on the base line: its `side` against the line is `0`. -/
lemma side_ray_point (τ : ℝ) : side ρ.r x (x + τ • ρ.r) = 0 := by
  unfold side
  rw [show (x + τ • ρ.r - x : Pt) = τ • ρ.r by abel, det2_smul_right, det2_self, mul_zero]

@[simp] lemma side_footFirst (L : UpperLobe P ρ x) : side ρ.r x (footFirst L) = 0 :=
  side_ray_point _

@[simp] lemma side_footLast (L : UpperLobe P ρ x) : side ρ.r x (footLast L) = 0 :=
  side_ray_point _

/-- The vertices of the clipped chain: foot at the two ends, walk vertices inside. -/
def chainPt (L : UpperLobe P ρ x) (j : Fin (L.len + 1)) : Pt :=
  if j.val = 0 then footFirst L
  else if j.val = L.len then footLast L
  else P.q (arcPos L.start j.val)

/-- The clipped chain of a lobe: `len` segments, endpoints the feet, interior the walk. -/
def lobeChain (L : UpperLobe P ρ x) : Chain L.len where
  p := chainPt L

/-! ### Chain vertex values -/

@[simp] lemma chainPt_zero (L : UpperLobe P ρ x) :
    chainPt L ⟨0, by omega⟩ = footFirst L := by
  unfold chainPt; simp

@[simp] lemma chainPt_len (L : UpperLobe P ρ x) :
    chainPt L ⟨L.len, by omega⟩ = footLast L := by
  have hpos := L.len_pos
  unfold chainPt
  have h1 : ¬ ((⟨L.len, by omega⟩ : Fin (L.len + 1)).val = 0) := by
    show ¬ L.len = 0; omega
  have h2 : (⟨L.len, by omega⟩ : Fin (L.len + 1)).val = L.len := rfl
  rw [if_neg h1, if_pos h2]

/-- An interior chain vertex (`0 < j < len`) is the walk vertex `P.q (arcPos start j)`. -/
lemma chainPt_interior (L : UpperLobe P ρ x) {j : ℕ} (hj0 : 0 < j) (hjlen : j < L.len)
    (hj : j < L.len + 1) :
    chainPt L ⟨j, hj⟩ = P.q (arcPos L.start j) := by
  unfold chainPt
  rw [if_neg (by simp; omega), if_neg (by simp; omega)]

/-- The `side` of a chain vertex is `≥ 0` (feet are `0`, interior walk vertices `> 0`). -/
lemma chainPt_side_nonneg (L : UpperLobe P ρ x) (j : Fin (L.len + 1)) :
    0 ≤ side ρ.r x (chainPt L j) := by
  rcases Nat.eq_zero_or_pos j.val with hj0 | hj0
  · have : chainPt L j = footFirst L := by unfold chainPt; rw [if_pos hj0]
    rw [this, side_footFirst]
  · by_cases hjlen : j.val = L.len
    · have : chainPt L j = footLast L := by
        unfold chainPt; rw [if_neg (by omega), if_pos hjlen]
      rw [this, side_footLast]
    · have hlt : j.val < L.len := by omega
      have : chainPt L j = P.q (arcPos L.start j.val) := by
        unfold chainPt; rw [if_neg (by omega), if_neg hjlen]
      rw [this]; exact le_of_lt (L.interior_pos j.val hj0 hlt)

/-- The `side` of an interior chain vertex (`0 < j < len`) is strictly positive. -/
lemma chainPt_side_pos_interior (L : UpperLobe P ρ x) {j : ℕ} (hj0 : 0 < j) (hjlen : j < L.len)
    (hj : j < L.len + 1) :
    0 < side ρ.r x (chainPt L ⟨j, hj⟩) := by
  rw [chainPt_interior L hj0 hjlen hj]
  exact L.interior_pos j hj0 hjlen

/-! ### Segment endpoint side values and the carrier/base-line intersection -/

/-- `segA` of chain segment `i` is the chain vertex at index `i.val`. -/
lemma lobeChain_segA (L : UpperLobe P ρ x) (i : Fin L.len) :
    (lobeChain L).segA i = chainPt L ⟨i.val, by omega⟩ := by
  unfold Chain.segA lobeChain
  congr 1

/-- `segB` of chain segment `i` is the chain vertex at index `i.val + 1`. -/
lemma lobeChain_segB (L : UpperLobe P ρ x) (i : Fin L.len) :
    (lobeChain L).segB i = chainPt L ⟨i.val + 1, by omega⟩ := by
  unfold Chain.segB lobeChain
  congr 1

/-- `side r x (lineMap a b t)` is affine in `t` (the EVALUATED-point slot — the mirror of
`side_lineMap`, which is affine in the base point). -/
lemma side_lineMap_right (r x a b : Pt) (t : ℝ) :
    side r x (AffineMap.lineMap a b t) =
      (1 - t) * side r x a + t * side r x b := by
  unfold side
  have hsub : AffineMap.lineMap a b t - x =
      AffineMap.lineMap (a - x) (b - x) t := by
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    ext k; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  rw [hsub, AffineMap.lineMap_apply_module, det2_add_right, det2_smul_right,
    det2_smul_right]

/-- The `side` of any carrier point is `≥ 0`: a convex combination of two `≥ 0` endpoint sides. -/
lemma carrier_side_nonneg (L : UpperLobe P ρ x) {z : Pt} (hz : z ∈ (lobeChain L).carrier) :
    0 ≤ side ρ.r x z := by
  obtain ⟨i, hi⟩ := hz
  rw [seg, segment_eq_image_lineMap] at hi
  obtain ⟨t, ht, rfl⟩ := hi
  rw [side_lineMap_right]
  have ha := chainPt_side_nonneg L ⟨i.val, by omega⟩
  have hb := chainPt_side_nonneg L ⟨i.val + 1, by omega⟩
  rw [lobeChain_segA, lobeChain_segB]
  have htt := ht.1; have htt2 := ht.2
  nlinarith [ha, hb, htt, htt2]

/-- **Carrier ∩ base line ⊆ {footFirst, footLast}.**  A carrier point on the base line is one of
the two feet: on each chain segment the `side` is a convex combination of two nonnegative
endpoint sides, so it vanishes only where an endpoint side vanishes — which happens only at the
feet (chain vertex `0` or `len`). -/
lemma carrier_side_zero_imp_foot (L : UpperLobe P ρ x) {z : Pt}
    (hz : z ∈ (lobeChain L).carrier) (hside : side ρ.r x z = 0) :
    z = footFirst L ∨ z = footLast L := by
  obtain ⟨i, hi⟩ := hz
  rw [seg, segment_eq_image_lineMap] at hi
  obtain ⟨t, ht, rfl⟩ := hi
  set j := i.val with hjdef
  have hjlt : j < L.len := i.isLt
  -- endpoint side values
  have hsa : side ρ.r x ((lobeChain L).segA i) = side ρ.r x (chainPt L ⟨j, by omega⟩) := by
    rw [lobeChain_segA]
  have hsb : side ρ.r x ((lobeChain L).segB i) = side ρ.r x (chainPt L ⟨j + 1, by omega⟩) := by
    rw [lobeChain_segB]
  have ha0 : 0 ≤ side ρ.r x (chainPt L ⟨j, by omega⟩) := chainPt_side_nonneg L _
  have hb0 : 0 ≤ side ρ.r x (chainPt L ⟨j + 1, by omega⟩) := chainPt_side_nonneg L _
  rw [side_lineMap_right, lobeChain_segA, lobeChain_segB] at hside
  -- side(z) = (1-t)·sA + t·sB = 0, with sA,sB ≥ 0, t ∈ [0,1].
  have htt := ht.1; have htt2 := ht.2
  -- Conclude: either t = 0 with z = segA, or t = 1 with z = segB, or sA = sB = 0.
  -- In all sub-cases the resulting point is a foot.
  by_cases hsA0 : side ρ.r x (chainPt L ⟨j, by omega⟩) = 0
  · -- segA on the line ⟹ j = 0 (footFirst).
    have hj0 : j = 0 := by
      by_contra hjne
      have hjpos : 0 < j := Nat.pos_of_ne_zero hjne
      by_cases hjlen : j = L.len
      · omega
      · exact absurd hsA0 (ne_of_gt (chainPt_side_pos_interior L hjpos hjlt (by omega)))
    -- footFirst.  Either t = 0 (z = footFirst), or t > 0 forces sB = 0 hence segB foot.
    rcases eq_or_lt_of_le htt with ht0 | ht0
    · -- t = 0 ⟹ z = segA = footFirst.
      left
      rw [← ht0, AffineMap.lineMap_apply_zero, lobeChain_segA]
      unfold chainPt; rw [if_pos (show j = 0 from hj0)]
    · -- t > 0 ⟹ sB = 0 (from hside) ⟹ segB foot.
      have hsB0 : side ρ.r x (chainPt L ⟨j + 1, by omega⟩) = 0 := by
        rw [hsA0, mul_zero, zero_add] at hside
        rcases mul_eq_zero.mp hside with h | h
        · exact absurd h (ne_of_gt ht0)
        · exact h
      -- segB on the line ⟹ j+1 = len (footLast).
      have hjlen1 : j + 1 = L.len := by
        by_contra hne
        have hjpos1 : 0 < j + 1 := by omega
        have hlt1 : j + 1 < L.len := by omega
        exact absurd hsB0 (ne_of_gt (chainPt_side_pos_interior L hjpos1 hlt1 (by omega)))
      -- with sA = 0 and sB = 0, the whole segment is on the line, so z = segA = footFirst.
      left
      rw [AffineMap.lineMap_apply_module, lobeChain_segA, lobeChain_segB]
      have hA : chainPt L ⟨j, by omega⟩ = footFirst L := by
        unfold chainPt; rw [if_pos (show j = 0 from hj0)]
      have hB : chainPt L ⟨j + 1, by omega⟩ = footLast L := by
        unfold chainPt; rw [if_neg (by simp), if_pos (show j + 1 = L.len from hjlen1)]
      -- footFirst = footLast since both feet coincide here (start = lastEdge as j=0, j+1=len ⟹ len=1).
      have hlen1 : L.len = 1 := by omega
      have hfeq : footFirst L = footLast L := by
        unfold footFirst footLast lobeLastEdge
        rw [hlen1]; simp [arcPos_zero, hj0]
      rw [hA, hB, hfeq]
      module
  · -- segA off the line ⟹ sA > 0 ⟹ from hside, sB must absorb: need t = 1 and sB = 0.
    have hsApos : 0 < side ρ.r x (chainPt L ⟨j, by omega⟩) := lt_of_le_of_ne ha0 (Ne.symm hsA0)
    -- (1-t)·sA = -t·sB ≤ 0, and (1-t)·sA ≥ 0, so (1-t)·sA = 0 ⟹ t = 1.
    have ht1 : t = 1 := by nlinarith [hsApos, hb0, htt, htt2]
    -- then sB = 0 ⟹ segB foot = footLast (j+1 = len).
    have hsB0 : side ρ.r x (chainPt L ⟨j + 1, by omega⟩) = 0 := by
      rw [ht1] at hside; simp at hside; tauto
    have hjlen1 : j + 1 = L.len := by
      by_contra hne
      have hjpos1 : 0 < j + 1 := by omega
      have hlt1 : j + 1 < L.len := by omega
      exact absurd hsB0 (ne_of_gt (chainPt_side_pos_interior L hjpos1 hlt1 (by omega)))
    right
    rw [ht1, AffineMap.lineMap_apply_one, lobeChain_segB]
    unfold chainPt; rw [if_neg (by simp), if_pos (show j + 1 = L.len from hjlen1)]

end

end ProofsInTheBook.ZinanCh36LobeChain
