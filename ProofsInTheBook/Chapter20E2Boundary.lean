import ProofsInTheBook.Chapter20DissectionEngine
import ProofsInTheBook.Chapter20E2Frontier
import ProofsInTheBook.Chapter20

/-!
# Chapter 20 (Monsky) — boundary atomic red-green parity

This file contains the boundary half of the atomic E2 bookkeeping: the
red-green atomic edges with odd atomic multiplicity are odd in number.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

variable (D : SquareDissection)

open scoped Classical in
lemma atomicMult_eq_zero_of_not_isAtomic {e : Sym2 D.vtx}
    (he : ¬ IsAtomicEdge D e) :
    atomicMult D e = 0 := by
  classical
  unfold atomicMult
  refine Finset.sum_eq_zero fun i _ => ?_
  have hnot : e ∉ triAtomicEdges D i := by
    intro hi
    exact he ⟨i, hi⟩
  exact List.count_eq_zero_of_not_mem hnot

open scoped Classical in
lemma isAtomic_of_odd_atomicMult {e : Sym2 D.vtx}
    (hodd : Odd (atomicMult D e)) :
    IsAtomicEdge D e := by
  classical
  by_contra he
  have hzero := atomicMult_eq_zero_of_not_isAtomic (D := D) (e := e) he
  simp [hzero] at hodd

open scoped Classical in
lemma odd_atomicMult_iff_isAtomic_boundary (e : Sym2 D.vtx) :
    Odd (atomicMult D e) ↔ IsAtomicEdge D e ∧ OnSquareBoundary D e := by
  classical
  constructor
  · intro hodd
    have he : IsAtomicEdge D e := isAtomic_of_odd_atomicMult (D := D) hodd
    refine ⟨he, ?_⟩
    by_contra hbd
    have hev := atomicMult_even_of_interior D e he hbd
    exact Nat.not_even_iff_odd.mpr hodd hev
  · rintro ⟨he, hbd⟩
    have hone := atomicMult_eq_one_of_boundary D e he hbd
    rw [hone]
    exact odd_one

open scoped Classical in
lemma oddAtomicRG_filter_eq_atomicBoundaryRG :
    (Finset.univ.filter fun e : Sym2 D.vtx =>
      edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧ Odd (atomicMult D e)) =
    (Finset.univ.filter fun e : Sym2 D.vtx =>
      edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧
        IsAtomicEdge D e ∧ OnSquareBoundary D e) := by
  classical
  ext e
  simp [odd_atomicMult_iff_isAtomic_boundary (D := D) e]

lemma unitSquare_corner00_extreme :
    ((0, 0) : ℝ × ℝ) ∈
      (Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)).extremePoints ℝ := by
  have hsquare :
      Set.Icc ((0, 0) : ℝ × ℝ) (1, 1) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Set.mem_Icc, Prod.le_def]
  rw [hsquare, extremePoints_prod]
  simp [Set.extremePoints_Icc]

lemma unitSquare_corner10_extreme :
    ((1, 0) : ℝ × ℝ) ∈
      (Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)).extremePoints ℝ := by
  have hsquare :
      Set.Icc ((0, 0) : ℝ × ℝ) (1, 1) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Set.mem_Icc, Prod.le_def]
  rw [hsquare, extremePoints_prod]
  simp [Set.extremePoints_Icc]

lemma unitSquare_corner11_extreme :
    ((1, 1) : ℝ × ℝ) ∈
      (Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)).extremePoints ℝ := by
  have hsquare :
      Set.Icc ((0, 0) : ℝ × ℝ) (1, 1) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Set.mem_Icc, Prod.le_def]
  rw [hsquare, extremePoints_prod]
  simp [Set.extremePoints_Icc]

lemma unitSquare_corner01_extreme :
    ((0, 1) : ℝ × ℝ) ∈
      (Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)).extremePoints ℝ := by
  have hsquare :
      Set.Icc ((0, 0) : ℝ × ℝ) (1, 1) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Set.mem_Icc, Prod.le_def]
  rw [hsquare, extremePoints_prod]
  simp [Set.extremePoints_Icc]

lemma exists_vertex_coord_of_extreme_unitSquare {c : ℝ × ℝ}
    (hc : c ∈ (Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)).extremePoints ℝ) :
    ∃ v : D.vtx, D.coord v = c := by
  let square : Set (ℝ × ℝ) := Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)
  have hc_mem : c ∈ square := by
    simpa [square] using extremePoints_subset hc
  have hcover_mem : c ∈ ⋃ i : Fin D.n, convexHull ℝ
      {D.coord (D.tri i).1, D.coord (D.tri i).2.1, D.coord (D.tri i).2.2} := by
    simpa [square, D.cover] using hc_mem
  rcases Set.mem_iUnion.mp hcover_mem with ⟨i, hi⟩
  let T : Set (ℝ × ℝ) := convexHull ℝ
      {D.coord (D.tri i).1, D.coord (D.tri i).2.1, D.coord (D.tri i).2.2}
  have hTsubset : T ⊆ square := by
    intro x hx
    have hxUnion : x ∈ ⋃ j : Fin D.n, convexHull ℝ
        {D.coord (D.tri j).1, D.coord (D.tri j).2.1, D.coord (D.tri j).2.2} := by
      exact Set.mem_iUnion.mpr ⟨i, by simpa [T] using hx⟩
    simpa [square, D.cover] using hxUnion
  have hcT : c ∈ T := by
    simpa [T] using hi
  have hsqExtreme : IsExtreme ℝ square {c} := by
    rw [isExtreme_singleton]
    simpa [square] using hc
  have hTExtremeSet : IsExtreme ℝ T {c} := by
    exact hsqExtreme.mono hTsubset (by simpa using hcT)
  have hcTExtreme : c ∈ T.extremePoints ℝ := by
    rw [← isExtreme_singleton]
    exact hTExtremeSet
  have hmemVerts : c ∈ ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
      D.coord (D.tri i).2.2} : Set (ℝ × ℝ)) := by
    have h := extremePoints_convexHull_subset (𝕜 := ℝ)
      (A := ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
        D.coord (D.tri i).2.2} : Set (ℝ × ℝ))) hcTExtreme
    simpa [T] using h
  rcases hmemVerts with h | h | h
  · exact ⟨(D.tri i).1, h.symm⟩
  · exact ⟨(D.tri i).2.1, h.symm⟩
  · exact ⟨(D.tri i).2.2, h.symm⟩

lemma exists_square_corners :
    ∃ c00 c10 c11 c01 : D.vtx,
      D.coord c00 = (0, 0) ∧ D.coord c10 = (1, 0) ∧
      D.coord c11 = (1, 1) ∧ D.coord c01 = (0, 1) := by
  obtain ⟨c00, h00⟩ :=
    exists_vertex_coord_of_extreme_unitSquare (D := D) unitSquare_corner00_extreme
  obtain ⟨c10, h10⟩ :=
    exists_vertex_coord_of_extreme_unitSquare (D := D) unitSquare_corner10_extreme
  obtain ⟨c11, h11⟩ :=
    exists_vertex_coord_of_extreme_unitSquare (D := D) unitSquare_corner11_extreme
  obtain ⟨c01, h01⟩ :=
    exists_vertex_coord_of_extreme_unitSquare (D := D) unitSquare_corner01_extreme
  exact ⟨c00, c10, c11, c01, h00, h10, h11, h01⟩

abbrev unitSquareSetLocal : Set (ℝ × ℝ) :=
  Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)

noncomputable def triHullLocal (i : Fin D.n) : Set (ℝ × ℝ) :=
  convexHull ℝ {D.coord (D.tri i).1, D.coord (D.tri i).2.1, D.coord (D.tri i).2.2}

lemma triHullLocal_subset_unitSquare (i : Fin D.n) :
    triHullLocal D i ⊆ unitSquareSetLocal := by
  intro x hx
  have hxUnion :
      x ∈ ⋃ j : Fin D.n, convexHull ℝ
        {D.coord (D.tri j).1, D.coord (D.tri j).2.1, D.coord (D.tri j).2.2} := by
    exact Set.mem_iUnion.mpr ⟨i, by simpa [triHullLocal] using hx⟩
  rw [D.cover] at hxUnion
  simpa [unitSquareSetLocal] using hxUnion

lemma not_mem_interior_triHull_of_mem_frontier_unitSquare {x : ℝ × ℝ}
    (hx : x ∈ frontier unitSquareSetLocal) (i : Fin D.n) :
    x ∉ interior (triHullLocal D i) := by
  have hxSq : x ∈ unitSquareSetLocal := by
    have hxf :
        x ∈ frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
      simpa [unitSquareSetLocal] using hx
    rw [frontier_unitSquare] at hxf
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using
      ⟨⟨hxf.1, hxf.2.2.1⟩, ⟨hxf.2.1, hxf.2.2.2.1⟩⟩
  have hxNotInterior : x ∉ interior unitSquareSetLocal :=
    (mem_frontier_iff_notMem_interior hxSq).mp hx
  intro hxTri
  exact hxNotInterior (interior_mono (triHullLocal_subset_unitSquare D i) hxTri)

open scoped Classical in
lemma mem_sideInteriorChain_iff_local {p q w : D.vtx} :
    w ∈ sideInteriorChain D p q ↔ OnSide D p q w ∧ w ≠ p ∧ w ≠ q := by
  classical
  unfold sideInteriorChain
  rw [List.mem_insertionSort, Finset.mem_toList]
  simp [OnSide]

open scoped Classical in
lemma sideInteriorChain_nodup_local (p q : D.vtx) :
    (sideInteriorChain D p q).Nodup := by
  classical
  unfold sideInteriorChain
  have hperm :
      ((Finset.univ.filter (fun w =>
          OnSide D p q w ∧ w ≠ p ∧ w ≠ q)).toList.insertionSort
        (fun w₁ w₂ => sideParam D p q w₁ ≤ sideParam D p q w₂)).Perm
        (Finset.univ.filter (fun w =>
          OnSide D p q w ∧ w ≠ p ∧ w ≠ q)).toList :=
    List.perm_insertionSort _ _
  exact (List.Perm.nodup_iff hperm).mpr
    (Finset.nodup_toList (Finset.univ.filter (fun w =>
      OnSide D p q w ∧ w ≠ p ∧ w ≠ q)))

lemma left_not_mem_sideInteriorChain_local (p q : D.vtx) :
    p ∉ sideInteriorChain D p q := by
  intro hp
  exact (mem_sideInteriorChain_iff_local (D := D)).mp hp |>.2.1 rfl

lemma right_not_mem_sideInteriorChain_local (p q : D.vtx) :
    q ∉ sideInteriorChain D p q := by
  intro hq
  exact (mem_sideInteriorChain_iff_local (D := D)).mp hq |>.2.2 rfl

lemma sideChain_nodup_local {p q : D.vtx} (hpq : p ≠ q) :
    (p :: sideInteriorChain D p q ++ [q]).Nodup := by
  classical
  rw [List.nodup_append, List.nodup_cons]
  refine ⟨⟨left_not_mem_sideInteriorChain_local D p q,
    sideInteriorChain_nodup_local D p q⟩, List.nodup_singleton q, ?_⟩
  intro a ha b hb hab
  rw [List.mem_cons] at ha
  rw [List.mem_singleton] at hb
  subst b
  rcases ha with rfl | ha
  · exact hpq hab
  · exact right_not_mem_sideInteriorChain_local D p q (hab ▸ ha)

lemma endpoints_mem_of_mem_consecutiveEdges_local {α : Type*} {l : List α} {a b : α}
    (h : s(a, b) ∈ consecutiveEdges l) : a ∈ l ∧ b ∈ l := by
  induction l with
  | nil =>
      simp [consecutiveEdges] at h
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [consecutiveEdges] at h
      | cons y ys =>
          rw [consecutiveEdges, List.mem_cons] at h
          rcases h with h | h
          · rw [Sym2.eq_iff] at h
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
          · have hh := ih h
            simp [hh.1, hh.2]

lemma consecutiveEdges_nodup_of_nodup_local {α : Type*} [DecidableEq α] :
    ∀ {l : List α}, l.Nodup → (consecutiveEdges l).Nodup
  | [], _ => by simp [consecutiveEdges]
  | [_], _ => by simp [consecutiveEdges]
  | a :: b :: rest, h => by
      rw [consecutiveEdges, List.nodup_cons]
      refine ⟨?_, consecutiveEdges_nodup_of_nodup_local (List.Nodup.of_cons h)⟩
      intro hmem
      have hend := endpoints_mem_of_mem_consecutiveEdges_local (l := b :: rest) hmem
      exact List.Nodup.notMem h hend.1

lemma not_diag_mem_consecutiveEdges_of_nodup_local {α : Type*} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) (a : α) :
    s(a, a) ∉ consecutiveEdges l := by
  induction l with
  | nil =>
      simp [consecutiveEdges]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [consecutiveEdges]
      | cons y ys =>
          rw [consecutiveEdges, List.mem_cons]
          rintro (h | h)
          · rw [Sym2.eq_iff] at h
            rcases h with ⟨hax, hay⟩ | ⟨hay, hax⟩
            · subst x
              subst y
              exact List.Nodup.notMem hnd (by simp)
            · subst x
              subst y
              exact List.Nodup.notMem hnd (by simp)
          · exact ih (List.Nodup.of_cons hnd) h

lemma ne_of_mk_mem_consecutiveEdges_of_nodup_local {α : Type*} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) {a b : α}
    (h : s(a, b) ∈ consecutiveEdges l) : a ≠ b := by
  intro hab
  subst b
  exact not_diag_mem_consecutiveEdges_of_nodup_local hnd a h

lemma onSide_left_local (p q : D.vtx) : OnSide D p q p := by
  exact wbtw_self_left (R := ℝ) (D.coord p) (D.coord q)

lemma onSide_right_local (p q : D.vtx) : OnSide D p q q := by
  exact wbtw_self_right (R := ℝ) (D.coord p) (D.coord q)

lemma sideInteriorChain_onSide_local {p q w : D.vtx}
    (hw : w ∈ sideInteriorChain D p q) : OnSide D p q w :=
  (mem_sideInteriorChain_iff_local (D := D)).mp hw |>.1

lemma onSide_of_mem_sideChain_local {p q w : D.vtx}
    (hw : w ∈ p :: sideInteriorChain D p q ++ [q]) : OnSide D p q w := by
  rw [List.mem_append] at hw
  rcases hw with hw | hw
  · rw [List.mem_cons] at hw
    rcases hw with hwp | hw
    · rw [hwp]
      exact onSide_left_local D p q
    · exact sideInteriorChain_onSide_local D hw
  · rw [List.mem_singleton] at hw
    rw [hw]
    exact onSide_right_local D p q

lemma endpoints_onSide_of_mem_sideAtomicEdges_local {p q a b : D.vtx}
    (h : s(a, b) ∈ sideAtomicEdges D p q) :
    OnSide D p q a ∧ OnSide D p q b := by
  unfold sideAtomicEdges at h
  have hend := endpoints_mem_of_mem_consecutiveEdges_local h
  exact ⟨onSide_of_mem_sideChain_local D hend.1,
    onSide_of_mem_sideChain_local D hend.2⟩

lemma ne_of_mk_mem_sideAtomicEdges_local {p q a b : D.vtx} (hpq : p ≠ q)
    (h : s(a, b) ∈ sideAtomicEdges D p q) : a ≠ b := by
  unfold sideAtomicEdges at h
  exact ne_of_mk_mem_consecutiveEdges_of_nodup_local (sideChain_nodup_local D hpq) h

lemma sideAtomicEdges_nodup_local {p q : D.vtx} (hpq : p ≠ q) :
    (sideAtomicEdges D p q).Nodup := by
  unfold sideAtomicEdges
  exact consecutiveEdges_nodup_of_nodup_local (sideChain_nodup_local D hpq)

lemma sideParam_spec_of_onSide {p q w : D.vtx} (hpq : p ≠ q)
    (hw : OnSide D p q w) :
    sideParam D p q w ∈ Set.Icc (0 : ℝ) 1 ∧
      AffineMap.lineMap (D.coord p) (D.coord q) (sideParam D p q w) = D.coord w := by
  unfold OnSide at hw
  obtain ⟨t, ht, htw⟩ := hw
  have hcoord_ne : D.coord q ≠ D.coord p := by
    intro h
    exact hpq (D.coord_inj h.symm)
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · have hparam : sideParam D p q w = t := by
      unfold sideParam
      rw [if_pos hx]
      have hxf := congrArg Prod.fst htw
      simp [AffineMap.lineMap_apply] at hxf
      field_simp [hx]
      linarith
    constructor
    · simpa [hparam] using ht
    · simpa [hparam] using htw
  · have hy : (D.coord q).2 ≠ (D.coord p).2 := by
      intro hy
      apply hcoord_ne
      ext <;> simp [not_not.mp hx, hy]
    have hparam : sideParam D p q w = t := by
      unfold sideParam
      rw [if_neg hx]
      have hyf := congrArg Prod.snd htw
      simp [AffineMap.lineMap_apply] at hyf
      field_simp [hy]
      linarith
    constructor
    · simpa [hparam] using ht
    · simpa [hparam] using htw

lemma sideParam_left_eq_local {p q : D.vtx} (hpq : p ≠ q) :
    sideParam D p q p = 0 := by
  unfold sideParam
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · simp [hx]
  · have hcoord_ne : D.coord q ≠ D.coord p := by
      intro h
      exact hpq (D.coord_inj h.symm)
    have hy : (D.coord q).2 ≠ (D.coord p).2 := by
      intro hy
      apply hcoord_ne
      ext <;> simp [not_not.mp hx, hy]
    simp [hx]

lemma sideParam_right_eq_local {p q : D.vtx} (hpq : p ≠ q) :
    sideParam D p q q = 1 := by
  unfold sideParam
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · rw [if_pos hx]
    field_simp [hx]
  · rw [if_neg hx]
    have hcoord_ne : D.coord q ≠ D.coord p := by
      intro h
      exact hpq (D.coord_inj h.symm)
    have hy : (D.coord q).2 ≠ (D.coord p).2 := by
      intro hy
      apply hcoord_ne
      ext <;> simp [not_not.mp hx, hy]
    field_simp [hy]

open scoped Classical in
lemma sideInteriorChain_pairwise_sideParam (p q : D.vtx) :
    List.Pairwise (fun w₁ w₂ => sideParam D p q w₁ ≤ sideParam D p q w₂)
      (sideInteriorChain D p q) := by
  classical
  unfold sideInteriorChain
  exact List.pairwise_insertionSort _ _

open scoped Classical in
lemma sideChain_pairwise_sideParam {p q : D.vtx} (hpq : p ≠ q) :
    List.Pairwise (fun w₁ w₂ => sideParam D p q w₁ ≤ sideParam D p q w₂)
      (p :: sideInteriorChain D p q ++ [q]) := by
  classical
  rw [List.pairwise_append]
  refine ⟨?_, by simp, ?_⟩
  · rw [List.pairwise_cons]
    constructor
    · intro x hx
      rw [sideParam_left_eq_local (D := D) hpq]
      exact (sideParam_spec_of_onSide (D := D) hpq
        (sideInteriorChain_onSide_local D hx)).1.1
    · exact sideInteriorChain_pairwise_sideParam D p q
  · intro a ha b hb
    rw [List.mem_singleton] at hb
    rw [hb, sideParam_right_eq_local (D := D) hpq]
    rw [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [sideParam_left_eq_local (D := D) hpq]
      norm_num
    · exact (sideParam_spec_of_onSide (D := D) hpq
        (sideInteriorChain_onSide_local D ha)).1.2

lemma not_sideParam_between_of_mem_consecutiveEdges_pairwise
    {α : Type*} {f : α → ℝ} :
    ∀ {l : List α} {a b w : α},
      List.Pairwise (fun x y => f x ≤ f y) l →
      s(a, b) ∈ consecutiveEdges l →
      w ∈ l →
      ¬ (f a < f w ∧ f w < f b)
  | [], a, b, w, _hpair, h, _hw => by
      simp [consecutiveEdges] at h
  | [_x], a, b, w, _hpair, h, _hw => by
      simp [consecutiveEdges] at h
  | x :: y :: rest, a, b, w, hpair, h, hw => by
      rw [List.pairwise_cons] at hpair
      have hxy0 : f x ≤ f y := hpair.1 y (by simp)
      rw [consecutiveEdges, List.mem_cons] at h
      rcases h with hfirst | htail
      · rw [Sym2.eq_iff] at hfirst
        rcases hfirst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [List.mem_cons] at hw
          intro hbetween
          rcases hw with rfl | hw
          · linarith
          · rw [List.mem_cons] at hw
            rcases hw with rfl | hwrest
            · linarith
            · have hyw : f b ≤ f w := by
                have htailPair := hpair.2
                rw [List.pairwise_cons] at htailPair
                exact htailPair.1 w hwrest
              linarith
        · intro hbetween
          linarith
      · rw [List.mem_cons] at hw
        rcases hw with rfl | hwtail
        · have hend := endpoints_mem_of_mem_consecutiveEdges_local htail
          have hxa : f w ≤ f a := hpair.1 a (by simpa using hend.1)
          intro hbetween
          linarith
        · exact not_sideParam_between_of_mem_consecutiveEdges_pairwise
            hpair.2 htail hwtail

lemma not_sideParam_between_of_mem_sideAtomicEdges {p q a b w : D.vtx}
    (hpq : p ≠ q) (h : s(a, b) ∈ sideAtomicEdges D p q)
    (hw : w ∈ p :: sideInteriorChain D p q ++ [q]) :
    ¬ (sideParam D p q a < sideParam D p q w ∧
      sideParam D p q w < sideParam D p q b) := by
  unfold sideAtomicEdges at h
  exact not_sideParam_between_of_mem_consecutiveEdges_pairwise
    (sideChain_pairwise_sideParam (D := D) hpq) h hw

lemma mem_consecutiveEdges_of_pairwise_no_between
    {α : Type*} {f : α → ℝ} {P : α → Prop} :
    ∀ {l : List α} {a b : α},
      l.Nodup →
      (∀ x, x ∈ l → P x) →
      (∀ x y, P x → P y → f x = f y → x = y) →
      l.Pairwise (fun x y => f x ≤ f y) →
      a ∈ l → b ∈ l → f a < f b →
      (∀ z, z ∈ l → ¬ (f a < f z ∧ f z < f b)) →
      s(a, b) ∈ consecutiveEdges l
  | [], a, b, _hnd, _hall, _hinj, _hpair, ha, _hb, _hlt, _hno => by
      simp at ha
  | x :: [], a, b, _hnd, _hall, _hinj, _hpair, ha, hb, hlt, _hno => by
      simp at ha hb
      subst a
      subst b
      linarith
  | x :: y :: ys, a, b, hnd, hall, hinj, hpair, ha, hb, hlt, hno => by
      rw [consecutiveEdges, List.mem_cons]
      rw [List.mem_cons] at ha hb
      have hpair' := List.pairwise_cons.mp hpair
      have hx_le_tail : ∀ t ∈ y :: ys, f x ≤ f t := hpair'.1
      have htail_pair : (y :: ys).Pairwise (fun x y => f x ≤ f y) := hpair'.2
      have htail_nd : (y :: ys).Nodup := List.Nodup.of_cons hnd
      have htail_all : ∀ z, z ∈ y :: ys → P z := by
        intro z hz
        exact hall z (by simp [hz])
      rcases ha with rfl | ha_tail
      · rcases hb with rfl | hb_tail
        · linarith
        · rw [List.mem_cons] at hb_tail
          rcases hb_tail with rfl | hb_ys
          · exact Or.inl rfl
          · have hxy_le : f a ≤ f y := hx_le_tail y (by simp)
            have hxy_ne : a ≠ y := by
              intro hxy
              exact (List.Nodup.notMem hnd) (by simp [hxy])
            have hxy_lt : f a < f y := by
              refine lt_of_le_of_ne hxy_le ?_
              intro heq
              exact hxy_ne (hinj a y (hall a (by simp)) (hall y (by simp)) heq)
            have hy_le_b : f y ≤ f b :=
              (List.pairwise_cons.mp htail_pair).1 b hb_ys
            have hy_ne_b : y ≠ b := by
              intro hyb
              subst b
              exact (List.Nodup.notMem htail_nd) hb_ys
            have hy_lt_b : f y < f b := by
              refine lt_of_le_of_ne hy_le_b ?_
              intro heq
              exact hy_ne_b (hinj y b (hall y (by simp))
                (hall b (by simp [hb_ys])) heq)
            exact False.elim (hno y (by simp) ⟨hxy_lt, hy_lt_b⟩)
      · rcases hb with rfl | hb_tail
        · have hx_le_a : f b ≤ f a := hx_le_tail a ha_tail
          exact False.elim (by linarith)
        · exact Or.inr
            (mem_consecutiveEdges_of_pairwise_no_between
              (l := y :: ys) (f := f) (P := P)
              htail_nd htail_all hinj htail_pair ha_tail hb_tail hlt
              (fun z hz => hno z (by simp [hz])))

lemma sideParam_injective_onSide_local {p q a b : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b)
    (hparam : sideParam D p q a = sideParam D p q b) :
    a = b := by
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hb_spec := sideParam_spec_of_onSide (D := D) hpq hb
  apply D.coord_inj
  calc
    D.coord a = AffineMap.lineMap (D.coord p) (D.coord q) (sideParam D p q a) :=
      ha_spec.2.symm
    _ = AffineMap.lineMap (D.coord p) (D.coord q) (sideParam D p q b) := by
      rw [hparam]
    _ = D.coord b := hb_spec.2

lemma sideParam_eq_of_lineMap_local {p q w : D.vtx} (hpq : p ≠ q) {t : ℝ}
    (hw : D.coord w = AffineMap.lineMap (D.coord p) (D.coord q) t) :
    sideParam D p q w = t := by
  have hcoord_ne : D.coord q ≠ D.coord p := by
    intro h
    exact hpq (D.coord_inj h.symm)
  unfold sideParam
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · simp [hx]
    have hfst := congrArg Prod.fst hw
    simp [AffineMap.lineMap_apply] at hfst
    field_simp [hx]
    linarith
  · simp [hx]
    have hxeq : (D.coord q).1 = (D.coord p).1 := by exact not_not.mp hx
    have hy : (D.coord q).2 - (D.coord p).2 ≠ 0 := by
      intro hzero
      apply hcoord_ne
      ext
      · exact hxeq
      · linarith
    have hsnd := congrArg Prod.snd hw
    simp [AffineMap.lineMap_apply] at hsnd
    field_simp [hy]
    linarith

lemma lineMap_param_injective_local {p q : D.vtx} (hpq : p ≠ q) {t u : ℝ}
    (h : AffineMap.lineMap (D.coord p) (D.coord q) t =
      AffineMap.lineMap (D.coord p) (D.coord q) u) :
    t = u := by
  have hcoord_ne : D.coord q ≠ D.coord p := by
    intro hcoord
    exact hpq (D.coord_inj hcoord.symm)
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · have hfst := congrArg Prod.fst h
    simp [AffineMap.lineMap_apply] at hfst
    rcases hfst with htu | hzero
    · exact htu
    · exact False.elim (hx (by linarith))
  · have hxeq : (D.coord q).1 = (D.coord p).1 := by exact not_not.mp hx
    have hy : (D.coord q).2 - (D.coord p).2 ≠ 0 := by
      intro hzero
      apply hcoord_ne
      ext
      · exact hxeq
      · linarith
    have hsnd := congrArg Prod.snd h
    simp [AffineMap.lineMap_apply] at hsnd
    rcases hsnd with htu | hzero
    · exact htu
    · exact False.elim (hy hzero)

lemma onSide_of_sideParam_interval_local {p q u v a : D.vtx} (hpq : p ≠ q)
    (hu : OnSide D p q u) (hv : OnSide D p q v) (ha : OnSide D p q a)
    (hlt : sideParam D p q u < sideParam D p q v)
    (hua : sideParam D p q u ≤ sideParam D p q a)
    (hav : sideParam D p q a ≤ sideParam D p q v) :
    OnSide D u v a := by
  let tu := sideParam D p q u
  let tv := sideParam D p q v
  let ta := sideParam D p q a
  have hu_spec := sideParam_spec_of_onSide (D := D) hpq hu
  have hv_spec := sideParam_spec_of_onSide (D := D) hpq hv
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hden : tv - tu ≠ 0 := by
    dsimp [tu, tv]
    linarith
  have hden_pos : 0 < tv - tu := by
    dsimp [tu, tv]
    linarith
  let r : ℝ := (ta - tu) / (tv - tu)
  unfold OnSide
  rw [← mem_segment_iff_wbtw (R := ℝ), segment_eq_image_lineMap]
  refine ⟨r, ⟨?_, ?_⟩, ?_⟩
  · dsimp [r, tu, tv, ta]
    exact div_nonneg (sub_nonneg.mpr hua) (le_of_lt hden_pos)
  · dsimp [r, tu, tv, ta]
    rw [div_le_one hden_pos]
    linarith
  · calc
      AffineMap.lineMap (D.coord u) (D.coord v) r
          = AffineMap.lineMap
              (AffineMap.lineMap (D.coord p) (D.coord q) tu)
              (AffineMap.lineMap (D.coord p) (D.coord q) tv) r := by
              rw [hu_spec.2, hv_spec.2]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ((1 - r) * tu + r * tv) := by
              ext <;> simp [AffineMap.lineMap_apply] <;> ring
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ta := by
              congr 1
              dsimp [r]
              field_simp [hden]
              ring
      _ = D.coord a := ha_spec.2

lemma mem_sideChain_of_onSide_local {p q w : D.vtx}
    (hw : OnSide D p q w) :
    w ∈ p :: sideInteriorChain D p q ++ [q] := by
  by_cases hwp : w = p
  · simp [hwp]
  by_cases hwq : w = q
  · simp [hwq]
  have hwint : w ∈ sideInteriorChain D p q := by
    rw [mem_sideInteriorChain_iff_local]
    exact ⟨hw, hwp, hwq⟩
  simp [hwint]

lemma lineMap_lineMap_param (P Q : ℝ × ℝ) (ta tb r : ℝ) :
    AffineMap.lineMap
        (AffineMap.lineMap P Q ta) (AffineMap.lineMap P Q tb) r =
      AffineMap.lineMap P Q ((1 - r) * ta + r * tb) := by
  ext <;> simp [AffineMap.lineMap_apply] <;> ring

lemma sbtw_of_sideParam_between_local {p q a b z : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b) (hz : OnSide D p q z)
    (haz : sideParam D p q a < sideParam D p q z)
    (hzb : sideParam D p q z < sideParam D p q b) :
    Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  let ta := sideParam D p q a
  let tz := sideParam D p q z
  let tb := sideParam D p q b
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hz_spec := sideParam_spec_of_onSide (D := D) hpq hz
  have hb_spec := sideParam_spec_of_onSide (D := D) hpq hb
  have hden : tb - ta ≠ 0 := by
    dsimp [ta, tb]
    linarith
  have hden_pos : 0 < tb - ta := by
    dsimp [ta, tb]
    linarith
  have hnumer_pos : 0 < tz - ta := by
    dsimp [ta, tz]
    linarith
  let r : ℝ := (tz - ta) / (tb - ta)
  have hr : r ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [r, ta, tz, tb]
      exact div_pos hnumer_pos hden_pos
    · dsimp [r, ta, tz, tb]
      rw [div_lt_one (sub_pos.mpr (by simpa [ta, tz, tb] using haz.trans hzb))]
      linarith
  rw [sbtw_iff_mem_image_Ioo_and_ne]
  constructor
  · refine ⟨r, hr, ?_⟩
    calc
      AffineMap.lineMap (D.coord a) (D.coord b) r
          = AffineMap.lineMap
              (AffineMap.lineMap (D.coord p) (D.coord q) ta)
              (AffineMap.lineMap (D.coord p) (D.coord q) tb) r := by
              rw [ha_spec.2, hb_spec.2]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ((1 - r) * ta + r * tb) := by
              rw [lineMap_lineMap_param]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) tz := by
              congr 1
              dsimp [r]
              field_simp [hden]
              ring
      _ = D.coord z := hz_spec.2
  · intro hab
    have habv : a = b := D.coord_inj hab
    subst b
    linarith

lemma sideParam_between_of_sbtw_local {p q a b z : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b) (hz : OnSide D p q z)
    (hs : Sbtw ℝ (D.coord a) (D.coord z) (D.coord b)) :
    (sideParam D p q a < sideParam D p q z ∧
        sideParam D p q z < sideParam D p q b) ∨
      (sideParam D p q b < sideParam D p q z ∧
        sideParam D p q z < sideParam D p q a) := by
  let ta := sideParam D p q a
  let tz := sideParam D p q z
  let tb := sideParam D p q b
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hz_spec := sideParam_spec_of_onSide (D := D) hpq hz
  have hb_spec := sideParam_spec_of_onSide (D := D) hpq hb
  rcases hs.mem_image_Ioo with ⟨r, hr, hzr⟩
  have hz_param : tz = (1 - r) * ta + r * tb := by
    dsimp [tz]
    apply sideParam_eq_of_lineMap_local D hpq
    calc
      D.coord z = AffineMap.lineMap (D.coord a) (D.coord b) r := hzr.symm
      _ = AffineMap.lineMap
            (AffineMap.lineMap (D.coord p) (D.coord q) ta)
            (AffineMap.lineMap (D.coord p) (D.coord q) tb) r := by
            rw [ha_spec.2, hb_spec.2]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ((1 - r) * ta + r * tb) := by
            rw [lineMap_lineMap_param]
  have hne_param : ta ≠ tb := by
    intro htab
    have hcoord : D.coord a = D.coord b := by
      calc
        D.coord a = AffineMap.lineMap (D.coord p) (D.coord q) ta := ha_spec.2.symm
        _ = AffineMap.lineMap (D.coord p) (D.coord q) tb := by rw [htab]
        _ = D.coord b := hb_spec.2
    exact hs.left_ne_right hcoord
  rcases lt_or_gt_of_ne hne_param with hlt | hgt
  · left
    change ta < tz ∧ tz < tb
    rw [hz_param]
    constructor <;> nlinarith [hr.1, hr.2, hlt]
  · right
    change tb < tz ∧ tz < ta
    rw [hz_param]
    constructor <;> nlinarith [hr.1, hr.2, hgt]

lemma mem_sideAtomicEdges_of_onSide_no_sideParam_between
    {p q a b : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b)
    (hlt : sideParam D p q a < sideParam D p q b)
    (hno : ∀ z : D.vtx, OnSide D p q z →
      ¬ (sideParam D p q a < sideParam D p q z ∧
        sideParam D p q z < sideParam D p q b)) :
    s(a, b) ∈ sideAtomicEdges D p q := by
  let chain := p :: sideInteriorChain D p q ++ [q]
  have ha_mem : a ∈ chain := mem_sideChain_of_onSide_local (D := D) ha
  have hb_mem : b ∈ chain := mem_sideChain_of_onSide_local (D := D) hb
  have hall : ∀ x, x ∈ chain → OnSide D p q x := by
    intro x hx
    exact onSide_of_mem_sideChain_local D hx
  unfold sideAtomicEdges
  exact mem_consecutiveEdges_of_pairwise_no_between
    (l := chain) (f := sideParam D p q) (P := fun x => OnSide D p q x)
    (sideChain_nodup_local D hpq) hall
    (fun x y hx hy hxy => sideParam_injective_onSide_local D hpq hx hy hxy)
    (sideChain_pairwise_sideParam (D := D) hpq) ha_mem hb_mem hlt
    (fun z hz => hno z (hall z hz))

lemma mem_sideAtomicEdges_of_onSide_no_sbtw
    {p q a b : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b) (hab : a ≠ b)
    (hno : ∀ z : D.vtx, ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b)) :
    s(a, b) ∈ sideAtomicEdges D p q := by
  have hparam_ne : sideParam D p q a ≠ sideParam D p q b := by
    intro hparam
    exact hab (sideParam_injective_onSide_local D hpq ha hb hparam)
  rcases lt_or_gt_of_ne hparam_ne with hlt | hgt
  · exact mem_sideAtomicEdges_of_onSide_no_sideParam_between (D := D) hpq ha hb hlt
      (fun z hz hbetween =>
        hno z (sbtw_of_sideParam_between_local (D := D) hpq ha hb hz hbetween.1 hbetween.2))
  · have hmem : s(b, a) ∈ sideAtomicEdges D p q :=
      mem_sideAtomicEdges_of_onSide_no_sideParam_between (D := D) hpq hb ha hgt
        (fun z hz hbetween =>
          hno z ((sbtw_of_sideParam_between_local (D := D) hpq hb ha hz
            hbetween.1 hbetween.2).symm))
    simpa [Sym2.eq_swap] using hmem

lemma segment_subset_of_onSide_local {p q a b : D.vtx}
    (ha : OnSide D p q a) (hb : OnSide D p q b) :
    segment ℝ (D.coord a) (D.coord b) ⊆ segment ℝ (D.coord p) (D.coord q) := by
  exact (convex_segment (D.coord p) (D.coord q)).segment_subset
    (Wbtw.mem_segment ha) (Wbtw.mem_segment hb)

lemma not_sbtw_of_mem_sideAtomicEdges {p q a b z : D.vtx} (hpq : p ≠ q)
    (h : s(a, b) ∈ sideAtomicEdges D p q) :
    ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  intro hs
  have hmem :
      s(a, b) ∈ consecutiveEdges (p :: sideInteriorChain D p q ++ [q]) := by
    simpa [sideAtomicEdges] using h
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D h
  have hzseg :
      D.coord z ∈ segment ℝ (D.coord p) (D.coord q) :=
    segment_subset_of_onSide_local D hon.1 hon.2 hs.wbtw.mem_segment
  have hzon : OnSide D p q z := (mem_segment_iff_wbtw (R := ℝ)).mp hzseg
  have hzmem : z ∈ p :: sideInteriorChain D p q ++ [q] :=
    mem_sideChain_of_onSide_local (D := D) hzon
  rcases sideParam_between_of_sbtw_local (D := D) hpq hon.1 hon.2 hzon hs with hbetween | hbetween
  · exact not_sideParam_between_of_mem_sideAtomicEdges D hpq h hzmem hbetween
  · have hswap : s(b, a) ∈ sideAtomicEdges D p q := by
      simpa [Sym2.eq_swap] using h
    exact not_sideParam_between_of_mem_sideAtomicEdges D hpq hswap hzmem hbetween

lemma endpoints_onSide_of_midpoint_openSegment_of_square_sideAtomic
    {p q a b u v : D.vtx} (hpq : p ≠ q)
    (hside : s(a, b) ∈ sideAtomicEdges D p q)
    (hu : OnSide D p q u) (hv : OnSide D p q v)
    (hmuv : midpoint ℝ (D.coord a) (D.coord b) ∈
      openSegment ℝ (D.coord u) (D.coord v)) :
    OnSide D u v a ∧ OnSide D u v b := by
  let ta := sideParam D p q a
  let tb := sideParam D p q b
  let tu := sideParam D p q u
  let tv := sideParam D p q v
  let tm := (ta + tb) / 2
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D hside
  have ha := hon.1
  have hb := hon.2
  have hab : a ≠ b := ne_of_mk_mem_sideAtomicEdges_local D hpq hside
  have hcoord_ab : D.coord a ≠ D.coord b := by
    intro hcoord
    exact hab (D.coord_inj hcoord)
  have hno : ∀ z : D.vtx, ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) :=
    fun z => not_sbtw_of_mem_sideAtomicEdges D hpq hside
  have hmid_ne_vertex : ∀ z : D.vtx,
      D.coord z ≠ midpoint ℝ (D.coord a) (D.coord b) := by
    intro z hz
    exact hno z (by
      simpa [hz] using sbtw_midpoint_of_ne (R := ℝ) hcoord_ab)
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hb_spec := sideParam_spec_of_onSide (D := D) hpq hb
  have hu_spec := sideParam_spec_of_onSide (D := D) hpq hu
  have hv_spec := sideParam_spec_of_onSide (D := D) hpq hv
  have hm_pq :
      midpoint ℝ (D.coord a) (D.coord b) =
        AffineMap.lineMap (D.coord p) (D.coord q) tm := by
    calc
      midpoint ℝ (D.coord a) (D.coord b)
          = AffineMap.lineMap (D.coord a) (D.coord b) ((1 : ℝ) / 2) := by
              rw [midpoint]
              ext <;> simp [AffineMap.lineMap_apply, invOf_eq_inv] <;> ring
      _ = AffineMap.lineMap
            (AffineMap.lineMap (D.coord p) (D.coord q) ta)
            (AffineMap.lineMap (D.coord p) (D.coord q) tb) ((1 : ℝ) / 2) := by
            rw [ha_spec.2, hb_spec.2]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) tm := by
            ext <;> simp [AffineMap.lineMap_apply, tm, ta, tb] <;> ring
  rw [openSegment_eq_image_lineMap] at hmuv
  rcases hmuv with ⟨r, hr, hmuv⟩
  have htm_uv : tm = (1 - r) * tu + r * tv := by
    apply lineMap_param_injective_local (D := D) hpq
    calc
      AffineMap.lineMap (D.coord p) (D.coord q) tm
          = midpoint ℝ (D.coord a) (D.coord b) := hm_pq.symm
      _ = AffineMap.lineMap (D.coord u) (D.coord v) r := hmuv.symm
      _ = AffineMap.lineMap
            (AffineMap.lineMap (D.coord p) (D.coord q) tu)
            (AffineMap.lineMap (D.coord p) (D.coord q) tv) r := by
            rw [hu_spec.2, hv_spec.2]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ((1 - r) * tu + r * tv) := by
            rw [lineMap_lineMap_param]
  have hparam_ne : ta ≠ tb := by
    intro htab
    exact hab (sideParam_injective_onSide_local D hpq ha hb htab)
  have huv_ne : tu ≠ tv := by
    intro htuv
    have huvcoord : D.coord u = D.coord v := by
      calc
        D.coord u = AffineMap.lineMap (D.coord p) (D.coord q) tu := hu_spec.2.symm
        _ = AffineMap.lineMap (D.coord p) (D.coord q) tv := by rw [htuv]
        _ = D.coord v := hv_spec.2
    have hm_eq_u : midpoint ℝ (D.coord a) (D.coord b) = D.coord u := by
      rw [huvcoord] at hmuv
      have hm_eq_v : midpoint ℝ (D.coord a) (D.coord b) = D.coord v := by
        simpa [AffineMap.lineMap_apply] using hmuv.symm
      exact hm_eq_v.trans huvcoord.symm
    exact hmid_ne_vertex u hm_eq_u.symm
  rcases lt_or_gt_of_ne hparam_ne with htab | htba
  · have htm_ab : ta < tm ∧ tm < tb := by
      dsimp [tm]
      constructor <;> nlinarith
    have hnot_u_between : ¬ (ta < tu ∧ tu < tb) := by
      intro hbetween
      exact hno u (sbtw_of_sideParam_between_local
        (D := D) hpq ha hb hu hbetween.1 hbetween.2)
    have hnot_v_between : ¬ (ta < tv ∧ tv < tb) := by
      intro hbetween
      exact hno v (sbtw_of_sideParam_between_local
        (D := D) hpq ha hb hv hbetween.1 hbetween.2)
    rcases lt_or_gt_of_ne huv_ne with htuv | hvtu
    · have htu_tm : tu < tm := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, htuv]
      have htm_tv : tm < tv := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, htuv]
      have htu_le_ta : tu ≤ ta := by
        by_contra hle
        exact hnot_u_between ⟨lt_of_not_ge hle, lt_trans htu_tm htm_ab.2⟩
      have htb_le_tv : tb ≤ tv := by
        by_contra hle
        exact hnot_v_between ⟨lt_trans htm_ab.1 htm_tv, lt_of_not_ge hle⟩
      constructor
      · exact onSide_of_sideParam_interval_local (D := D) hpq hu hv ha htuv
          htu_le_ta (le_trans htab.le htb_le_tv)
      · exact onSide_of_sideParam_interval_local (D := D) hpq hu hv hb htuv
          (le_trans htu_le_ta htab.le) htb_le_tv
    · have htv_tm : tv < tm := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, hvtu]
      have htm_tu : tm < tu := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, hvtu]
      have htv_le_ta : tv ≤ ta := by
        by_contra hle
        exact hnot_v_between ⟨lt_of_not_ge hle, lt_trans htv_tm htm_ab.2⟩
      have htb_le_tu : tb ≤ tu := by
        by_contra hle
        exact hnot_u_between ⟨lt_trans htm_ab.1 htm_tu, lt_of_not_ge hle⟩
      constructor
      · have h := onSide_of_sideParam_interval_local (D := D) hpq hv hu ha hvtu
          htv_le_ta (le_trans htab.le htb_le_tu)
        simpa [OnSide, wbtw_comm (R := ℝ)] using h
      · have h := onSide_of_sideParam_interval_local (D := D) hpq hv hu hb hvtu
          (le_trans htv_le_ta htab.le) htb_le_tu
        simpa [OnSide, wbtw_comm (R := ℝ)] using h
  · have htm_ba : tb < tm ∧ tm < ta := by
      dsimp [tm]
      constructor <;> nlinarith
    have hnot_u_between : ¬ (tb < tu ∧ tu < ta) := by
      intro hbetween
      exact hno u ((sbtw_of_sideParam_between_local
        (D := D) hpq hb ha hu hbetween.1 hbetween.2).symm)
    have hnot_v_between : ¬ (tb < tv ∧ tv < ta) := by
      intro hbetween
      exact hno v ((sbtw_of_sideParam_between_local
        (D := D) hpq hb ha hv hbetween.1 hbetween.2).symm)
    rcases lt_or_gt_of_ne huv_ne with htuv | hvtu
    · have htu_tm : tu < tm := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, htuv]
      have htm_tv : tm < tv := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, htuv]
      have htu_le_tb : tu ≤ tb := by
        by_contra hle
        exact hnot_u_between ⟨lt_of_not_ge hle, lt_trans htu_tm htm_ba.2⟩
      have hta_le_tv : ta ≤ tv := by
        by_contra hle
        exact hnot_v_between ⟨lt_trans htm_ba.1 htm_tv, lt_of_not_ge hle⟩
      constructor
      · exact onSide_of_sideParam_interval_local (D := D) hpq hu hv ha htuv
          (le_trans htu_le_tb htba.le) hta_le_tv
      · exact onSide_of_sideParam_interval_local (D := D) hpq hu hv hb htuv
          htu_le_tb (le_trans htba.le hta_le_tv)
    · have htv_tm : tv < tm := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, hvtu]
      have htm_tu : tm < tu := by
        rw [htm_uv]
        nlinarith [hr.1, hr.2, hvtu]
      have htv_le_tb : tv ≤ tb := by
        by_contra hle
        exact hnot_v_between ⟨lt_of_not_ge hle, lt_trans htv_tm htm_ba.2⟩
      have hta_le_tu : ta ≤ tu := by
        by_contra hle
        exact hnot_u_between ⟨lt_trans htm_ba.1 htm_tu, lt_of_not_ge hle⟩
      constructor
      · have h := onSide_of_sideParam_interval_local (D := D) hpq hv hu ha hvtu
          (le_trans htv_le_tb htba.le) hta_le_tu
        simpa [OnSide, wbtw_comm (R := ℝ)] using h
      · have h := onSide_of_sideParam_interval_local (D := D) hpq hv hu hb hvtu
          htv_le_tb (le_trans htba.le hta_le_tu)
        simpa [OnSide, wbtw_comm (R := ℝ)] using h

lemma mem_triAtomicEdges_iff_local {i : Fin D.n} {e : Sym2 D.vtx} :
    e ∈ triAtomicEdges D i ↔
      e ∈ sideAtomicEdges D (D.tri i).1 (D.tri i).2.1 ∨
      e ∈ sideAtomicEdges D (D.tri i).2.1 (D.tri i).2.2 ∨
      e ∈ sideAtomicEdges D (D.tri i).2.2 (D.tri i).1 := by
  simp [triAtomicEdges, or_assoc]

lemma tri_v₁_ne_v₂_local (i : Fin D.n) : (D.tri i).1 ≠ (D.tri i).2.1 := by
  intro h
  apply D.nondeg i
  simpa [h, doubleArea]

lemma tri_v₂_ne_v₃_local (i : Fin D.n) : (D.tri i).2.1 ≠ (D.tri i).2.2 := by
  intro h
  apply D.nondeg i
  simpa [h, doubleArea]

lemma tri_v₃_ne_v₁_local (i : Fin D.n) : (D.tri i).2.2 ≠ (D.tri i).1 := by
  intro h
  apply D.nondeg i
  simpa [h, doubleArea]

lemma not_sbtw_of_mem_triAtomicEdges {i : Fin D.n} {a b z : D.vtx}
    (h : s(a, b) ∈ triAtomicEdges D i) :
    ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  rw [mem_triAtomicEdges_iff_local] at h
  rcases h with h | h | h
  · exact not_sbtw_of_mem_sideAtomicEdges D (tri_v₁_ne_v₂_local D i) h
  · exact not_sbtw_of_mem_sideAtomicEdges D (tri_v₂_ne_v₃_local D i) h
  · exact not_sbtw_of_mem_sideAtomicEdges D (tri_v₃_ne_v₁_local D i) h

lemma not_sbtw_of_isAtomicEdge_mk {a b z : D.vtx}
    (he : IsAtomicEdge D s(a, b)) :
    ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  rcases he with ⟨i, hi⟩
  exact not_sbtw_of_mem_triAtomicEdges D hi

lemma coord_bottom_of_onSide {p q v : D.vtx}
    (hp : D.coord p = (0, 0)) (hq : D.coord q = (1, 0))
    (h : OnSide D p q v) :
    ∃ x : ℝ, D.coord v = (x, 0) := by
  unfold OnSide at h
  obtain ⟨t, _ht, hv⟩ := h
  refine ⟨(D.coord v).1, ?_⟩
  ext
  · rfl
  · have hy := congrArg Prod.snd hv
    simpa [hp, hq, AffineMap.lineMap_apply] using hy.symm

lemma coord_right_of_onSide {p q v : D.vtx}
    (hp : D.coord p = (1, 0)) (hq : D.coord q = (1, 1))
    (h : OnSide D p q v) :
    ∃ y : ℝ, D.coord v = (1, y) := by
  unfold OnSide at h
  obtain ⟨t, _ht, hv⟩ := h
  refine ⟨(D.coord v).2, ?_⟩
  ext
  · have hx := congrArg Prod.fst hv
    simpa [hp, hq, AffineMap.lineMap_apply] using hx.symm
  · rfl

lemma coord_top_of_onSide {p q v : D.vtx}
    (hp : D.coord p = (1, 1)) (hq : D.coord q = (0, 1))
    (h : OnSide D p q v) :
    ∃ x : ℝ, D.coord v = (x, 1) := by
  unfold OnSide at h
  obtain ⟨t, _ht, hv⟩ := h
  refine ⟨(D.coord v).1, ?_⟩
  ext
  · rfl
  · have hy := congrArg Prod.snd hv
    simpa [hp, hq, AffineMap.lineMap_apply] using hy.symm

lemma coord_left_of_onSide {p q v : D.vtx}
    (hp : D.coord p = (0, 1)) (hq : D.coord q = (0, 0))
    (h : OnSide D p q v) :
    ∃ y : ℝ, D.coord v = (0, y) := by
  unfold OnSide at h
  obtain ⟨t, _ht, hv⟩ := h
  refine ⟨(D.coord v).2, ?_⟩
  ext
  · have hx := congrArg Prod.fst hv
    simpa [hp, hq, AffineMap.lineMap_apply] using hx.symm
  · rfl

lemma mem_segment_unit_bottom (p : ℝ × ℝ) :
    p ∈ segment ℝ ((0, 0) : ℝ × ℝ) (1, 0) ↔
      0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa [AffineMap.lineMap_apply] using ht
  · intro hp
    refine ⟨p.1, ⟨hp.1, hp.2.1⟩, ?_⟩
    ext <;> simp [AffineMap.lineMap_apply, hp.2.2]

lemma mem_segment_unit_right (p : ℝ × ℝ) :
    p ∈ segment ℝ ((1, 0) : ℝ × ℝ) (1, 1) ↔
      p.1 = 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa [AffineMap.lineMap_apply] using ht
  · intro hp
    refine ⟨p.2, ⟨hp.2.1, hp.2.2⟩, ?_⟩
    ext <;> simp [AffineMap.lineMap_apply, hp.1]

lemma mem_segment_unit_top (p : ℝ × ℝ) :
    p ∈ segment ℝ ((1, 1) : ℝ × ℝ) (0, 1) ↔
      0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 1 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · simp [Prod.smul_mk, Prod.mk_add_mk]
      linarith [ht.2]
    · constructor
      · simp [Prod.smul_mk, Prod.mk_add_mk]
        linarith [ht.1]
      · simp [Prod.smul_mk, Prod.mk_add_mk]
  · intro hp
    refine ⟨1 - p.1, ⟨?_, ?_⟩, ?_⟩
    · linarith
    · linarith
    · ext <;> simp [AffineMap.lineMap_apply, hp.2.2] <;> ring

lemma mem_segment_unit_left (p : ℝ × ℝ) :
    p ∈ segment ℝ ((0, 1) : ℝ × ℝ) (0, 0) ↔
      p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · simp [Prod.smul_mk, Prod.mk_add_mk]
    · constructor
      · simp [Prod.smul_mk, Prod.mk_add_mk]
        linarith [ht.2]
      · simp [Prod.smul_mk, Prod.mk_add_mk]
        linarith [ht.1]
  · intro hp
    refine ⟨1 - p.2, ⟨?_, ?_⟩, ?_⟩
    · linarith
    · linarith
    · ext <;> simp [AffineMap.lineMap_apply, hp.1] <;> ring

lemma onSide_bottom_of_coord {c00 c10 v : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (hx0 : 0 ≤ (D.coord v).1) (hx1 : (D.coord v).1 ≤ 1)
    (hy : (D.coord v).2 = 0) :
    OnSide D c00 c10 v := by
  unfold OnSide
  rw [← mem_segment_iff_wbtw (R := ℝ)]
  rw [h00, h10, mem_segment_unit_bottom]
  exact ⟨hx0, hx1, hy⟩

lemma onSide_right_of_coord {c10 c11 v : D.vtx}
    (h10 : D.coord c10 = (1, 0)) (h11 : D.coord c11 = (1, 1))
    (hx : (D.coord v).1 = 1) (hy0 : 0 ≤ (D.coord v).2)
    (hy1 : (D.coord v).2 ≤ 1) :
    OnSide D c10 c11 v := by
  unfold OnSide
  rw [← mem_segment_iff_wbtw (R := ℝ)]
  rw [h10, h11, mem_segment_unit_right]
  exact ⟨hx, hy0, hy1⟩

lemma onSide_top_of_coord {c11 c01 v : D.vtx}
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    (hx0 : 0 ≤ (D.coord v).1) (hx1 : (D.coord v).1 ≤ 1)
    (hy : (D.coord v).2 = 1) :
    OnSide D c11 c01 v := by
  unfold OnSide
  rw [← mem_segment_iff_wbtw (R := ℝ)]
  rw [h11, h01, mem_segment_unit_top]
  exact ⟨hx0, hx1, hy⟩

lemma onSide_left_of_coord {c01 c00 v : D.vtx}
    (h01 : D.coord c01 = (0, 1)) (h00 : D.coord c00 = (0, 0))
    (hx : (D.coord v).1 = 0) (hy0 : 0 ≤ (D.coord v).2)
    (hy1 : (D.coord v).2 ≤ 1) :
    OnSide D c01 c00 v := by
  unfold OnSide
  rw [← mem_segment_iff_wbtw (R := ℝ)]
  rw [h01, h00, mem_segment_unit_left]
  exact ⟨hx, hy0, hy1⟩

lemma bottom_segment_subset_frontier
    {c00 c10 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0)) :
    segment ℝ (D.coord c00) (D.coord c10) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
  intro x hx
  rw [h00, h10, mem_segment_unit_bottom] at hx
  rw [frontier_unitSquare]
  exact ⟨hx.1, hx.2.1, by linarith, by linarith, Or.inr <| Or.inr <| Or.inl hx.2.2⟩

lemma right_segment_subset_frontier
    {c10 c11 : D.vtx}
    (h10 : D.coord c10 = (1, 0)) (h11 : D.coord c11 = (1, 1)) :
    segment ℝ (D.coord c10) (D.coord c11) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
  intro x hx
  rw [h10, h11, mem_segment_unit_right] at hx
  rw [frontier_unitSquare]
  exact ⟨by linarith, by linarith, hx.2.1, hx.2.2, Or.inr <| Or.inl hx.1⟩

lemma top_segment_subset_frontier
    {c11 c01 : D.vtx}
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1)) :
    segment ℝ (D.coord c11) (D.coord c01) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
  intro x hx
  rw [h11, h01, mem_segment_unit_top] at hx
  rw [frontier_unitSquare]
  exact ⟨hx.1, hx.2.1, by linarith, by linarith, Or.inr <| Or.inr <| Or.inr hx.2.2⟩

lemma left_segment_subset_frontier
    {c01 c00 : D.vtx}
    (h01 : D.coord c01 = (0, 1)) (h00 : D.coord c00 = (0, 0)) :
    segment ℝ (D.coord c01) (D.coord c00) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
  intro x hx
  rw [h01, h00, mem_segment_unit_left] at hx
  rw [frontier_unitSquare]
  exact ⟨by linarith, by linarith, hx.2.1, hx.2.2, Or.inl hx.1⟩

lemma onSquareBoundary_mk_iff {a b : D.vtx} :
    OnSquareBoundary D s(a, b) ↔
      segment ℝ (D.coord a) (D.coord b) ⊆
        frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
  rfl

lemma tri_vertex₁_mem_unitSquare (i : Fin D.n) :
    D.coord (D.tri i).1 ∈ unitSquareSetLocal := by
  exact triHullLocal_subset_unitSquare D i (by
    unfold triHullLocal
    exact subset_convexHull ℝ
      ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
        D.coord (D.tri i).2.2} : Set (ℝ × ℝ)) (by simp))

lemma tri_vertex₂_mem_unitSquare (i : Fin D.n) :
    D.coord (D.tri i).2.1 ∈ unitSquareSetLocal := by
  exact triHullLocal_subset_unitSquare D i (by
    unfold triHullLocal
    exact subset_convexHull ℝ
      ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
        D.coord (D.tri i).2.2} : Set (ℝ × ℝ)) (by simp))

lemma tri_vertex₃_mem_unitSquare (i : Fin D.n) :
    D.coord (D.tri i).2.2 ∈ unitSquareSetLocal := by
  exact triHullLocal_subset_unitSquare D i (by
    unfold triHullLocal
    exact subset_convexHull ℝ
      ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
        D.coord (D.tri i).2.2} : Set (ℝ × ℝ)) (by simp))

lemma openSegment_endpoints_on_bottom_of_mem_unitSquare
    {u v m : ℝ × ℝ} (hu : u ∈ unitSquareSetLocal) (hv : v ∈ unitSquareSetLocal)
    (hm : m ∈ openSegment ℝ u v) (hmy : m.2 = 0) :
    u.2 = 0 ∧ v.2 = 0 := by
  have hu' : 0 ≤ u.2 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.1.2
  have hv' : 0 ≤ v.2 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.1.2
  rw [openSegment_eq_image] at hm
  rcases hm with ⟨t, ht, hm⟩
  have hsnd := congrArg Prod.snd hm
  simp [hmy, Prod.smul_mk, Prod.mk_add_mk] at hsnd
  constructor <;> nlinarith [ht.1, ht.2, hu', hv', hsnd]

lemma openSegment_endpoints_on_top_of_mem_unitSquare
    {u v m : ℝ × ℝ} (hu : u ∈ unitSquareSetLocal) (hv : v ∈ unitSquareSetLocal)
    (hm : m ∈ openSegment ℝ u v) (hmy : m.2 = 1) :
    u.2 = 1 ∧ v.2 = 1 := by
  have hu' : u.2 ≤ 1 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.2.2
  have hv' : v.2 ≤ 1 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.2.2
  rw [openSegment_eq_image] at hm
  rcases hm with ⟨t, ht, hm⟩
  have hsnd := congrArg Prod.snd hm
  simp [hmy, Prod.smul_mk, Prod.mk_add_mk] at hsnd
  constructor <;> nlinarith [ht.1, ht.2, hu', hv', hsnd]

lemma openSegment_endpoints_on_left_of_mem_unitSquare
    {u v m : ℝ × ℝ} (hu : u ∈ unitSquareSetLocal) (hv : v ∈ unitSquareSetLocal)
    (hm : m ∈ openSegment ℝ u v) (hmx : m.1 = 0) :
    u.1 = 0 ∧ v.1 = 0 := by
  have hu' : 0 ≤ u.1 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.1.1
  have hv' : 0 ≤ v.1 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.1.1
  rw [openSegment_eq_image] at hm
  rcases hm with ⟨t, ht, hm⟩
  have hfst := congrArg Prod.fst hm
  simp [hmx, Prod.smul_mk, Prod.mk_add_mk] at hfst
  constructor <;> nlinarith [ht.1, ht.2, hu', hv', hfst]

lemma openSegment_endpoints_on_right_of_mem_unitSquare
    {u v m : ℝ × ℝ} (hu : u ∈ unitSquareSetLocal) (hv : v ∈ unitSquareSetLocal)
    (hm : m ∈ openSegment ℝ u v) (hmx : m.1 = 1) :
    u.1 = 1 ∧ v.1 = 1 := by
  have hu' : u.1 ≤ 1 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.2.1
  have hv' : v.1 ≤ 1 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.2.1
  rw [openSegment_eq_image] at hm
  rcases hm with ⟨t, ht, hm⟩
  have hfst := congrArg Prod.fst hm
  simp [hmx, Prod.smul_mk, Prod.mk_add_mk] at hfst
  constructor <;> nlinarith [ht.1, ht.2, hu', hv', hfst]

lemma isAtomic_of_mem_squareSideAtomicEdges
    {p q a b : D.vtx} (hpq : p ≠ q)
    (hside : s(a, b) ∈ sideAtomicEdges D p q)
    (hfront : segment ℝ (D.coord p) (D.coord q) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)))
    (support : ∀ u v : D.vtx,
      D.coord u ∈ unitSquareSetLocal → D.coord v ∈ unitSquareSetLocal →
      midpoint ℝ (D.coord a) (D.coord b) ∈
        openSegment ℝ (D.coord u) (D.coord v) →
      OnSide D p q u ∧ OnSide D p q v) :
    IsAtomicEdge D s(a, b) := by
  let m := midpoint ℝ (D.coord a) (D.coord b)
  have honSquare := endpoints_onSide_of_mem_sideAtomicEdges_local D hside
  have hmSide :
      m ∈ segment ℝ (D.coord p) (D.coord q) :=
    segment_subset_of_onSide_local D honSquare.1 honSquare.2
      (by simpa [m] using midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
  have hmFront : m ∈ frontier unitSquareSetLocal := by
    simpa [unitSquareSetLocal, m] using hfront hmSide
  have hmSq : m ∈ unitSquareSetLocal := by
    have hmf :
        m ∈ frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
      simpa [unitSquareSetLocal] using hmFront
    rw [frontier_unitSquare] at hmf
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using
      ⟨⟨hmf.1, hmf.2.2.1⟩, ⟨hmf.2.1, hmf.2.2.2.1⟩⟩
  have hmUnion :
      m ∈ ⋃ i : Fin D.n, convexHull ℝ
        {D.coord (D.tri i).1, D.coord (D.tri i).2.1, D.coord (D.tri i).2.2} := by
    have hmSq' : m ∈ Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1) := by
      simpa [unitSquareSetLocal] using hmSq
    rw [← D.cover] at hmSq'
    exact hmSq'
  rcases Set.mem_iUnion.mp hmUnion with ⟨i, hmi⟩
  have hmiLocal : m ∈ triHullLocal D i := by
    simpa [triHullLocal] using hmi
  have hmTriFront : m ∈ frontier (triHullLocal D i) := by
    exact (mem_frontier_iff_notMem_interior hmiLocal).mpr
      (not_mem_interior_triHull_of_mem_frontier_unitSquare (D := D) hmFront i)
  have hab : a ≠ b := ne_of_mk_mem_sideAtomicEdges_local D hpq hside
  have hcoord_ab : D.coord a ≠ D.coord b := by
    intro hcoord
    exact hab (D.coord_inj hcoord)
  have hno : ∀ z : D.vtx, ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) :=
    fun z => not_sbtw_of_mem_sideAtomicEdges D hpq hside
  have hmid_ne_vertex : ∀ z : D.vtx, D.coord z ≠ m := by
    intro z hz
    exact hno z (by
      simpa [m, hz] using sbtw_midpoint_of_ne (R := ℝ) hcoord_ab)
  rw [triHullLocal, frontier_convexHull_triangle_of_doubleArea_ne_zero
      (D.coord (D.tri i).1) (D.coord (D.tri i).2.1) (D.coord (D.tri i).2.2)
      (D.nondeg i)] at hmTriFront
  rcases hmTriFront with h₁₂₂₃ | h₃₁
  · rcases h₁₂₂₃ with h₁₂ | h₂₃
    · have hmopen :
        m ∈ openSegment ℝ (D.coord (D.tri i).1) (D.coord (D.tri i).2.1) :=
        mem_openSegment_of_ne_left_right (hmid_ne_vertex (D.tri i).1)
          (hmid_ne_vertex (D.tri i).2.1) h₁₂
      have huv := support (D.tri i).1 (D.tri i).2.1
        (tri_vertex₁_mem_unitSquare D i) (tri_vertex₂_mem_unitSquare D i)
        (by simpa [m] using hmopen)
      have habuv := endpoints_onSide_of_midpoint_openSegment_of_square_sideAtomic
        (D := D) hpq hside huv.1 huv.2 (by simpa [m] using hmopen)
      refine ⟨i, ?_⟩
      rw [mem_triAtomicEdges_iff_local]
      exact Or.inl (mem_sideAtomicEdges_of_onSide_no_sbtw D
        (tri_v₁_ne_v₂_local D i) habuv.1 habuv.2 hab hno)
    · have hmopen :
        m ∈ openSegment ℝ (D.coord (D.tri i).2.1) (D.coord (D.tri i).2.2) :=
        mem_openSegment_of_ne_left_right (hmid_ne_vertex (D.tri i).2.1)
          (hmid_ne_vertex (D.tri i).2.2) h₂₃
      have huv := support (D.tri i).2.1 (D.tri i).2.2
        (tri_vertex₂_mem_unitSquare D i) (tri_vertex₃_mem_unitSquare D i)
        (by simpa [m] using hmopen)
      have habuv := endpoints_onSide_of_midpoint_openSegment_of_square_sideAtomic
        (D := D) hpq hside huv.1 huv.2 (by simpa [m] using hmopen)
      refine ⟨i, ?_⟩
      rw [mem_triAtomicEdges_iff_local]
      exact Or.inr <| Or.inl (mem_sideAtomicEdges_of_onSide_no_sbtw D
        (tri_v₂_ne_v₃_local D i) habuv.1 habuv.2 hab hno)
  · have hmopen :
        m ∈ openSegment ℝ (D.coord (D.tri i).2.2) (D.coord (D.tri i).1) :=
      mem_openSegment_of_ne_left_right (hmid_ne_vertex (D.tri i).2.2)
        (hmid_ne_vertex (D.tri i).1) h₃₁
    have huv := support (D.tri i).2.2 (D.tri i).1
      (tri_vertex₃_mem_unitSquare D i) (tri_vertex₁_mem_unitSquare D i)
      (by simpa [m] using hmopen)
    have habuv := endpoints_onSide_of_midpoint_openSegment_of_square_sideAtomic
      (D := D) hpq hside huv.1 huv.2 (by simpa [m] using hmopen)
    refine ⟨i, ?_⟩
    rw [mem_triAtomicEdges_iff_local]
    exact Or.inr <| Or.inr (mem_sideAtomicEdges_of_onSide_no_sbtw D
      (tri_v₃_ne_v₁_local D i) habuv.1 habuv.2 hab hno)

lemma bottom_squareSideAtomic_atomicBoundary
    {c00 c10 a b : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (hside : s(a, b) ∈ sideAtomicEdges D c00 c10) :
    IsAtomicEdge D s(a, b) ∧ OnSquareBoundary D s(a, b) := by
  have h0010 : c00 ≠ c10 := by
    intro h
    have : ((0, 0) : ℝ × ℝ) = (1, 0) := by
      rw [← h00, h, h10]
    norm_num at this
  have hfront := bottom_segment_subset_frontier (D := D) h00 h10
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D hside
  have hbd : OnSquareBoundary D s(a, b) := by
    rw [onSquareBoundary_mk_iff]
    exact (segment_subset_of_onSide_local D hon.1 hon.2).trans hfront
  have hatom : IsAtomicEdge D s(a, b) :=
    isAtomic_of_mem_squareSideAtomicEdges (D := D) h0010 hside hfront
      (fun u v hu hv hmopen => by
        have hmSide :
            midpoint ℝ (D.coord a) (D.coord b) ∈
              segment ℝ (D.coord c00) (D.coord c10) :=
          segment_subset_of_onSide_local D hon.1 hon.2
            (midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
        have hmb := hmSide
        rw [h00, h10, mem_segment_unit_bottom] at hmb
        have huv_y := openSegment_endpoints_on_bottom_of_mem_unitSquare hu hv hmopen hmb.2.2
        have hux0 : 0 ≤ (D.coord u).1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.1.1
        have hux1 : (D.coord u).1 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.2.1
        have hvx0 : 0 ≤ (D.coord v).1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.1.1
        have hvx1 : (D.coord v).1 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.2.1
        exact ⟨onSide_bottom_of_coord D h00 h10 hux0 hux1 huv_y.1,
          onSide_bottom_of_coord D h00 h10 hvx0 hvx1 huv_y.2⟩)
  exact ⟨hatom, hbd⟩

lemma right_squareSideAtomic_atomicBoundary
    {c10 c11 a b : D.vtx}
    (h10 : D.coord c10 = (1, 0)) (h11 : D.coord c11 = (1, 1))
    (hside : s(a, b) ∈ sideAtomicEdges D c10 c11) :
    IsAtomicEdge D s(a, b) ∧ OnSquareBoundary D s(a, b) := by
  have h1011 : c10 ≠ c11 := by
    intro h
    have : ((1, 0) : ℝ × ℝ) = (1, 1) := by
      rw [← h10, h, h11]
    norm_num at this
  have hfront := right_segment_subset_frontier (D := D) h10 h11
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D hside
  have hbd : OnSquareBoundary D s(a, b) := by
    rw [onSquareBoundary_mk_iff]
    exact (segment_subset_of_onSide_local D hon.1 hon.2).trans hfront
  have hatom : IsAtomicEdge D s(a, b) :=
    isAtomic_of_mem_squareSideAtomicEdges (D := D) h1011 hside hfront
      (fun u v hu hv hmopen => by
        have hmSide :
            midpoint ℝ (D.coord a) (D.coord b) ∈
              segment ℝ (D.coord c10) (D.coord c11) :=
          segment_subset_of_onSide_local D hon.1 hon.2
            (midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
        have hmr := hmSide
        rw [h10, h11, mem_segment_unit_right] at hmr
        have huv_x := openSegment_endpoints_on_right_of_mem_unitSquare hu hv hmopen hmr.1
        have huy0 : 0 ≤ (D.coord u).2 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.1.2
        have huy1 : (D.coord u).2 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.2.2
        have hvy0 : 0 ≤ (D.coord v).2 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.1.2
        have hvy1 : (D.coord v).2 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.2.2
        exact ⟨onSide_right_of_coord D h10 h11 huv_x.1 huy0 huy1,
          onSide_right_of_coord D h10 h11 huv_x.2 hvy0 hvy1⟩)
  exact ⟨hatom, hbd⟩

lemma top_squareSideAtomic_atomicBoundary
    {c11 c01 a b : D.vtx}
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    (hside : s(a, b) ∈ sideAtomicEdges D c11 c01) :
    IsAtomicEdge D s(a, b) ∧ OnSquareBoundary D s(a, b) := by
  have h1101 : c11 ≠ c01 := by
    intro h
    have : ((1, 1) : ℝ × ℝ) = (0, 1) := by
      rw [← h11, h, h01]
    norm_num at this
  have hfront := top_segment_subset_frontier (D := D) h11 h01
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D hside
  have hbd : OnSquareBoundary D s(a, b) := by
    rw [onSquareBoundary_mk_iff]
    exact (segment_subset_of_onSide_local D hon.1 hon.2).trans hfront
  have hatom : IsAtomicEdge D s(a, b) :=
    isAtomic_of_mem_squareSideAtomicEdges (D := D) h1101 hside hfront
      (fun u v hu hv hmopen => by
        have hmSide :
            midpoint ℝ (D.coord a) (D.coord b) ∈
              segment ℝ (D.coord c11) (D.coord c01) :=
          segment_subset_of_onSide_local D hon.1 hon.2
            (midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
        have hmt := hmSide
        rw [h11, h01, mem_segment_unit_top] at hmt
        have huv_y := openSegment_endpoints_on_top_of_mem_unitSquare hu hv hmopen hmt.2.2
        have hux0 : 0 ≤ (D.coord u).1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.1.1
        have hux1 : (D.coord u).1 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.2.1
        have hvx0 : 0 ≤ (D.coord v).1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.1.1
        have hvx1 : (D.coord v).1 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.2.1
        exact ⟨onSide_top_of_coord D h11 h01 hux0 hux1 huv_y.1,
          onSide_top_of_coord D h11 h01 hvx0 hvx1 huv_y.2⟩)
  exact ⟨hatom, hbd⟩

lemma left_squareSideAtomic_atomicBoundary
    {c01 c00 a b : D.vtx}
    (h01 : D.coord c01 = (0, 1)) (h00 : D.coord c00 = (0, 0))
    (hside : s(a, b) ∈ sideAtomicEdges D c01 c00) :
    IsAtomicEdge D s(a, b) ∧ OnSquareBoundary D s(a, b) := by
  have h0100 : c01 ≠ c00 := by
    intro h
    have : ((0, 1) : ℝ × ℝ) = (0, 0) := by
      rw [← h01, h, h00]
    norm_num at this
  have hfront := left_segment_subset_frontier (D := D) h01 h00
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D hside
  have hbd : OnSquareBoundary D s(a, b) := by
    rw [onSquareBoundary_mk_iff]
    exact (segment_subset_of_onSide_local D hon.1 hon.2).trans hfront
  have hatom : IsAtomicEdge D s(a, b) :=
    isAtomic_of_mem_squareSideAtomicEdges (D := D) h0100 hside hfront
      (fun u v hu hv hmopen => by
        have hmSide :
            midpoint ℝ (D.coord a) (D.coord b) ∈
              segment ℝ (D.coord c01) (D.coord c00) :=
          segment_subset_of_onSide_local D hon.1 hon.2
            (midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
        have hml := hmSide
        rw [h01, h00, mem_segment_unit_left] at hml
        have huv_x := openSegment_endpoints_on_left_of_mem_unitSquare hu hv hmopen hml.1
        have huy0 : 0 ≤ (D.coord u).2 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.1.2
        have huy1 : (D.coord u).2 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.2.2
        have hvy0 : 0 ≤ (D.coord v).2 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.1.2
        have hvy1 : (D.coord v).2 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.2.2
        exact ⟨onSide_left_of_coord D h01 h00 huv_x.1 huy0 huy1,
          onSide_left_of_coord D h01 h00 huv_x.2 hvy0 hvy1⟩)
  exact ⟨hatom, hbd⟩

lemma ne_of_mem_triAtomicEdges_local {i : Fin D.n} {a b : D.vtx}
    (h : s(a, b) ∈ triAtomicEdges D i) : a ≠ b := by
  rw [mem_triAtomicEdges_iff_local] at h
  rcases h with h | h | h
  · exact ne_of_mk_mem_sideAtomicEdges_local D (tri_v₁_ne_v₂_local D i) h
  · exact ne_of_mk_mem_sideAtomicEdges_local D (tri_v₂_ne_v₃_local D i) h
  · exact ne_of_mk_mem_sideAtomicEdges_local D (tri_v₃_ne_v₁_local D i) h

lemma ne_of_isAtomicEdge_mk {a b : D.vtx}
    (he : IsAtomicEdge D s(a, b)) : a ≠ b := by
  rcases he with ⟨i, hi⟩
  exact ne_of_mem_triAtomicEdges_local D hi

lemma square_side_cases_of_segment_subset_frontier
    {c00 c10 c11 c01 a b : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    (hseg : segment ℝ (D.coord a) (D.coord b) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1))) :
    (OnSide D c00 c10 a ∧ OnSide D c00 c10 b) ∨
      (OnSide D c10 c11 a ∧ OnSide D c10 c11 b) ∨
      (OnSide D c11 c01 a ∧ OnSide D c11 c01 b) ∨
      (OnSide D c01 c00 a ∧ OnSide D c01 c00 b) := by
  let m := midpoint ℝ (D.coord a) (D.coord b)
  have haFront := hseg (left_mem_segment ℝ (D.coord a) (D.coord b))
  have hbFront := hseg (right_mem_segment ℝ (D.coord a) (D.coord b))
  have hmFront := hseg (midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
  rw [frontier_unitSquare] at haFront hbFront hmFront
  rcases haFront with ⟨ha0x, ha1x, ha0y, ha1y, _⟩
  rcases hbFront with ⟨hb0x, hb1x, hb0y, hb1y, _⟩
  rcases hmFront with ⟨_hm0x, _hm1x, _hm0y, _hm1y, hmcase⟩
  rcases hmcase with hm0x | hm1x | hm0y | hm1y
  · have hsum : (D.coord a).1 + (D.coord b).1 = 0 := by
      have h := hm0x
      simp [m, midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at h
      linarith
    have ha_x : (D.coord a).1 = 0 := by linarith [ha0x, hb0x, hsum]
    have hb_x : (D.coord b).1 = 0 := by linarith [ha0x, hb0x, hsum]
    exact Or.inr <| Or.inr <| Or.inr
      ⟨onSide_left_of_coord D h01 h00 ha_x ha0y ha1y,
        onSide_left_of_coord D h01 h00 hb_x hb0y hb1y⟩
  · have hsum : (D.coord a).1 + (D.coord b).1 = 2 := by
      have h := hm1x
      simp [m, midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at h
      linarith
    have ha_x : (D.coord a).1 = 1 := by linarith [ha1x, hb1x, hsum]
    have hb_x : (D.coord b).1 = 1 := by linarith [ha1x, hb1x, hsum]
    exact Or.inr <| Or.inl
      ⟨onSide_right_of_coord D h10 h11 ha_x ha0y ha1y,
        onSide_right_of_coord D h10 h11 hb_x hb0y hb1y⟩
  · have hsum : (D.coord a).2 + (D.coord b).2 = 0 := by
      have h := hm0y
      simp [m, midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at h
      linarith
    have ha_y : (D.coord a).2 = 0 := by linarith [ha0y, hb0y, hsum]
    have hb_y : (D.coord b).2 = 0 := by linarith [ha0y, hb0y, hsum]
    exact Or.inl
      ⟨onSide_bottom_of_coord D h00 h10 ha0x ha1x ha_y,
        onSide_bottom_of_coord D h00 h10 hb0x hb1x hb_y⟩
  · have hsum : (D.coord a).2 + (D.coord b).2 = 2 := by
      have h := hm1y
      simp [m, midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at h
      linarith
    have ha_y : (D.coord a).2 = 1 := by linarith [ha1y, hb1y, hsum]
    have hb_y : (D.coord b).2 = 1 := by linarith [ha1y, hb1y, hsum]
    exact Or.inr <| Or.inr <| Or.inl
      ⟨onSide_top_of_coord D h11 h01 ha0x ha1x ha_y,
        onSide_top_of_coord D h11 h01 hb0x hb1x hb_y⟩

lemma square_corner_ne {a b : D.vtx} {pa pb : ℝ × ℝ}
    (ha : D.coord a = pa) (hb : D.coord b = pb) (hp : pa ≠ pb) : a ≠ b := by
  intro h
  apply hp
  calc
    pa = D.coord a := ha.symm
    _ = D.coord b := by rw [h]
    _ = pb := hb

lemma bottom_right_sideAtomicEdges_disjoint
    {c00 c10 c11 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h0010 : c00 ≠ c10) :
    (sideAtomicEdges D c00 c10).Disjoint (sideAtomicEdges D c10 c11) := by
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hne : a ≠ b := ne_of_mk_mem_sideAtomicEdges_local D h0010 he₁
      have hb := endpoints_onSide_of_mem_sideAtomicEdges_local D he₁
      have hr := endpoints_onSide_of_mem_sideAtomicEdges_local D he₂
      obtain ⟨xa, hxa⟩ := coord_bottom_of_onSide (D := D) h00 h10 hb.1
      obtain ⟨ya, hya⟩ := coord_right_of_onSide (D := D) h10 h11 hr.1
      obtain ⟨xb, hxb⟩ := coord_bottom_of_onSide (D := D) h00 h10 hb.2
      obtain ⟨yb, hyb⟩ := coord_right_of_onSide (D := D) h10 h11 hr.2
      have hacoord : D.coord a = (1, 0) := by
        ext
        · simpa using congrArg Prod.fst hya
        · simpa using congrArg Prod.snd hxa
      have hbcoord : D.coord b = (1, 0) := by
        ext
        · simpa using congrArg Prod.fst hyb
        · simpa using congrArg Prod.snd hxb
      exact hne (D.coord_inj (hacoord.trans hbcoord.symm))

lemma right_top_sideAtomicEdges_disjoint
    {c10 c11 c01 : D.vtx}
    (h10 : D.coord c10 = (1, 0)) (h11 : D.coord c11 = (1, 1))
    (h01 : D.coord c01 = (0, 1)) (h1011 : c10 ≠ c11) :
    (sideAtomicEdges D c10 c11).Disjoint (sideAtomicEdges D c11 c01) := by
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hne : a ≠ b := ne_of_mk_mem_sideAtomicEdges_local D h1011 he₁
      have hr := endpoints_onSide_of_mem_sideAtomicEdges_local D he₁
      have ht := endpoints_onSide_of_mem_sideAtomicEdges_local D he₂
      obtain ⟨ya, hya⟩ := coord_right_of_onSide (D := D) h10 h11 hr.1
      obtain ⟨xa, hxa⟩ := coord_top_of_onSide (D := D) h11 h01 ht.1
      obtain ⟨yb, hyb⟩ := coord_right_of_onSide (D := D) h10 h11 hr.2
      obtain ⟨xb, hxb⟩ := coord_top_of_onSide (D := D) h11 h01 ht.2
      have hacoord : D.coord a = (1, 1) := by
        ext
        · simpa using congrArg Prod.fst hya
        · simpa using congrArg Prod.snd hxa
      have hbcoord : D.coord b = (1, 1) := by
        ext
        · simpa using congrArg Prod.fst hyb
        · simpa using congrArg Prod.snd hxb
      exact hne (D.coord_inj (hacoord.trans hbcoord.symm))

lemma top_left_sideAtomicEdges_disjoint
    {c11 c01 c00 : D.vtx}
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    (h00 : D.coord c00 = (0, 0)) (h1101 : c11 ≠ c01) :
    (sideAtomicEdges D c11 c01).Disjoint (sideAtomicEdges D c01 c00) := by
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hne : a ≠ b := ne_of_mk_mem_sideAtomicEdges_local D h1101 he₁
      have ht := endpoints_onSide_of_mem_sideAtomicEdges_local D he₁
      have hl := endpoints_onSide_of_mem_sideAtomicEdges_local D he₂
      obtain ⟨xa, hxa⟩ := coord_top_of_onSide (D := D) h11 h01 ht.1
      obtain ⟨ya, hya⟩ := coord_left_of_onSide (D := D) h01 h00 hl.1
      obtain ⟨xb, hxb⟩ := coord_top_of_onSide (D := D) h11 h01 ht.2
      obtain ⟨yb, hyb⟩ := coord_left_of_onSide (D := D) h01 h00 hl.2
      have hacoord : D.coord a = (0, 1) := by
        ext
        · simpa using congrArg Prod.fst hya
        · simpa using congrArg Prod.snd hxa
      have hbcoord : D.coord b = (0, 1) := by
        ext
        · simpa using congrArg Prod.fst hyb
        · simpa using congrArg Prod.snd hxb
      exact hne (D.coord_inj (hacoord.trans hbcoord.symm))

lemma left_bottom_sideAtomicEdges_disjoint
    {c01 c00 c10 : D.vtx}
    (h01 : D.coord c01 = (0, 1)) (h00 : D.coord c00 = (0, 0))
    (h10 : D.coord c10 = (1, 0)) (h0100 : c01 ≠ c00) :
    (sideAtomicEdges D c01 c00).Disjoint (sideAtomicEdges D c00 c10) := by
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hne : a ≠ b := ne_of_mk_mem_sideAtomicEdges_local D h0100 he₁
      have hl := endpoints_onSide_of_mem_sideAtomicEdges_local D he₁
      have hb := endpoints_onSide_of_mem_sideAtomicEdges_local D he₂
      obtain ⟨ya, hya⟩ := coord_left_of_onSide (D := D) h01 h00 hl.1
      obtain ⟨xa, hxa⟩ := coord_bottom_of_onSide (D := D) h00 h10 hb.1
      obtain ⟨yb, hyb⟩ := coord_left_of_onSide (D := D) h01 h00 hl.2
      obtain ⟨xb, hxb⟩ := coord_bottom_of_onSide (D := D) h00 h10 hb.2
      have hacoord : D.coord a = (0, 0) := by
        ext
        · simpa using congrArg Prod.fst hya
        · simpa using congrArg Prod.snd hxa
      have hbcoord : D.coord b = (0, 0) := by
        ext
        · simpa using congrArg Prod.fst hyb
        · simpa using congrArg Prod.snd hxb
      exact hne (D.coord_inj (hacoord.trans hbcoord.symm))

lemma bottom_top_sideAtomicEdges_disjoint
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1)) :
    (sideAtomicEdges D c00 c10).Disjoint (sideAtomicEdges D c11 c01) := by
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hb := endpoints_onSide_of_mem_sideAtomicEdges_local D he₁
      have ht := endpoints_onSide_of_mem_sideAtomicEdges_local D he₂
      obtain ⟨xa, hxa⟩ := coord_bottom_of_onSide (D := D) h00 h10 hb.1
      obtain ⟨x'a, hx'a⟩ := coord_top_of_onSide (D := D) h11 h01 ht.1
      have hy0 := congrArg Prod.snd hxa
      have hy1 := congrArg Prod.snd hx'a
      linarith

lemma right_left_sideAtomicEdges_disjoint
    {c10 c11 c01 c00 : D.vtx}
    (h10 : D.coord c10 = (1, 0)) (h11 : D.coord c11 = (1, 1))
    (h01 : D.coord c01 = (0, 1)) (h00 : D.coord c00 = (0, 0)) :
    (sideAtomicEdges D c10 c11).Disjoint (sideAtomicEdges D c01 c00) := by
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hr := endpoints_onSide_of_mem_sideAtomicEdges_local D he₁
      have hl := endpoints_onSide_of_mem_sideAtomicEdges_local D he₂
      obtain ⟨ya, hya⟩ := coord_right_of_onSide (D := D) h10 h11 hr.1
      obtain ⟨y'a, hy'a⟩ := coord_left_of_onSide (D := D) h01 h00 hl.1
      have hx1 := congrArg Prod.fst hya
      have hx0 := congrArg Prod.fst hy'a
      linarith

open scoped Classical in
lemma squareBoundaryEdgeList_nodup_of_square_corners
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1)) :
    (squareBoundaryEdgeList
      (sideInteriorChain D c00 c10)
      (sideInteriorChain D c10 c11)
      (sideInteriorChain D c11 c01)
      (sideInteriorChain D c01 c00)
      c00 c10 c11 c01).Nodup := by
  classical
  have h0010 : c00 ≠ c10 :=
    square_corner_ne D h00 h10 (by norm_num)
  have h1011 : c10 ≠ c11 :=
    square_corner_ne D h10 h11 (by norm_num)
  have h1101 : c11 ≠ c01 :=
    square_corner_ne D h11 h01 (by norm_num)
  have h0100 : c01 ≠ c00 :=
    square_corner_ne D h01 h00 (by norm_num)
  let B := sideAtomicEdges D c00 c10
  let R := sideAtomicEdges D c10 c11
  let T := sideAtomicEdges D c11 c01
  let L := sideAtomicEdges D c01 c00
  have hB : B.Nodup := sideAtomicEdges_nodup_local D h0010
  have hR : R.Nodup := sideAtomicEdges_nodup_local D h1011
  have hT : T.Nodup := sideAtomicEdges_nodup_local D h1101
  have hL : L.Nodup := sideAtomicEdges_nodup_local D h0100
  have hBR : B.Disjoint R :=
    bottom_right_sideAtomicEdges_disjoint D h00 h10 h11 h0010
  have hBT : B.Disjoint T :=
    bottom_top_sideAtomicEdges_disjoint D h00 h10 h11 h01
  have hBL : B.Disjoint L :=
    (left_bottom_sideAtomicEdges_disjoint D h01 h00 h10 h0100).symm
  have hRT : R.Disjoint T :=
    right_top_sideAtomicEdges_disjoint D h10 h11 h01 h1011
  have hRL : R.Disjoint L :=
    right_left_sideAtomicEdges_disjoint D h10 h11 h01 h00
  have hTL : T.Disjoint L :=
    top_left_sideAtomicEdges_disjoint D h11 h01 h00 h1101
  have hT_L : (T ++ L).Nodup := List.Nodup.append hT hL hTL
  have hR_TL : R.Disjoint (T ++ L) := by
    rw [List.disjoint_append_right]
    exact ⟨hRT, hRL⟩
  have hR_T_L : (R ++ T ++ L).Nodup := by
    simpa [List.append_assoc] using List.Nodup.append hR hT_L hR_TL
  have hB_RTL : B.Disjoint (R ++ T ++ L) := by
    rw [List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨⟨hBR, hBT⟩, hBL⟩
  have hAll : (B ++ R ++ T ++ L).Nodup := by
    simpa [List.append_assoc] using List.Nodup.append hB hR_T_L hB_RTL
  simpa [squareBoundaryEdgeList, sideAtomicEdges, B, R, T, L, List.append_assoc] using hAll

open scoped Classical in
lemma squareBoundarySideAtomicList_RG_odd
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1)) :
    Odd (listEdgeRGCount
      (squareBoundaryEdgeList
        (sideInteriorChain D c00 c10)
        (sideInteriorChain D c10 c11)
        (sideInteriorChain D c11 c01)
        (sideInteriorChain D c01 c00)
        c00 c10 c11 c01)
      (realTwoAdicColor ∘ D.coord)) := by
  classical
  refine squareBoundaryVertexChainRGCount_odd_of_side_colors
    (sideInteriorChain D c00 c10)
    (sideInteriorChain D c10 c11)
    (sideInteriorChain D c11 c01)
    (sideInteriorChain D c01 c00)
    c00 c10 c11 c01 (realTwoAdicColor ∘ D.coord)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [h00]
  · simp [h10]
  · simp [h11]
  · simp [h01]
  · intro v hv
    obtain ⟨x, hx⟩ := coord_bottom_of_onSide (D := D) h00 h10
      ((mem_sideInteriorChain_iff_local (D := D)).mp hv).1
    simpa [Function.comp_def, hx] using realTwoAdicColor_bottom_red_or_green x
  · intro v hv
    obtain ⟨y, hy⟩ := coord_right_of_onSide (D := D) h10 h11
      ((mem_sideInteriorChain_iff_local (D := D)).mp hv).1
    simpa [Function.comp_def, hy] using realTwoAdicColor_right_green_or_blue y
  · intro v hv
    obtain ⟨x, hx⟩ := coord_top_of_onSide (D := D) h11 h01
      ((mem_sideInteriorChain_iff_local (D := D)).mp hv).1
    simpa [Function.comp_def, hx] using realTwoAdicColor_top_green_or_blue x
  · intro v hv
    obtain ⟨y, hy⟩ := coord_left_of_onSide (D := D) h01 h00
      ((mem_sideInteriorChain_iff_local (D := D)).mp hv).1
    simpa [Function.comp_def, hy] using realTwoAdicColor_left_red_or_blue y

lemma atomicBoundary_mem_squareBoundaryEdgeList_of_square_corners
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    {e : Sym2 D.vtx}
    (he : IsAtomicEdge D e ∧ OnSquareBoundary D e) :
    e ∈ (squareBoundaryEdgeList
      (sideInteriorChain D c00 c10)
      (sideInteriorChain D c10 c11)
      (sideInteriorChain D c11 c01)
      (sideInteriorChain D c01 c00)
      c00 c10 c11 c01).toFinset := by
  classical
  induction e using Sym2.ind with
  | h a b =>
      have h0010 : c00 ≠ c10 := square_corner_ne D h00 h10 (by norm_num)
      have h1011 : c10 ≠ c11 := square_corner_ne D h10 h11 (by norm_num)
      have h1101 : c11 ≠ c01 := square_corner_ne D h11 h01 (by norm_num)
      have h0100 : c01 ≠ c00 := square_corner_ne D h01 h00 (by norm_num)
      have hab : a ≠ b := ne_of_isAtomicEdge_mk D he.1
      have hno : ∀ z : D.vtx, ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) :=
        fun z => not_sbtw_of_isAtomicEdge_mk D he.1
      have hseg :
          segment ℝ (D.coord a) (D.coord b) ⊆
            frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) :=
        (onSquareBoundary_mk_iff (D := D)).mp he.2
      rcases square_side_cases_of_segment_subset_frontier
          (D := D) h00 h10 h11 h01 hseg with hbot | hrest
      · have hmem : s(a, b) ∈ sideAtomicEdges D c00 c10 :=
          mem_sideAtomicEdges_of_onSide_no_sbtw D h0010 hbot.1 hbot.2 hab hno
        have hlist :
            s(a, b) ∈ squareBoundaryEdgeList
              (sideInteriorChain D c00 c10)
              (sideInteriorChain D c10 c11)
              (sideInteriorChain D c11 c01)
              (sideInteriorChain D c01 c00)
              c00 c10 c11 c01 := by
          have hmem' :
              s(a, b) ∈ consecutiveEdges
                (c00 :: sideInteriorChain D c00 c10 ++ [c10]) := by
            simpa [sideAtomicEdges] using hmem
          simpa [squareBoundaryEdgeList, List.mem_append] using
            (Or.inl hmem' :
              s(a, b) ∈ consecutiveEdges
                (c00 :: sideInteriorChain D c00 c10 ++ [c10]) ∨
              s(a, b) ∈ consecutiveEdges
                (c10 :: sideInteriorChain D c10 c11 ++ [c11]) ∨
              s(a, b) ∈ consecutiveEdges
                (c11 :: sideInteriorChain D c11 c01 ++ [c01]) ∨
              s(a, b) ∈ consecutiveEdges
                (c01 :: sideInteriorChain D c01 c00 ++ [c00]))
        simpa using hlist
      · rcases hrest with hrightSide | hrest
        · have hmem : s(a, b) ∈ sideAtomicEdges D c10 c11 :=
            mem_sideAtomicEdges_of_onSide_no_sbtw D h1011 hrightSide.1 hrightSide.2 hab hno
          have hlist :
              s(a, b) ∈ squareBoundaryEdgeList
                (sideInteriorChain D c00 c10)
                (sideInteriorChain D c10 c11)
                (sideInteriorChain D c11 c01)
                (sideInteriorChain D c01 c00)
                c00 c10 c11 c01 := by
            have hmem' :
                s(a, b) ∈ consecutiveEdges
                  (c10 :: sideInteriorChain D c10 c11 ++ [c11]) := by
              simpa [sideAtomicEdges] using hmem
            simpa [squareBoundaryEdgeList, List.mem_append] using
              (Or.inr <| Or.inl hmem' :
                s(a, b) ∈ consecutiveEdges
                  (c00 :: sideInteriorChain D c00 c10 ++ [c10]) ∨
                s(a, b) ∈ consecutiveEdges
                  (c10 :: sideInteriorChain D c10 c11 ++ [c11]) ∨
                s(a, b) ∈ consecutiveEdges
                  (c11 :: sideInteriorChain D c11 c01 ++ [c01]) ∨
                s(a, b) ∈ consecutiveEdges
                  (c01 :: sideInteriorChain D c01 c00 ++ [c00]))
          simpa using hlist
        · rcases hrest with htopSide | hleftSide
          · have hmem : s(a, b) ∈ sideAtomicEdges D c11 c01 :=
              mem_sideAtomicEdges_of_onSide_no_sbtw D h1101 htopSide.1 htopSide.2 hab hno
            have hlist :
                s(a, b) ∈ squareBoundaryEdgeList
                  (sideInteriorChain D c00 c10)
                  (sideInteriorChain D c10 c11)
                  (sideInteriorChain D c11 c01)
                  (sideInteriorChain D c01 c00)
                  c00 c10 c11 c01 := by
              have hmem' :
                  s(a, b) ∈ consecutiveEdges
                    (c11 :: sideInteriorChain D c11 c01 ++ [c01]) := by
                simpa [sideAtomicEdges] using hmem
              simpa [squareBoundaryEdgeList, List.mem_append] using
                (Or.inr <| Or.inr <| Or.inl hmem' :
                  s(a, b) ∈ consecutiveEdges
                    (c00 :: sideInteriorChain D c00 c10 ++ [c10]) ∨
                  s(a, b) ∈ consecutiveEdges
                    (c10 :: sideInteriorChain D c10 c11 ++ [c11]) ∨
                  s(a, b) ∈ consecutiveEdges
                    (c11 :: sideInteriorChain D c11 c01 ++ [c01]) ∨
                  s(a, b) ∈ consecutiveEdges
                    (c01 :: sideInteriorChain D c01 c00 ++ [c00]))
            simpa using hlist
          · have hmem : s(a, b) ∈ sideAtomicEdges D c01 c00 :=
              mem_sideAtomicEdges_of_onSide_no_sbtw D h0100 hleftSide.1 hleftSide.2 hab hno
            have hlist :
                s(a, b) ∈ squareBoundaryEdgeList
                  (sideInteriorChain D c00 c10)
                  (sideInteriorChain D c10 c11)
                  (sideInteriorChain D c11 c01)
                  (sideInteriorChain D c01 c00)
                  c00 c10 c11 c01 := by
              have hmem' :
                  s(a, b) ∈ consecutiveEdges
                    (c01 :: sideInteriorChain D c01 c00 ++ [c00]) := by
                simpa [sideAtomicEdges] using hmem
              simpa [squareBoundaryEdgeList, List.mem_append] using
                (Or.inr <| Or.inr <| Or.inr hmem' :
                  s(a, b) ∈ consecutiveEdges
                    (c00 :: sideInteriorChain D c00 c10 ++ [c10]) ∨
                  s(a, b) ∈ consecutiveEdges
                    (c10 :: sideInteriorChain D c10 c11 ++ [c11]) ∨
                  s(a, b) ∈ consecutiveEdges
                    (c11 :: sideInteriorChain D c11 c01 ++ [c01]) ∨
                  s(a, b) ∈ consecutiveEdges
                    (c01 :: sideInteriorChain D c01 c00 ++ [c00]))
            simpa using hlist

lemma squareBoundaryEdgeList_mem_atomicBoundary_of_square_corners
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    {e : Sym2 D.vtx}
    (he : e ∈ (squareBoundaryEdgeList
      (sideInteriorChain D c00 c10)
      (sideInteriorChain D c10 c11)
      (sideInteriorChain D c11 c01)
      (sideInteriorChain D c01 c00)
      c00 c10 c11 c01).toFinset) :
    IsAtomicEdge D e ∧ OnSquareBoundary D e := by
  classical
  induction e using Sym2.ind with
  | h a b =>
      have hlist :
          s(a, b) ∈ squareBoundaryEdgeList
            (sideInteriorChain D c00 c10)
            (sideInteriorChain D c10 c11)
            (sideInteriorChain D c11 c01)
            (sideInteriorChain D c01 c00)
            c00 c10 c11 c01 := by
        simpa using he
      have hcases :
          s(a, b) ∈ sideAtomicEdges D c00 c10 ∨
          s(a, b) ∈ sideAtomicEdges D c10 c11 ∨
          s(a, b) ∈ sideAtomicEdges D c11 c01 ∨
          s(a, b) ∈ sideAtomicEdges D c01 c00 := by
        simpa [squareBoundaryEdgeList, sideAtomicEdges, List.mem_append,
          List.append_assoc] using hlist
      rcases hcases with hbot | hright | htop | hleft
      · exact bottom_squareSideAtomic_atomicBoundary D h00 h10 hbot
      · exact right_squareSideAtomic_atomicBoundary D h10 h11 hright
      · exact top_squareSideAtomic_atomicBoundary D h11 h01 htop
      · exact left_squareSideAtomic_atomicBoundary D h01 h00 hleft

lemma atomicBoundary_iff_squareBoundaryEdgeList_of_square_corners
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    (e : Sym2 D.vtx) :
    IsAtomicEdge D e ∧ OnSquareBoundary D e ↔
      e ∈ (squareBoundaryEdgeList
        (sideInteriorChain D c00 c10)
        (sideInteriorChain D c10 c11)
        (sideInteriorChain D c11 c01)
        (sideInteriorChain D c01 c00)
        c00 c10 c11 c01).toFinset := by
  constructor
  · exact atomicBoundary_mem_squareBoundaryEdgeList_of_square_corners
      (D := D) h00 h10 h11 h01
  · exact squareBoundaryEdgeList_mem_atomicBoundary_of_square_corners
      (D := D) h00 h10 h11 h01

open scoped Classical in
lemma atomicBoundaryRG_card_odd_of_squareBoundaryEdgeList
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    (hboundary : ∀ e : Sym2 D.vtx,
      IsAtomicEdge D e ∧ OnSquareBoundary D e ↔
        e ∈ (squareBoundaryEdgeList
          (sideInteriorChain D c00 c10)
          (sideInteriorChain D c10 c11)
          (sideInteriorChain D c11 c01)
          (sideInteriorChain D c01 c00)
          c00 c10 c11 c01).toFinset) :
    Odd (Finset.univ.filter fun e : Sym2 D.vtx =>
      edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧
        IsAtomicEdge D e ∧ OnSquareBoundary D e).card := by
  classical
  let L :=
    squareBoundaryEdgeList
      (sideInteriorChain D c00 c10)
      (sideInteriorChain D c10 c11)
      (sideInteriorChain D c11 c01)
      (sideInteriorChain D c01 c00)
      c00 c10 c11 c01
  have hset :
      (Finset.univ.filter fun e : Sym2 D.vtx =>
        edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧
          IsAtomicEdge D e ∧ OnSquareBoundary D e) =
      (L.toFinset.filter fun e : Sym2 D.vtx =>
        edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1) := by
    ext e
    have hb' : IsAtomicEdge D e ∧ OnSquareBoundary D e ↔ e ∈ L := by
      rw [hboundary e]
      simp [L]
    by_cases hrg : edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1
    · simp [hrg, hb']
    · simp [hrg]
  have hnodup : L.Nodup := by
    simpa [L] using squareBoundaryEdgeList_nodup_of_square_corners
      (D := D) h00 h10 h11 h01
  have hcard :
      (L.toFinset.filter fun e : Sym2 D.vtx =>
        edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1).card =
      listEdgeRGCount L (realTwoAdicColor ∘ D.coord) := by
    simpa [boundaryEdgeRedGreenCount, L] using
      boundaryEdgeRedGreenCount_toFinset L (realTwoAdicColor ∘ D.coord) hnodup
  have hoddList : Odd (listEdgeRGCount L (realTwoAdicColor ∘ D.coord)) := by
    simpa [L] using squareBoundarySideAtomicList_RG_odd
      (D := D) h00 h10 h11 h01
  rw [hset, hcard]
  exact hoddList

open scoped Classical in
theorem oddAtomicRG_card_odd :
    Odd (Finset.univ.filter fun e : Sym2 D.vtx =>
      edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧
        Odd (atomicMult D e)).card := by
  classical
  obtain ⟨c00, c10, c11, c01, h00, h10, h11, h01⟩ :=
    exists_square_corners (D := D)
  rw [oddAtomicRG_filter_eq_atomicBoundaryRG (D := D)]
  exact atomicBoundaryRG_card_odd_of_squareBoundaryEdgeList
    (D := D) h00 h10 h11 h01
    (atomicBoundary_iff_squareBoundaryEdgeList_of_square_corners
      (D := D) h00 h10 h11 h01)

end ProofsInTheBook.Chapter20
