import ProofsInTheBook.Chapter20E2Frontier

/-!
# Chapter 20 E2 cover lemmas

General connected-cover packaging for the local E2 incidence argument.
-/

namespace ProofsInTheBook.Chapter20

open scoped Topology
open Set

namespace Chapter20E2Cover

abbrev P := ℝ × ℝ

/-- The open disk around `m`, cut by a strict signed half-plane for the oriented
line through `a,b`.  The sign is normally `1` or `-1`. -/
def signedOpenHalfDisk (a b m : P) (ε σ : ℝ) : Set P :=
  {x | dist x m < ε ∧ 0 < σ * doubleArea a b x}

lemma doubleArea_affine_combo (a b x y : P) (μ ν : ℝ) (hμν : μ + ν = 1) :
    doubleArea a b (μ • x + ν • y) =
      μ * doubleArea a b x + ν * doubleArea a b y := by
  unfold doubleArea
  simp [Prod.smul_def]
  ring_nf
  linear_combination (b.1 * a.2 - a.1 * b.2) * hμν

lemma convex_signedOpenHalfDisk (a b m : P) {ε σ : ℝ} :
    Convex ℝ (signedOpenHalfDisk a b m ε σ) := by
  intro x hx y hy μ ν hμ hν hμν
  constructor
  · exact (convex_ball m ε) hx.1 hy.1 hμ hν hμν
  · rw [doubleArea_affine_combo a b x y μ ν hμν]
    have hxpos : 0 < σ * doubleArea a b x := hx.2
    have hypos : 0 < σ * doubleArea a b y := hy.2
    have hcombo :
        0 < μ * (σ * doubleArea a b x) + ν * (σ * doubleArea a b y) := by
      by_cases hμ0 : μ = 0
      · have hν1 : ν = 1 := by nlinarith
        nlinarith
      · have hμpos : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hμ0)
        have hνnonneg : 0 ≤ ν * (σ * doubleArea a b y) := mul_nonneg hν hypos.le
        have hμterm : 0 < μ * (σ * doubleArea a b x) := mul_pos hμpos hxpos
        nlinarith
    convert hcombo using 1
    ring

lemma isPreconnected_signedOpenHalfDisk (a b m : P) {ε σ : ℝ} :
    IsPreconnected (signedOpenHalfDisk a b m ε σ) :=
  (convex_signedOpenHalfDisk a b m).isPreconnected

/-- A nonempty preconnected set covered by finitely many closed sets with
pairwise-disjoint interiors, and avoiding every frontier, lies in one interior. -/
theorem exists_subset_interior_of_preconnected_covered_closed
    {α : Type*} [TopologicalSpace α] {N : ℕ}
    (C : Fin N → Set α) (S : Set α)
    (hclosed : ∀ k, IsClosed (C k))
    (hdisj : ∀ k l, k ≠ l → Disjoint (interior (C k)) (interior (C l)))
    (hSpre : IsPreconnected S) (hSne : S.Nonempty)
    (hcover : S ⊆ ⋃ k, C k)
    (hfront : ∀ k, Disjoint S (frontier (C k))) :
    ∃ k, S ⊆ interior (C k) := by
  classical
  have hcoverInt : S ⊆ ⋃ k, interior (C k) := by
    intro x hxS
    rcases Set.mem_iUnion.mp (hcover hxS) with ⟨k, hxC⟩
    have hxClosure : x ∈ closure (C k) := by
      simpa [(hclosed k).closure_eq] using hxC
    have hxUnion : x ∈ interior (C k) ∪ frontier (C k) := by
      rwa [closure_eq_interior_union_frontier] at hxClosure
    rcases hxUnion with hxInt | hxFront
    · exact Set.mem_iUnion.mpr ⟨k, hxInt⟩
    · exact False.elim (Set.disjoint_left.mp (hfront k) hxS hxFront)
  rcases hSne with ⟨x₀, hx₀S⟩
  rcases Set.mem_iUnion.mp (hcoverInt hx₀S) with ⟨k₀, hx₀k₀⟩
  let U : Set α := interior (C k₀)
  let V : Set α := ⋃ k : {k : Fin N // k ≠ k₀}, interior (C k.1)
  have hUopen : IsOpen U := isOpen_interior
  have hVopen : IsOpen V := isOpen_iUnion fun _ => isOpen_interior
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    rcases Set.mem_iUnion.mp hxV with ⟨k, hxk⟩
    exact Set.disjoint_left.mp (hdisj k₀ k.1 (Ne.symm k.2)) hxU hxk
  have hSUV : S ⊆ U ∪ V := by
    intro x hxS
    rcases Set.mem_iUnion.mp (hcoverInt hxS) with ⟨k, hxk⟩
    by_cases hk : k = k₀
    · exact Or.inl (by simpa [U, hk] using hxk)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨k, hk⟩, hxk⟩)
  have hSU : (S ∩ U).Nonempty := ⟨x₀, hx₀S, by simpa [U] using hx₀k₀⟩
  exact ⟨k₀, hSpre.subset_left_of_subset_union hUopen hVopen hUV hSUV hSU⟩

end Chapter20E2Cover

export Chapter20E2Cover
  (signedOpenHalfDisk
   doubleArea_affine_combo
   convex_signedOpenHalfDisk
   isPreconnected_signedOpenHalfDisk
   exists_subset_interior_of_preconnected_covered_closed)

end ProofsInTheBook.Chapter20
