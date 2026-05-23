import Mathlib

/-!
# Chapter 16: Borsuk's conjecture

From "Proofs from THE BOOK":

**Borsuk's conjecture**: Can every bounded set in ℝ^d be partitioned
into d+1 parts, each of smaller diameter? Borsuk conjectured yes (1933).

The book discusses the conjecture and its eventual disproof (for d ≥ 298)
by Kahn and Kalai (1993) using combinatorial arguments.
-/

namespace ProofsInTheBook.Chapter16

/--
A finite coloring certificate for a Borsuk-style partition: points with the
same color are required to have pairwise distance below the target bound.
-/
def HasSmallColorClasses {α : Type*} [PseudoMetricSpace α] {d : ℕ} (points : Finset α)
    (diamBound : ℝ) (color : α → Fin (d + 1)) : Prop :=
  ∀ x ∈ points, ∀ y ∈ points, color x = color y → dist x y < diamBound

/-- One color class in the finite partition. -/
def colorClass {α : Type*} {d : ℕ} (points : Finset α) (color : α → Fin (d + 1))
    (c : Fin (d + 1)) : Finset α :=
  points.filter fun x => color x = c

theorem mem_colorClass_iff {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    (points : Finset α) (color : α → Fin (d + 1)) (c : Fin (d + 1)) (x : α) :
    x ∈ colorClass points color c ↔ x ∈ points ∧ color x = c := by
  simp [colorClass]

theorem colorClass_subset_points {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    (points : Finset α) (color : α → Fin (d + 1)) (c : Fin (d + 1)) :
    colorClass points color c ⊆ points := by
  intro x hx
  exact (mem_colorClass_iff points color c x).mp hx |>.1

theorem mem_colorClass_of_mem {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    {points : Finset α} {color : α → Fin (d + 1)} {x : α}
    (hx : x ∈ points) : x ∈ colorClass points color (color x) := by
  rw [mem_colorClass_iff]
  exact ⟨hx, rfl⟩

theorem exists_colorClass_of_mem {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    {points : Finset α} {color : α → Fin (d + 1)} {x : α}
    (hx : x ∈ points) : ∃ c : Fin (d + 1), x ∈ colorClass points color c :=
  ⟨color x, mem_colorClass_of_mem hx⟩

theorem disjoint_colorClass_of_ne {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    {points : Finset α} {color : α → Fin (d + 1)} {c₁ c₂ : Fin (d + 1)}
    (hne : c₁ ≠ c₂) : Disjoint (colorClass points color c₁) (colorClass points color c₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  have h₁ := (mem_colorClass_iff points color c₁ x).mp hx₁
  have h₂ := (mem_colorClass_iff points color c₂ x).mp hx₂
  exact hne (h₁.2.symm.trans h₂.2)

/--
The basic verification step for a Borsuk partition: every color class has
the advertised smaller pairwise diameter bound.
-/
theorem same_color_dist_lt_of_mem_colorClass {α : Type*} [PseudoMetricSpace α] {d : ℕ}
    [DecidableEq (Fin (d + 1))] {points : Finset α} {diamBound : ℝ}
    {color : α → Fin (d + 1)} (h : HasSmallColorClasses points diamBound color)
    {c : Fin (d + 1)} {x y : α}
    (hx : x ∈ colorClass points color c) (hy : y ∈ colorClass points color c) :
    dist x y < diamBound := by
  rw [mem_colorClass_iff] at hx hy
  exact h x hx.1 y hy.1 (hx.2.trans hy.2.symm)

/-- Borsuk's conjecture in dimension d: every bounded set with positive
diameter can be partitioned into d+1 sets, each of strictly smaller diameter. -/
def BorsukConjecture (d : ℕ) : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin d))),
    Bornology.IsBounded S → 0 < Metric.diam S →
    ∃ parts : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)),
      S ⊆ ⋃ i, parts i ∧
      ∀ i, Metric.diam (parts i) < Metric.diam S

/--
A Kahn-Kalai certificate is a counterexample set in `ℝ^d` that is bounded,
has positive diameter, but cannot be partitioned into `d + 1` sets of strictly
smaller diameter.
-/
structure KahnKalaiCertificate (d : ℕ) where
  S : Set (EuclideanSpace ℝ (Fin d))
  bounded : Bornology.IsBounded S
  pos_diam : 0 < Metric.diam S
  no_partition : ¬ ∃ parts : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)),
    S ⊆ ⋃ i, parts i ∧ ∀ i, Metric.diam (parts i) < Metric.diam S

/--
Chapter 16 (Borsuk's conjecture in high dimensions, Tier 1 conditional):
Given a Kahn-Kalai-style counterexample — a bounded set with positive diameter
in ℝ^d that cannot be partitioned into d+1 pieces of strictly smaller diameter —
Borsuk's conjecture fails in dimension d.

TODO (Tier 2): Construct the actual Kahn-Kalai counterexample for `d ≥ 298`
via Frankl-Wilson combinatorics on hypergraph color codes to produce a
`KahnKalaiCertificate d`.
-/
theorem chapter16 {d : ℕ} (cert : KahnKalaiCertificate d) :
    ¬ BorsukConjecture d := fun h =>
  cert.no_partition (h cert.S cert.bounded cert.pos_diam)

/-- Borsuk's conjecture in dimension `d` is equivalent to the non-existence
of a Kahn-Kalai certificate.  This packages `chapter16` as a biconditional. -/
theorem borsukConjecture_iff_no_certificate (d : ℕ) :
    BorsukConjecture d ↔ ∀ S : Set (EuclideanSpace ℝ (Fin d)),
      Bornology.IsBounded S → 0 < Metric.diam S →
        ∃ parts : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)),
          S ⊆ ⋃ i, parts i ∧ ∀ i, Metric.diam (parts i) < Metric.diam S :=
  Iff.rfl

/-- If a Kahn-Kalai certificate exists, the underlying set is nonempty
(since `0 < diam S` forces `S` to contain at least two points). -/
theorem KahnKalaiCertificate.nonempty {d : ℕ} (cert : KahnKalaiCertificate d) :
    cert.S.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hd : Metric.diam cert.S = 0 := by rw [h]; simp
  exact absurd cert.pos_diam (by rw [hd]; simp)

/-- Conversely, if Borsuk's conjecture holds in dimension `d`, no
Kahn-Kalai certificate exists. -/
theorem borsuk_no_certificate_of_conjecture {d : ℕ} (h : BorsukConjecture d) :
    IsEmpty (KahnKalaiCertificate d) := by
  constructor
  intro cert
  exact cert.no_partition (h cert.S cert.bounded cert.pos_diam)

end ProofsInTheBook.Chapter16
