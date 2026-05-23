import Mathlib

/-!
# Chapter 20: One square and an odd number of triangles

From "Proofs from THE BOOK":

**Monsky's theorem**: A square cannot be divided into an odd number
of triangles of equal area.

The book's proof uses a 2-adic valuation argument: define a coloring
of the plane using the 2-adic valuation of coordinates, then apply
Sperner's lemma to show the triangulation must have an even count.
-/

namespace ProofsInTheBook.Chapter20

/-- The three colors used in Monsky's 2-adic coloring argument. -/
inductive MonskyColor where
  | red | green | blue
  deriving DecidableEq, Repr

open MonskyColor

/-- A triangle is trichromatic when its three vertex colors are pairwise different. -/
def TrichromaticTriangle (a b c : MonskyColor) : Prop :=
  a ≠ b ∧ b ≠ c ∧ c ≠ a

/-- Orientation-free red-green edge predicate used in the Sperner parity count. -/
def RedGreenEdge (a b : MonskyColor) : Prop :=
  (a = red ∧ b = green) ∨ (a = green ∧ b = red)

instance decidableRedGreenEdge (a b : MonskyColor) : Decidable (RedGreenEdge a b) := by
  unfold RedGreenEdge
  infer_instance

instance decidableTrichromaticTriangle (a b c : MonskyColor) :
    Decidable (TrichromaticTriangle a b c) := by
  unfold TrichromaticTriangle
  infer_instance

theorem trichromatic_of_eq_red_green_blue {a b c : MonskyColor}
    (ha : a = red) (hb : b = green) (hc : c = blue) : TrichromaticTriangle a b c := by
  subst a
  subst b
  subst c
  simp [TrichromaticTriangle]

theorem not_trichromatic_of_first_two_same {a b c : MonskyColor}
    (hab : a = b) : ¬ TrichromaticTriangle a b c := by
  intro h
  exact h.1 hab

/-- `RedGreenEdge` is symmetric in its two arguments. -/
theorem redGreenEdge_symm {a b : MonskyColor} : RedGreenEdge a b ↔ RedGreenEdge b a := by
  unfold RedGreenEdge; tauto

/-- A `RedGreenEdge` pair has distinct vertices. -/
theorem redGreenEdge_ne {a b : MonskyColor} (h : RedGreenEdge a b) : a ≠ b := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst ha <;> subst hb <;> decide

/-- A `RedGreenEdge` pair never contains a blue vertex. -/
theorem redGreenEdge_not_blue {a b : MonskyColor} (h : RedGreenEdge a b) :
    a ≠ blue ∧ b ≠ blue := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst ha <;> subst hb <;> exact ⟨by decide, by decide⟩

/-- A self-loop is never a red-green edge. -/
@[simp]
theorem not_redGreenEdge_self (a : MonskyColor) : ¬ RedGreenEdge a a := by
  cases a <;> decide

/-- A red-green edge between `a` and `b` forces one to be red and the other green. -/
theorem redGreenEdge_cases {a b : MonskyColor} (h : RedGreenEdge a b) :
    (a = red ∧ b = green) ∨ (a = green ∧ b = red) := h

/-- `TrichromaticTriangle` is invariant under cyclic permutation of vertices. -/
theorem trichromaticTriangle_cycle {a b c : MonskyColor} :
    TrichromaticTriangle a b c ↔ TrichromaticTriangle b c a := by
  cases a <;> cases b <;> cases c <;> decide

/-- `TrichromaticTriangle` is invariant under reverse-cyclic permutation. -/
theorem trichromaticTriangle_swap_outer {a b c : MonskyColor} :
    TrichromaticTriangle a b c ↔ TrichromaticTriangle c b a := by
  cases a <;> cases b <;> cases c <;> decide

/-- In a trichromatic triangle, the set of vertex colors equals all of MonskyColor. -/
theorem trichromaticTriangle_iff_red_green_blue_present {a b c : MonskyColor} :
    TrichromaticTriangle a b c ↔
      ((a = red ∨ b = red ∨ c = red) ∧
       (a = green ∨ b = green ∨ c = green) ∧
       (a = blue ∨ b = blue ∨ c = blue)) := by
  cases a <;> cases b <;> cases c <;> decide

/--
Local Sperner parity atom: a triangle is trichromatic exactly when it has an
odd number of red-green edges.
-/
theorem odd_redGreenEdges_iff_trichromatic (a b c : MonskyColor) :
    Odd
      ((if RedGreenEdge a b then 1 else 0 : ℕ) +
       (if RedGreenEdge b c then 1 else 0 : ℕ) +
       (if RedGreenEdge c a then 1 else 0 : ℕ)) ↔
      TrichromaticTriangle a b c := by
  cases a <;> cases b <;> cases c <;> decide

theorem redGreenEdges_zmod_two_eq_trichromatic (a b c : MonskyColor) :
    ((if RedGreenEdge a b then 1 else 0 : ZMod 2) +
     (if RedGreenEdge b c then 1 else 0 : ZMod 2) +
     (if RedGreenEdge c a then 1 else 0 : ZMod 2)) =
    (if TrichromaticTriangle a b c then 1 else 0 : ZMod 2) := by
  cases a <;> cases b <;> cases c <;> decide

/--
Abstract Sperner parity lemma: in a finite triangulation where each edge
belongs to at most two triangles, the number of trichromatic triangles has
the same parity as the number of red-green boundary edges.

`triangles` is the finite set of triangles, each given by three color assignments.
`boundaryRG` counts red-green edges on the boundary (shared by exactly one triangle).
-/
private theorem sum_nat_mod_two_eq_sum_mod_two
    {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ x ∈ s, f x) % 2 = (∑ x ∈ s, f x % 2) % 2 := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    conv_lhs => rw [Nat.add_mod (f a) _ 2, ih]
    conv_rhs => rw [Nat.add_mod (f a % 2) _ 2]
    simp

theorem sperner_parity_abstract
    (n : ℕ) (triangleColors : Fin n → MonskyColor × MonskyColor × MonskyColor)
    (boundaryRGCount : ℕ)
    (totalRG : ℕ)
    (htotal : totalRG = ∑ i : Fin n,
      ((if RedGreenEdge (triangleColors i).1 (triangleColors i).2.1 then 1 else 0) +
       (if RedGreenEdge (triangleColors i).2.1 (triangleColors i).2.2 then 1 else 0) +
       (if RedGreenEdge (triangleColors i).2.2 (triangleColors i).1 then 1 else 0)))
    (hparity : totalRG % 2 = boundaryRGCount % 2) :
    (Finset.univ.filter fun i : Fin n =>
      TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
        (triangleColors i).2.2).card % 2 = boundaryRGCount % 2 := by
  classical
  let f : Fin n → ℕ := fun i =>
    (if RedGreenEdge (triangleColors i).1 (triangleColors i).2.1 then 1 else 0) +
    (if RedGreenEdge (triangleColors i).2.1 (triangleColors i).2.2 then 1 else 0) +
    (if RedGreenEdge (triangleColors i).2.2 (triangleColors i).1 then 1 else 0)
  let T : Fin n → Prop := fun i =>
    TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
      (triangleColors i).2.2
  have hlocal : ∀ i : Fin n, f i % 2 = if T i then 1 else 0 := by
    intro i
    have hodd := odd_redGreenEdges_iff_trichromatic (triangleColors i).1
      (triangleColors i).2.1 (triangleColors i).2.2
    by_cases ht : T i
    · rw [if_pos ht]
      exact Nat.odd_iff.mp (hodd.mpr ht)
    · rw [if_neg ht]
      by_contra h
      have : f i % 2 = 1 := by omega
      exact ht (hodd.mp (Nat.odd_iff.mpr this))
  have hreplace : (∑ i : Fin n, f i % 2) = ∑ i : Fin n, if T i then 1 else 0 :=
    Finset.sum_congr rfl fun i _ => hlocal i
  have hcard : (∑ i : Fin n, if T i then (1 : ℕ) else 0) =
      (Finset.univ.filter T).card := by
    rw [← Finset.sum_filter]; simp
  calc (Finset.univ.filter T).card % 2
      = (∑ i : Fin n, if T i then (1 : ℕ) else 0) % 2 := by rw [hcard]
    _ = (∑ i : Fin n, f i % 2) % 2 := by rw [hreplace]
    _ = (∑ i : Fin n, f i) % 2 := (sum_nat_mod_two_eq_sum_mod_two _ _).symm
    _ = totalRG % 2 := by rw [htotal]
    _ = boundaryRGCount % 2 := hparity

/--
Corollary: if the boundary red-green edge count is odd, at least one triangle
is trichromatic.
-/
theorem exists_trichromatic_of_odd_boundary
    (n : ℕ) (triangleColors : Fin n → MonskyColor × MonskyColor × MonskyColor)
    (boundaryRGCount : ℕ)
    (totalRG : ℕ)
    (htotal : totalRG = ∑ i : Fin n,
      ((if RedGreenEdge (triangleColors i).1 (triangleColors i).2.1 then 1 else 0) +
       (if RedGreenEdge (triangleColors i).2.1 (triangleColors i).2.2 then 1 else 0) +
       (if RedGreenEdge (triangleColors i).2.2 (triangleColors i).1 then 1 else 0)))
    (hparity : totalRG % 2 = boundaryRGCount % 2)
    (hodd : Odd boundaryRGCount) :
    ∃ i : Fin n,
      TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
        (triangleColors i).2.2 := by
  by_contra hall
  push Not at hall
  have hempty : (Finset.univ.filter fun i : Fin n =>
      TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
        (triangleColors i).2.2) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _
    exact hall i
  have hcard0 : (Finset.univ.filter fun i : Fin n =>
      TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
        (triangleColors i).2.2).card = 0 := by
    simp [hempty]
  have := sperner_parity_abstract n triangleColors boundaryRGCount totalRG htotal hparity
  rw [hcard0] at this
  rcases hodd with ⟨k, hk⟩
  omega

/-- Certificate for Monsky's theorem: a 2-adic-style coloring of triangle
vertices together with the double-counting witness that boundary red-green
edge count is odd. This is the part that requires 2-adic extension to ℝ
(via transcendence basis / Hahn series, not in Mathlib). -/
structure MonskyCertificate (n : ℕ) where
  /-- The triangle colorings induced by a (hypothetical) equal-area
      odd-triangulation of the unit square. -/
  triangleColors : Fin n → MonskyColor × MonskyColor × MonskyColor
  /-- The boundary red-green edge count (from the square's edge contour). -/
  boundaryRGCount : ℕ
  /-- Total RG edge count summed over all triangles. -/
  totalRG : ℕ
  /-- Total = sum of triangle-local RG counts (double-counting bookkeeping). -/
  htotal : totalRG = ∑ i : Fin n,
    ((if RedGreenEdge (triangleColors i).1 (triangleColors i).2.1 then 1 else 0) +
     (if RedGreenEdge (triangleColors i).2.1 (triangleColors i).2.2 then 1 else 0) +
     (if RedGreenEdge (triangleColors i).2.2 (triangleColors i).1 then 1 else 0))
  /-- 2-adic constraint: parity of total RG = parity of boundary RG. -/
  hparity : totalRG % 2 = boundaryRGCount % 2
  /-- Crux of Monsky's argument: boundary RG count is ODD (from the unit
      square's specific 2-adic coloring at corners). -/
  hodd : Odd boundaryRGCount

/- Tier 2 work (deferred): given a hypothetical equal-area triangulation of
the unit square into an ODD number of triangles, construct a MonskyCertificate
by:
1. Using Hahn series / transcendence basis to extend the 2-adic valuation
   v₂ : ℚ → ℤ to v₂' : ℝ → ℤ.
2. Color each point (x, y) ∈ ℝ² by:
   - red if v₂'(x) > 0 ∧ v₂'(y) > 0
   - green if v₂'(x) ≤ 0 ∧ v₂'(x) ≤ v₂'(y)
   - blue if v₂'(y) < 0 ∧ v₂'(y) < v₂'(x)
3. Verify the unit square corners (0,0), (1,0), (0,1), (1,1) get 3 distinct
   colors with odd boundary RG count.
4. The "total RG = boundary RG mod 2" identity follows from double-counting
   per Sperner.
The 2-adic extension to ℝ is non-trivial in Lean — likely needs Mathlib's
HahnSeries / WellOrderedExtension machinery. -/

/-- Chapter 20 (Monsky's theorem, Tier 1 conditional):
Given a Monsky 2-adic coloring certificate (which packages the 2-adic
extension construction + the double-counting parity result + the odd-boundary
witness), there exists a trichromatic triangle — corresponding to the
contradiction that closes the proof (such a triangle has area with 2-adic
valuation incompatible with 1/(odd integer)).
-/
theorem chapter20 {n : ℕ} (cert : MonskyCertificate n) :
    ∃ i : Fin n,
      TrichromaticTriangle (cert.triangleColors i).1
        (cert.triangleColors i).2.1 (cert.triangleColors i).2.2 :=
  exists_trichromatic_of_odd_boundary n cert.triangleColors
    cert.boundaryRGCount cert.totalRG cert.htotal cert.hparity cert.hodd

end ProofsInTheBook.Chapter20
