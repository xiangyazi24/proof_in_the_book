import Agafonov.Kamae1973.SectionFiveSelectorGrowth
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Affine-floor selectors

The selector `k ↦ floor (b * k + c)` is strictly increasing and has eventual
linear growth when `b ≥ 1` and `c ≥ 0`. These are the elementary selector
properties used in Kamae (1973), Example 2, p. 149.
-/

namespace Agafonov.Kamae1973

open Filter Topology

noncomputable section

/-- The affine-floor selector `k ↦ floor (b * k + c)` from Kamae (1973),
Example 2, p. 149. -/
noncomputable def affineFloorSelector
    (b c : ℝ) (k : ℕ) : ℕ :=
  Nat.floor (b * (k : ℝ) + c)

private theorem affineFloorArgument_nonneg
    (b c : ℝ) (hb : 1 ≤ b) (hc : 0 ≤ c) (k : ℕ) :
    0 ≤ b * (k : ℝ) + c := by
  exact add_nonneg
    (mul_nonneg (zero_le_one.trans hb) (Nat.cast_nonneg k)) hc

private theorem affineFloorArgument_succ
    (b c : ℝ) (hb : 1 ≤ b) (k : ℕ) :
    b * (k : ℝ) + c + 1 ≤
      b * ((k + 1 : ℕ) : ℝ) + c := by
  calc
    b * (k : ℝ) + c + 1 ≤ b * (k : ℝ) + c + b :=
      add_le_add_left hb (b * (k : ℝ) + c)
    _ = b * ((k + 1 : ℕ) : ℝ) + c := by
      simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      ac_rfl

/-- Affine-floor selectors with slope at least one are strictly increasing.
This is the monotonicity assertion used in Kamae (1973), Example 2, p. 149. -/
theorem affineFloorSelector_strictMono
    (b c : ℝ) (hb : 1 ≤ b) (hc : 0 ≤ c) :
    StrictMono (affineFloorSelector b c) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have harg := affineFloorArgument_nonneg b c hb hc k
  have hstep := affineFloorArgument_succ b c hb k
  have hfloor :
      Nat.floor (b * (k : ℝ) + c) + 1 ≤
        Nat.floor (b * ((k + 1 : ℕ) : ℝ) + c) := by
    calc
      Nat.floor (b * (k : ℝ) + c) + 1 =
          Nat.floor (b * (k : ℝ) + c + (1 : ℝ)) := by
        symm
        simpa using (Nat.floor_add_natCast harg 1)
      _ ≤ Nat.floor (b * ((k + 1 : ℕ) : ℝ) + c) :=
        Nat.floor_mono hstep
  unfold affineFloorSelector
  omega

/-- Affine-floor selectors satisfy the eventual-linear growth condition (4.10).
This is the growth assertion used in Kamae (1973), Example 2, p. 149. -/
theorem affineFloorSelector_hasLinearGrowth
    (b c : ℝ) (hb : 1 ≤ b) (hc : 0 ≤ c) :
    HasLinearGrowth (affineFloorSelector b c) := by
  refine ⟨b + c, Filter.eventually_atTop.2 ⟨1, ?_⟩⟩
  intro n hn
  have harg := affineFloorArgument_nonneg b c hb hc n
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hcScale : c ≤ c * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hnReal hc
    simpa using h
  unfold affineFloorSelector
  calc
    ((Nat.floor (b * (n : ℝ) + c) : ℕ) : ℝ) ≤
        b * (n : ℝ) + c := Nat.floor_le harg
    _ ≤ b * (n : ℝ) + c * (n : ℝ) :=
      add_le_add_left hcScale (b * (n : ℝ))
    _ = (b + c) * (n : ℝ) := by
      rw [add_mul]

end

end Agafonov.Kamae1973

#print axioms Agafonov.Kamae1973.affineFloorSelector_strictMono
#print axioms Agafonov.Kamae1973.affineFloorSelector_hasLinearGrowth
