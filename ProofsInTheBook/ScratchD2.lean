import ProofsInTheBook.BricardCube

noncomputable section
open ProofsInTheBook.TetPearls
open ProofsInTheBook.BricardCube

namespace ScratchD2

-- test: carrier of kt012 in {coordDiff 1 0 <= 0} (x1 <= x0)
example : kt012.carrier ⊆ {y : Pt3 | coordDiff 1 0 y ≤ 0} := by
  apply carrier_subset_coordDiff_le
  intro i
  fin_cases i <;>
    simp only [kt012, kv012, coordDiff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, PiLp.toLp_apply] <;> norm_num

example : Disjoint kt012.interior kt102.interior := by
  apply disjoint_interior_of_separating (p := 1) (q := 0) (by decide)
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;>
      simp only [kt012, kv012, coordDiff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, PiLp.toLp_apply] <;> norm_num
  · apply carrier_subset_coordDiff_le
    intro i; fin_cases i <;>
      simp only [kt102, kv102, coordDiff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, PiLp.toLp_apply] <;> norm_num

end ScratchD2
