import Mathlib

lemma test_subtype {m : ℕ} (s : Fin (m + 1) → Fin (m + 2)) (j i : Fin (m + 1)) (P : Fin (m + 2) → Prop)
    (hj : P (s j)) (hi : P (s i)) (h_eq : j = i) :
    (⟨s j, hj⟩ : {x // P x}) = ⟨s i, hi⟩ := by
  simp only [h_eq]

EOF
