import Mathlib

lemma test {m : ℕ} (p : Fin (m + 2)) : StrictMono (Fin.succAbove p) :=
  Fin.strictMono_succAbove p

