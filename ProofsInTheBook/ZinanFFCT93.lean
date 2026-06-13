import ProofsInTheBook.ZinanFFCT92
import ProofsInTheBook.ZinanFFCT10

/-!
# `ZinanFFCT93` -- checked obstruction to the proposed planar no-repeat core

The planar core isolated in `ZinanFFCT92` is false as stated.  A convex
triangle traversed twice satisfies the affine-plane condition, all cyclic weak
edge supports, nonzero cyclic edges, and every non-wrapping strict turn, but it
has nonadjacent repeated vertices.
-/

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT92

namespace ProofsInTheBook.ZinanFFCT93

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## The doubled-triangle planar chain. -/

def triA : E3 := !₂[(0 : ℝ), 0, 1]
def triB : E3 := !₂[(1 : ℝ), 0, 1]
def triC : E3 := !₂[(0 : ℝ), 1, 1]
def triH : E3 := !₂[(0 : ℝ), 0, 1]

def triTwice : Fin 6 → E3 :=
  ![triA, triB, triC, triA, triB, triC]

theorem triTwice_plane :
    ∀ i : Fin 6, (⟪triH, triTwice i⟫ : ℝ) = 1 := by
  intro i
  fin_cases i
  · change (⟪triH, triA⟫ : ℝ) = 1
    rw [triH, triA, ProofsInTheBook.ZinanFFCT10.innerE3]
    norm_num
  · change (⟪triH, triB⟫ : ℝ) = 1
    rw [triH, triB, ProofsInTheBook.ZinanFFCT10.innerE3]
    norm_num
  · change (⟪triH, triC⟫ : ℝ) = 1
    rw [triH, triC, ProofsInTheBook.ZinanFFCT10.innerE3]
    norm_num
  · change (⟪triH, triA⟫ : ℝ) = 1
    rw [triH, triA, ProofsInTheBook.ZinanFFCT10.innerE3]
    norm_num
  · change (⟪triH, triB⟫ : ℝ) = 1
    rw [triH, triB, ProofsInTheBook.ZinanFFCT10.innerE3]
    norm_num
  · change (⟪triH, triC⟫ : ℝ) = 1
    rw [triH, triC, ProofsInTheBook.ZinanFFCT10.innerE3]
    norm_num

theorem triTwice_support :
    ∀ i j : Fin 6, 0 ≤ det3 (triTwice i) (triTwice (i + 1)) (triTwice j) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [
      show ((⟨0, by omega⟩ : Fin 6) + 1) = ⟨1, by omega⟩ from rfl,
      show ((⟨1, by omega⟩ : Fin 6) + 1) = ⟨2, by omega⟩ from rfl,
      show ((⟨2, by omega⟩ : Fin 6) + 1) = ⟨3, by omega⟩ from rfl,
      show ((⟨3, by omega⟩ : Fin 6) + 1) = ⟨4, by omega⟩ from rfl,
      show ((⟨4, by omega⟩ : Fin 6) + 1) = ⟨5, by omega⟩ from rfl,
      show ((⟨5, by omega⟩ : Fin 6) + 1) = ⟨0, by omega⟩ from rfl,
      triTwice] <;>
    norm_num [triA, triB, triC, ProofsInTheBook.ZinanFFCT10.det3E3]

theorem triTwice_edge_ne :
    ∀ i : Fin 6, triTwice i ≠ triTwice (i + 1) := by
  intro i h
  fin_cases i
  · have hh := congrArg (fun v : E3 => v 0) h
    norm_num [triTwice, triA, triB, triC] at hh
  · have hh := congrArg (fun v : E3 => v 0) h
    simp only [
      show ((⟨1, by omega⟩ : Fin 6) + 1) = ⟨2, by omega⟩ from rfl,
      triTwice, triA, triB, triC] at hh
    norm_num at hh
  · have hh := congrArg (fun v : E3 => v 1) h
    simp only [
      show ((⟨2, by omega⟩ : Fin 6) + 1) = ⟨3, by omega⟩ from rfl,
      triTwice, triA, triB, triC] at hh
    norm_num at hh
  · have hh := congrArg (fun v : E3 => v 0) h
    simp only [
      show ((⟨3, by omega⟩ : Fin 6) + 1) = ⟨4, by omega⟩ from rfl,
      triTwice, triA, triB, triC] at hh
    norm_num at hh
  · have hh := congrArg (fun v : E3 => v 0) h
    simp only [
      show ((⟨4, by omega⟩ : Fin 6) + 1) = ⟨5, by omega⟩ from rfl,
      triTwice, triA, triB, triC] at hh
    norm_num at hh
  · have hh := congrArg (fun v : E3 => v 1) h
    simp only [
      show ((⟨5, by omega⟩ : Fin 6) + 1) = ⟨0, by omega⟩ from rfl,
      triTwice, triA, triB, triC] at hh
    norm_num at hh

theorem triTwice_strict_turn :
    ∀ r : ℕ, ∀ (hr2 : r + 2 < 5 + 1),
      0 < det3 (triTwice ⟨r, by omega⟩)
        (triTwice ⟨r + 1, by omega⟩) (triTwice ⟨r + 2, hr2⟩) := by
  intro r hr2
  have hr_le : r ≤ 3 := by omega
  interval_cases r <;>
    norm_num [triTwice, triA, triB, triC, ProofsInTheBook.ZinanFFCT10.det3E3]

theorem triTwice_repeat : triTwice ⟨0, by omega⟩ = triTwice ⟨3, by omega⟩ := by
  rfl

/-! ## Consequence: the FFCT92 planar core cannot be supplied. -/

theorem not_planarClosedWeakStrictNoRepeat :
    ¬ PlanarClosedWeakStrictNoRepeat := by
  intro hplanar
  have hnr := hplanar (n := 5) (by omega) triH triTwice
    triTwice_plane triTwice_support triTwice_edge_ne triTwice_strict_turn
    0 3 (by omega) (by omega) (by omega)
  exact hnr triTwice_repeat

#check not_planarClosedWeakStrictNoRepeat

end ProofsInTheBook.ZinanFFCT93
