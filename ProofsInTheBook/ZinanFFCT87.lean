import ProofsInTheBook.ZinanFFCT86

/-!
# `ZinanFFCT87` -- collision-branch structural bricks

This file records the route-agnostic facts available from a WBS cross-piece
collision at the support-stuck supremum.  It deliberately does not attempt the
remaining endpoint inequality of `CrossPieceCollisionEndpointAtSup`.

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT86

namespace ProofsInTheBook.ZinanFFCT87

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## Collision-immediate zero supports. -/

/-- Cyclic predecessor in `Fin (n+1)`.  For value `0` this wraps to `n`;
otherwise it is the usual predecessor. -/
def predFin {n : ℕ} (r : Fin (n + 1)) : Fin (n + 1) :=
  ⟨(r.val + n) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- The support on the edge based at the collided tail vertex vanishes
identically: after rewriting the third vertex by the collision, the determinant
has the same vector in slots 1 and 3.  The successor is the cyclic `Fin`
successor, so the `s = n` case wraps to `0`. -/
theorem collision_identicalZeroSupport_succ
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1)
    (heq : openedWBS A B k ⟨r, hr⟩ = openedWBS A B k ⟨s, hs⟩) :
    sOrient (openedWBS A B k ⟨s, hs⟩)
      (openedWBS A B k (⟨s, hs⟩ + 1))
      (openedWBS A B k ⟨r, hr⟩) = 0 := by
  rw [heq, sOrient]
  exact ProofsInTheBook.SphericalDiagCut.det3_self_right _ _

/-- The support on the edge ending at the collided fixed vertex vanishes
identically: after rewriting the third vertex by the collision, the determinant
has the same vector in slots 2 and 3.  The predecessor is stated as a natural
index, so the side condition `0 < r` makes the boundary explicit. -/
theorem collision_identicalZeroSupport_predFin
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1)
    (heq : openedWBS A B k ⟨r, hr⟩ = openedWBS A B k ⟨s, hs⟩) :
    sOrient (openedWBS A B k (predFin ⟨r, hr⟩))
      (openedWBS A B k ⟨r, hr⟩)
      (openedWBS A B k ⟨s, hs⟩) = 0 := by
  rw [← heq, sOrient]
  exact ProofsInTheBook.SphericalDiagCut.det3_self_mid _ _

/-- The two determinant-zero readouts packaged together for the collision
shape used by `CrossPieceCollisionEndpointAtSup`. -/
theorem collision_identicalZeroSupports
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1)
    (_hrs : r + 2 ≤ s)
    (heq : openedWBS A B k ⟨r, hr⟩ = openedWBS A B k ⟨s, hs⟩) :
    sOrient (openedWBS A B k ⟨s, hs⟩)
        (openedWBS A B k (⟨s, hs⟩ + 1))
        (openedWBS A B k ⟨r, hr⟩) = 0 ∧
      sOrient (openedWBS A B k (predFin ⟨r, hr⟩))
        (openedWBS A B k ⟨r, hr⟩)
        (openedWBS A B k ⟨s, hs⟩) = 0 := by
  exact ⟨collision_identicalZeroSupport_succ A B k hr hs heq,
    collision_identicalZeroSupport_predFin A B k hr hs heq⟩

/-! ## Rigid fixed-prefix and rotated-tail congruence. -/

/-- Vertices at or before the opening axis are fixed by the WBS opening. -/
theorem openedWBS_fixed_vertex
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {p : ℕ} (hp : p < n + 1) (hpK : p ≤ (openingAxis k).val) :
    openedWBS A B k ⟨p, hp⟩ = A ⟨p, hp⟩ := by
  unfold openedWBS
  exact openTail_fixed A (openingAxis k) (-(monitoredSupWBS A B k)) hpK

/-- Distances inside the fixed prefix are unchanged. -/
theorem openedWBS_fixed_sDist
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {p q : ℕ} (hp : p < n + 1) (hq : q < n + 1)
    (hpK : p ≤ (openingAxis k).val) (hqK : q ≤ (openingAxis k).val) :
    sDist (openedWBS A B k ⟨p, hp⟩) (openedWBS A B k ⟨q, hq⟩) =
      sDist (A ⟨p, hp⟩) (A ⟨q, hq⟩) := by
  rw [openedWBS_fixed_vertex A B k hp hpK,
    openedWBS_fixed_vertex A B k hq hqK]

/-- Vertices strictly after the opening axis are a common `rotS2` image. -/
theorem openedWBS_tail_vertex
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {p : ℕ} (hp : p < n + 1) (hKp : (openingAxis k).val < p) :
    openedWBS A B k ⟨p, hp⟩ =
      rotS2 (A (openingAxis k)) (-(monitoredSupWBS A B k)) (A ⟨p, hp⟩) := by
  unfold openedWBS
  exact openTail_rot A (openingAxis k) (-(monitoredSupWBS A B k)) hKp

/-- Distances inside any post-axis tail sub-arm are unchanged by the common
rotation. -/
theorem openedWBS_tail_sDist
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {s p q : ℕ} (hsK : (openingAxis k).val < s)
    (hsp : s ≤ p) (hsq : s ≤ q)
    (hp : p < n + 1) (hq : q < n + 1) :
    sDist (openedWBS A B k ⟨p, hp⟩) (openedWBS A B k ⟨q, hq⟩) =
      sDist (A ⟨p, hp⟩) (A ⟨q, hq⟩) := by
  rw [openedWBS_tail_vertex A B k hp (by omega),
    openedWBS_tail_vertex A B k hq (by omega),
    sDist_rotS2]

/-- Spherical angles inside any post-axis tail sub-arm are unchanged by the
common rotation. -/
theorem openedWBS_tail_sphAngle
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {s p q t : ℕ} (hsK : (openingAxis k).val < s)
    (hsp : s ≤ p) (hsq : s ≤ q) (hst : s ≤ t)
    (hp : p < n + 1) (hq : q < n + 1) (ht : t < n + 1) :
    sphAngle (openedWBS A B k ⟨p, hp⟩) (openedWBS A B k ⟨q, hq⟩)
        (openedWBS A B k ⟨t, ht⟩) =
      sphAngle (A ⟨p, hp⟩) (A ⟨q, hq⟩) (A ⟨t, ht⟩) := by
  rw [openedWBS_tail_vertex A B k hp (by omega),
    openedWBS_tail_vertex A B k hq (by omega),
    openedWBS_tail_vertex A B k ht (by omega),
    sphAngle_rotS2]

/-- The fixed-prefix endpoint distance through a collision-side vertex is
unchanged. -/
theorem openedWBS_zero_to_fixed_sDist
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {r : ℕ} (hr : r < n + 1) (hrK : r ≤ (openingAxis k).val) :
    sDist (openedWBS A B k 0) (openedWBS A B k ⟨r, hr⟩) =
      sDist (A 0) (A ⟨r, hr⟩) := by
  change sDist (openedWBS A B k ⟨0, by omega⟩) (openedWBS A B k ⟨r, hr⟩) =
    sDist (A ⟨0, by omega⟩) (A ⟨r, hr⟩)
  exact openedWBS_fixed_sDist A B k (p := 0) (q := r) (by omega) hr
    (Nat.zero_le _) hrK

/-- The rotated-tail endpoint distance from a tail collision-side vertex to
the last vertex is unchanged. -/
theorem openedWBS_tail_to_last_sDist
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {s : ℕ} (hs : s < n + 1) (hsK : (openingAxis k).val < s) :
    sDist (openedWBS A B k ⟨s, hs⟩) (openedWBS A B k (Fin.last n)) =
      sDist (A ⟨s, hs⟩) (A (Fin.last n)) := by
  change sDist (openedWBS A B k ⟨s, hs⟩) (openedWBS A B k ⟨n, by omega⟩) =
    sDist (A ⟨s, hs⟩) (A ⟨n, by omega⟩)
  exact openedWBS_tail_sDist A B k (s := s) (p := s) (q := n)
    hsK (le_refl _) (by omega) hs (by omega)

/-- The endpoint of the opened WBS arm is definitionally its first-last
spherical distance. -/
theorem openedWBS_endpt_eq_sDist
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    endpt (openedWBS A B k) =
      sDist (openedWBS A B k 0) (openedWBS A B k (Fin.last n)) := rfl

/-! ## Deleting the collided loop. -/

/-- Delete the loop `r+1, ..., s` from an arm `P` by keeping the prefix
`[0..r]` and then shifting to the suffix `[s+1..n]`.  The new arm has
`n - (s - r)` edges, i.e. `n + 1 - (s - r)` vertices. -/
def deleteLoopArm {n : ℕ} (P : Fin (n + 1) → S2)
    (r s : ℕ) (hrs : r ≤ s) (hsn : s ≤ n) :
    Fin ((n - (s - r)) + 1) → S2 :=
  fun m =>
    if hm : m.val ≤ r then
      P ⟨m.val, by have := m.isLt; omega⟩
    else
      P ⟨m.val + (s - r), by have := m.isLt; omega⟩

@[simp] theorem deleteLoopArm_apply_head
    {n : ℕ} (P : Fin (n + 1) → S2)
    {r s : ℕ} (hrs : r ≤ s) (hsn : s ≤ n)
    {m : Fin ((n - (s - r)) + 1)} (hm : m.val ≤ r) :
    deleteLoopArm P r s hrs hsn m = P ⟨m.val, by have := m.isLt; omega⟩ := by
  simp [deleteLoopArm, hm]

@[simp] theorem deleteLoopArm_apply_tail
    {n : ℕ} (P : Fin (n + 1) → S2)
    {r s : ℕ} (hrs : r ≤ s) (hsn : s ≤ n)
    {m : Fin ((n - (s - r)) + 1)} (hm : r < m.val) :
    deleteLoopArm P r s hrs hsn m =
      P ⟨m.val + (s - r), by have := m.isLt; omega⟩ := by
  simp [deleteLoopArm, (not_le.mpr hm)]

/-- The loop-deleted arm starts at the same first vertex. -/
theorem deleteLoopArm_zero
    {n : ℕ} (P : Fin (n + 1) → S2)
    {r s : ℕ} (hrs : r ≤ s) (hsn : s ≤ n) :
    deleteLoopArm P r s hrs hsn 0 = P 0 := by
  rw [deleteLoopArm_apply_head P hrs hsn (Nat.zero_le _)]
  rfl

/-- The loop-deleted arm ends at the original last vertex, using the collision
when the deleted loop reaches the original last vertex. -/
theorem deleteLoopArm_last_eq_last_of_collision
    {n : ℕ} (P : Fin (n + 1) → S2)
    {r s : ℕ} (hrs : r ≤ s) (hsn : s ≤ n)
    (hr : r < n + 1) (hs : s < n + 1)
    (heq : P ⟨r, hr⟩ = P ⟨s, hs⟩) :
    deleteLoopArm P r s hrs hsn (Fin.last (n - (s - r))) = P (Fin.last n) := by
  by_cases hsnlt : s < n
  · have htail : r < (Fin.last (n - (s - r))).val := by
      simp [Fin.val_last]
      omega
    rw [deleteLoopArm_apply_tail P hrs hsn htail]
    apply congrArg P
    apply Fin.ext
    simp [Fin.val_last]
    omega
  · have hsn_eq : s = n := by omega
    have hhead : (Fin.last (n - (s - r))).val ≤ r := by
      simp [Fin.val_last]
      omega
    rw [deleteLoopArm_apply_head P hrs hsn hhead]
    have hlast_eq_r :
        (⟨(Fin.last (n - (s - r))).val, by have := (Fin.last (n - (s - r))).isLt; omega⟩ :
          Fin (n + 1)) = ⟨r, hr⟩ := by
      apply Fin.ext
      simp [Fin.val_last]
      omega
    rw [hlast_eq_r]
    trans P ⟨s, hs⟩
    · exact heq
    · apply congrArg P
      apply Fin.ext
      simp [Fin.val_last]
      omega

/-- Deleting a collided loop preserves the endpoint distance, because the
first and last vertices are unchanged after identifying `P r` with `P s`. -/
theorem deleteLoopArm_endpt_eq_of_collision
    {n : ℕ} (P : Fin (n + 1) → S2)
    {r s : ℕ} (hrs : r ≤ s) (hsn : s ≤ n)
    (hr : r < n + 1) (hs : s < n + 1)
    (heq : P ⟨r, hr⟩ = P ⟨s, hs⟩) :
    endpt (deleteLoopArm P r s hrs hsn) = endpt P := by
  unfold endpt
  rw [deleteLoopArm_zero P hrs hsn,
    deleteLoopArm_last_eq_last_of_collision P hrs hsn hr hs heq]

/-- The WBS-specialized loop-deleted arm for a collision branch. -/
def deleteLoopOpenedWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    (r s : ℕ) (hrs : r ≤ s) (hsn : s ≤ n) :
    Fin ((n - (s - r)) + 1) → S2 :=
  deleteLoopArm (openedWBS A B k) r s hrs hsn

/-- Endpoint preservation for the WBS-specialized loop deletion. -/
theorem deleteLoopOpenedWBS_endpt_eq
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {r s : ℕ} (hrs : r ≤ s) (hsn : s ≤ n)
    (hr : r < n + 1) (hs : s < n + 1)
    (heq : openedWBS A B k ⟨r, hr⟩ = openedWBS A B k ⟨s, hs⟩) :
    endpt (deleteLoopOpenedWBS A B k r s hrs hsn) =
      endpt (openedWBS A B k) := by
  exact deleteLoopArm_endpt_eq_of_collision (openedWBS A B k) hrs hsn hr hs heq

/-- At the glue base, the left endpoint of the deleted arm is the collided
tail vertex `P s`. -/
theorem deleteLoopArm_glue_left_eq
    {n : ℕ} (P : Fin (n + 1) → S2)
    {r s : ℕ} (hrs : r ≤ s) (hsn : s ≤ n)
    (hr : r < n + 1) (hs : s < n + 1)
    (heq : P ⟨r, hr⟩ = P ⟨s, hs⟩) :
    deleteLoopArm P r s hrs hsn ⟨r, by omega⟩ = P ⟨s, hs⟩ := by
  rw [deleteLoopArm_apply_head P hrs hsn (le_refl r)]
  exact heq

/-- At a non-wrap glue base, the right endpoint is the original successor
`s+1`.  The wrap case `s = n` is an endpoint/wrap support issue and is left in
the residual report rather than being used as an endpoint route. -/
theorem deleteLoopArm_glue_right_eq_of_lt
    {n : ℕ} (P : Fin (n + 1) → S2)
    {r s : ℕ} (hrs : r ≤ s) (hsn : s ≤ n) (hslt : s < n) :
    deleteLoopArm P r s hrs hsn (⟨r, by omega⟩ + 1) =
      P ⟨s + 1, by omega⟩ := by
  have hsucc :
      (⟨r, by omega⟩ + 1 : Fin ((n - (s - r)) + 1)) =
        ⟨r + 1, by omega⟩ := by
    apply Fin.ext
    have hone : ((1 : Fin ((n - (s - r)) + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (by omega)]
  rw [hsucc, deleteLoopArm_apply_tail P hrs hsn (Nat.lt_succ_self r)]
  apply congrArg P
  apply Fin.ext
  simp
  omega

/-- The glue edge of the loop-deleted arm is short because it is the original
edge `(s, s+1)` of `P` after the collision identifies `r` with `s`. -/
theorem deleteLoopArm_glue_edge_short
    {n : ℕ} {P : Fin (n + 1) → S2} (hP : WeakConvexSphArm P)
    {r s : ℕ} (hrs : r ≤ s) (hsn : s ≤ n) (hslt : s < n)
    (hr : r < n + 1) (hs : s < n + 1)
    (heq : P ⟨r, hr⟩ = P ⟨s, hs⟩) :
    ShortArc
      (deleteLoopArm P r s hrs hsn ⟨r, by omega⟩)
      (deleteLoopArm P r s hrs hsn (⟨r, by omega⟩ + 1)) := by
  rw [deleteLoopArm_glue_left_eq P hrs hsn hr hs heq,
    deleteLoopArm_glue_right_eq_of_lt P hrs hsn hslt]
  have hedge := hP.closed_convex.edge_short ⟨s, hs⟩
  have hsucc : (⟨s, hs⟩ + 1 : Fin (n + 1)) = ⟨s + 1, by omega⟩ := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (by omega)]
  simpa [hsucc] using hedge

/-- The two residual facts that block a blind proof of weak convexity for the
deleted loop.  The glue edge itself is derivable; what remains is the incoming
glue joint's support and the wrap-edge support family for the new closed arm. -/
def DeleteLoopGlueResidual {n : ℕ} (P : Fin (n + 1) → S2) (r s : ℕ)
    (hrs : r ≤ s) (hsn : s ≤ n) : Prop :=
  (∀ (_hr0 : 0 < r), 0 ≤ sOrient
      (deleteLoopArm P r s hrs hsn ⟨r - 1, by omega⟩)
      (deleteLoopArm P r s hrs hsn ⟨r, by omega⟩)
      (deleteLoopArm P r s hrs hsn (⟨r, by omega⟩ + 1))) ∧
    ∀ v : Fin ((n - (s - r)) + 1),
      0 ≤ sOrient
        (deleteLoopArm P r s hrs hsn (Fin.last (n - (s - r))))
        (deleteLoopArm P r s hrs hsn 0)
        (deleteLoopArm P r s hrs hsn v)

/-! ## Guards. -/

#print axioms collision_identicalZeroSupports
#print axioms openedWBS_tail_sDist
#print axioms openedWBS_tail_sphAngle
#print axioms deleteLoopOpenedWBS_endpt_eq
#print axioms deleteLoopArm_glue_edge_short

end ProofsInTheBook.ZinanFFCT87
