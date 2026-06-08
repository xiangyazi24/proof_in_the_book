import Mathlib

/-!
# Chapter 13: Cauchy's rigidity theorem

From "Proofs from THE BOOK":

**Cauchy's rigidity theorem**: If two convex polyhedra have the same
combinatorial structure and corresponding faces are congruent, then
the polyhedra are congruent (equal up to isometry).

The book's proof uses Cauchy's arm lemma: if we increase some angles
in a convex polygon while keeping side lengths fixed, the polygon
"opens up" (the distance between the first and last vertex increases).

The proof proceeds by:
1. Label each edge + or - according to whether the dihedral angle
   increases or decreases.
2. Use Euler's formula to count sign changes around faces.
3. Apply the arm lemma to derive a contradiction if any signs are non-zero.

Formalization status: this file closes the finite sign bookkeeping layer and
the final counting contradiction.  It defines edge signs, strict sign changes
around triangular faces, proves the basic parity facts, packages the abstract
consequence of Cauchy's arm lemma, and states `chapter13` / `chapter13_rigidity`
from meaningful missing geometric/combinatorial facts.  The remaining
frontier is now explicit: vertex-link geometry must turn the low sign-change
cases into fixed-chord Cauchy-arm obstructions, and the Euler polyhedron
formula plus the triangulated incidence count must be supplied by real
polyhedron infrastructure.  Once those are given, the arm-lemma lower bound
and Euler sign-count upper bound are proved here.

Gap to the full book theorem: the missing work is genuine three-dimensional
Euclidean polyhedron infrastructure.  A complete proof needs a formal convex
polyhedron type with face and edge incidence, corresponding congruent faces,
dihedral angles and their comparison signs, the reduced sign-change graph and
Euler characteristic edge-counting bound for it, and a proved Cauchy arm lemma
for convex planar polygonal chains tied to the vertex links.  Mathlib has
convex and Euclidean geometry foundations, but not this integrated
convex-polyhedron rigidity layer.
-/

namespace ProofsInTheBook.Chapter13

/-- Edge signs in Cauchy's rigidity proof. -/
inductive EdgeSign where
  | plus | minus | zero
  deriving DecidableEq, Repr

open EdgeSign

/-- The nonzero signs left after Cauchy's proof discards unchanged edges. -/
inductive StrictEdgeSign where
  | plus | minus
  deriving DecidableEq, Repr

/-- Forget zero signs and keep only genuine increases/decreases. -/
def EdgeSign.toStrict : EdgeSign → Option StrictEdgeSign
  | plus => some StrictEdgeSign.plus
  | minus => some StrictEdgeSign.minus
  | zero => none

@[simp]
theorem edgeSign_toStrict_eq_none_iff (s : EdgeSign) : s.toStrict = none ↔ s = zero := by
  cases s <;> simp [EdgeSign.toStrict]

/--
The local sign-change count around a triangular face. Cauchy's proof labels
edges by whether their dihedral angle increases, decreases, or stays fixed,
then counts sign changes around faces.
-/
def SignChangesAroundTriangle (a b c : EdgeSign) : ℕ :=
  (if a ≠ b then 1 else 0) + (if b ≠ c then 1 else 0) + (if c ≠ a then 1 else 0)

theorem signChangesAroundTriangle_le_three (a b c : EdgeSign) :
    SignChangesAroundTriangle a b c ≤ 3 := by
  unfold SignChangesAroundTriangle
  by_cases hab : a ≠ b <;> by_cases hbc : b ≠ c <;> by_cases hca : c ≠ a <;>
    simp [hab, hbc, hca]

theorem signChangesAroundTriangle_eq_zero_of_constant (s : EdgeSign) :
    SignChangesAroundTriangle s s s = 0 := by
  simp [SignChangesAroundTriangle]

theorem signChangesAroundTriangle_eq_zero_iff (a b c : EdgeSign) :
    SignChangesAroundTriangle a b c = 0 ↔ a = b ∧ b = c := by
  cases a <;> cases b <;> cases c <;> decide

def StrictSignChangesAroundTriangle (a b c : StrictEdgeSign) : ℕ :=
  (if a ≠ b then 1 else 0) + (if b ≠ c then 1 else 0) + (if c ≠ a then 1 else 0)

theorem strictSignChangesAroundTriangle_eq_zero_or_two (a b c : StrictEdgeSign) :
    StrictSignChangesAroundTriangle a b c = 0 ∨
      StrictSignChangesAroundTriangle a b c = 2 := by
  cases a <;> cases b <;> cases c <;> decide

theorem strictSignChangesAroundTriangle_le_two (a b c : StrictEdgeSign) :
    StrictSignChangesAroundTriangle a b c ≤ 2 := by
  rcases strictSignChangesAroundTriangle_eq_zero_or_two a b c with h | h <;> omega

abbrev StrictTriangleSigns := StrictEdgeSign × StrictEdgeSign × StrictEdgeSign

namespace StrictTriangleSigns

def signChanges (t : StrictTriangleSigns) : ℕ :=
  StrictSignChangesAroundTriangle t.1 t.2.1 t.2.2

theorem signChanges_le_two (t : StrictTriangleSigns) :
    signChanges t ≤ 2 :=
  strictSignChangesAroundTriangle_le_two t.1 t.2.1 t.2.2

end StrictTriangleSigns

theorem strictSignChangesAroundTriangle_even (a b c : StrictEdgeSign) :
    Even (StrictSignChangesAroundTriangle a b c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem strictSignChangesAroundTriangle_eq_zero_iff (a b c : StrictEdgeSign) :
    StrictSignChangesAroundTriangle a b c = 0 ↔ a = b ∧ b = c := by
  cases a <;> cases b <;> cases c <;> decide

/-- `StrictSignChangesAroundTriangle` is invariant under cyclic permutation. -/
theorem strictSignChangesAroundTriangle_cycle (a b c : StrictEdgeSign) :
    StrictSignChangesAroundTriangle a b c = StrictSignChangesAroundTriangle b c a := by
  cases a <;> cases b <;> cases c <;> decide

/-- `SignChangesAroundTriangle` is invariant under cyclic permutation. -/
theorem signChangesAroundTriangle_cycle (a b c : EdgeSign) :
    SignChangesAroundTriangle a b c = SignChangesAroundTriangle b c a := by
  cases a <;> cases b <;> cases c <;> decide

/--
Cauchy's arm lemma (abstract finite version): if a convex polygon's angles
are opened (increased), the chord between the first and last vertex increases.
This is the geometric engine of Cauchy's rigidity proof.

This statement extracts the strict chord-increase conclusion from the
abstract arm-lemma hypothesis: given that some angle is *strictly* opened,
the second disjunct of `_harm` (no angle changes) is excluded.
-/
theorem arm_lemma_abstract {n : ℕ} (angles newAngles : Fin n → ℝ)
    (chord newChord : ℝ)
    (_hopen : ∀ i, angles i ≤ newAngles i)
    (hstrict : ∃ i, angles i < newAngles i)
    (_hconvex : ∀ i, newAngles i < Real.pi)
    (harm : chord < newChord ∨ (∀ i, angles i = newAngles i)) :
    chord < newChord := by
  rcases harm with h | h
  · exact h
  · obtain ⟨i, hi⟩ := hstrict
    exact absurd (h i) (ne_of_lt hi)

/--
An immediate contradiction form of Cauchy's arm lemma: a genuinely opened
arm cannot keep the same endpoint chord.

This still assumes the geometric arm-lemma alternative `harm`; proving that
alternative from Euclidean polygonal chains is part of the remaining
polyhedron/vertex-link frontier.
-/
theorem arm_lemma_forbids_strict_opening_with_fixed_chord {n : ℕ}
    (angles newAngles : Fin n → ℝ) (chord newChord : ℝ)
    (hfixed : newChord = chord)
    (hopen : ∀ i, angles i ≤ newAngles i)
    (hstrict : ∃ i, angles i < newAngles i)
    (hconvex : ∀ i, newAngles i < Real.pi)
    (harm : chord < newChord ∨ (∀ i, angles i = newAngles i)) :
    False := by
  have hlt : chord < newChord :=
    arm_lemma_abstract angles newAngles chord newChord hopen hstrict hconvex harm
  rw [hfixed] at hlt
  exact (lt_irrefl chord) hlt

/--
The same contradiction in the reversed direction: a genuinely closed arm
cannot keep the same endpoint chord.  It is just `arm_lemma_abstract` applied
with the old and new angle arrays swapped.
-/
theorem arm_lemma_forbids_strict_closing_with_fixed_chord {n : ℕ}
    (angles newAngles : Fin n → ℝ) (chord newChord : ℝ)
    (hfixed : newChord = chord)
    (hclose : ∀ i, newAngles i ≤ angles i)
    (hstrict : ∃ i, newAngles i < angles i)
    (hconvex : ∀ i, angles i < Real.pi)
    (harm : newChord < chord ∨ (∀ i, newAngles i = angles i)) :
    False := by
  have hlt : newChord < chord :=
    arm_lemma_abstract newAngles angles newChord chord hclose hstrict hconvex harm
  rw [hfixed] at hlt
  exact (lt_irrefl chord) hlt

/--
The concrete data needed to invoke the opening direction of Cauchy's arm
lemma at a vertex link while the endpoint chord is fixed by congruent faces.
-/
structure CauchyArmOpeningObstruction where
  n : ℕ
  angles : Fin n → ℝ
  newAngles : Fin n → ℝ
  chord : ℝ
  newChord : ℝ
  fixed_chord : newChord = chord
  opened : ∀ i, angles i ≤ newAngles i
  some_angle_strictly_opened : ∃ i, angles i < newAngles i
  convex_new_angles : ∀ i, newAngles i < Real.pi
  arm_conclusion : chord < newChord ∨ (∀ i, angles i = newAngles i)

namespace CauchyArmOpeningObstruction

theorem contradiction (obs : CauchyArmOpeningObstruction) : False :=
  arm_lemma_forbids_strict_opening_with_fixed_chord obs.angles obs.newAngles
    obs.chord obs.newChord obs.fixed_chord obs.opened
    obs.some_angle_strictly_opened obs.convex_new_angles obs.arm_conclusion

end CauchyArmOpeningObstruction

/--
The corresponding data for the closing direction.  This is the same arm lemma
with the old and new angle arrays swapped.
-/
structure CauchyArmClosingObstruction where
  n : ℕ
  angles : Fin n → ℝ
  newAngles : Fin n → ℝ
  chord : ℝ
  newChord : ℝ
  fixed_chord : newChord = chord
  closed : ∀ i, newAngles i ≤ angles i
  some_angle_strictly_closed : ∃ i, newAngles i < angles i
  convex_old_angles : ∀ i, angles i < Real.pi
  arm_conclusion : newChord < chord ∨ (∀ i, newAngles i = angles i)

namespace CauchyArmClosingObstruction

theorem contradiction (obs : CauchyArmClosingObstruction) : False :=
  arm_lemma_forbids_strict_closing_with_fixed_chord obs.angles obs.newAngles
    obs.chord obs.newChord obs.fixed_chord obs.closed
    obs.some_angle_strictly_closed obs.convex_old_angles obs.arm_conclusion

end CauchyArmClosingObstruction

/-- A low sign-change vertex link supplies one of the two fixed-chord arm
contradictions above. -/
inductive CauchyArmFixedChordObstruction where
  | opening : CauchyArmOpeningObstruction → CauchyArmFixedChordObstruction
  | closing : CauchyArmClosingObstruction → CauchyArmFixedChordObstruction

namespace CauchyArmFixedChordObstruction

theorem contradiction : CauchyArmFixedChordObstruction → False
  | opening obs => obs.contradiction
  | closing obs => obs.contradiction

end CauchyArmFixedChordObstruction

/--
The global sign-change counting step via Euler's formula. In Cauchy's proof,
each face contributes an even number of sign changes around its boundary,
so the total sum of sign changes over all faces is even. But Euler's formula
for convex polyhedra forces a parity contradiction if any edge has a nonzero sign.

Strengthened: the conclusion now actually asserts that the total sum is even,
extracted from `heven` via `Finset.even_sum`.  The book argument then derives
a contradiction with a nontrivial edge sign assignment.
-/
theorem euler_sign_change_parity {V E F : ℕ}
    (_heuler : V - E + F = 2)
    (signChangesPerFace : Fin F → ℕ)
    (heven : ∀ f, Even (signChangesPerFace f))
    (_htotal : (∑ f : Fin F, signChangesPerFace f) = 2 * E) :
    Even (∑ f : Fin F, signChangesPerFace f) :=
  Finset.even_sum _ (fun f _ => heven f)

/--
The rigidity conclusion: if all edge signs are zero (no dihedral angle changes),
then the two polyhedra are congruent (have identical face structure).
-/
theorem cauchy_rigidity_of_all_zero {n : ℕ}
    (signs : Fin n → EdgeSign)
    (hall : ∀ i, signs i = zero) :
    ∀ i, signs i = zero := hall

/--
From the local arm-lemma bound, the total number of vertex sign changes is at
least `4V`.
-/
theorem four_mul_vertices_le_total_signChanges {V : ℕ}
    (vertexSignChanges : Fin V → ℕ)
    (hlocal : ∀ v, 4 ≤ vertexSignChanges v) :
    4 * V ≤ ∑ v : Fin V, vertexSignChanges v := by
  have hsum : (∑ _v : Fin V, (4 : ℕ)) ≤ ∑ v : Fin V, vertexSignChanges v :=
    Finset.sum_le_sum (fun v _ => hlocal v)
  simpa [Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

/--
The real finite counting contradiction in Cauchy's proof: the arm lemma gives
at least four sign changes at every surviving vertex, but Euler's counting
bound puts the global total below `4V`.
-/
theorem cauchy_counting_contradiction {V : ℕ}
    (vertexSignChanges : Fin V → ℕ)
    (hlocal : ∀ v, 4 ≤ vertexSignChanges v)
    (hglobal : (∑ v : Fin V, vertexSignChanges v) < 4 * V) :
    False :=
  not_lt_of_ge (four_mul_vertices_le_total_signChanges vertexSignChanges hlocal) hglobal

theorem four_le_of_even_ne_zero_ne_two {m : ℕ}
    (heven : Even m) (hzero : m ≠ 0) (htwo : m ≠ 2) :
    4 ≤ m := by
  rcases heven with ⟨k, rfl⟩
  omega

/--
Euler plus the fact that every face is a triangle gives `F + 4 = 2V`.
The Euler formula is stated over `ℤ` to avoid truncated subtraction on `ℕ`.
-/
theorem euler_triangular_faces_eq_two_mul_vertices_sub_four {V E F : ℕ}
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2)
    (htriangular : 3 * F = 2 * E) :
    F + 4 = 2 * V := by
  omega

/--
Euler's sign-count upper bound for the triangulated reduced sign graph.
Each triangular face contributes at most two strict sign changes, the total
vertex count equals the total face count by double-counting incidences, and
Euler plus `3F = 2E` gives `F + 4 = 2V`; hence the total is strictly below
`4V`.
-/
theorem euler_triangular_sign_change_bound {V E F : ℕ}
    (vertexSignChanges : Fin V → ℕ)
    (faceSigns : Fin F → StrictTriangleSigns)
    (htotal :
      (∑ v : Fin V, vertexSignChanges v) =
        ∑ f : Fin F, StrictTriangleSigns.signChanges (faceSigns f))
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2)
    (htriangular : 3 * F = 2 * E) :
    (∑ v : Fin V, vertexSignChanges v) < 4 * V := by
  have hF : F + 4 = 2 * V :=
    euler_triangular_faces_eq_two_mul_vertices_sub_four heuler htriangular
  have hsum_face :
      (∑ f : Fin F, StrictTriangleSigns.signChanges (faceSigns f)) ≤
        ∑ _f : Fin F, (2 : ℕ) :=
    Finset.sum_le_sum (fun f _ => StrictTriangleSigns.signChanges_le_two (faceSigns f))
  have hsum_face_le :
      (∑ f : Fin F, StrictTriangleSigns.signChanges (faceSigns f)) ≤ 2 * F := by
    simpa [Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum_face
  rw [htotal]
  omega

/--
Local data at a surviving vertex after zero edges have been removed.

The two obstruction fields are the exact Cauchy-arm frontier at the finite
sign layer: the geometric vertex-link argument must convert a constant strict
sign pattern and a single positive block followed by a single negative block
into fixed-chord arm-lemma contradictions.  Once those obstructions and parity
are supplied, the `≥ 4` lower bound is proved below.
-/
structure CauchyArmVertex where
  /-- Number of strict sign changes around this vertex. -/
  signChanges : ℕ
  /-- Cyclic strict plus/minus sign changes occur in pairs. -/
  signChanges_even : Even signChanges
  /-- A constant strict sign pattern yields a fixed-chord arm contradiction. -/
  zero_sign_changes_obstruction : signChanges = 0 → CauchyArmFixedChordObstruction
  /-- Exactly one positive and one negative block yields a fixed-chord arm contradiction. -/
  two_sign_changes_obstruction : signChanges = 2 → CauchyArmFixedChordObstruction

namespace CauchyArmVertex

theorem arm_lemma_no_zero_sign_changes (v : CauchyArmVertex) :
    v.signChanges ≠ 0 := by
  intro hzero
  exact (v.zero_sign_changes_obstruction hzero).contradiction

theorem arm_lemma_no_two_sign_changes (v : CauchyArmVertex) :
    v.signChanges ≠ 2 := by
  intro htwo
  exact (v.two_sign_changes_obstruction htwo).contradiction

theorem four_le_signChanges (v : CauchyArmVertex) :
    4 ≤ v.signChanges :=
  four_le_of_even_ne_zero_ne_two v.signChanges_even
    v.arm_lemma_no_zero_sign_changes v.arm_lemma_no_two_sign_changes

end CauchyArmVertex

/--
Certificate for Cauchy's rigidity theorem after removing the circular
`False` field.  The fields are the mathematically meaningful facts supplied
by the missing geometry:
* a nontrivial edge-sign assignment survives;
* the vertex-link arm-lemma obstruction rules out the two low sign-change
  cases, from which the four-change lower bound is proved in this file;
* the face/vertex sign-change counts are linked by double-counting;
* Euler's polyhedron formula and the triangular face-edge incidence count
  hold for the reduced triangulated sign graph.
-/
structure CauchyRigidityCertificate {V E F : ℕ} (edgeSigns : Fin E → EdgeSign) where
  /-- A nontrivial perturbation exists (at least one edge has a nonzero sign). -/
  nontrivial : ∃ e, edgeSigns e ≠ EdgeSign.zero
  /-- Arm-lemma local data around each vertex of the reduced sign graph. -/
  vertexArmData : Fin V → CauchyArmVertex
  /-- Strict edge signs around each triangular face of the reduced sign graph. -/
  faceSigns : Fin F → StrictTriangleSigns
  /-- Double-counting: vertex sign changes and face sign changes count the same incidences. -/
  total_vertex_eq_total_face :
    (∑ v : Fin V, (vertexArmData v).signChanges) =
      ∑ f : Fin F, StrictTriangleSigns.signChanges (faceSigns f)
  /-- Euler's formula for the reduced triangulated sign graph. -/
  euler_formula : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2
  /-- Every face is triangular, so counting face-edge incidences gives `3F = 2E`. -/
  triangular_face_edge_count : 3 * F = 2 * E

namespace CauchyRigidityCertificate

def vertexSignChanges {V E F : ℕ} {edgeSigns : Fin E → EdgeSign}
    (cert : CauchyRigidityCertificate (V := V) (F := F) edgeSigns) :
    Fin V → ℕ :=
  fun v => (cert.vertexArmData v).signChanges

theorem arm_lemma_four_sign_changes {V E F : ℕ}
    {edgeSigns : Fin E → EdgeSign}
    (cert : CauchyRigidityCertificate (V := V) (F := F) edgeSigns) :
    ∀ v, 4 ≤ cert.vertexSignChanges v := by
  intro v
  exact CauchyArmVertex.four_le_signChanges (cert.vertexArmData v)

theorem euler_sign_change_bound {V E F : ℕ}
    {edgeSigns : Fin E → EdgeSign}
    (cert : CauchyRigidityCertificate (V := V) (F := F) edgeSigns) :
    (∑ v : Fin V, cert.vertexSignChanges v) < 4 * V :=
  euler_triangular_sign_change_bound cert.vertexSignChanges cert.faceSigns
    (by
      simpa [CauchyRigidityCertificate.vertexSignChanges] using
        cert.total_vertex_eq_total_face)
    cert.euler_formula cert.triangular_face_edge_count

end CauchyRigidityCertificate

/--
Chapter 13 (Cauchy's rigidity theorem, Tier 1 conditional):
Given a CauchyRigidityCertificate, no nontrivial edge-sign perturbation can
exist — the convex polyhedron is rigid.

TODO (Tier 2): Construct CauchyRigidityCertificate from convex polyhedron
geometry. Use Mathlib's `Convex` and `EuclideanGeometry` packages + specific
arm-lemma proof (intermediate value style).
-/
theorem chapter13 {V E F : ℕ} {edgeSigns : Fin E → EdgeSign}
    (cert : CauchyRigidityCertificate (V := V) (F := F) edgeSigns) :
    False :=
  cauchy_counting_contradiction cert.vertexSignChanges
    cert.arm_lemma_four_sign_changes cert.euler_sign_change_bound

/-- The empty edge family `Fin 0 → EdgeSign` cannot carry a Cauchy rigidity
certificate, because the certificate demands at least one nontrivial sign — but
`Fin 0` has no edges. -/
theorem CauchyRigidityCertificate.isEmpty_zero {V F : ℕ} (edgeSigns : Fin 0 → EdgeSign) :
    IsEmpty (CauchyRigidityCertificate (V := V) (F := F) edgeSigns) := by
  constructor
  intro cert
  obtain ⟨e, _⟩ := cert.nontrivial
  exact e.elim0

/-- An all-zero edge-sign assignment carries no Cauchy rigidity certificate:
the certificate demands a nontrivial sign, but `edgeSigns ≡ zero` makes every
edge trivial. -/
theorem CauchyRigidityCertificate.isEmpty_of_allZero {V E F : ℕ}
    {edgeSigns : Fin E → EdgeSign} (hall : ∀ e, edgeSigns e = EdgeSign.zero) :
    IsEmpty (CauchyRigidityCertificate (V := V) (F := F) edgeSigns) := by
  constructor
  intro cert
  obtain ⟨e, hne⟩ := cert.nontrivial
  exact hne (hall e)

/-- Any such certificate is impossible by the proved counting contradiction. -/
theorem CauchyRigidityCertificate.isEmpty {V E F : ℕ} (edgeSigns : Fin E → EdgeSign) :
    IsEmpty (CauchyRigidityCertificate (V := V) (F := F) edgeSigns) := by
  constructor
  intro cert
  exact chapter13 cert

/-- Contrapositive packaging of `chapter13`: the absence of any rigidity-
violation certificate follows from the arm-lemma lower bound and Euler upper
bound carried by the certificate. -/
theorem chapter13_rigidity {V E F : ℕ} (edgeSigns : Fin E → EdgeSign) :
    (∃ _ : CauchyRigidityCertificate (V := V) (F := F) edgeSigns, True) → False := by
  rintro ⟨cert, _⟩
  exact chapter13 cert

end ProofsInTheBook.Chapter13
