import ProofsInTheBook.ZinanCh36Interval
import ProofsInTheBook.ZinanCh36Harvest
import ProofsInTheBook.PolygonWindingBound
import ProofsInTheBook.PolygonWindingPath
import ProofsInTheBook.PolygonGeometryDischarge

/-!
# `ZinanCh36InteriorValue` — the signed interior-VALUE package (Route C)

The harvest (`ZinanCh36Harvest`) closes the Chapter-36 chain UP TO a single residue: the
alternation kernel pins the winding's *membership* in `{0, 1, -1}` but not WHICH value, and every
consumer below the bound needs a *specific* interior winding value (`= 1` for "inside the parent",
`= 1` for "inside the left ear").

This file implements the WORKER-grade bricks of the **interior-value package** (Route C, the
split-induction value package). The keystone is the sign-parametrized predicate

  `WindValuesWithSign P s := (s = 1 ∨ s = -1) ∧ ∀ ρ x, off-boundary → windCross P ρ x ∈ {0, s}`

which says the polygon `P` is "value-coherent with sign `s`": at every generic off-boundary point
the signed winding is either `0` (exterior) or exactly `s` (interior).  The kernel bound
`windCross_mem_final` (`windCross ∈ {0, 1, -1}`) is the UNSIGNED version; `WindValuesWithSign`
upgrades it to a 2-valued `{0, s}` discipline.

The ear split closes **algebraically**: at a diagonal `windCross_L + windCross_R = windCross_P`,
with `windCross_L, windCross_R ∈ {0, s}` (the package on each sub-polygon) and the *unconditional*
bound `windCross_P ∈ {0, 1, -1}` (from `windCross_mem_final`), the both-interior state
`L = R = s` would force `P = 2s ∉ {0, ±1}` — excluded.  So the sign survives the split, and the
sharper distribution `L = s → (R = 0 ∧ P = s)` holds.

## Sign discipline (orientation-dependence)

The winding is orientation-dependent: reversing the vertex order flips the sign.  We parametrize by
`s ∈ {1, -1}` throughout; the `= 1` consumers of the harvest become wrappers at `s = 1`.

## Off-boundary side conditions (hypothesis-shape note)

The two genericity guards used everywhere here are exactly those of `windCross_mem_final`:
`hoff : ¬ OnBoundary P x` and `hvert : ∀ k, side ρ.r x (P.q k) ≠ 0`.  We bundle them per-polygon
inside `WindValuesWithSign`.  For the split bricks the point `x` must be off ALL THREE boundaries
(parent `P`, left `L`, right `R`) with the respective vertex guards; we take those as the weakest
hypotheses that make the proof go through (documented in the report).

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36InteriorValue

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonWinding
  (windCross windCross_split_common windCross_ne_zero_of_odd_crossing)
open ProofsInTheBook.PolygonWindingBound
open ProofsInTheBook.ZinanCh36Interval (windCross_mem_final)

noncomputable section

variable {n : ℕ}

/-! ## Brick 1 — the signed value package `WindValuesWithSign` and its odd consequence -/

/-- **The signed interior-value package.**  `WindValuesWithSign P s` asserts that `s` is a unit
sign (`±1`) and that at every generic off-boundary point of `P` (off the boundary, ray avoiding all
vertices) the signed winding is either `0` (exterior) or exactly `s` (interior).  This is the
2-valued upgrade of the unsigned kernel bound `windCross ∈ {0, 1, -1}`: it pins the interior value
to the single sign `s`. -/
def WindValuesWithSign (P : StrictSimplePolygon n) (s : ℤ) : Prop :=
  (s = 1 ∨ s = -1) ∧
    ∀ (ρ : RayDirection P) (x : Pt),
      ¬ OnBoundary P x → (∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) →
        windCross P ρ x = 0 ∨ windCross P ρ x = s

/-- **The package's sign is a unit.** -/
theorem WindValuesWithSign.sign_unit {P : StrictSimplePolygon n} {s : ℤ}
    (hP : WindValuesWithSign P s) : s = 1 ∨ s = -1 :=
  hP.1

/-- **The package's value dichotomy at a generic off-boundary point.** -/
theorem WindValuesWithSign.values {P : StrictSimplePolygon n} {s : ℤ}
    (hP : WindValuesWithSign P s) (ρ : RayDirection P) (x : Pt)
    (hoff : ¬ OnBoundary P x) (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) :
    windCross P ρ x = 0 ∨ windCross P ρ x = s :=
  hP.2 ρ x hoff hvert

/-- **Odd crossing pins the winding to the sign `s`.**  Under the package, if the (unsigned)
crossing number at a generic off-boundary point is ODD, the signed winding is exactly `s` — not
just nonzero.  Reason: `windCross ∈ {0, s}` (package) and `windCross ≠ 0` (odd crossing forces
nonzero, since `0` is even), so `windCross = s`. -/
theorem wind_eq_sign_of_odd {P : StrictSimplePolygon n} {s : ℤ}
    (hP : WindValuesWithSign P s) (ρ : RayDirection P) {x : Pt}
    (hoff : ¬ OnBoundary P x) (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (hodd : Odd (CrossingNumber' P ρ x)) :
    windCross P ρ x = s := by
  have hne : windCross P ρ x ≠ 0 :=
    windCross_ne_zero_of_odd_crossing P ρ hodd
  rcases hP.values ρ x hoff hvert with h0 | hs
  · exact absurd h0 hne
  · exact hs

/-! ## Brick 2 — the signed exterior route (value `1` generalized to `s`)

We generalize the harvest's `earDeletedExterior_winding_route` / the bound's
`earDeleted_exterior_of_bound` from the hard-coded value `1` to the sign parameter `s`: at an inside
parent point (`windCross_P = s`) where the LEFT ear also contains the point (`windCross_L = s`), the
diagonal split `windCross_L + windCross_R = windCross_P` forces `windCross_R = 0`, so the ear point
lies OUTSIDE the ear-deleted polygon `R`.  Routed through the algebraic split + the proved exterior
bridge `notClosedRegion'_of_windZero` — NOT the machine-refuted half-plane anchor. -/

/-- **The signed winding route to `earDeletedExterior`.**  Sign-parametrized form of
`PolygonWindingBound.earDeleted_exterior_of_bound`: at a parent-interior point `windCross_P = s`
with the left ear also interior (`windCross_L = s`), the right ear-deleted sub-polygon has winding
`0`, hence the point is not in its closed region.  The proof is the algebraic cancellation
`windCross_L + windCross_R = windCross_P` ⟹ `windCross_R = s - s = 0`, fed to the proved
zero-winding exterior bridge.  This is a 40–70 line adaptation of `earDeleted_exterior_of_bound`,
verbatim except the constant `1` is replaced by `s` (the split identity is sign-agnostic). -/
theorem earDeletedExterior_winding_route_sign {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) {x : Pt} {s : ℤ}
    (hoffR : ¬ OnBoundary (buildRightPoly h rax) x)
    (hLin : windCross (buildLeftPoly h lax) σL x = s)
    (hPin : windCross P ρ x = s) :
    ¬ ClosedRegion' (buildRightPoly h rax) σR x := by
  have hsplit := windCross_split_common h lax rax σL σR hL hR x
  -- windCross_L + windCross_R = windCross_P, with windCross_L = s and windCross_P = s
  have hR0 : windCross (buildRightPoly h rax) σR x = 0 := by
    rw [hLin, hPin] at hsplit; omega
  exact outside_of_subWinding_zero (buildRightPoly h rax) σR hoffR hR0

/-! ## Brick 3 — the split identity / value distribution at an ear diagonal

At an ear diagonal the parent `P` splits into the left triangle `L` and the right polygon `R` with
`windCross_L + windCross_R = windCross_P`.  Given `WindValuesWithSign L s` and
`WindValuesWithSign R s` and the UNCONDITIONAL bound `windCross_P ∈ {0, 1, -1}` (from
`windCross_mem_final`), the both-interior state `L = R = s` would force `P = 2s ∉ {0, ±1}` —
excluded.  We conclude the sharper distribution lemma. -/

/-- **The signed split value distribution at an ear diagonal.**  For a point `x` off ALL THREE
boundaries (parent `P`, left `L`, right `R`) with the respective ray-vertex genericity guards,
under `WindValuesWithSign L s` and `WindValuesWithSign R s` (the package on each sub-polygon and the
common sign `s`):

* each sub-winding is in `{0, s}` (package),
* the parent winding is in `{0, 1, -1}` (unconditional kernel bound), and
* the split identity `windCross_L + windCross_R = windCross_P` holds.

The both-interior state (`L = R = s`) is EXCLUDED, because it would force `P = 2s`, which is `2` or
`-2`, neither in `{0, 1, -1}`.  So exactly one of the following holds, and in every case the parent
inherits the package value:

  `(L = 0 ∧ R = 0 ∧ P = 0)  ∨  (L = s ∧ R = 0 ∧ P = s)  ∨  (L = 0 ∧ R = s ∧ P = s)`.

In particular `windCross_P ∈ {0, s}` — the package value propagates to the parent. -/
theorem windValues_split_offAll {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) {x : Pt} {s : ℤ}
    (hValL : WindValuesWithSign (buildLeftPoly h lax) s)
    (hValR : WindValuesWithSign (buildRightPoly h rax) s)
    (hoffP : ¬ OnBoundary P x) (hvertP : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (hoffL : ¬ OnBoundary (buildLeftPoly h lax) x)
    (hvertL : ∀ k, side σL.r x ((buildLeftPoly h lax).q k) ≠ 0)
    (hoffR : ¬ OnBoundary (buildRightPoly h rax) x)
    (hvertR : ∀ k, side σR.r x ((buildRightPoly h rax).q k) ≠ 0) :
    (windCross (buildLeftPoly h lax) σL x = 0 ∧
        windCross (buildRightPoly h rax) σR x = 0 ∧ windCross P ρ x = 0) ∨
      (windCross (buildLeftPoly h lax) σL x = s ∧
        windCross (buildRightPoly h rax) σR x = 0 ∧ windCross P ρ x = s) ∨
      (windCross (buildLeftPoly h lax) σL x = 0 ∧
        windCross (buildRightPoly h rax) σR x = s ∧ windCross P ρ x = s) := by
  -- The three winding facts: package on L, package on R, unconditional bound on P.
  have hsplit := windCross_split_common h lax rax σL σR hL hR x
  have hLval := hValL.values σL x hoffL hvertL
  have hRval := hValR.values σR x hoffR hvertR
  have hPb := windCross_mem_final (P := P) (ρ := ρ) (x := x) hoffP hvertP
  have hsu : s = 1 ∨ s = -1 := hValL.1
  -- Everything is integer arithmetic from here.  `omega` resolves all cases, using that the
  -- both-interior state L = R = s would force P = 2s, excluded by the {0,1,-1} bound.
  rcases hLval with hL0 | hLs <;> rcases hRval with hR0 | hRs <;>
    rcases hPb with hP0 | hP1 | hPm1 <;> rcases hsu with hs1 | hsm1 <;> omega

/-- **The parent inherits the package value** (the headline consequence of the split).  Under the
same hypotheses, the parent winding is in `{0, s}` — i.e. `WindValuesWithSign` propagates from the
two sub-polygons to the parent at this point.  Immediate from `windValues_split_offAll`. -/
theorem windValues_parent_of_split {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) {x : Pt} {s : ℤ}
    (hValL : WindValuesWithSign (buildLeftPoly h lax) s)
    (hValR : WindValuesWithSign (buildRightPoly h rax) s)
    (hoffP : ¬ OnBoundary P x) (hvertP : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (hoffL : ¬ OnBoundary (buildLeftPoly h lax) x)
    (hvertL : ∀ k, side σL.r x ((buildLeftPoly h lax).q k) ≠ 0)
    (hoffR : ¬ OnBoundary (buildRightPoly h rax) x)
    (hvertR : ∀ k, side σR.r x ((buildRightPoly h rax).q k) ≠ 0) :
    windCross P ρ x = 0 ∨ windCross P ρ x = s := by
  rcases windValues_split_offAll h lax rax σL σR hL hR hValL hValR
      hoffP hvertP hoffL hvertL hoffR hvertR with
    ⟨_, _, hP⟩ | ⟨_, _, hP⟩ | ⟨_, _, hP⟩
  · exact Or.inl hP
  · exact Or.inr hP
  · exact Or.inr hP

/-! ## Brick 4 — interior ear-triangle points get value `s`

A point interior to the ear triangle has ODD crossing number against the right ear-deleted polygon
is NOT what we use here; instead the package on the LEFT triangle gives the value at left-interior
points.  The design's brick is: under the package on the left ear `L`, a left-interior point (an
off-boundary point whose LEFT crossing is odd) has `windCross_L = s`; combined with the split this
forces `windCross_P = s` (parent-interior) and `windCross_R = 0` (right-exterior). -/

/-- **Ear-interior points get value `s` (right values ⟹ interior value).**  Under the package on
both sub-polygons, at a point off all three boundaries whose LEFT (ear-triangle) crossing number is
ODD — i.e. genuinely interior to the ear triangle — the left winding is `s`
(`wind_eq_sign_of_odd`), and therefore by the split distribution the parent winding is `s` (the
point is inside the parent) and the right ear-deleted winding is `0` (the point is outside the
ear-deleted polygon).  This is the value-producing brick the bound alone cannot synthesize. -/
theorem earInterior_values_of_rightValues {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) {x : Pt} {s : ℤ}
    (hValL : WindValuesWithSign (buildLeftPoly h lax) s)
    (hValR : WindValuesWithSign (buildRightPoly h rax) s)
    (hoffP : ¬ OnBoundary P x) (hvertP : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (hoffL : ¬ OnBoundary (buildLeftPoly h lax) x)
    (hvertL : ∀ k, side σL.r x ((buildLeftPoly h lax).q k) ≠ 0)
    (hoffR : ¬ OnBoundary (buildRightPoly h rax) x)
    (hvertR : ∀ k, side σR.r x ((buildRightPoly h rax).q k) ≠ 0)
    (hLodd : Odd (CrossingNumber' (buildLeftPoly h lax) σL x)) :
    windCross (buildLeftPoly h lax) σL x = s ∧
      windCross (buildRightPoly h rax) σR x = 0 ∧
      windCross P ρ x = s := by
  -- Left-interior ⟹ left winding = s.
  have hLs : windCross (buildLeftPoly h lax) σL x = s :=
    wind_eq_sign_of_odd hValL σL hoffL hvertL hLodd
  -- Feed into the split distribution; the L = s branch is the only consistent one.
  rcases windValues_split_offAll h lax rax σL σR hL hR hValL hValR
      hoffP hvertP hoffL hvertL hoffR hvertR with
    ⟨hL0, _, _⟩ | ⟨_, hR0, hP⟩ | ⟨hL0', _, _⟩
  · -- L = 0 contradicts L = s (s ≠ 0).
    rcases hValL.1 with h1 | h1 <;> · rw [hLs] at hL0; omega
  · exact ⟨hLs, hR0, hP⟩
  · -- L = 0 contradicts L = s.
    rcases hValL.1 with h1 | h1 <;> · rw [hLs] at hL0'; omega

/-- **The ear-deleted exterior, from the package + ear-interior point** (Brick 4 ⟹ exterior).
Combining `earInterior_values_of_rightValues` with the signed exterior route: at an ear-interior
point under the package, the ear-deleted polygon `R` does not contain the point.  This is the
`earDeletedExterior` conclusion derived purely from the value package — no half-plane anchor. -/
theorem earDeletedExterior_of_package_interior {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) {x : Pt} {s : ℤ}
    (hValL : WindValuesWithSign (buildLeftPoly h lax) s)
    (hValR : WindValuesWithSign (buildRightPoly h rax) s)
    (hoffP : ¬ OnBoundary P x) (hvertP : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (hoffL : ¬ OnBoundary (buildLeftPoly h lax) x)
    (hvertL : ∀ k, side σL.r x ((buildLeftPoly h lax).q k) ≠ 0)
    (hoffR : ¬ OnBoundary (buildRightPoly h rax) x)
    (hvertR : ∀ k, side σR.r x ((buildRightPoly h rax).q k) ≠ 0)
    (hLodd : Odd (CrossingNumber' (buildLeftPoly h lax) σL x)) :
    ¬ ClosedRegion' (buildRightPoly h rax) σR x := by
  obtain ⟨hLs, _hR0, hPs⟩ :=
    earInterior_values_of_rightValues h lax rax σL σR hL hR hValL hValR
      hoffP hvertP hoffL hvertL hoffR hvertR hLodd
  exact earDeletedExterior_winding_route_sign h lax rax σL σR hL hR hoffR hLs hPs

end

end ProofsInTheBook.ZinanCh36InteriorValue

/-! ## Axiom audit (clean-3 expected: `propext`, `Classical.choice`, `Quot.sound`) -/

#print axioms ProofsInTheBook.ZinanCh36InteriorValue.wind_eq_sign_of_odd
#print axioms ProofsInTheBook.ZinanCh36InteriorValue.earDeletedExterior_winding_route_sign
#print axioms ProofsInTheBook.ZinanCh36InteriorValue.windValues_split_offAll
#print axioms ProofsInTheBook.ZinanCh36InteriorValue.windValues_parent_of_split
#print axioms ProofsInTheBook.ZinanCh36InteriorValue.earInterior_values_of_rightValues
#print axioms ProofsInTheBook.ZinanCh36InteriorValue.earDeletedExterior_of_package_interior
