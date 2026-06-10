(pbook2 wave-7, 2026-06-10, via tab paste — FULL design for the Ch36 sign-sync master bricks)

CORRECTION to wave-6: "declared tree sign" alone is unsound; needs the SIBLING SIGN SYNCHRONIZATION
lemma per split. Mechanism is LOCAL (no shoelace): the shared diagonal is traversed oppositely by
the two children; IsDiagonal' puts the diagonal segment in ClosedRegion' P so the parent winding at
diagMid is ≠ 0 (odd-crossing bridge); two-sided tube points z± = diagMid ± ε·perp give child jumps
L₊≠L₋, R₊≠R₋ with values in {0,sL}/{0,sR}, split identities L+R=P at both, P₊=P₋≠0 (parent local
constancy) ⟹ sL = sR by pure omega (signs_eq_from_split_local).

MASTER PRIMITIVE is RAY-INDEXED and GUARD-FREE (no ∀ρ, no hvert — local constancy covers vertex-ray
points):
  RayWindValuesWithSign P ρ s := (s = ±1) ∧ ∀ x, ¬OnBoundary P x → windCross P ρ x ∈ {0, s}
  RayOrientedWindData P ρ := ⟨s, hs, values⟩ (Prop structure)
Bridge to the landed guard-ful WindValuesWithSign only where needed.

NON-CIRCULARITY: do NOT assume full EarCutData (it contains the exterior field being produced).
  EarValueSplitData P ρ i := {hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i), lax, rax,
    σL, σR, hLr : σL.r = ρ.r, hRr}
Induction: rayOrientedWindData_all_of_earValueSplits (ear, Esplit : 4 ≤ m → EarValueSplitData) →
∀ P ρ, RayOrientedWindData P ρ. Strong induction on m; base m=3 = triangle_rayWindValuesWithSign
(triSign = if 0 < orient q0 q1 q2 then 1 else -1, sign DECLARED by the theorem, flips under
reversal — correct); step: IH on right + triangle base on left + split_child_signs_eq + the
perturb-aware rayWindValues_split.

ORDERED BRICKS (W=worker, M=master):
1 W 30-50: RayWindValuesWithSign + RayOrientedWindData (+ bridge of_raywise).
2 M/W 250-450: triSign + triangle_rayWindValuesWithSign (reuse Fin 3 enumeration, keep eSign not count).
3 W 70-110: windCross_ne_of_symmDiff_singleton (after windCross_eq_sum_crossing_eSign): crossing
  sets differing by exactly {e} ⟹ signed sums differ (eSign e = ±1).
4 W/M 100-180: diagMid (midpoint), diagMid_off_parent_boundary, diagMid_parent_wind_ne_zero
  (IsDiagonal' segment-in-ClosedRegion' + odd-crossing + windCross_ne_zero_of_odd_crossing).
5 M 250-400: exists_two_sided_diag_points (ε-tube: z± off ALL THREE boundaries, parent winding
  z± = z by local constancy) + child_windCross_diff_across_diag (signed single-diagonal jump via 3;
  crossing sets at z₊/z₋ differ by exactly the diagonal edge — PolygonLocalJump has count-shaped
  infra, add the signed-sum variant).
6 W 40-70: signs_eq_from_split_local — pure omega: L±∈{0,sL}, R±∈{0,sR}, jumps, splits, P₊=P₋≠0 ⟹ sL=sR.
7 M 80-140: split_child_signs_eq (assembly of 4+5+6).
8 W 80-120: rayWindValues_split_offAll (ray-indexed, x off all three; values+final bound+split identity).
9 W/M 80-140: subBoundary_of_parentOff_is_diag (child boundary edge = parent edge or diagonal;
  parent-off + child-on ⟹ x ∈ openSegment (P.q i) (P.q j); endpoints are parent vertices).
10 M 180-280: exists_near_diag_point_off_all (punctured normal segment x + ε·perpVec avoids all
  finitely many edges; finite segment separation, NO interior connectivity).
11 W 50-80: rayWindValues_split (perturb wrapper: by_cases both-off → 8; else 9 → on-diagonal →
  windCross_locally_constant_off_boundary (PolygonWindingExterior, LANDED signed local constancy) +
  10 → transfer).
12 M 180-260: rayOrientedWindData_all_of_earValueSplits (strong induction; 2 base, 7 sync, 11 splice
  via rayOrientedWindData_of_split 50-90).
13 W 150-280: consumer wiring — earInterior_values_unconditional, EarCutData_of_interiorValues,
  polygonGeomResidue_of_interiorValues → artGallery_strict_mod_M. (earDeletedExterior_winding_route_sign
  ALREADY LANDED in ZinanCh36InteriorValue.)

AUDITS: no half-plane (reflex safe); strict simplicity excludes degenerate ears; signs never
hard-coded (everything through triSign + sync; the exterior conclusion windCross_R = 0 is
sign-invariant); NO vertex-generic guards on value theorems (perturb + local constancy instead).
