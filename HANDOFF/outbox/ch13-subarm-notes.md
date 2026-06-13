# Ch13 DIRECT subarm-route — design notes (Opus autonomous session)

Goal: prove `ProperCrossPieceNoCollisionAtSup` (FFCT100) → unconditional Ch13 headline
via `spherical_arm_mono_ch13_of_properNoCollision` (already in FFCT100).
This DROPS `hcollision` (the v11 residue `CrossPieceCollisionEndpointAtSup`).

## Reduction map (already in repo)
- FFCT100 `collisionEndpoint_of_properNoCollision : ProperCrossPieceNoCollisionAtSup → CrossPieceCollisionEndpointAtSup`
  (full-closure r=0∧s=n handled there: endpt openedWBS = sDist self = 0 ≤ endpt B).
- FFCT100 `spherical_arm_mono_ch13_of_properNoCollision : ProperCrossPieceNoCollisionAtSup → SphericalArmMonotone`.
So my ONLY target is the theorem `ProperCrossPieceNoCollisionAtSup`.

## Statement to prove
Proper case: strict A,B, SameSides, JointLe, jointAngle A k < jointAngle B k,
SupportStuckWBS, r+2≤s, r≤K<s (K=openingAxis k), (0<r ∨ s<n)
⟹ openedWBS A B k ⟨r⟩ ≠ openedWBS A B k ⟨s⟩.
By contradiction: assume `heq` (collision). δ := monitoredSupWBS A B k.

## KILLED routes (numerically refuted — do NOT retry)
- **Route B (cap / `endpt_openTail_interior_mono_neg`)**: needs cap δ+sphAngle(A_r,A_K,A_s)≤π.
  NUMERICS: sphAngle(A_r,A_K,A_s) > sphAngle(A_0,A_K,A_last) ALWAYS (155497/155497).
  The subarm base angle is the LARGER one (cyclic polygon: A_0,A_last are closing-edge-adjacent,
  subtend the SMALL angle; interior r,s subtend the LARGE one). So the subarm cap is FALSE in
  general → the collision is a genuine OVER-opening past the cap. Cap-based monotonicity is dead.
- Turning-bound route (FFCT103-110): circular, abandoned (prior sessions).

## TRUE route (numerically verified): subarm IH + weak-target via LIMIT
- A_sub := intervalArm A r m (m=s-r, 2≤m, and proper ⟹ m≤n-1<n). STRICT (strictConvex_intervalArm_of_wrap).
- O := openTail A_sub K' (-δ), K'=K-r (= openingAxis of subarm joint k', k'.val=k.val-r).
  Lemma 2: O t = openedWBS (r+t)  [funext, case r+t≤K].  So endpt O = sDist(openedWBS r, openedWBS s) = 0 by heq.
- endpt A_sub = sDist(A_r,A_s) > 0 (A_r≠A_s via strictConvex_noNonadjacentRepeat, r+2≤s nonadjacent).
- NEED: endpt A_sub ≤ endpt O  (=0)  ⟹ contradiction.
  This is WEAK-TARGET monotonicity (strict source A_sub, target O is the MORE-open one but only WEAK).
  MainPlusNR has STRICT target only → does NOT apply directly.

## Why weak-target / why limit
- At the collision, O is DEGENERATE: O(0)=O(m) ⟹ closing edge zero-length ⟹ O is NOT WeakConvexSphArm.
  So even an abstract weak-target lemma can't be applied to O_δ directly.
- NUMERICS: weak-target monotonicity (strict A, weak B, SameSides, JointLe ⟹ endpt A≤endpt B) holds
  (13037/13037, 0 violations). And: a weakly-convex opened arm NEVER has a nonadjacent coincidence
  (549885/549885). And can't even construct weak-convex closed polygon w/ nonadjacent coincidence (118152/0).
- ⟹ LIMIT-FROM-BELOW: for t<δ (t admissible), O_t = openTail A_sub K' (-t) is WEAKLY convex
  (= intervalArm of opened_t which is weak convex since t admissible: supports≥0). For t<δ near δ,
  endpt(O_t)>0 (non-degenerate). weak-target(A_sub,O_t): endpt A_sub ≤ endpt O_t. Continuity:
  endpt O_t = sDist(A_r, rotS2(A_K,-t)(A_s)) → sDist(A_r,rotS2(A_K,-δ)(A_s)) = endpt O = 0.
  le_of_tendsto on 𝓝[<]δ ⟹ endpt A_sub ≤ 0. Contradiction.

## Remaining residue(s) to grind
1. **Weak-target monotonicity** (per weakly-convex O_t): strict A_sub, weak O_t, SameSides, JointLe,
   ihdim ⟹ endpt A_sub ≤ endpt O_t. Prove by closure of MainPlusNR (strict-target).
   Sub-approach: O_t = opening of strict A_sub; OR abstract closure via strict approx (joints+ε keeps sides).
2. **Admissible accumulates at δ from below**: need sequence t_n<δ, t_n admissible, t_n→δ.
   Checking numerically whether admissible set is an interval [0,δ] (opened_t weak-convex ∀t∈[0,δ]).
   If interval, the sup gives the sequence cleanly.
3. δ=0 case: openedWBS=A, collision ⟹ A_r=A_s nonadjacent, direct contradiction (strictConvex_noNonadjacentRepeat).
4. r=K case (K'=0, not interior): O = rigid rotation of A_sub (axis index 0), endpt O = endpt A_sub by
   sDist_rotS2 isometry; collision ⟹ endpt A_sub=0 ⟹ A_K=A_s contradiction. (NO IH/limit needed.)

## Key repo lemmas
- endpt_openTail_interior (SZFinal:251), continuous_rot (SphRot:289), sDist_rotS2 (isometry),
  intervalArm_* (SZStepClose, FFCT52,74), strictConvex_intervalArm_of_wrap (FFCT52:493) needs IntervalWrapDataStrict,
  weakConvex_intervalArm_of_wrap (FFCT52:394) needs IntervalWrapData (wrap_short + wrap_support),
  monitoredSupWBS_mem / _mem_Icc / _lt_pi (FFCT45), MainPlusNR (FFCT74:61), mainPlusNR_all_v11 (FFCT86).
- NO "strict below sup" lemma exists (admissible interior strictness not banked) — use WEAK below sup instead.
