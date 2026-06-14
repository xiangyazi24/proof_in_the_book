# DOCTRINE — Ch13 Cauchy rigidity: wire the real arm lemma in

## Main goal (one sentence)
Make Chapter 13's Cauchy-rigidity chain genuinely rest on the PROVEN spherical arm lemma
(`ZinanFFCT111.spherical_arm_mono_final_ch13`), eliminating the §3.3 gap where
`CauchyArmOpeningObstruction.arm_conclusion` POSITS the arm lemma's conclusion as a structure field
instead of deriving it — and push Ch13 toward unconditional.

## Audit finding that motivates this
`chapter13 : CauchyRigidityCertificate → False` is the faithful COMBINATORIAL skeleton (sign-count +
Euler double-count), but the geometric arm lemma is posited: `CauchyArmOpeningObstruction` has a field
`arm_conclusion : chord < newChord ∨ (∀ i, angles i = newAngles i)`, and `.contradiction` is a 3-line
trivial unpacking. Chapter13.lean does not even import FFCT111. `CauchyRigidityCertificate` is mentioned
ONLY in Chapter13.lean — never constructed from geometry.

## Avenues (ranked)

### (a) PRIMARY — strict arm lemma → genuine spherical-arm obstruction
Prove the STRICT arm lemma and use it to refute a genuine obstruction that carries real spherical-arm data.
- (a1) `endpt_openTail_interior_mono_strict`: `0 < θ` (strict interior opening, oriented sign STRICT
  negative from strict convexity) ⟹ `endpt A < endpt (openTail A K (-θ))`. Built from strict variants of
  `openedAngle_ge_of_oriented_neg` (θ>0 ⟹ sphAngle strictly larger) and `reach_base_endpoint_mono`
  (sphAngle strictly larger ⟹ sDist strictly larger; spherical law of cosines, cos strict-antitone on (0,π)).
- (a2) `spherical_arm_mono_strict : SphericalArmMonotoneStrict` — joints A ≤ B (equal sides, both strict
  convex), SOME joint strict ⟹ `sDist(A 0)(A last) < sDist(B 0)(B last)`. Thread (a1) through the
  per-joint opening induction of FFCT111's monotone proof: the strictly-opened joint contributes `<`,
  the rest `≤`.
- (a3) From (a2): the dichotomy `chord < newChord ∨ all joints equal` is a THEOREM, not a field. Restate
  `CauchyArmOpeningObstruction`/`ClosingObstruction` to carry the two spherical arms (A,B with equal sides)
  instead of abstract `angles : Fin n → ℝ`; `.contradiction` then uses (a2) + fixed_chord.
- (a4) Rewire `CauchyArmVertex` so `zero/two_sign_changes_obstruction` are derived (the 0/2-sign-change
  combinatorial→arm reduction), shrinking the certificate to genuine geometric+sign content.
- Terminal SUCCESS: a clean-3 theorem deriving the fixed-chord contradiction from
  `spherical_arm_mono_final_ch13` with NO posited arm conclusion; FFCT111 actually used in the Ch13 chain.
- Terminal FAILURE: a concrete proof that the strict arm lemma is false (it is NOT — it's standard) — so
  failure here can only be "this specific Lean threading blocked at tactic X", which is then a new vector.

### (b) Equality-case route (if (a2) threading is awkward)
Instead of strict, prove the EQUALITY characterization directly: joints A ≤ B, equal sides, `sDist A = sDist B`
⟹ `∀ i, jointAngle A i = jointAngle B i`. This IS the dichotomy's second branch and suffices for `arm_conclusion`.
Same base lemma (a1) in equality form (`endpt A = endpt(openTail) ⟹ θ = 0`).

### (c) Polytope-level assembly (the large layer D)
Define convex polytope vertex spherical links, dihedral-angle sign data, and construct
`CauchyRigidityCertificate` from two combinatorially-equivalent non-congruent convex polytopes with
congruent faces. Produces genuine `CauchyArmVertex` data via the link arms. LARGE. Pursue after (a).

### (d) Fallback — faithfulness-only improvement
If full realization blocks, at minimum replace the posited `arm_conclusion` field with the real arm
lemma applied to an explicitly-carried spherical arm in the obstruction, and document the exact remaining
(c) gap. Strictly better faithfulness than the current posited stub.

## Fallbacks if all blocked
Dispatch the strict-arm-lemma threading to ChatGPT 5.5 Pro (math audit) / a fresh Opus subagent (Lean grind).
The arm lemma core (FFCT111) is done; (a) is bounded geometric work, not open research.

## Working location
New file `ProofsInTheBook/ZinanFFCT112.lean` (one writer = me). Build LOCAL `command lake`. Commit per
milestone on branch zinan-overnight. clean-3 acceptance via `#print axioms`.
