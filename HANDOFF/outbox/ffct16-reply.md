# FFCT16 reply — `GnomonicNoflatJoint` falsified (kernel-anchored, clean-3)

## Status: DONE

New file `ProofsInTheBook/ZinanFFCT16.lean` created (only this file; nothing else edited; no git commit).
It proves unconditionally:

```
theorem gnomonicNoflatJoint_false : ¬ ProofsInTheBook.ZinanFFCT8.GnomonicNoflatJoint
```

## Axioms output

```
'ProofsInTheBook.ZinanFFCT16.gnomonicNoflatJoint_false' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Clean-3. Zero `error:` on `lake env lean ProofsInTheBook/ZinanFFCT16.lean` (uisai2). No
`sorry`/`axiom`/`admit`/`native_decide` (the only textual match is the doc-comment prose on line 33).

## The counterexample (exactly as specified, all rational, verified)

- `n = 2`, interior `v = 1`, normal `h = e₃ = (0,0,1)`.
- Fold-back arm `A = [(3/5,0,4/5), (−3/5,0,4/5), (0,0,1)]` — three points on the great circle `y = 0`,
  fold-back at `A 1`. Weakly convex (every triple coplanar in `y = 0` ⇒ all supports `= 0`).
- Strict arm `B = [(0,0,1), (24/25,0,7/25), (12/13,3/13,−4/13)]`. All three non-incident supports
  `= +72/325 > 0` (cyclic, no reflection needed). Open hemisphere via the NORMALIZED raw normal
  `w = (612,75,316)` (raw inners `316, 676, 485 > 0`), normalized by `(‖w‖)⁻¹ • w` with positivity
  transport (`‖w‖ > 0` since `w 0 = 612 ≠ 0`).
- `SameSides`: side inners match (`7/25` and `4/5`); `sideLen = arccos ∘ sInner`, equal inners ⇒ equal
  side lengths (via `show … = arccos (sInner …)` then `rw` the two inner equalities).
- `JointLe`: `Fin (2−1) = Fin 1`, only joint at `i.val = 0`. Tangents at the fold vertex `A 1` are
  positive multiples (`tangentTo A1 A2 = (5/8) • tangentTo A1 A0`, both ∝ (4,0,3)), so
  `sphAngle A0 A1 A2 = 0` via `InnerProductGeometry.angle_eq_zero_iff`. Hence `jointAngle A 0 = 0 ≤
  jointAngle B 0` (the latter `≥ 0` by `sphAngle_nonneg`; B's joint never computed).
- Refuted conclusion: `gproj e₃ (A i)` scales `A i` (which has `y = 0`) by a positive scalar, so all
  three gnomonic images keep `y = 0`; thus `det3 (gproj …) (gproj …) (gproj …) = 0` by `det3_y0`,
  contradicting `0 < …`. (No need to compute `gproj` images, no `det3` multilinearity — just
  `gproj`, `PiLp.smul_apply`, and `(A i) 1 = 0`.)

## Deviations / implementation notes (all sound, no shortcuts)

- Used the FFCT2/FFCT10 explicit-`S2` idiom (`!₂[…]` literals, `EuclideanSpace.norm_eq +
  Fin.sum_univ_three` norm proofs, `innerE3`/`det3E3`/`inner_eq_coord`).
- The `B` det3 supports over `Fin 3` are evaluated with a local `bArm_eval` (cf. FFCT10 `cxF_eval`) +
  three `show ((⟨k,_⟩:Fin 3)+1) = ⟨k+1 mod,_⟩ from rfl` successor-normalization simp lemmas, then
  `norm_num [det3E3]`. `strict_nonincident` discharges the incident `j` cases by `exfalso; … decide`.
- Vector equality (`tangent_parallel`) via `SphericalRotation.ext_coord` (not `funext`, since E3 is a
  `PiLp`), then `Matrix.cons_val*` + `norm_num`.

## Meaning (playbook §3.3)

`GnomonicNoflatJoint` is an over-strong predicate: it silently assumes the arm cannot fold back on
itself, but a weakly convex great-circle fold-back satisfies every premise (incl. `JointLe` with a
strictly convex equal-sided `B`) while its interior gnomonic orientation is exactly `0`. This is the
third same-family false residue in the Ch13 supporting-line route (cf. FFCT10
`planarWeakNoflatStrictEdge_false`, FFCT15 backward-case). The genuinely missing input remains the
monotone polar-angle / total-turning `< 2π` ordering, which a local angle datum cannot supply.

## Verify command

```
scp -q ProofsInTheBook/ZinanFFCT16.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ && \
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && \
  lake env lean ProofsInTheBook/ZinanFFCT16.lean 2>&1 | tail'
```
