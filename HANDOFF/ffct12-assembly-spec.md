# FFCT12 — prove `PlanarWeakNoflatStrictEdgeCore` (Ch13 corrected planar residue)

**Target file: `ProofsInTheBook/ZinanFFCT12.lean` (NEW FILE — create it; do not touch any other file).**
Imports: `ProofsInTheBook.ZinanFFCT10` (which imports FFCT9/FFCT8).
Verify ONLY with `lake env lean ProofsInTheBook/ZinanFFCT12.lean` (deps are already built).
STRICT: NO `sorry`, NO `axiom`, NO `admit`, NO `native_decide`. If a step genuinely blocks,
STOP and report exactly what blocks in `HANDOFF/outbox/ffct12-reply.md`; do not fake or weaken.

## Goal

```lean
theorem planarWeakNoflatStrictEdgeCore_holds : PlanarWeakNoflatStrictEdgeCore
```

where `PlanarWeakNoflatStrictEdgeCore` is defined in `ZinanFFCT10` (read it first; also read
`ZinanFFCT9.lean` §0–§5 — all the machinery you need is there, plus the §2 kills in FFCT10).

## The complete proof design (verified by counterexample analysis; follow it)

Context: `f : Fin (n+1) → E3` in the affine plane `⟪h,·⟫ = 1`, with
`hinj : Function.Injective f`, `hplane`, `hweak` (every directed edge `(a, a+1)` weakly supports
every vertex), `hnoflat` (interior joints strict left turns), `hfirst` (no vertex on the backward
extension of edge `(0,1)`), `hlast` (no vertex on the forward extension of edge `(n-1, n)`).
Goal: `0 < det3 (f i) (f (i+1)) (f j)` for non-incident `j` (with the two carve-outs).

`h ≠ 0`: from `hplane` at any index (`⟪0, x⟫ = 0 ≠ 1`).

### Bridges (prove first; small)

B1. `det3_plane_eq` (FFCT9): `det3 a u w * ‖h‖^2 = det3 h (u-a) (w-a)` for `a,u,w` in the plane.
    So the goal is equivalent to `0 < det3 h (f (i+1) - f i) (f j - f i)` (apex `f i`), and
    likewise `0 < det3 h b ρ ↔ 0 < det3 (apex) (apex+b) (apex+ρ)`-style transports.
    Also note row identities provable by `simp only [det3]; ring`:
    `det3 a b c = det3 c a b = det3 b c a` (cyclic) and `det3 a b c = -det3 b a c` (swap).

B2. Antiparallel decomposition: for `b ≠ 0`, `ρ ≠ 0`,
    `theta b ρ = Real.pi → ∃ t : ℝ, 0 < t ∧ ρ = -t • b`.
    Proof: `theta = arccos (ncos b ρ)`; `Real.arccos_eq_pi` gives `ncos b ρ = -1`, i.e.
    `⟪b, ρ⟫ = -(‖b‖*‖ρ‖)`. Then `⟪b, -ρ⟫ = ‖b‖*‖-ρ‖` and Mathlib's
    `real_inner_eq_norm_mul_iff` (or `inner_eq_norm_mul_iff_real` — grep for the exact name)
    gives `‖-ρ‖ • b = ‖b‖ • (-ρ)`, hence `ρ = -(‖ρ‖/‖b‖) • b` with `t = ‖ρ‖/‖b‖ > 0`.

B3. Same decomposition from `ncos (ρ₁) (ρ₂) = -1` (for the `hcons` discharge): identical algebra.

### Forward case (`j ≥ i + 2`): apply `ZinanFFCT9.forward_strict_support` with

- normal `h`, base `b = f (i+1) - f i`, `N = j - (i+1)`,
- chain `ρs t = f (i+1+t) - f i` for `t ≤ N` (so `ρs 0 = b`, `ρs N = f j - f i`).
  (Define `ρs : ℕ → E3 := fun t => f ⟨min (i+1+t) n, …⟩ - f ⟨i, …⟩` or use a junk-padded
  function — only values `t ≤ N` matter; pick whatever makes index proofs easiest.)
- `hb0/hperp`: in-plane differences are ⊥ `h` (from `hplane`, `inner_sub_right`).
- `hb`/`hne`: nonzero by `hinj` (distinct indices).
- `hsupp t`: `0 ≤ det3 h b (ρs t) = ‖h‖² · det3 (f i) (f (i+1)) (f (i+1+t))` — by B1 + `hweak`
  (edge `(i, i+1)` at vertex `i+1+t`).
- `hturn t`: `0 ≤ det3 h (ρs t) (ρs (t+1))`. By B1 with apex `f i`:
  `det3 h (ρs t) (ρs (t+1)) = ‖h‖² · det3 (f i) (f a) (f (a+1))` with `a = i+1+t`; cyclic
  rotation `det3 (f i) (f a) (f (a+1)) = det3 (f a) (f (a+1)) (f i)` = `hweak` edge `(a, a+1)`
  at vertex `i`. ✓
- `hcons t`: `-1 < ncos (ρs t) (ρs (t+1))`. By contradiction: `ncos = -1` (use `ncos_mem` for
  `≥ -1`) gives, via B3, `f (a+1) - f i = -s • (f a - f i)`, `s > 0`, with `a = i+1+t`.
  Then `f i = (1/(1+s)) • f (a+1) + (s/(1+s)) • f a` (affine combination), so
  `det3 (f i) (f (i+1)) (f i) = 0` expands (multilinearity, FFCT10 `det3_add_right`/
  `det3_smul_right` after rewriting the THIRD argument; you may prefer to expand
  `det3 (f i) (f (i+1)) (f (a+1)) = -s · det3 (f i) (f (i+1)) (f a)` directly from
  `f (a+1) - f i = -s • (f a - f i)` and B1-style transport) — giving
  `da1 = -s · da` where `da = det3 (f i) (f (i+1)) (f a) ≥ 0`, `da1 = det3 (f i) (f (i+1)) (f (a+1)) ≥ 0`
  (both `hweak`). Hence `da = da1 = 0`: `f a` and `f (a+1)` lie on the line through
  `f i, f (i+1)`. Write `f a - f i = c • b` (from `da = 0`… see Collinearity note below) and
  `f (a+1) - f i = c' • b`; antiparallelism gives `c' = -s·c`, and `f a ≠ f i`, `f a ≠ f (i+1)`
  (`hinj`) give `c ∉ {0, 1}`. Cases:
    - `c < 0`: `f a` on the backward extension of edge `(i, i+1)`:
      if `i ≥ 1` → `ZinanFFCT10.no_backward_collinear_kill` with predecessor edge
      (`hsupp := hweak` edge `(i-1, i)` at vertex `a`, `hjoint := hnoflat` at `v = i`);
      if `i = 0` → contradiction with `hfirst` directly.
    - `c > 1`: `f a` on the forward extension past `f (i+1)`:
      `f a = f (i+1) + (c-1) • b`. Since `a ≤ n` and `a ≥ i+2`, we have `i+2 ≤ n`, so the
      successor edge `(i+1, i+2)` exists →
      `ZinanFFCT10.no_forward_collinear_kill` (`hsupp := hweak` edge `(i+1, i+2)` at vertex `a`,
      `hjoint := hnoflat` at `v = i+1`). (No `hlast` needed here: `i+1 ≤ n-1` always in this
      branch.)
    - `0 < c < 1`: then `c' = -s·c < 0`, so `f (a+1)` is on the backward extension — apply the
      `c < 0` argument to `a+1` instead. (One of `f a`, `f (a+1)` always has negative parameter
      when they antiparallel-straddle; handle by `rcases lt_trichotomy c 0`.)
  Collinearity note: from `da = 0` and `nsin`/`det3h_sq` you can get `f a - f i ∈ span {b}`:
  cleanest is FFCT9's `det3h_sq` (`det3 h b u = 0` + Cauchy-Schwarz equality ⟹ `u ∥ b`); or use
  Mathlib `inner_mul_le_norm_mul_norm` equality case via
  `(det3 h b u)² = ‖h‖²(‖b‖²‖u‖² - ⟪b,u⟫²)` (FFCT9 `det3h_sq` with `u,b ⊥ h`):
  `det3 h b u = 0 → ⟪b,u⟫² = ‖b‖²‖u‖²` → `abs_real_inner_eq_norm_iff…`/
  `real_inner_eq_norm_mul_iff` (sign split) → `u = c • b`.
- `hnoflat` (first joint strict): `0 < det3 h b (ρs 1) = ‖h‖² · det3 (f i) (f (i+1)) (f (i+2))`,
  which is `hnoflat` at `v = i+1` (cyclic rotation; `i+1 ≥ 1` ✓, `i+2 ≤ n` since `j ≤ n`,
  `j ≥ i+2`). ✓
- `hnotanti` (`theta b (ρs N) ≠ π`): by contradiction via B2: `f j - f i = -t • b`, `t > 0`,
  i.e. `f j = f i - t • (f (i+1) - f i)`. Cases:
    - `i ≥ 1`: `no_backward_collinear_kill` (predecessor edge + `hnoflat` at `v = i`).
    - `i = 0`: exactly `hfirst` applied to `j`. ✓
- Conclusion `0 < det3 h b (ρs N)` transports back through B1 (`‖h‖² > 0`).

### Backward case (`j ≤ i - 1`): apply `forward_strict_support` with normal `-h` and the
reversed chain from apex `f (i+1)`:

- base `b' = f i - f (i+1)`, `N' = (i+1) - j`, chain `σs t = f (i+1-t) - f (i+1)`
  (`σs 0 = 0`?? NO — careful: `σs 0` must equal `b'`; set `σs t = f (i - t) - f (i+1)` for the
  chain visiting `i, i-1, …, j`, so `σs 0 = b'`, `σs (i - j) = f j - f (i+1)`, `N' = i - j`).
- `hperp`: differences ⊥ `h` hence ⊥ `-h`. `(-h) ≠ 0` ✓.
- KEY sign identities (all by `simp only [det3]; ring` row algebra + B1):
  - `hsupp`: `det3 (-h) b' (σs t) = -det3 h b' (σs t) = -‖h‖²·det3 (f (i+1)) (f i) (f (i-t))
    = ‖h‖²·det3 (f i) (f (i+1)) (f (i-t)) ≥ 0` — `hweak` edge `(i, i+1)` at vertex `i-t`. ✓
  - `hturn`: `det3 (-h) (σs t) (σs (t+1)) = ‖h‖²·det3 (f (a-1)) (f a) (f (i+1)) ≥ 0` with
    `a = i - t` — `hweak` edge `(a-1, a)` at vertex `i+1` (after one row swap + one cyclic
    rotation; check the exact sign chain CAREFULLY with `det3` `ring` lemmas first). Needs
    `a - 1 ≥ 0` i.e. `t ≤ N'-1` ✓ (`a-1 ≥ j ≥ 0`).
  - first-joint: `0 < det3 (-h) b' (σs 1) = ‖h‖²·det3 (f (i-1)) (f i) (f (i+1))` — `hnoflat` at
    `v = i` (`i ≥ 1` holds since `j ≤ i-1` requires `i ≥ 1`). ✓
- `hcons`: same antiparallel analysis as forward, mirrored: `ncos (σs t) (σs (t+1)) = -1` puts
  `f (i+1)` strictly inside the segment `(f a, f (a-1))`, forcing both onto the line through
  `f i, f (i+1)`; parameter trichotomy again; the `> 1` ("beyond `f (i+1)`") branch uses the
  successor edge `(i+1, i+2)` when `i+1 ≤ n-1`, and `hlast` when `i+1 = n`; the `< 0` branch
  uses `no_backward_collinear_kill` at the predecessor edge `(i-1, i)` (exists: `i ≥ 1`); for
  `i = 1`… note predecessor edge `(i-1, i) = (0, 1)` exists for all `i ≥ 1`. ✓
- `hnotanti`: `theta b' (σs N') = π` ⟹ `f j = f (i+1) + t • (f (i+1) - f i)`, `t > 0` (beyond
  the far end). Cases: `i+1 ≤ n-1` → `no_forward_collinear_kill` (successor edge `(i+1, i+2)`,
  `hnoflat` at `v = i+1`); `i+1 = n` (i.e. `i = n-1`) → exactly `hlast` applied to `j`. ✓
- Conclusion: `0 < det3 (-h) b' (σs N') = ‖h‖²·det3 (f i) (f (i+1)) (f j)` ✓ (same sign chain
  as `hsupp`).

### Remaining bookkeeping

- `j = i + 1`, `j = i` excluded by hypothesis; `j ≥ i+2` forward; `j ≤ i-1` backward — `omega`.
- The carve-outs `¬(i = 0 ∧ j = n)`, `¬(i = n-1 ∧ j = 0)` are NOT needed by this proof
  (hfirst/hlast subsume them) — fine, just don't use them.
- Indexing: prefer working with `i j : ℕ` and explicit `Fin.mk`; all bound proofs by `omega`.
  When `Fin (n+1)` subtraction appears, rewrite via explicit `⟨i - t, by omega⟩` naturals.
- `Function.Injective f` usage: `f ⟨a,_⟩ = f ⟨b,_⟩ → (⟨a,_⟩ : Fin (n+1)) = ⟨b,_⟩ → a = b`
  (`Fin.mk.injEq`), contradiction by `omega`.

### Output

End the file with the headline:

```lean
theorem planarWeakNoflatStrictEdgeCore_holds : PlanarWeakNoflatStrictEdgeCore := by
  ...
```

and `#print axioms ProofsInTheBook.ZinanFFCT12.planarWeakNoflatStrictEdgeCore_holds`
(must be exactly `[propext, Classical.choice, Quot.sound]`).

Write progress + any blocker to `HANDOFF/outbox/ffct12-reply.md`. Kill any background
processes you start before exiting.
