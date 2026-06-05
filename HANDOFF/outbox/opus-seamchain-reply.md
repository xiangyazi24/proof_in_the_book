# Opus — PlanarMapSeamChain.lean (Ch35 F-count seam-chain core) — reply

## Status

- **Step 1 (the ABSTRACT seam-chain theorem): COMPLETE, unconditional, axioms-clean.**
- **Step 2 (specialization to `faceCorr₂` → `numCyclesCutPhi2_holds`): BLOCKED by a
  genuine mathematical mismatch — NOT carried out, and deliberately not faked.**

`ProofsInTheBook/PlanarMapSeamChain.lean` — 830 lines, `0` sorry / `0` axiom /
`0` admit / `0` native_decide. Verified with `lake env lean` (exit 0) and a full
`lake build ProofsInTheBook.PlanarMapSeamChain` (8443 jobs, "Build completed
successfully"). `#print axioms` on the headline theorem:

```
numCycles_mul_seamChain_delta depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What is proven (Step 1 — the full abstract theorem, the deepest open core)

Headline (FAITHFUL to the design, unconditional):

```
theorem SeamChainData.numCycles_mul_seamChain_delta (S : SeamChainData X) :
    ((numCycles (S.p * cycleOfList (seamList S.γ S.u S.v)) : ℤ) - (numCycles S.p : ℤ))
      = -((S.k : ℤ) - 1)
```

i.e. multiplying `p` by one cap chain in normal form
`L = [γ₀,u₀,v₀, …, γ_{k−1},u_{k−1},v_{k−1}]` (hypotheses: `L.Nodup`, `p γᵢ = γᵢ`,
`p uᵢ = vᵢ`) drops `numCycles` by exactly `k−1`. Every layer of the design is built
and machine-checked:

- **Layer A** — integer swap dichotomy `numCycles_mul_swap_delta` (`±1` by `SameCycle`).
- **Layer B** — the prefix walk `formPerm_take_succ` (one consecutive swap per step) and
  the signed walk delta `numCycles_take_delta` (`Δ = ∑ stepSign`), by induction over the
  prefix; `stepSign` is the per-step pivot `SameCycle Pⱼ L[j] L[j+1]`.
- **Layer C** — the partial-product action: `mul_take_apply_getElem`
  (`(p·formPerm(take m))(L[r]) = p(L[(r+1)%m])`) and `mul_take_apply_of_not_mem`, plus
  the invariant-set confinement `not_sameCycle_of_invariant`.
- **Layer D** — `seamList`/`seamFn` indexing (`seamList_getElem_{gamma,u,v}`), the four
  block-action lemmas `P_apply_{gamma_inner,gamma_last,v_inner,v_last,u_last}`, the two
  active sets `ActiveGU`/`ActiveVG` with forward invariance, the nodup distinctness
  exclusions, and the THREE step classifications — exactly the design's active seam-cycle
  invariant:
  - `seam_gamma_u_merge` : `¬ SameCycle (P (3i+1)) (γ i) (u i)`  (merge, −1)
  - `seam_u_v_split`     : `SameCycle (P (3i+2)) (u i) (v i)`   (split, +1; explicit
     forward path `uᵢ→γ₀→v₀→…→γᵢ→vᵢ` via `sameCycle_gamma0_gamma_at_split`)
  - `seam_v_gamma_merge` : `¬ SameCycle (P (3i+3)) (v i) (γ_{i+1})`  (merge, −1)
  - per-step values `stepSign_block_{A,B,C}`, the telescoping partial sum
    `seam_partial_sum` (`∑_{j<3n+2} = −n` by induction), and the final assembly.

This is the genuine, reusable, unconditional permutation mathematics the chapter had
never carried out (the design's "one irreducible topological core"). It is the part that
deserved an Opus proof and it is done.

## Why Step 2 is blocked (honest, source-verified — playbook §3.3)

The design (CH35_FCHAIN_DESIGN.md §8–§10) specializes by asserting:
`faceCorr₂ = plusCorr * minusCorr`, two **disjoint** cap chains, each equal to
`cycleOfList (seamList capⱼ movableInⱼ movableOutⱼ)` in clean normal form with
`phiLift (movableInᵢ) = movableOutᵢ`.

**Those specialization premises are FALSE for the actual `faceCorr₂`, by the
repository's own kernel reconnaissance** (documented verbatim in
`PlanarMapCutCap2F.lean`, lines 31–53):

- "the naive face-survival bijection of the design is **false as stated**; old faces do
  not survive intact."
- "The `+`-caps do **not** form a pure orbit in general" → "no unconditional
  `+`-cap `k`-cycle lemma to peel off." The cap action diverts into **bank darts**
  (`prevIdx`/`nextIdx`, see `cutCapPhi2_capP_action`), so there is no movable-pair
  `phiLift uᵢ = vᵢ` seam normal form.
- "`faceCorr₂` … is a **single long cycle plus the `+`-cap cycle** … *not* a product of
  `2k−2` disjoint transpositions" → it is **not** two disjoint seam chains.
- `PlanarMapCutCap2F.lean` line 49: "`φ'₂` admits **no projection semiconjugacy**" — the
  per-step `SameCycle` dichotomy "does **not** reduce to a clean `φ`-fact."

Grep confirms the gap is structural, not a wiring oversight: `plusCorr`, `minusCorr`,
`plusCap`, `*Movable*`, `faceCorr2_eq_plus_mul_minus`, and any
`faceCorr2 = formPerm/cycleOfList …` characterization **do not exist anywhere in the
repo**. The base file `PlanarMapCutCap2FWalk.lean` provides only the free factorization
`φ'₂ = phiLift · faceCorr₂`, `numCyclesCutPhi2_iff`, and caps = fixed points — it does
**not** supply any seam decomposition of `faceCorr₂`.

To "complete" Step 2 I would have to either (a) prove map-specific lemmas the repo's
kernel checks show are false, or (b) instantiate `SeamChainData` for `faceCorr₂` from
non-existent definitions and bolt the count on — producing a **VACUOUS / non-faithful**
conditional theorem (the most insidious anti-pattern in playbook §3.3: clean `#print
axioms` + green build that never discharges the real content). I did **not** do this.
`numCyclesCutPhi2_holds` therefore remains the single named open core, exactly as the
upstream files already document it, and `cutCapMap2_F` stays conditional on it
(`cutCapMap2_F_walk`, already in the repo).

## The one resistant joint (named, honest)

**`numCyclesCutPhi2_holds`** — the bridge from the (now-proven) abstract theorem to the
concrete `faceCorr₂`. It is blocked not by Lean difficulty but because the design's
two-disjoint-clean-seam-chain model of `faceCorr₂` is contradicted by the repository's
kernel reconnaissance. Closing it requires first establishing the TRUE orbit structure of
`faceCorr₂` (single long cycle ⊔ `+`-cap cycle, with bank-dart interleaving) and a walk
whose active invariant tracks that real, cut-dependent face-adjacency combinatorics — a
different (and strictly larger) development than the clean abstract chain. The abstract
theorem proven here is a genuine, kernel-anchored building block for that future work, but
it is not on its own sufficient, and I will not paper over the gap.

## Files

- Owned/written: `ProofsInTheBook/PlanarMapSeamChain.lean` (830 lines, clean).
- No other file touched. Branch `main`, no commits (per instructions).

## Verification commands run

```
rsync … PlanarMapSeamChain.lean uisai1:…
ssh uisai1 'lake env lean ProofsInTheBook/PlanarMapSeamChain.lean'   # exit 0
ssh uisai1 'lake build ProofsInTheBook.PlanarMapSeamChain'          # 8443 jobs OK
ssh uisai1 'lake env lean /tmp/axcheck.lean'  # axioms: propext, Classical.choice, Quot.sound
```
