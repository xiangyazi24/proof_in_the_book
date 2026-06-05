import ProofsInTheBook.PlanarMapSeamChain

/-!
# Specialising the seam-chain machinery to `faceCorr₂` (Chapter 35, the F-count)

This file builds the **proven, axiom-clean** abstract count machinery for the
corrected Chapter 35 face count `numCycles φ'₂ = M.F + 2`, matched to the **true**
cycle structure of `faceCorr₂ = phiLift⁻¹ · φ'₂` that we re-derived by direct
Lean-kernel computation (see `§ Kernel truth` below).

## What is proven here (unconditional, `0` sorry/axiom)

* `PureFixed.numCycles_mul_pureCycle` — a cycle of `m` pure `p`-fixed points drops
  `numCycles` by exactly `m − 1` (handles the pure `−`-cap chain and the all-pure
  triangle case).
* `MixedSeam.MixedSeamData.numCycles_mul_mixedChain` — a **mixed** cap chain in the
  kernel-true normal form (`p γᵢ = γᵢ`, `p vᵢ = u_{i+1}`) drops `numCycles` by exactly
  `k − 1`, via the signed walk with the mixed merge/split pattern `−,−,−,+,−,−,+,+`.
* `MixedSeam.mkFromCore` — reduced constructor that **derives** two of the three merge
  families (the two singleton merges, from `cap_fixed` + `Nodup`), so the only
  non-mechanical inputs are `merge_u_v` (one gap-face fact) and the two split
  `SameCycle` links.
* `Assembly.numCycles_two_factor` — telescopes a mixed `+`-chain and a pure `−`-chain
  on disjoint supports to the total drop `(k−1) + (m−1)`, with the second factor
  evaluated against the correct base `p · c₊` (no transport subtlety).

## Honest remaining joint (NOT closed here)

Concluding the headline `numCyclesCutPhi2_holds : ∀ C, C.NumCyclesCutPhi2`
unconditionally still requires **instantiating** the above for the concrete
`faceCorr₂` of every cut: the factorisation `faceCorr₂ = c₊ · c₋` on disjoint supports
(absent from the repo), the `+`-chain's `MixedSeamData` over `phiLift`, and in
particular its `merge_u_v` and **two split `SameCycle` links** — the genuinely
cut-dependent, genus-`0` content for which `φ'₂` has **no projection semiconjugacy**.
That instantiation is the one isolated topological joint; it is the `F`-analogue of the
`V'` machinery and is left as the named open core `NumCyclesCutPhi2`
(`PlanarMapCutCap2Counts.lean`), with all the reusable count algebra now proven.

## Kernel truth (re-derived in this campaign, verbatim)

`faceCorr₂` was computed on the corrected computable mirror `cutSigmaC2 ∘ cutAlphaC`
(triangle, `PlanarMapCutCapEval.lean`) and on a hand-built tetrahedron cut `0→1→3→0`
(the mixed cut the prior reconnaissance flagged).  Encoding `inl d ↦ d`,
`c_i^+ ↦ 100+i`, `c_i^- ↦ 200+i`:

* **Triangle (k = 3).**  `faceCorr₂` = `(100 102 101)(200 201 202)` with the six base
  darts `0,1,2,3,4,5` all **fixed**.  Both cap chains are **pure** `k`-cycles of
  `phiLift`-fixed points.  `numCycles φ'₂ = 4 = F + 2`.

* **Tetra cut `0→1→3→0` (k = 3, the mixed case).**  `faceCorr₂` =
  `(100 1 3 102 4 10 101 9 7)(200 201 202)` with base darts `0,2,5,6,8,11` **fixed**.
  The `−`-cap chain `(200 201 202)` is **pure**.  The `+`-cap chain is a **mixed**
  `9`-cycle `γ₀ u₀ v₀ γ₁ u₁ v₁ γ₂ u₂ v₂` with
  `γ₀,γ₁,γ₂ = 100,102,101`, `u₀,u₁,u₂ = 1,4,9`, `v₀,v₁,v₂ = 3,10,7`, and the
  kernel-verified `phiLift`-arrows

      phiLift γᵢ = γᵢ            (caps are phiLift-fixed)
      phiLift vᵢ = u_{i+1}       (3↦4, 10↦9, 7↦1 — the genus-0 seam incidence)

  Each gap face-orbit of `phiLift` is `(uᵢ, externals…, v_{i-1})`; e.g. the orbit
  `(1 2 7) = (u₀, 2, v₂)` with `phiLift v₂ = u₀`.  The per-step signed walk over the
  `9`-cycle is `−,−,−,+,−,−,+,+` (5 merges, 3 splits), summing to `−2 = −(k−1)`, so
  `numCycles (phiLift · (+chain)) = numCycles phiLift − (k−1)`, and likewise `−(k−1)`
  for the pure `−`-chain; total `(F + 2k) − (k−1) − (k−1) = F + 2`.

The decisive correction over the prior design: the seam incidence is `phiLift vᵢ =
u_{i+1}` (inter-block, across a cap), **not** the design's `phiLift uᵢ = vᵢ`
(intra-block).  The two are not interconvertible by rotation/reversal, so the proven
abstract `SeamChainData` theorem (which assumes `p uᵢ = vᵢ`) does **not** apply to the
mixed `+`-chain as-is; we build the matching active-set invariant here.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List

namespace ProofsInTheBook.PlanarMap

namespace SeamSpec

open SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Mini-lemma: a cycle of pure `p`-fixed points merges to one cycle

If `L` is a nodup list of points each **fixed** by `p`, then
`numCycles (p · formPerm L) = numCycles p − (L.length − 1)`: the `L.length`
singletons merge into a single new cycle.  Every walk step `L[j]–L[j+1]` is a merge,
confined by the forward-invariant prefix set `{L[0],…,L[j]}` (closed under
`P_m = p · formPerm (take m)` because `formPerm` cycles inside the prefix and `p`
fixes each of its points). -/

namespace PureFixed

variable (p : Equiv.Perm X) {L : List X}

/-- The prefix set `{L[0],…,L[m-1]}` of a list, as a `Set`. -/
def prefixSet (L : List X) (m : ℕ) : Set X := {x | x ∈ L.take m}

/-- For an all-`p`-fixed nodup prefix, `P_m = p · formPerm (take m)` keeps the prefix
set forward-invariant: `formPerm` maps a prefix point to another prefix point, and
`p` fixes it. -/
lemma prefixSet_invariant (hL : L.Nodup) (hfix : ∀ x ∈ L, p x = x) {m : ℕ}
    (hm : m ≤ L.length) :
    ∀ x ∈ prefixSet L m, (p * cycleOfList (L.take m)) x ∈ prefixSet L m := by
  intro x hx
  -- x ∈ take m. formPerm (take m) maps it to another element of take m.
  have hxtake : x ∈ L.take m := hx
  have hmem : (cycleOfList (L.take m)) x ∈ L.take m := by
    simp only [cycleOfList]
    -- formPerm of a list maps members to members
    have : (L.take m).formPerm x ∈ L.take m := by
      rcases List.mem_iff_getElem.mp hxtake with ⟨r, hr, rfl⟩
      have hnodup : (L.take m).Nodup := (List.take_sublist m L).nodup hL
      rw [List.formPerm_apply_getElem _ hnodup r hr]
      exact List.getElem_mem _
    exact this
  -- p fixes it (it's a member of L)
  have hmemL : (cycleOfList (L.take m)) x ∈ L := List.mem_of_mem_take hmem
  rw [Equiv.Perm.mul_apply, hfix _ hmemL]
  exact hmem

/-- Each walk step of an all-`p`-fixed nodup list is a **merge** (`stepSign = −1`):
`L[j]` lies in the invariant prefix set `take (j+1)`, while `L[j+1]` does not. -/
lemma stepSign_eq_neg_one (hL : L.Nodup) (hfix : ∀ x ∈ L, p x = x) {j : ℕ}
    (hj : j + 1 < L.length) :
    stepSign p L j = -1 := by
  have hjlt : j < L.length := by omega
  simp only [stepSign, dif_pos hj]
  rw [if_neg]
  -- ¬ SameCycle (P_{j+1}) L[j] L[j+1]: invariant prefix take (j+1)
  apply not_sameCycle_of_invariant (A := prefixSet L (j + 1))
  · -- L[j] ∈ take (j+1)
    show (L[j]'hjlt) ∈ L.take (j + 1)
    have hjm : j < (L.take (j + 1)).length := by rw [List.length_take]; omega
    rw [show (L[j]'hjlt) = (L.take (j+1))[j]'hjm from (List.getElem_take).symm]
    exact List.getElem_mem hjm
  · -- L[j+1] ∉ take (j+1)
    intro hmem
    have hmem' : (L[j+1]'hj) ∈ L.take (j + 1) := hmem
    rw [List.mem_iff_getElem] at hmem'
    obtain ⟨r, hr, hre⟩ := hmem'
    rw [List.getElem_take] at hre
    have hrlt : r < L.length := by
      rw [List.length_take] at hr; omega
    have : j + 1 = r := (List.Nodup.getElem_inj_iff hL).mp hre.symm
    rw [List.length_take] at hr
    omega
  · exact prefixSet_invariant p hL hfix (by omega)

/-- **Pure-fixed-point cycle count.**  For a nodup list `L` of `p`-fixed points,
`numCycles (p · formPerm L) = numCycles p − (L.length − 1)` (integer form). -/
theorem numCycles_mul_pureCycle (hL : L.Nodup) (hfix : ∀ x ∈ L, p x = x)
    (hpos : 0 < L.length) :
    ((numCycles (p * cycleOfList L) : ℤ) - (numCycles p : ℤ))
      = -((L.length : ℤ) - 1) := by
  have hlen1 : L.length - 1 + 1 ≤ L.length := by omega
  have hwalk := numCycles_take_delta p hL (L.length - 1) hlen1
  have htake : L.take (L.length - 1 + 1) = L := by
    apply List.take_of_length_le; omega
  rw [htake] at hwalk
  rw [hwalk]
  -- sum of (L.length - 1) copies of -1
  have hsum : ∀ j ∈ Finset.range (L.length - 1), stepSign p L j = -1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact stepSign_eq_neg_one p hL hfix (by omega)
  rw [Finset.sum_congr rfl hsum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_neg, mul_one]
  push_cast [Nat.cast_sub (by omega : 1 ≤ L.length)]
  ring

end PureFixed

/-! ## The mixed seam chain: `p vᵢ = u_{i+1}` with gap face-orbits

The `+`-cap chain of `faceCorr₂` is **not** in `SeamChainData` form (`p uᵢ = vᵢ`);
the kernel-true seam incidence is `p vᵢ = u_{i+1}` (inter-block), with each gap face
orbit `Fᵢ` of `p` a forward-`p`-invariant set carrying `uᵢ` and `v_{i-1}`.

We package the kernel-true data as `MixedSeamData` and run the same signed walk.  The
computable actions of `P m = p · formPerm (take m)` on the seam letters are

  `P m (u t) = u_{t+1}`   (when `v_t` is in the prefix: `formPerm u_t = v_t`, then `p v_t = u_{t+1}`)
  `P m (v t) = γ_{t+1}`   (when `γ_{t+1}` is in the prefix: `p γ = γ`)
  last-letter wraps land on `γ₀`.

The action `P m (γ t) = p (u t)` exits the seam list into the face orbit `F t`, which
is why every active set carrying a consumed cap must carry the whole face orbit — the
single piece of genuinely cut-dependent (genus-0) data, supplied as the forward
invariance hypothesis `face_inv`.

### Signed pattern (kernel-verified, `−,−,−,+,−,−,+,+` at `k = 3`)

  `γ₀–u₀`            : merge   (`γ₀` is `p`-fixed singleton, `u₀ ∈ F₀`, `γ₀ ∉ F₀`)
  `γᵢ–uᵢ` (`i ≥ 1`)  : split   (`γᵢ` wraps to `γ₀`; the active cycle already reached `uᵢ`)
  `uᵢ–vᵢ` (`i<k-1`)  : merge   (`uᵢ` reaches `γ₀..F₀..F_i`; `vᵢ` not yet)
  `u_{k-1}–v_{k-1}`  : split   (`v_{k-1}` closes the last gap face into the cycle)
  `vᵢ–γ_{i+1}`(`i<k-1`): merge  (`vᵢ` in active faces; `γ_{i+1}` a fresh `p`-fixed singleton)

Net `= −(2k−1) + k = −(k−1)`, matching the pure case.

`MixedSeamData` packages the per-step `SameCycle` facts (`merge_*`, `split_*`) as
fields, against which `numCycles_mul_mixedChain` proves the count **unconditionally**
(the genuine reusable content: the mixed signed-walk telescoping).  Of those fields,
the two **singleton** merges `merge_gamma0_u0` and `merge_v_gamma` are *derived* from
`cap_fixed` + `Nodup` by the reduced constructor `mkFromCore` (the merge-target is a
`p`-fixed cap outside the prefix, hence a `P`-singleton).  The remaining non-mechanical
inputs are `merge_u_v` (one gap-face exclusion) and the two split links
`split_gamma_u` / `split_last_uv` — the genus-`0`, cut-dependent `SameCycle` advances
(verified kernel-true on the triangle and the tetra cut), here without a projection
semiconjugacy.  They are the one isolated topological joint of the concrete
instantiation. -/

namespace MixedSeam

variable (p : Equiv.Perm X)

/-- Packaged data for one **mixed** cap chain in normal form
`[γ₀,u₀,v₀, …, γ_{k-1},u_{k-1},v_{k-1}]`, with the kernel-true seam incidence
`p vᵢ = u_{i+1}` (cyclic) and `p γᵢ = γᵢ`.  The two split `SameCycle` links are the
genuinely cut-dependent (genus-0) facts; all merges are derived. -/
structure MixedSeamData (X : Type*) [Fintype X] [DecidableEq X] where
  p : Equiv.Perm X
  k : ℕ
  hk : 0 < k
  γ : Fin k → X
  u : Fin k → X
  v : Fin k → X
  nodup_seam : (seamList γ u v).Nodup
  cap_fixed : ∀ i, p (γ i) = γ i
  /-- The inter-block seam incidence `p vᵢ = u_{i+1}` (cyclic). -/
  seam_pair : ∀ i : Fin k, p (v i) = u ⟨((i : ℕ) + 1) % k, Nat.mod_lt _ hk⟩
  /-- **Merge exclusions** (the active-set membership facts confining the three merge
  families), supplied as kernel-true data: at each merge site the to-be-merged target
  lies outside the fused active set.  These are forward-`P`-invariant-set witnesses. -/
  merge_gamma0_u0 : ¬ (p * cycleOfList ((seamList γ u v).take 1)).SameCycle
      (γ ⟨0, hk⟩) (u ⟨0, hk⟩)
  merge_u_v : ∀ i : Fin k, (i : ℕ) + 1 < k →
      ¬ (p * cycleOfList ((seamList γ u v).take (3 * (i : ℕ) + 2))).SameCycle (u i) (v i)
  merge_v_gamma : ∀ (i : Fin k) (hi : (i : ℕ) + 1 < k),
      ¬ (p * cycleOfList ((seamList γ u v).take (3 * (i : ℕ) + 3))).SameCycle
        (v i) (γ ⟨((i : ℕ) + 1), hi⟩)
  /-- **Split link 1** (`γᵢ–uᵢ` for `i ≥ 1`): the active cycle of `P (3i)` already
  contains both `γᵢ` and `uᵢ` (genus-0 gap-face threading). -/
  split_gamma_u : ∀ i : Fin k, 0 < (i : ℕ) →
      (p * cycleOfList ((seamList γ u v).take (3 * (i : ℕ) + 1))).SameCycle (γ i) (u i)
  /-- **Split link 2** (`u_{k-1}–v_{k-1}`): the last movable pair closes into one
  cycle (genus-0 gap-face threading of the final face). -/
  split_last_uv : ∀ i : Fin k, (i : ℕ) + 1 = k →
      (p * cycleOfList ((seamList γ u v).take (3 * (i : ℕ) + 2))).SameCycle (u i) (v i)

/-! ### Deriving the two singleton merges

`merge_gamma0_u0` and `merge_v_gamma` need **no** face data: at those two sites the
merge-target is a `p`-fixed cap **outside** the current prefix, hence a fixed point of
`P m` (formPerm fixes off-prefix points), hence a singleton `P m`-cycle, so `SameCycle`
to it forces equality — excluded by `Nodup`.  Only `merge_u_v` (the `uᵢ–vᵢ` site, where
`vᵢ` maps forward under `p`) genuinely needs the gap-face structure.  We package the
reduced obligations in `mkFromCore`, discharging the two singleton merges. -/

/-- A point fixed by `q` is a singleton `q`-cycle: `SameCycle q b a → b = a`. -/
lemma eq_of_sameCycle_fixed {q : Equiv.Perm X} {a b : X} (ha : q a = a)
    (h : q.SameCycle b a) : b = a := by
  obtain ⟨n, hn⟩ := h.symm.exists_nat_pow_eq
  have hpow : ∀ m : ℕ, (q ^ m) a = a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, ha]
  rw [hpow] at hn; exact hn.symm

/-- `(p · formPerm (L.take m))` fixes a `p`-fixed point off the prefix. -/
lemma P_fixed_of_off_prefix {p : Equiv.Perm X} {L : List X} {x : X} {m : ℕ}
    (hx : x ∉ L.take m) (hfix : p x = x) :
    (p * cycleOfList (L.take m)) x = x := by
  rw [mul_take_apply_of_not_mem p hx, hfix]

/-- **Reduced constructor.**  Build a `MixedSeamData` from the genuinely-needed data:
the structural equations, `merge_u_v`, and the two split links.  The two singleton
merges (`merge_gamma0_u0`, `merge_v_gamma`) are **derived** from `cap_fixed` + `Nodup`.
This isolates the non-mechanical content to exactly `merge_u_v` (one face-invariance
fact) and the two split `SameCycle` links (the genus-0 core). -/
def mkFromCore (p : Equiv.Perm X) (k : ℕ) (hk : 0 < k)
    (γ u v : Fin k → X)
    (nodup_seam : (seamList γ u v).Nodup)
    (cap_fixed : ∀ i, p (γ i) = γ i)
    (seam_pair : ∀ i : Fin k, p (v i) = u ⟨((i : ℕ) + 1) % k, Nat.mod_lt _ hk⟩)
    (merge_u_v : ∀ i : Fin k, (i : ℕ) + 1 < k →
      ¬ (p * cycleOfList ((seamList γ u v).take (3 * (i : ℕ) + 2))).SameCycle (u i) (v i))
    (split_gamma_u : ∀ i : Fin k, 0 < (i : ℕ) →
      (p * cycleOfList ((seamList γ u v).take (3 * (i : ℕ) + 1))).SameCycle (γ i) (u i))
    (split_last_uv : ∀ i : Fin k, (i : ℕ) + 1 = k →
      (p * cycleOfList ((seamList γ u v).take (3 * (i : ℕ) + 2))).SameCycle (u i) (v i)) :
    MixedSeamData X where
  p := p; k := k; hk := hk; γ := γ; u := u; v := v
  nodup_seam := nodup_seam; cap_fixed := cap_fixed; seam_pair := seam_pair
  merge_u_v := merge_u_v; split_gamma_u := split_gamma_u; split_last_uv := split_last_uv
  merge_gamma0_u0 := by
    -- P (take 1) fixes γ₀? take 1 = [γ₀]; formPerm[γ₀] = id, so P = p, p γ₀ = γ₀.
    intro hsc
    -- γ₀ is the unique prefix element; SameCycle (p · formPerm[γ₀]) γ₀ u₀.
    have hform : cycleOfList ((seamList γ u v).take 1) = 1 := by
      have hlen : 1 ≤ (seamList γ u v).length := by rw [seamList_length]; omega
      rcases hh : seamList γ u v with _ | ⟨a, rest⟩
      · rw [hh] at hlen; simp at hlen
      · simp only [cycleOfList, List.take_succ_cons, List.take_zero,
          List.formPerm_singleton]
    rw [hform, mul_one] at hsc
    have hgu : γ ⟨0, hk⟩ = u ⟨0, hk⟩ :=
      (eq_of_sameCycle_fixed (cap_fixed ⟨0, hk⟩) hsc.symm).symm
    -- contradiction with nodup (γ₀ at index 0, u₀ at index 1)
    have h' : (seamList γ u v)[0]'(by rw [seamList_length]; omega)
        = (seamList γ u v)[1]'(by rw [seamList_length]; omega) := by
      have hg := seamList_getElem_gamma γ u v ⟨0, hk⟩
      have hu := seamList_getElem_u γ u v ⟨0, hk⟩
      simp only [Fin.val_mk, Nat.mul_zero, Nat.zero_add] at hg hu
      rw [getElem_congr rfl (show (0:ℕ) = 3 * (0:ℕ) from rfl)] at hg
      rw [getElem_congr rfl (show (1:ℕ) = 3 * (0:ℕ) + 1 from rfl)] at hu
      rw [hg, hu]; exact hgu
    have := (List.Nodup.getElem_inj_iff nodup_seam).mp h'
    omega
  merge_v_gamma := by
    intro i hi hsc
    -- γ_{i+1} at seam-index 3(i+1) = 3i+3 ∉ take (3i+3); p γ_{i+1} = γ_{i+1}.
    have hidx : 3 * ((i : ℕ) + 1) = 3 * (i : ℕ) + 3 := by ring
    have hnotmem : γ ⟨(i : ℕ) + 1, hi⟩ ∉ (seamList γ u v).take (3 * (i : ℕ) + 3) := by
      intro hmem
      rw [List.mem_iff_getElem] at hmem
      obtain ⟨r, hr, hre⟩ := hmem
      rw [List.getElem_take] at hre
      rw [List.length_take] at hr
      have hrlt : r < (seamList γ u v).length := by rw [seamList_length]; omega
      have hgr : (seamList γ u v)[3 * (i:ℕ) + 3]'(by rw [seamList_length]; have := hi; omega)
          = γ ⟨(i:ℕ)+1, hi⟩ := by
        rw [getElem_congr rfl hidx.symm]
        exact seamList_getElem_gamma γ u v ⟨(i:ℕ)+1, hi⟩
      have heq : (seamList γ u v)[r]'hrlt
          = (seamList γ u v)[3 * (i:ℕ) + 3]'(by rw [seamList_length]; have := hi; omega) := by
        rw [hgr, hre]
      have := (List.Nodup.getElem_inj_iff nodup_seam).mp heq
      omega
    have hPfix := P_fixed_of_off_prefix hnotmem (cap_fixed ⟨(i:ℕ)+1, hi⟩)
    have hve := eq_of_sameCycle_fixed hPfix hsc
    -- v i = γ_{i+1} contradicts nodup
    have h' : (seamList γ u v)[3 * (i:ℕ) + 2]'(by rw [seamList_length]; have := hi; omega)
        = (seamList γ u v)[3 * (i:ℕ) + 3]'(by rw [seamList_length]; have := hi; omega) := by
      have hv := seamList_getElem_v γ u v i
      have hg : (seamList γ u v)[3 * (i:ℕ) + 3]'(by rw [seamList_length]; have := hi; omega)
          = γ ⟨(i:ℕ)+1, hi⟩ := by
        rw [getElem_congr rfl hidx.symm]
        exact seamList_getElem_gamma γ u v ⟨(i:ℕ)+1, hi⟩
      rw [hv, hg]; exact hve
    have := (List.Nodup.getElem_inj_iff nodup_seam).mp h'
    omega

namespace MixedSeamData

variable (S : MixedSeamData X)

/-- `stepSign` at `j = 3i` (the `γᵢ–uᵢ` step): `−1` for `i = 0`, `+1` for `i ≥ 1`. -/
lemma stepSign_A (i : Fin S.k) :
    stepSign S.p (seamList S.γ S.u S.v) (3 * (i : ℕ))
      = if (i : ℕ) = 0 then -1 else 1 := by
  have hj : 3 * (i : ℕ) + 1 < (seamList S.γ S.u S.v).length := by
    rw [seamList_length]; have := i.2; omega
  have hg : (seamList S.γ S.u S.v)[3 * (i:ℕ)]'(by omega) = S.γ i :=
    seamList_getElem_gamma S.γ S.u S.v i
  have hu : (seamList S.γ S.u S.v)[3 * (i:ℕ) + 1]'hj = S.u i :=
    seamList_getElem_u S.γ S.u S.v i
  simp only [stepSign, dif_pos hj, hg, hu]
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
  · -- i = 0: RHS = -1, need SameCycle false (merge)
    have hi0 : i = (⟨0, S.hk⟩ : Fin S.k) := by apply Fin.ext; simpa using h0
    have hm1 : (3 * (i:ℕ) + 1) = 1 := by omega
    have hnsc : ¬ (S.p * cycleOfList ((seamList S.γ S.u S.v).take (3 * (i:ℕ) + 1))).SameCycle
        (S.γ i) (S.u i) := by rw [hm1, hi0]; exact S.merge_gamma0_u0
    rw [if_neg hnsc, if_pos h0]
  · -- i ≥ 1: RHS = 1, need SameCycle true (split)
    rw [if_pos (S.split_gamma_u i hpos), if_neg (by omega : ¬ (i:ℕ) = 0)]

/-- `stepSign` at `j = 3i+1` (the `uᵢ–vᵢ` step): `+1` for the last block
(`i+1 = k`), `−1` otherwise. -/
lemma stepSign_B (i : Fin S.k) :
    stepSign S.p (seamList S.γ S.u S.v) (3 * (i : ℕ) + 1)
      = if (i : ℕ) + 1 = S.k then 1 else -1 := by
  have hj : 3 * (i:ℕ) + 1 + 1 < (seamList S.γ S.u S.v).length := by
    rw [seamList_length]; have := i.2; omega
  have hu : (seamList S.γ S.u S.v)[3 * (i:ℕ) + 1]'(by omega) = S.u i :=
    seamList_getElem_u S.γ S.u S.v i
  have hv : (seamList S.γ S.u S.v)[3 * (i:ℕ) + 1 + 1]'hj = S.v i := by
    rw [getElem_congr rfl (show 3 * (i:ℕ) + 1 + 1 = 3 * (i:ℕ) + 2 from by ring)]
    exact seamList_getElem_v S.γ S.u S.v i
  have hpre : (3 * (i:ℕ) + 1 + 1) = 3 * (i:ℕ) + 2 := by ring
  simp only [stepSign, dif_pos hj, hu, hv, hpre]
  rcases Nat.lt_or_ge ((i:ℕ) + 1) S.k with hlt | hge
  · -- not last block: merge
    rw [if_neg (S.merge_u_v i hlt), if_neg (by omega : ¬ (i:ℕ) + 1 = S.k)]
  · -- last block: i+1 = k (since i < k), split
    have hlast : (i:ℕ) + 1 = S.k := by have := i.2; omega
    rw [if_pos (S.split_last_uv i hlast), if_pos hlast]

/-- `stepSign` at `j = 3i+2` (the `vᵢ–γ_{i+1}` step), for `i+1 < k`: `−1` (merge). -/
lemma stepSign_C (i : Fin S.k) (hi : (i : ℕ) + 1 < S.k) :
    stepSign S.p (seamList S.γ S.u S.v) (3 * (i : ℕ) + 2) = -1 := by
  have hj : 3 * (i:ℕ) + 2 + 1 < (seamList S.γ S.u S.v).length := by
    rw [seamList_length]; omega
  have hv : (seamList S.γ S.u S.v)[3 * (i:ℕ) + 2]'(by omega) = S.v i :=
    seamList_getElem_v S.γ S.u S.v i
  have hg : (seamList S.γ S.u S.v)[3 * (i:ℕ) + 2 + 1]'hj = S.γ ⟨(i:ℕ) + 1, hi⟩ := by
    rw [getElem_congr rfl (show 3 * (i:ℕ) + 2 + 1 = 3 * ((i:ℕ) + 1) from by ring)]
    have := seamList_getElem_gamma S.γ S.u S.v ⟨(i:ℕ) + 1, hi⟩
    simpa using this
  have hpre : (3 * (i:ℕ) + 2 + 1) = 3 * (i:ℕ) + 3 := by ring
  simp only [stepSign, dif_pos hj, hv, hg, hpre]
  rw [if_neg (S.merge_v_gamma i hi)]

/-- **The partial signed sum over the first `n` full blocks** (`3n` steps), for
`1 ≤ n ≤ k − 1`.  Block `0` is `(−1,−1,−1) = −3`; each later full block (`1 ≤ i < k−1`)
is `(+1,−1,−1) = −1`.  Hence the cumulative is `−(n + 2)`. -/
lemma block_sum (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ S.k - 1) :
    ∑ j ∈ Finset.range (3 * n), stepSign S.p (seamList S.γ S.u S.v) j
      = -((n : ℤ) + 2) := by
  induction n with
  | zero => omega
  | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- n = 1: just block 0 (steps 0,1,2) = A(0)+B(0)+C(0) = -1-1-1 = -3
        subst hm0
        rw [show 3 * (0 + 1) = 0 + 1 + 1 + 1 from rfl,
          Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_zero]
        have hk2 : 2 ≤ S.k := by omega
        have hA := S.stepSign_A ⟨0, S.hk⟩
        have hB := S.stepSign_B ⟨0, S.hk⟩
        have hC := S.stepSign_C ⟨0, S.hk⟩ (by simp only [Fin.val_mk]; omega)
        simp only [Fin.val_mk, Nat.mul_zero, Nat.zero_add, if_true,
          if_neg (by omega : ¬ (1 : ℕ) = S.k)] at hA hB hC ⊢
        rw [hA, hB, hC]; ring
      · -- n = m+1 with m ≥ 1: block m is (+1,-1,-1) = -1
        have hmk : m ≤ S.k - 1 := by omega
        have ihm := ih hmpos hmk
        have hmlt : m < S.k := by omega
        have hmnext : (m : ℕ) + 1 < S.k := by omega
        rw [show 3 * (m + 1) = 3 * m + 1 + 1 + 1 from by ring,
          Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ihm]
        have hA := S.stepSign_A ⟨m, hmlt⟩
        have hB := S.stepSign_B ⟨m, hmlt⟩
        have hC := S.stepSign_C ⟨m, hmlt⟩ (by simp only [Fin.val_mk]; omega)
        simp only [Fin.val_mk] at hA hB hC
        rw [show 3 * m = 3 * m from rfl, hA, if_neg (by omega)]
        rw [show 3 * m + 1 = 3 * (m : ℕ) + 1 from rfl, hB, if_neg (by omega)]
        rw [show 3 * m + 1 + 1 = 3 * (m : ℕ) + 2 from by ring, hC]
        push_cast; ring

/-- **The mixed one-chain count.**  `numCycles (p · formPerm (seamList γ u v)) =
numCycles p − (k − 1)`. -/
theorem numCycles_mul_mixedChain :
    ((numCycles (S.p * cycleOfList (seamList S.γ S.u S.v)) : ℤ)
      - (numCycles S.p : ℤ)) = -((S.k : ℤ) - 1) := by
  have hlen : (seamList S.γ S.u S.v).length = 3 * S.k := seamList_length S.γ S.u S.v
  have h3k : 3 * S.k - 1 + 1 ≤ (seamList S.γ S.u S.v).length := by
    rw [hlen]; have := S.hk; omega
  have hwalk := numCycles_take_delta S.p S.nodup_seam (3 * S.k - 1) h3k
  have htake : (seamList S.γ S.u S.v).take (3 * S.k - 1 + 1) = seamList S.γ S.u S.v := by
    apply List.take_of_length_le; rw [hlen]; have := S.hk; omega
  rw [htake] at hwalk
  rw [hwalk]
  -- The total has `3k-1` steps.  Split off the first `3(k-1)` (full blocks `0..k-2`),
  -- then the last block's two steps (A,B at `i = k-1`, with B a split since `i+1 = k`).
  have hk := S.hk
  rcases Nat.eq_or_lt_of_le hk with hk1 | hk2
  · -- k = 1: only the last block (steps 0,1), A(0) = -1 (since i=0), B(0) = +1 (i+1=k).
    have hkeq : S.k = 1 := hk1.symm
    rw [show 3 * S.k - 1 = 0 + 1 + 1 from by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    have hA := S.stepSign_A ⟨0, S.hk⟩
    have hB := S.stepSign_B ⟨0, S.hk⟩
    simp only [Fin.val_mk, Nat.mul_zero, Nat.zero_add, if_true,
      if_pos (by omega : (0 : ℕ) + 1 = S.k)] at hA hB ⊢
    rw [hA, hB, hkeq]; norm_num
  · -- k ≥ 2: first `3(k-1)` steps via block_sum at n = k-1, plus the last 2 steps.
    have hkm1 : 1 ≤ S.k - 1 := by omega
    have hbs := S.block_sum (S.k - 1) hkm1 (le_refl _)
    have hsplit : 3 * S.k - 1 = 3 * (S.k - 1) + 1 + 1 := by omega
    rw [hsplit, Finset.sum_range_succ, Finset.sum_range_succ, hbs]
    -- last block index i = k-1
    have hlast : (S.k - 1) < S.k := by omega
    have hA := S.stepSign_A ⟨S.k - 1, hlast⟩
    have hB := S.stepSign_B ⟨S.k - 1, hlast⟩
    simp only [Fin.val_mk] at hA hB
    rw [show 3 * (S.k - 1) = 3 * (S.k - 1) from rfl, hA, if_neg (by omega)]
    rw [show 3 * (S.k - 1) + 1 = 3 * (S.k - 1) + 1 from rfl, hB, if_pos (by omega)]
    push_cast [Nat.cast_sub (by omega : 1 ≤ S.k)]
    ring

end MixedSeamData

end MixedSeam

/-! ## Two-factor assembly (mixed `+`-chain · pure `−`-chain)

`faceCorr₂ = c₊ · c₋` on disjoint supports, with `c₊` a mixed cap chain (a
`MixedSeamData` over `phiLift`) and `c₋` a pure cycle of `phiLift`-fixed caps.  The
total count telescopes:

  `numCycles (p · c₊ · c₋) = numCycles p + Δ₊ + Δ₋`,
  `Δ₊ = −(k−1)` (mixed chain, base `p`),
  `Δ₋ = −(m−1)` (pure chain, base `p · c₊` — the `−`-caps are still fixed by `p · c₊`
                  because `c₊` has support disjoint from them).

No transport subtlety: the second factor is evaluated against the **correct** base
`p · c₊`, against which the pure `−`-caps remain singleton fixed points. -/

namespace Assembly

open MixedSeam

variable (p : Equiv.Perm X)

/-- **Telescoped two-factor count.**  Given a mixed `+`-chain (`S₊ : MixedSeamData`
with `S₊.p = p`) realising `c₊ = formPerm (seamList …)`, and a pure `−`-chain `Lm`
(nodup, each point fixed by `p · c₊`), the count of `p · c₊ · c₋` drops by
`(k−1) + (Lm.length − 1)`. -/
theorem numCycles_two_factor
    (S : MixedSeam.MixedSeamData X) (hSp : S.p = p)
    {Lm : List X} (hLm_nodup : Lm.Nodup) (hLm_pos : 0 < Lm.length)
    (hLm_fixed : ∀ x ∈ Lm,
      (p * cycleOfList (seamList S.γ S.u S.v)) x = x) :
    ((numCycles (p * cycleOfList (seamList S.γ S.u S.v) * cycleOfList Lm) : ℤ)
      - (numCycles p : ℤ)) = -((S.k : ℤ) - 1) - ((Lm.length : ℤ) - 1) := by
  -- Δ₊ = -(k-1), base p
  have hplus := S.numCycles_mul_mixedChain
  rw [hSp] at hplus
  -- Δ₋ = -(m-1), base p · c₊
  have hminus := PureFixed.numCycles_mul_pureCycle
    (p * cycleOfList (seamList S.γ S.u S.v)) hLm_nodup hLm_fixed hLm_pos
  -- telescope
  have htel :
      ((numCycles (p * cycleOfList (seamList S.γ S.u S.v) * cycleOfList Lm) : ℤ)
        - (numCycles p : ℤ))
      = ((numCycles (p * cycleOfList (seamList S.γ S.u S.v)) : ℤ) - (numCycles p : ℤ))
        + ((numCycles (p * cycleOfList (seamList S.γ S.u S.v) * cycleOfList Lm) : ℤ)
            - (numCycles (p * cycleOfList (seamList S.γ S.u S.v)) : ℤ)) := by ring
  rw [htel, hplus, hminus]; ring

end Assembly

end SeamSpec

end ProofsInTheBook.PlanarMap
