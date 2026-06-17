# Ch13 recovery — ChatGPT 5.5 Pro complete design (2026-06-13)

## The corrected, VERIFIED-TRUE theorem (planar, self-contained)
`core_of_nondeg` (FFCT108) is SOUND. The corrected sufficient theorem uses TWO strict closed-convexity conditions in pure-sine form:

```
def closeSupp θ ρ n j := ∑ r ∈ Ico 0 n, ∑ i ∈ Ico j n, ρ r * ρ i * sin(θ i − θ r)   -- = Im(conj s_0 · s_j) = det(S, s_j)
def finalSupp θ ρ n k := - ∑ i ∈ Ico k (n-1), ρ i * sin(θ i − θ (n-1))
```
- **CloseStrict**: ∀ k, 1≤k≤n-1 → 0 < closeSupp θ ρ n k   (every interior vertex strictly LEFT of closing edge P_n→P_0 ⟹ P_k≠P_n ⟹ s_k≠0, no proper suffix closes)
- **FinalStrict**: ∀ k, 1≤k≤n-2 → 0 < finalSupp θ ρ n k    (strict final-edge support ⟹ b_k≠π)

`correctedDiscreteFenchel_closedStrict (premises + hfwd + hbwd + CloseStrict + FinalStrict) : θ(n-1)−θ_0 < 2π`.

## Lean route (ChatGPT gave full skeletons — all reuse FFCT108 machinery):
1. `im_conj_chord_mul_chord : (conj(chord θ ρ n 0) * chord θ ρ n k).im = closeSupp θ ρ n k` (map_sum, conj_exp, exp_ofReal_mul_I).
2. `suffix_ne_of_closeStrict (hcloseStrict) : chord θ ρ n k ≠ 0` (chord_k=0 ⟹ closeSupp=0 ⟹ contradict hcloseStrict>0).
3. `b_ne_pi_of_finalStrict (hpos hfinalStrict hsuffix_ne) : (θ(n-1)−θ k)−aang ≠ π` (im_end_chord + im_rot_chord; b_k=π ⟹ sin=0 ⟹ sum=0 ⟹ contradict finalStrict; k=n-1 case via aang_last gives b=0≠π).
4. `hnd_of_closeStrict_finalStrict` assembles → the DiscreteFenchelNondeg per-instance form.
5. `correctedDiscreteFenchel_closedStrict := core_of_nondeg ... (hnd_of_...)`.

NOTE: session already committed FFCT109 with a variant `discreteFenchelCore_of_strict_final_support` taking `hsuffix_ne` as hypothesis. ChatGPT's `closeSupp` version DERIVES hsuffix_ne from CloseStrict — cleaner/self-contained. Reconcile: FFCT109 can take closeSupp instead of raw suffix_ne.

## 🔴 THE CRITICAL FINDING (spherical side — the real remaining crux)
The strict conditions require the gnomonic arm to be GLOBALLY STRICTLY CONVEX (strict support at ALL nonincident vertices: 0 < sOrient(P_i,P_{i+1},P_j) for j≠i,i+1). ChatGPT confirms:
- A globally strictly convex spherical arc in an open hemisphere DOES supply CloseStrict + FinalStrict (strict spherical supports → strict planar det3 → strict sine sums, via the gnomonic positive-factor bridge + area-sine formula).
- **BUT the current `openedWBS_gnomonicSingleWind` (FFCT97) supplies only WEAK global support** (gnomonic_edge_support_nonneg: 0≤det3) + strict CONSECUTIVE turns. NOT strict global. So the strict closed-support hypotheses are NOT supplied as written — A NEW GEOMETRIC LEMMA IS NEEDED.
- **"Open hemisphere ALONE does NOT prevent lapping"** — the repeated-lap counterexample embeds in an open hemisphere. What prevents lapping is strict GLOBAL convex support / no-repeat, not the hemisphere.

### The open question to resolve (carefully, NOT by blind grind):
openedWBS at the WBS sup is WEAK convex — the support-stuck contact gives det3=0 at ONE nonadjacent pair (the cross-piece). Is openedWBS strictly convex at ALL OTHER nonincident pairs? And is the stuck pair one of the (closing-edge,interior-k) / (final-edge,interior-k) pairs that CloseStrict/FinalStrict need? If the stuck pair avoids those, the strict conditions hold for the needed k's. If not, need to handle the stuck k separately (it may correspond exactly to the cross-piece collision we exclude via the proper/full-closure split in FFCT100).
Target geometric lemma: `openedWBS_strict_closed_supports` (FFCT97-derived): the opened arm supplies CloseStrict + FinalStrict for the interior k's, from strict convexity of the ORIGINAL strict arm A + the opening geometry.

## Chain (corrected):
correctedDiscreteFenchel_closedStrict [planar, done-ish FFCT109] + openedWBS_strict_closed_supports [spherical, NEW] → openedWBS one_wind<2π → FFCT103/101/100 → Ch13.
Full ChatGPT design is in the conversation transcript (user pasted it 2026-06-13).
