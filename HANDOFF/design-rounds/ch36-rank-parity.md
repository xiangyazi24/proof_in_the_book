I’ll keep this entirely in finite combinatorics, check the landed ZinanCh36Comb.lean API, and use a strengthened splice induction so boundary signs lift automatically.

I found the file’s current reductions stop before the no-adjacency core. I’ll avoid the fragile lift by proving a stronger even-ν-path gap separation invariant instead.

1. Pick the winner

Use route 1 + route 4: a direct global parity argument via the upper-depth / rank-parity coloring. Do not finish by splice induction.

The splice frame is true, but the lift boundary condition is exactly the hard theorem in local disguise. The clean invariant is:

lean
σ a = σ base * (-1) ^ rankτ(a)

on the single ν-cycle. Equivalently, every ν-edge flips τ-rank parity; since σ also flips along every ν-edge and the ν-graph is connected, σ must equal rank parity up to one global sign.

This closes the no-adjacency lemma immediately: τ-adjacent elements have opposite rank parity, so they must have opposite σ.

2. Why depth works despite left/right ambiguity

Your objection is right locally: an upper chord’s left endpoint need not have a fixed sign. So “upper depth jumps up iff σ = +1” is false as a local rule.

The correct invariant is global:

lean
rank parity, not opener/closer status, determines σ.

For a noncrossing perfect matching, every chord connects opposite τ-rank parity. This is because the vertices strictly inside a chord are paired among themselves, hence there are evenly many of them. Since upper chords and lower chords are both noncrossing perfect matchings, every ν-edge flips τ-rank parity. The single-cycle hypothesis then forces σ to be the same bipartite coloring.

3. What is already banked

ZinanCh36Comb.lean already contains the intended standalone combinatorics file, TauInterleaves, the reduction from adjacent sign inequality to Alt, the sign-iterate parity lemma, and the gap-side split. 

ZinanCh36Comb

The existing useful endpoints are:

lean
alt_map_of_chain
sigma_iterate
even_of_reaches_same_sign
side_of_adjacent

alt_map_of_chain reduces the final theorem to proving that consecutive τ-sorted elements have distinct signs. 

ZinanCh36Comb

 The sign-iterate theorem and even-reach theorem are already present and should be reused, not reproved. 

ZinanCh36Comb

4. Add rank and interval primitives

Add this section after side_of_adjacent.

lean
def rank (S : Finset ι) (τ : ι → ℝ) (a : ι) : ℕ :=
  (S.filter fun z => τ z < τ a).card

def Inside (S : Finset ι) (τ : ι → ℝ) (a b : ι) : Finset ι :=
  S.filter fun z =>
    min (τ a) (τ b) < τ z ∧ τ z < max (τ a) (τ b)

Basic lemmas:

lean
theorem mem_inside_iff :
    z ∈ Inside S τ a b ↔
      z ∈ S ∧ min (τ a) (τ b) < τ z ∧ τ z < max (τ a) (τ b)

theorem not_endpoint_of_mem_inside
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hz : z ∈ Inside S τ a b) :
    z ≠ a ∧ z ≠ b

Justification: Inside is the open τ-interval between chord endpoints. Endpoint exclusion is immediate from strict inequalities and τ-injectivity.

Worker: 40–70 lines.

5. ν is a permutation on S

The current hypotheses give only ν maps into S and one-orbit reachability. Bank the permutation API once.

lean
theorem nu_surjOn_of_cycle
    [DecidableEq ι]
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a) :
    ∀ b ∈ S, ∃ a ∈ S, ν a = b
lean
theorem nu_injOn_of_cycle
    [DecidableEq ι]
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hsurj : ∀ b ∈ S, ∃ a ∈ S, ν a = b) :
    ∀ a ∈ S, ∀ b ∈ S, ν a = ν b → a = b
lean
noncomputable def nuPred
    [DecidableEq ι]
    (S : Finset ι) (ν : ι → ι) (b : ι) : ι := ...
lean
theorem nuPred_mem
    (hb : b ∈ S) : nuPred S ν b ∈ S

theorem nu_nuPred
    (hb : b ∈ S) : ν (nuPred S ν b) = b

Justification: if S is nonempty, hcycle gives a return path to any b. The σ-flip and σ = ±1 rule out a fixed-point singleton obstruction. Finite surjectivity gives injectivity. In Lean, it is often easier to prove surjectivity first and use Finset.card_image for injectivity.

Worker/master mix: 120–200 lines.

6. Upper mate stays inside

For a positive-start upper chord (a, ν a), prove that any positive vertex inside it has its upper mate inside.

lean
theorem pos_mate_inside_of_inside
    [DecidableEq ι]
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = 1 → σ b = 1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    {a z : ι}
    (ha : a ∈ S) (hσa : σ a = 1)
    (hz : z ∈ Inside S τ a (ν a))
    (hσz : σ z = 1) :
    ν z ∈ Inside S τ a (ν a)

Proof: if ν z is outside the open interval while z is inside, the chords {a,νa} and {z,νz} τ-interleave. This contradicts hposNI. The cases ν z = a or ν z = ν a are eliminated by signs and injectivity.

Worker: 100–160 lines.

Mirror for negative-start lower chords:

lean
theorem neg_mate_inside_of_inside
    ...
    (hnegNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = -1 → σ b = -1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    (hσa : σ a = -1)
    (hz : z ∈ Inside S τ a (ν a))
    (hσz : σ z = -1) :
    ν z ∈ Inside S τ a (ν a)

Worker: same proof, 60–100 lines after the positive version.

7. Negative inside vertices are also paired inside

For the upper family, a negative vertex inside is not a start of an upper chord; it is the endpoint of one. Use nuPred.

lean
theorem neg_inside_has_pos_pred_inside
    [DecidableEq ι]
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ...)
    {a z : ι}
    (ha : a ∈ S) (hσa : σ a = 1)
    (hz : z ∈ Inside S τ a (ν a))
    (hσz : σ z = -1) :
    let p := nuPred S ν z
    p ∈ Inside S τ a (ν a) ∧ σ p = 1 ∧ ν p = z

Proof: nuPred gives ν p = z. The flip rule gives σ p = 1. If p were outside the interval while z is inside, then the positive-start chord {p,z} would interleave with {a,νa}, contradicting upper noninterleaving.

Mirror for positive inside vertices under a lower chord:

lean
theorem pos_inside_has_neg_pred_inside ...

Master/worker: 120–180 lines.

8. Even interior count for every ν-edge

Now bank the key theorem.

lean
theorem inside_card_even_of_pos_chord
    [DecidableEq ι]
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ...)
    {a : ι} (ha : a ∈ S) (hσa : σ a = 1) :
    Even (Inside S τ a (ν a)).card

Proof: partition Inside into σ = 1 and σ = -1. The map ν is a bijection from positive-inside vertices to negative-inside vertices, by Sections 6 and 7. Therefore the inside card is twice the positive-inside card.

Lower version:

lean
theorem inside_card_even_of_neg_chord ... :
    Even (Inside S τ a (ν a)).card

Unified version:

lean
theorem inside_card_even_of_chord
    ... {a : ι} (ha : a ∈ S) :
    Even (Inside S τ a (ν a)).card := by
  rcases hpm a ha with hpos | hneg
  · exact inside_card_even_of_pos_chord ...
  · exact inside_card_even_of_neg_chord ...

This is the true replacement for the failed no-adjacency induction.

Master brick: 250–400 lines.

9. Rank parity flips along every ν-edge

Bank the rank-difference formula.

lean
theorem rank_eq_rank_add_inside_left
    [DecidableEq ι]
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (ha : a ∈ S) (hb : b ∈ S)
    (hab : τ a < τ b) :
    rank S τ b = rank S τ a + 1 + (Inside S τ a b).card

There is also the symmetric case with τ b < τ a; the same theorem can be used after swapping.

Then:

lean
theorem rank_parity_flip_of_chord
    [DecidableEq ι]
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ...)
    (hnegNI : ...)
    {a : ι} (ha : a ∈ S) :
    rank S τ (ν a) % 2 ≠ rank S τ a % 2

Proof: ν a ≠ a follows from σ (ν a) = -σ a and σ a = ±1. By τ-injectivity, τ a ≠ τ (ν a), so split </>. The rank-difference formula plus even inside-card says the difference is 1 mod 2.

Worker after Section 8: 100–170 lines.

10. Rank parity after k ν-steps

Add the rank analogue of the landed sign-iterate lemma.

lean
theorem rank_parity_iterate
    [DecidableEq ι]
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ...)
    (hnegNI : ...)
    {a : ι} (ha : a ∈ S) :
    ∀ k : ℕ,
      rank S τ (ν^[k] a) % 2 = (rank S τ a + k) % 2

Proof: induction on k. The step uses rank_parity_flip_of_chord at ν^[k] a, whose membership is already banked as iterate_mem. 

ZinanCh36Comb

Worker: 60–100 lines.

11. Adjacent same sign contradiction

This is the core no-adjacency lemma, now short.

lean
theorem no_same_sign_of_tau_adjacent
    [DecidableEq ι]
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ...)
    (hnegNI : ...)
    {a b : ι}
    (ha : a ∈ S) (hb : b ∈ S)
    (hab : τ a < τ b)
    (hgap : ∀ z ∈ S, ¬ (τ a < τ z ∧ τ z < τ b)) :
    σ a ≠ σ b

Proof:

Assume σ a = σ b.

By hcycle, get k with ν^[k] a = b.

Landed even_of_reaches_same_sign gives Even k. 

ZinanCh36Comb

rank_parity_iterate plus rank_eq_succ_of_adjacent gives Odd k.

Contradiction.

The adjacent rank lemma used here is:

lean
theorem rank_eq_succ_of_adjacent
    [DecidableEq ι]
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (ha : a ∈ S) (hb : b ∈ S)
    (hab : τ a < τ b)
    (hgap : ∀ z ∈ S, ¬ (τ a < τ z ∧ τ z < τ b)) :
    rank S τ b = rank S τ a + 1

Worker after Sections 8–10: 120–180 lines.

12. Final chain theorem

Use the current alt_map_of_chain.

lean
theorem alt_of_twoSide_noncrossing_cycle
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (τ : ι → ℝ) (σ : ι → ℤ) (ν : ι → ι)
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = 1 → σ b = 1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    (hnegNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = -1 → σ b = -1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    {L : List ι}
    (hnd : L.Nodup)
    (hmem : ∀ a, a ∈ L ↔ a ∈ S)
    (hsort : L.Pairwise (fun a b => τ a < τ b)) :
    Alt (L.map σ)

Proof: apply alt_map_of_chain. For every adjacent pair a :: b in L, hsort gives τ a < τ b. The list adjacency and hmem give the no-between hgap. Then invoke no_same_sign_of_tau_adjacent.

Worker: 80–140 lines once no-adjacency is banked.

13. Why this closes the splice lift

Your removed upper pair [B1,B2] is adjacent because its interior is empty. The lift needed σB1 ≠ σl.

The rank invariant gives it immediately:

lean
rank(B1) = rank(l) + 1
σ(B1) = globalSign * (-1) ^ rank(B1)
σ(l)  = globalSign * (-1) ^ rank(l)

So σB1 = -σl. No local upper interleaving across the empty gap is needed.

This also explains why the worker’s local attacks collapsed: the boundary sign is not encoded in the local innermost upper chord; it is encoded in the global fact that σ is the unique bipartite coloring of the connected meander graph.

14. Route adjudication

Route 1 succeeds if phrased as rank/depth parity, not opener/closer orientation. It gives the shortest Lean proof.

Route 2 is unnecessary. A strengthened IH would essentially reprove the rank invariant but with heavier splice bookkeeping.

Route 3 is unnecessary. Double-splice fixes the boundary symptom but creates more preservation lemmas than needed.

Route 4 is the clean proof frame. The “parenthesis balance” is: each same-side noncrossing family is a perfect matching, hence every chord encloses evenly many vertices; therefore every cycle edge flips τ-rank parity.

15. Implementation order

rank, Inside, endpoint lemmas.

nu_surjOn_of_cycle, nu_injOn_of_cycle, nuPred.

pos_mate_inside_of_inside, neg_mate_inside_of_inside.

predecessor-inside lemmas.

inside_card_even_of_pos_chord, inside_card_even_of_neg_chord.

rank_eq_rank_add_inside_left, rank_parity_flip_of_chord.

rank_parity_iterate.

no_same_sign_of_tau_adjacent.

alt_of_twoSide_noncrossing_cycle.

The only master brick is inside-card even, because it is where same-color noninterleaving becomes the perfect-matching parity fact. Everything after that is finite rank arithmetic.
