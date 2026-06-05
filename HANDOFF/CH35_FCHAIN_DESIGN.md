I’ll formulate the count as an abstract seam-chain permutation theorem, driven by the active-cycle invariant and local phiLift seam equations, then specialize it to the two faceCorr2 chains.

The invariant you want is the active seam-cycle invariant.

It is not a statement about how many old faces occur among the seam darts. It is a statement about the explicit arrows of the partial permutation

lean
P_j := phiLift * cycleOfList [a₀, ..., a_j].

After a cyclic rotation of one cap chain, put the chain in the normal form

lean
[γ₀, u₀, v₀, γ₁, u₁, v₁, ..., γ_{k-1}, u_{k-1}, v_{k-1}]

where

lean
phiLift γᵢ = γᵢ
phiLift uᵢ = vᵢ

for every i.

If your kernel-stored chain begins at a movable dart, rotate the cyclic list so that each block starts at the cap. If the local equation is stored as phiLift vᵢ = uᵢ, swap the names uᵢ and vᵢ or reverse the block convention. The abstract theorem only needs the block form

lean
cap, phiLift-predecessor, phiLift-successor.

The correct chain-extension pivot is:

lean
SameCycle P_j a_j a_{j+1}

not SameCycle P_j a₀ a_{j+1}.

Equivalently, in one-based indexing, if

lean
P_j = phiLift * (a₁ ... a_j),

then the next step

lean
P_{j+1} = P_j * swap a_j a_{j+1}

is controlled by

lean
SameCycle P_j a_j a_{j+1}.

If true, multiplying by the swap splits a cycle and raises numCycles by 1. If false, it merges two cycles and lowers numCycles by 1.

1. One-chain normal form

Let

lean
p := phiLift

and let one cap chain be represented by the list

lean
L :=
  [γ₀, u₀, v₀,
   γ₁, u₁, v₁,
   ...
   γ_{k-1}, u_{k-1}, v_{k-1}]

with

lean
L[3*i]     = γᵢ
L[3*i + 1] = uᵢ
L[3*i + 2] = vᵢ.

Assume:

lean
h_nodup : L.Nodup
h_cap   : ∀ i, p (γ i) = γ i
h_pair  : ∀ i, p (u i) = v i

The local equation p (u i) = v i is the seam incidence fact. It says: in the lifted old face permutation, the two movable darts in block i are consecutive in the required direction.

Nothing in the proof asks whether block i and block j lie in the same old face. Repeated old faces are harmless.

Define the prefix cycle

lean
C_j := cycleOfList (L.take (j + 1))
P_j := p * C_j.

Then

lean
C_{j+1} = C_j * swap L[j] L[j+1]
P_{j+1} = P_j * swap L[j] L[j+1].

So the cycle-count change at step j is:

lean
if SameCycle P_j L[j] L[j+1]
then +1   -- split
else -1   -- merge
2. Exact step bookkeeping

There are 3k - 1 transposition steps.

They split into three families.

Type A: γᵢ -- uᵢ

For every i : Fin k, the step

lean
swap γᵢ uᵢ

occurs at state

lean
P_{3*i}.

It is always a merge:

lean
¬ SameCycle (P (3*i)) (γ i) (u i)

so it contributes -1.

There are k such steps.

Type B: uᵢ -- vᵢ

For every i : Fin k, the step

lean
swap uᵢ vᵢ

occurs at state

lean
P_{3*i + 1}.

It is always a split:

lean
SameCycle (P (3*i + 1)) (u i) (v i)

so it contributes +1.

There are k such steps.

Type C: vᵢ -- γ_{i+1}

For every i < k - 1, the step

lean
swap vᵢ γ_{i+1}

occurs at state

lean
P_{3*i + 2}.

It is always a merge:

lean
¬ SameCycle (P (3*i + 2)) (v i) (γ (i+1))

so it contributes -1.

There are k - 1 such steps.

Therefore:

lean
#merges = k + (k - 1) = 2*k - 1
#splits = k

and

lean
Δ = #splits - #merges
  = k - (2*k - 1)
  = 1 - k
  = -(k - 1).

So one chain drops the cycle count by exactly k - 1.

The telescoping is:

γᵢ -- uᵢ      merge   -1
uᵢ -- vᵢ      split   +1

for every block, and the only unpaired losses are

vᵢ -- γ_{i+1} merge   -1

for i = 0, ..., k-2.

That is the invariant behind the count.

3. The active seam-cycle invariant

The proof rests on the explicit action of

lean
P_j = p * cycleOfList [a₀, ..., a_j].

For a nodup prefix

lean
[a₀, ..., a_j],

the action is:

lean
P_j a_r = p a_{r+1}   if r < j
P_j a_j = p a₀
P_j x   = p x         if x is not in the prefix.

Specialize this to the seam list.

3.1 Before γᵢ -- uᵢ

At state

lean
P_{3*i}
=
p * cycleOfList [γ₀,u₀,v₀, ..., γᵢ],

the current active cycle is exactly

lean
{γ₀, γ₁, ..., γᵢ} ∪ {v₀, v₁, ..., v_{i-1}}.

More explicitly, the arrows are:

γᵢ → γ₀ → v₀ → γ₁ → v₁ → ... → γ_{i-1} → v_{i-1} → γᵢ.

Why?

Because:

lean
P_{3*i} γᵢ = p γ₀ = γ₀
P_{3*i} γ_r = p u_r = v_r       for r < i
P_{3*i} v_r = p γ_{r+1} = γ_{r+1}  for r < i

Thus:

lean
SameCycle (P (3*i)) (γ i) x
↔
(∃ r ≤ i, x = γ r) ∨ (∃ r < i, x = v r).

Since the seam list is nodup,

lean
uᵢ ∉ {γ₀, ..., γᵢ} ∪ {v₀, ..., v_{i-1}}.

Therefore:

lean
¬ SameCycle (P (3*i)) (γ i) (u i).

So γᵢ -- uᵢ is a merge.

Important: for i > 0, γᵢ is not necessarily untouched anymore. It was touched by the previous bridge step v_{i-1} -- γᵢ. The proof is not “γᵢ is fixed.” The proof is the stronger active-cycle description above.

3.2 Before uᵢ -- vᵢ

At state

lean
P_{3*i + 1}
=
p * cycleOfList [γ₀,u₀,v₀, ..., γᵢ,uᵢ],

there is a directed path

uᵢ → γ₀ → v₀ → γ₁ → v₁ → ... → γᵢ → vᵢ.

Indeed:

lean
P_{3*i+1} uᵢ = p γ₀ = γ₀
P_{3*i+1} γ_r = p u_r = v_r      for r < i
P_{3*i+1} v_r = p γ_{r+1} = γ_{r+1} for r < i
P_{3*i+1} γᵢ = p uᵢ = vᵢ

The last equality is the local seam-pair fact.

Hence:

lean
SameCycle (P (3*i + 1)) (u i) (v i).

So uᵢ -- vᵢ is a split.

This is the key point: the movable-movable step is a split because the cap-prefix has already made uᵢ and vᵢ lie in the same current orbit. It is not a global old-face count.

3.3 Before vᵢ -- γ_{i+1}

At state

lean
P_{3*i + 2}
=
p * cycleOfList [γ₀,u₀,v₀, ..., γᵢ,uᵢ,vᵢ],

the active cycle is exactly

lean
{γ₀, γ₁, ..., γᵢ} ∪ {v₀, v₁, ..., vᵢ}.

The arrows are:

vᵢ → γ₀ → v₀ → γ₁ → v₁ → ... → γᵢ → vᵢ.

Indeed:

lean
P_{3*i+2} vᵢ = p γ₀ = γ₀
P_{3*i+2} γ_r = p u_r = v_r        for r ≤ i
P_{3*i+2} v_r = p γ_{r+1} = γ_{r+1}  for r < i

Thus:

lean
SameCycle (P (3*i + 2)) (v i) x
↔
(∃ r ≤ i, x = γ r) ∨ (∃ r ≤ i, x = v r).

For i < k - 1, nodup gives:

lean
γ_{i+1} ∉ {γ₀, ..., γᵢ} ∪ {v₀, ..., vᵢ}.

Therefore:

lean
¬ SameCycle (P (3*i + 2)) (v i) (γ (i+1)).

So vᵢ -- γ_{i+1} is a merge.

These k - 1 bridge merges are exactly the net loss.

4. Why old face repetitions do not matter

The old face data only supplies the local equations

lean
phiLift uᵢ = vᵢ.

After a seam prefix has been multiplied in, the active cycle no longer follows arbitrary old phiLift orbits through already-processed seam darts. Those arrows have been rewired by the right multiplication with the chain prefix.

For example, at state P_{3*i+2}, the active cycle is closed:

vᵢ → γ₀ → v₀ → γ₁ → v₁ → ... → γᵢ → vᵢ.

Since this is already a closed cycle of a permutation, no later old dart can secretly belong to it, even if it lies in the same original phiLift-face orbit.

So the invariant is not:

lean
number of distinct old faces touched by the cycle

but rather:

lean
the exact current active cycle under the partial product.

That is why the count is independent of repeated faces and genus.

5. Abstract Lean-ready theorem

First prove the pure permutation theorem.

lean
structure SeamChainData
    (X : Type*) [Fintype X] [DecidableEq X] where
  p : Equiv.Perm X
  k : Nat
  hk : 0 < k

  γ : Fin k → X
  u : Fin k → X
  v : Fin k → X

  nodup_seam :
    (seamList γ u v).Nodup

  cap_fixed :
    ∀ i, p (γ i) = γ i

  seam_pair :
    ∀ i, p (u i) = v i

where

lean
def seamList {k : Nat}
    (γ u v : Fin k → X) : List X :=
  (List.finRange k).bind fun i => [γ i, u i, v i]

Define:

lean
def chainPrefixPerm (S : SeamChainData X) (j : Nat) : Equiv.Perm X :=
  S.p * cycleOfList ((seamList S.γ S.u S.v).take (j + 1))

Abbreviate:

lean
P_S j := chainPrefixPerm S j

Then the three step lemmas are:

lean
lemma seam_gamma_u_step_merge
    (S : SeamChainData X)
    (i : Fin S.k) :
  ¬ SameCycle (P_S S (3*i.val)) (S.γ i) (S.u i)
lean
lemma seam_u_v_step_split
    (S : SeamChainData X)
    (i : Fin S.k) :
  SameCycle (P_S S (3*i.val + 1)) (S.u i) (S.v i)
lean
lemma seam_v_gamma_step_merge
    (S : SeamChainData X)
    (i : Fin (S.k - 1)) :
  ¬ SameCycle
      (P_S S (3*i.val + 2))
      (S.v i.cast)
      (S.γ i.succ)

Then the one-chain count is:

lean
theorem numCycles_mul_seamChain_delta
    (S : SeamChainData X) :
  ((numCycles
      (S.p * cycleOfList (seamList S.γ S.u S.v)) : Int)
    - (numCycles S.p : Int))
  =
  - ((S.k : Int) - 1)

The proof is:

lean
calc
  ((numCycles
      (S.p * cycleOfList (seamList S.γ S.u S.v)) : Int)
    - (numCycles S.p : Int))
      =
        ∑ j in Finset.range (3*S.k - 1),
          (if SameCycle
                (P_S S j)
                ((seamList S.γ S.u S.v).get ⟨j, by omega⟩)
                ((seamList S.γ S.u S.v).get ⟨j+1, by omega⟩)
           then (1 : Int) else (-1 : Int)) := by
          exact numCycles_chain_walk_delta ...
  _ =
        (∑ i in Finset.range S.k, (-1 : Int))
      + (∑ i in Finset.range S.k, ( 1 : Int))
      + (∑ i in Finset.range (S.k - 1), (-1 : Int)) := by
          -- split the range into j = 3i, 3i+1, 3i+2
          -- use the three step-classification lemmas
          ...
  _ = - ((S.k : Int) - 1) := by
          omega

The important part is the range split:

lean
j = 3*i       -- γᵢ -- uᵢ : merge
j = 3*i + 1   -- uᵢ -- vᵢ : split
j = 3*i + 2   -- vᵢ -- γ_{i+1} : merge, only for i < k - 1
6. The generic permutation API needed
6.1 Same-cycle relation

Use your existing orbit relation, but the lemmas needed are:

lean
lemma sameCycle_refl :
  SameCycle p x x

lemma sameCycle_symm :
  SameCycle p x y → SameCycle p y x

lemma sameCycle_trans :
  SameCycle p x y → SameCycle p y z → SameCycle p x z
6.2 Swap dichotomy

The standard transposition dichotomy should be in integer form:

lean
lemma numCycles_mul_swap_delta
    (p : Equiv.Perm X) (x y : X) :
  ((numCycles (p * Equiv.swap x y) : Int)
    - (numCycles p : Int))
  =
  if SameCycle p x y then 1 else -1

Equivalent Nat versions:

lean
lemma numCycles_mul_swap_of_sameCycle
    (h : SameCycle p x y) :
  numCycles (p * Equiv.swap x y) = numCycles p + 1
lean
lemma numCycles_mul_swap_of_not_sameCycle
    (h : ¬ SameCycle p x y) :
  numCycles (p * Equiv.swap x y) + 1 = numCycles p

Use the integer version for summing.

6.3 List cycle prefix step

For the list cycle orientation

lean
cycleOfList [a₀, ..., a_j] = (a₀ a₁ ... a_j),

prove:

lean
lemma cycleOfList_take_succ
    (h : j + 1 < L.length) :
  cycleOfList (L.take (j + 2))
    =
  cycleOfList (L.take (j + 1))
    * Equiv.swap (L.get ⟨j, by omega⟩)
                 (L.get ⟨j+1, by omega⟩)

Then:

lean
lemma prefixPerm_succ
    (h : j + 1 < L.length) :
  p * cycleOfList (L.take (j + 2))
    =
  (p * cycleOfList (L.take (j + 1)))
    * Equiv.swap (L.get ⟨j, by omega⟩)
                 (L.get ⟨j+1, by omega⟩)

This gives the walk.

6.4 List-cycle action formula

For a nodup nonempty list L:

lean
lemma mul_cycleOfList_apply_of_mem_not_last
    (hN : L.Nodup)
    (hr : r + 1 < L.length) :
  (p * cycleOfList L) (L.get ⟨r, by omega⟩)
    =
  p (L.get ⟨r+1, by omega⟩)
lean
lemma mul_cycleOfList_apply_last
    (hN : L.Nodup)
    (hL : 0 < L.length) :
  (p * cycleOfList L) (L.get ⟨L.length - 1, by omega⟩)
    =
  p (L.get ⟨0, by omega⟩)
lean
lemma mul_cycleOfList_apply_of_not_mem
    (hx : x ∉ L) :
  (p * cycleOfList L) x = p x

These are enough to prove the active-cycle lemmas.

7. Active-cycle lemmas in Lean form

Define active sets:

lean
def ActiveBeforeGammaU
    (S : SeamChainData X) (i : Fin S.k) : Set X :=
  {x | (∃ r : Fin S.k, r.val ≤ i.val ∧ x = S.γ r) ∨
       (∃ r : Fin S.k, r.val < i.val ∧ x = S.v r)}
lean
def ActiveBeforeVGamma
    (S : SeamChainData X) (i : Fin S.k) : Set X :=
  {x | (∃ r : Fin S.k, r.val ≤ i.val ∧ x = S.γ r) ∨
       (∃ r : Fin S.k, r.val ≤ i.val ∧ x = S.v r)}

Then prove:

lean
lemma sameCycle_P3i_gamma_iff
    (S : SeamChainData X)
    (i : Fin S.k) :
  SameCycle (P_S S (3*i.val)) (S.γ i) x
    ↔
  x ∈ ActiveBeforeGammaU S i

Proof: exhibit the closed cycle

γᵢ → γ₀ → v₀ → γ₁ → v₁ → ... → γᵢ.

Use the action formula plus:

lean
S.cap_fixed
S.seam_pair
S.nodup_seam

Then:

lean
lemma sameCycle_P3i1_u_v
    (S : SeamChainData X)
    (i : Fin S.k) :
  SameCycle (P_S S (3*i.val + 1)) (S.u i) (S.v i)

Proof: exhibit the forward path

uᵢ → γ₀ → v₀ → γ₁ → v₁ → ... → γᵢ → vᵢ.

Finally:

lean
lemma sameCycle_P3i2_v_iff
    (S : SeamChainData X)
    (i : Fin S.k) :
  SameCycle (P_S S (3*i.val + 2)) (S.v i) x
    ↔
  x ∈ ActiveBeforeVGamma S i

Proof: exhibit the closed cycle

vᵢ → γ₀ → v₀ → γ₁ → v₁ → ... → γᵢ → vᵢ.

The step classification then becomes short.

lean
lemma seam_gamma_u_step_merge
    (S : SeamChainData X)
    (i : Fin S.k) :
  ¬ SameCycle (P_S S (3*i.val)) (S.γ i) (S.u i) := by
  intro h
  have hmem :
      S.u i ∈ ActiveBeforeGammaU S i :=
    (sameCycle_P3i_gamma_iff S i).mp h
  exact nodup_seam_not_u_in_activeBeforeGammaU S i hmem
lean
lemma seam_u_v_step_split
    (S : SeamChainData X)
    (i : Fin S.k) :
  SameCycle (P_S S (3*i.val + 1)) (S.u i) (S.v i) :=
by
  exact sameCycle_P3i1_u_v S i
lean
lemma seam_v_gamma_step_merge
    (S : SeamChainData X)
    (i : Fin (S.k - 1)) :
  ¬ SameCycle
      (P_S S (3*i.val + 2))
      (S.v i.cast)
      (S.γ i.succ) := by
  intro h
  have hmem :
      S.γ i.succ ∈ ActiveBeforeVGamma S i.cast :=
    (sameCycle_P3i2_v_iff S i.cast).mp h
  exact nodup_seam_not_next_gamma_in_activeBeforeVGamma S i hmem

The two nodup consequences are purely list-index facts.

8. Instantiating the theorem for the plus chain

For the plus chain, define:

lean
def plusSeamData : SeamChainData Dcut where
  p := phiLift
  k := k
  hk := hk
  γ := plusCap
  u := plusMovableIn
  v := plusMovableOut
  nodup_seam := plus_seamList_nodup
  cap_fixed := by
    intro i
    exact phiLift_plusCap_fixed i
  seam_pair := by
    intro i
    exact phiLift_plusMovableIn_eq_plusMovableOut i

The required map-specific facts are exactly:

lean
plusCorr_cycleOfList :
  plusCorr =
    cycleOfList
      (seamList plusCap plusMovableIn plusMovableOut)
lean
plus_seamList_nodup :
  (seamList plusCap plusMovableIn plusMovableOut).Nodup
lean
phiLift_plusCap_fixed :
  ∀ i, phiLift (plusCap i) = plusCap i
lean
phiLift_plusMovableIn_eq_plusMovableOut :
  ∀ i, phiLift (plusMovableIn i) = plusMovableOut i

Then:

lean
lemma plus_chain_drop :
  ((numCycles (phiLift * plusCorr) : Int)
    - (numCycles phiLift : Int))
  =
  - ((k : Int) - 1) := by
  rw [plusCorr_cycleOfList]
  exact numCycles_mul_seamChain_delta plusSeamData

This is the first -(k-1) drop.

9. The second chain after the first chain

Let

lean
p₁ := phiLift * plusCorr

The minus chain must be counted relative to p₁, not relative to phiLift.

Because the plus and minus correction cycles have disjoint supports, plusCorr fixes every minus seam dart.

The support lemma should be:

lean
lemma plusCorr_fixes_minusSeamSupport
    {x : Dcut}
    (hx : x ∈ minusSeamSupport) :
  plusCorr x = x

where

lean
minusSeamSupport =
  {minusCap i} ∪ {minusMovableIn i} ∪ {minusMovableOut i}.

Then:

lean
lemma p₁_agrees_phiLift_on_minusSeam
    {x : Dcut}
    (hx : x ∈ minusSeamSupport) :
  p₁ x = phiLift x := by
  unfold p₁
  rw [Equiv.Perm.mul_apply]
  rw [plusCorr_fixes_minusSeamSupport hx]

Therefore:

lean
lemma p₁_minusCap_fixed :
  ∀ i, p₁ (minusCap i) = minusCap i := by
  intro i
  rw [p₁_agrees_phiLift_on_minusSeam]
  · exact phiLift_minusCap_fixed i
  · exact minusCap_mem_minusSeamSupport i

and:

lean
lemma p₁_minusMovableIn_eq_minusMovableOut :
  ∀ i, p₁ (minusMovableIn i) = minusMovableOut i := by
  intro i
  rw [p₁_agrees_phiLift_on_minusSeam]
  · exact phiLift_minusMovableIn_eq_minusMovableOut i
  · exact minusMovableIn_mem_minusSeamSupport i

So define:

lean
def minusSeamDataAfterPlus : SeamChainData Dcut where
  p := phiLift * plusCorr
  k := k
  hk := hk
  γ := minusCap
  u := minusMovableIn
  v := minusMovableOut
  nodup_seam := minus_seamList_nodup
  cap_fixed := p₁_minusCap_fixed
  seam_pair := p₁_minusMovableIn_eq_minusMovableOut

Using:

lean
minusCorr_cycleOfList :
  minusCorr =
    cycleOfList
      (seamList minusCap minusMovableIn minusMovableOut)

you get:

lean
lemma minus_chain_drop_after_plus :
  ((numCycles (phiLift * plusCorr * minusCorr) : Int)
    - (numCycles (phiLift * plusCorr) : Int))
  =
  - ((k : Int) - 1) := by
  rw [minusCorr_cycleOfList]
  exact numCycles_mul_seamChain_delta minusSeamDataAfterPlus

So yes: the second chain is independent in precisely the required sense. The first chain does not alter the local seam equations of the second chain because the two chain supports are disjoint.

You do not need a projection semiconjugacy. You do not need a conjugation argument. You only need:

lean
plusCorr x = x

on the minus seam support.

10. Final face-count calculation

You already have:

lean
phiPrime2_factorization :
  phi'2 = phiLift * faceCorr2
lean
faceCorr2_eq_plus_mul_minus :
  faceCorr2 = plusCorr * minusCorr
lean
numCycles_phiLift :
  numCycles phiLift = F + 2*k

Together with:

lean
plus_chain_drop :
  ((numCycles (phiLift * plusCorr) : Int)
    - (numCycles phiLift : Int))
  =
  - ((k : Int) - 1)

and:

lean
minus_chain_drop_after_plus :
  ((numCycles (phiLift * plusCorr * minusCorr) : Int)
    - (numCycles (phiLift * plusCorr) : Int))
  =
  - ((k : Int) - 1)

the calculation is:

lean
calc
  (numCycles phi'2 : Int)
      =
    (numCycles (phiLift * plusCorr * minusCorr) : Int) := by
      rw [phiPrime2_factorization, faceCorr2_eq_plus_mul_minus]
  _ =
    (numCycles (phiLift * plusCorr) : Int)
      - ((k : Int) - 1) := by
      linarith [minus_chain_drop_after_plus]
  _ =
    (numCycles phiLift : Int)
      - ((k : Int) - 1)
      - ((k : Int) - 1) := by
      linarith [plus_chain_drop]
  _ =
    ((F : Int) + 2*(k : Int))
      - ((k : Int) - 1)
      - ((k : Int) - 1) := by
      rw [numCycles_phiLift]
  _ =
    (F : Int) + 2 := by
      ring

Then convert back to Nat:

lean
theorem numFaces_cutCapMap2 :
  F' = F + 2 := by
  have hInt :
      (F' : Int) = (F : Int) + 2 := by
    exact face_count_int
  omega

where F' is numCycles phi'2.

11. Dependency-ordered implementation list
Layer A: generic permutation lemmas
lean
SameCycle
sameCycle_refl
sameCycle_symm
sameCycle_trans
numCycles_mul_swap_delta

The critical dichotomy:

lean
((numCycles (p * swap x y) : Int) - (numCycles p : Int))
=
if SameCycle p x y then 1 else -1
Layer B: list-cycle walk
lean
cycleOfList
cycleOfList_take_succ
prefixPerm_succ
numCycles_chain_walk_delta

where the pivot is always:

lean
SameCycle P_j L[j] L[j+1].
Layer C: list-cycle action
lean
mul_cycleOfList_apply_of_mem_not_last
mul_cycleOfList_apply_last
mul_cycleOfList_apply_of_not_mem

These give the exact arrows of P_j.

Layer D: abstract seam chain

Definitions:

lean
seamList
SeamChainData
P_S
ActiveBeforeGammaU
ActiveBeforeVGamma

Active-cycle invariants:

lean
sameCycle_P3i_gamma_iff
sameCycle_P3i1_u_v
sameCycle_P3i2_v_iff

Step classification:

lean
seam_gamma_u_step_merge
seam_u_v_step_split
seam_v_gamma_step_merge

One-chain count:

lean
numCycles_mul_seamChain_delta
Layer E: plus chain

Map-specific facts:

lean
plusCorr_cycleOfList
plus_seamList_nodup
phiLift_plusCap_fixed
phiLift_plusMovableIn_eq_plusMovableOut

Then:

lean
plusSeamData
plus_chain_drop
Layer F: minus chain after plus

Support facts:

lean
plus_minus_chain_support_disjoint
plusCorr_fixes_minusSeamSupport
p₁_agrees_phiLift_on_minusSeam

Local equations:

lean
p₁_minusCap_fixed
p₁_minusMovableIn_eq_minusMovableOut

Then:

lean
minusSeamDataAfterPlus
minus_chain_drop_after_plus
Layer G: final face count

Use:

lean
phiPrime2_factorization
faceCorr2_eq_plus_mul_minus
numCycles_phiLift
plus_chain_drop
minus_chain_drop_after_plus

to prove:

lean
numCycles_phiPrime2 :
  numCycles phi'2 = F + 2

and therefore:

lean
F'_eq_F_add_two :
  F' = F + 2
12. The final invariant in one sentence

For each chain block

lean
γᵢ, uᵢ, vᵢ

with

lean
phiLift γᵢ = γᵢ
phiLift uᵢ = vᵢ,

the partial product has the following forced pattern:

before γᵢ -- uᵢ:
  uᵢ is outside the active seam cycle,
  so γᵢ -- uᵢ is a merge.

before uᵢ -- vᵢ:
  uᵢ and vᵢ are already in the active seam cycle,
  so uᵢ -- vᵢ is a split.

before vᵢ -- γ_{i+1}:
  γ_{i+1} is outside the active seam cycle,
  so vᵢ -- γ_{i+1} is a merge.

Thus each block has a cancelling merge/split pair, and the only net losses are the k - 1 inter-block cap merges. This gives the per-chain drop

lean
-(k - 1)

and the two chains give

lean
F' = F + 2.