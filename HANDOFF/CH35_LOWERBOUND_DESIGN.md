I’ll abandon old-face invariance and chain-shape assumptions, targeting only the lower bound via a quotient/coarsening argument on final phi'2 orbits. The promising variants are collapsing seam/cap gadgets, counting boundary-side fragments plus cap closures, or injecting old faces plus one forced cap class.

The orbit-label route is dead given the K4-sphere counterexample. The robust replacement is a one-sided transposition-walk certificate.

The key reduction is:

You do not need to classify all merge/split steps.
It is enough to exhibit k forced split steps in a fixed transposition word for faceCorr2.

If faceCorr2 is represented by a fixed word of length 4k - 2, then starting from

lean
numCycles phiLift = F + 2*k

and proving merely k forced splits gives

lean
numCycles (phiLift * faceCorr2)
  ≥ (F + 2*k) - (4*k - 2) + 2*k
  = F + 2.

So the lower bound is actually the full desired lower bound:

lean
F' ≥ F + 2.

This is genus-free and does not use the cycle structure of faceCorr2.

0. Important correction about parity

The parity argument is valid only from a verified transposition word or sign computation.

If you have a word

lean
faceCorr2 = t₀ * t₁ * ... * t_{m-1}

then

lean
numCycles (phiLift * faceCorr2)
  ≡ numCycles phiLift + m  [MOD 2].

So if m = 4*k - 2, then m is even and

lean
F' ≡ F + 2*k ≡ F  [MOD 2].

But do not infer parity from a visually reported unstable cycle structure unless that report is for the exact same permutation and convention. For example, a 6-cycle disjoint a 3-cycle has odd sign, hence would flip cycle-count parity relative to phiLift. If your verified F' - F = 2, then either that reported structure is not the same permutation, not the same side convention, or there are additional moved cycles omitted. The safe proof should use the verified fixed transposition word, not the unstable cycle display.

1. Chosen route

Use route E, but only one-sided.

You need a theorem of this form:

lean
theorem numCycles_lower_of_forced_splits
  (p : Equiv.Perm X)
  (W : Fin m → Swap X)
  (splitIdx : Fin s → Fin m)
  (hsinj : Function.Injective splitIdx)
  (hforced :
    ∀ i : Fin s,
      SameCycle
        (prefixPerm p W (splitIdx i).val)
        (W (splitIdx i)).x
        (W (splitIdx i)).y) :
  (numCycles (prefixPerm p W m) : Int)
    ≥
  (numCycles p : Int) - m + 2*s

Then instantiate with:

lean
p := phiLift
m := 4*k - 2
s := k
W := faceCorrWord

and:

lean
prefixPerm phiLift faceCorrWord (4*k - 2)
  = phiLift * faceCorr2
  = phi'2.

This gives:

lean
F' ≥ F + 2.

This is stronger than the requested F' ≥ F + 1.

2. Generic transposition-walk API

Define a swap record:

lean
structure Swap (X : Type*) where
  x : X
  y : X

Its permutation is:

lean
def Swap.perm [DecidableEq X] (s : Swap X) : Equiv.Perm X :=
  Equiv.swap s.x s.y

A transposition word:

lean
W : Fin m → Swap X

The prefix product before step j:

lean
def prefixPerm
    [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X)
    (j : Nat) : Equiv.Perm X :=
  p * Finset.prod
    (Finset.range j)
    (fun r =>
      if h : r < m then
        (W ⟨r, h⟩).perm
      else
        1)

For easier Lean work, define this recursively instead:

lean
def prefixPerm
    [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X) :
    Nat → Equiv.Perm X
| 0 =>
    p
| j + 1 =>
    if h : j < m then
      prefixPerm p W j * (W ⟨j, h⟩).perm
    else
      prefixPerm p W j

Then prove:

lean
lemma prefixPerm_succ
    [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X)
    {j : Nat}
    (hj : j < m) :
  prefixPerm p W (j+1)
    =
  prefixPerm p W j * (W ⟨j, hj⟩).perm := by
  simp [prefixPerm, hj]
3. Swap dichotomy

You already have this toolkit, but the exact form needed is the integer delta form.

lean
lemma numCycles_mul_swap_delta
    [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    (x y : X) :
  ((numCycles (p * Equiv.swap x y) : Int)
    - (numCycles p : Int))
  =
  if SameCycle p x y then 1 else -1

Then for a word step:

lean
lemma prefix_step_delta
    [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X)
    {j : Nat}
    (hj : j < m) :
  ((numCycles (prefixPerm p W (j+1)) : Int)
    - (numCycles (prefixPerm p W j) : Int))
  =
  if SameCycle
      (prefixPerm p W j)
      (W ⟨j, hj⟩).x
      (W ⟨j, hj⟩).y
  then 1 else -1 := by
  rw [prefixPerm_succ p W hj]
  exact numCycles_mul_swap_delta
    (prefixPerm p W j)
    (W ⟨j, hj⟩).x
    (W ⟨j, hj⟩).y
4. One-sided lower bound from forced splits

Define the step contribution:

lean
def stepDelta
    [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X)
    (j : Fin m) : Int :=
  if SameCycle
      (prefixPerm p W j.val)
      (W j).x
      (W j).y
  then 1 else -1

Telescoping:

lean
lemma numCycles_prefix_telescopes
    [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X) :
  ((numCycles (prefixPerm p W m) : Int)
    - (numCycles p : Int))
  =
  ∑ j : Fin m, stepDelta p W j

Proof by induction on m or by summing prefix_step_delta.

Now suppose you have s certified split indices:

lean
splitIdx : Fin s → Fin m

with:

lean
hsinj : Function.Injective splitIdx

and:

lean
hforced :
  ∀ i : Fin s,
    SameCycle
      (prefixPerm p W (splitIdx i).val)
      (W (splitIdx i)).x
      (W (splitIdx i)).y

Then each certified index contributes +1; every uncertified index contributes at least -1.

Formal lemma:

lean
lemma sum_stepDelta_lower_of_forced_splits
    [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m s : Nat}
    (W : Fin m → Swap X)
    (splitIdx : Fin s → Fin m)
    (hsinj : Function.Injective splitIdx)
    (hforced :
      ∀ i : Fin s,
        SameCycle
          (prefixPerm p W (splitIdx i).val)
          (W (splitIdx i)).x
          (W (splitIdx i)).y) :
  (∑ j : Fin m, stepDelta p W j)
    ≥
  (-(m : Int) + 2*(s : Int)) := by
  -- Let S be the finset image of splitIdx.
  -- On S, stepDelta = +1.
  -- Off S, stepDelta ≥ -1.
  -- Therefore sum ≥ s*(+1) + (m-s)*(-1) = -m + 2s.
  classical
  let S : Finset (Fin m) := Finset.univ.image splitIdx

  have hcardS : S.card = s := by
    simpa [S] using
      Finset.card_image_iff.mpr
        (by
          intro a _ b _ h
          exact hsinj h)

  have h_on :
      ∀ j ∈ S, stepDelta p W j = 1 := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, _, rfl⟩
    simp [stepDelta, hforced i]

  have h_off :
      ∀ j : Fin m, j ∉ S → stepDelta p W j ≥ (-1 : Int) := by
    intro j hj
    unfold stepDelta
    by_cases h :
      SameCycle
        (prefixPerm p W j.val)
        (W j).x
        (W j).y
    · simp [h]
    · simp [h]

  -- Split the total sum into S and Sᶜ.
  -- The S part is exactly s.
  -- The complement part is at least -(m-s).
  -- Finish by omega.
  exact by
    -- In actual Lean, use Finset.sum_filter / sum_sdiff,
    -- then h_on, h_off, hcardS, and omega.
    omega

Then:

lean
theorem numCycles_lower_of_forced_splits
    [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m s : Nat}
    (W : Fin m → Swap X)
    (splitIdx : Fin s → Fin m)
    (hsinj : Function.Injective splitIdx)
    (hforced :
      ∀ i : Fin s,
        SameCycle
          (prefixPerm p W (splitIdx i).val)
          (W (splitIdx i)).x
          (W (splitIdx i)).y) :
  (numCycles (prefixPerm p W m) : Int)
    ≥
  (numCycles p : Int) - (m : Int) + 2*(s : Int) := by
  have htel := numCycles_prefix_telescopes p W
  have hsum :=
    sum_stepDelta_lower_of_forced_splits
      p W splitIdx hsinj hforced
  linarith

This is the main generic reduction.

5. The cut-and-cap forced-split certificate

Now define the data you need from the closed forms.

lean
structure FaceCorrLowerCert where
  m : Nat
  hm : m = 4*k - 2

  W : Fin m → Swap Dcut

  word_eq :
    Finset.prod Finset.univ (fun j : Fin m => (W j).perm)
      =
    faceCorr2

  splitIdx : Fin k → Fin m

  splitIdx_injective :
    Function.Injective splitIdx

  forced_split :
    ∀ i : Fin k,
      SameCycle
        (prefixPerm phiLift W (splitIdx i).val)
        (W (splitIdx i)).x
        (W (splitIdx i)).y

Then the lower bound is immediate.

lean
theorem faceCorr_lower_from_cert
    (C : FaceCorrLowerCert) :
  (numCycles (phiLift * faceCorr2) : Int)
    ≥
  (numCycles phiLift : Int) - (4*k - 2 : Int) + 2*(k : Int) := by
  have hprefix :
      prefixPerm phiLift C.W C.m = phiLift * faceCorr2 := by
    -- unfold prefixPerm at full length and use C.word_eq
    -- orientation must match your word convention
    simpa [prefixPerm, C.word_eq]

  have h :=
    numCycles_lower_of_forced_splits
      phiLift
      C.W
      C.splitIdx
      C.splitIdx_injective
      C.forced_split

  rw [hprefix] at h
  simpa [C.hm] using h

Using:

lean
numCycles_phiLift :
  numCycles phiLift = F + 2*k

you get:

lean
theorem phiPrime_faces_lower :
  (numCycles phi'2 : Int) ≥ (F : Int) + 2 := by
  have hfac :
      phi'2 = phiLift * faceCorr2 := phiPrime2_factorization

  have hlow :
      (numCycles (phiLift * faceCorr2) : Int)
        ≥
      (numCycles phiLift : Int) - (4*k - 2 : Int) + 2*(k : Int) :=
    faceCorr_lower_from_cert lowerCert

  have hphi :
      (numCycles phiLift : Int) = (F : Int) + 2*(k : Int) := by
    exact_mod_cast numCycles_phiLift

  rw [← hfac]
  nlinarith

Arithmetic:

lean
(F + 2k) - (4k - 2) + 2k = F + 2.

So:

lean
theorem F'_ge_F_add_two :
  F' ≥ F + 2

in Nat, by converting the integer inequality back with omega.

6. How to prove the forced_split field from closed forms

This is where the per-class closed forms enter.

For each cycle edge index i : Fin k, choose one distinguished step in the fixed word:

lean
splitIdx i

This should be the local “closing” transposition for that edge. Its endpoints are some pair:

lean
closeL i := (W (splitIdx i)).x
closeR i := (W (splitIdx i)).y

The forced split lemma is:

lean
lemma forced_split_at_edge
    (i : Fin k) :
  SameCycle
    (prefixPerm phiLift W (splitIdx i).val)
    (closeL i)
    (closeR i)

You should not prove this by old-face labels. You prove it by an explicit local path under the current prefix permutation.

The robust shape is:

lean
closeL i
  --prefix--> z₁
  --prefix--> z₂
  ...
  --prefix--> closeR i

where every arrow is a closed-form rewrite for the prefix permutation before the split step.

Formal path helper:

lean
inductive PermPath (q : Equiv.Perm X) : X → X → Prop
| nil  : ∀ x, PermPath q x x
| step : ∀ {x y z}, q x = y → PermPath q y z → PermPath q x z

lemma sameCycle_of_permPath
    {q : Equiv.Perm X}
    {x y : X}
    (h : PermPath q x y) :
  SameCycle q x y := by
  induction h with
  | nil x =>
      exact SameCycle.refl _
  | step hxy hpath ih =>
      exact SameCycle.trans
        (sameCycle_of_apply_eq hxy)
        ih

Then each forced split is proved by a small closed-form path:

lean
lemma forced_split_at_edge
    (i : Fin k) :
  SameCycle
    (prefixPerm phiLift W (splitIdx i).val)
    (closeL i)
    (closeR i) := by
  apply sameCycle_of_permPath

  -- The path below is schematic. Replace the nodes with the
  -- actual per-class names from cutCapMap2.
  refine PermPath.step ?h₁
    (PermPath.step ?h₂
      (PermPath.step ?h₃
        (PermPath.nil _)))

  · simp [
      closeL,
      closeR,
      prefixPerm_before_split_closedForm_1,
      cycle_index_simp
    ]

  · simp [
      prefixPerm_before_split_closedForm_2,
      cycle_index_simp
    ]

  · simp [
      prefixPerm_before_split_closedForm_3,
      cycle_index_simp
    ]

The important point is that these paths are local. They use only:

lean
prefixPerm phiLift W (splitIdx i).val

and the closed-form equations for its action on a bounded list of seam/cap darts.

They do not mention old face orbits. They do not mention genus. They do not mention the cycle structure of faceCorr2.

7. What the forced split is conceptually

Each cycle edge contributes one local forced split.

In every case, the distinguished transposition has endpoints already in the same current orbit because the prefix has just installed a small local seam path between them.

Abstractly, for each i, the closed forms should prove a pattern of the following kind:

lean
P_i := prefixPerm phiLift W (splitIdx i).val

P_i (closeL i) = local₁ i
P_i (local₁ i) = local₂ i
...
P_i (local_r i) = closeR i

Therefore:

lean
SameCycle P_i (closeL i) (closeR i).

That step is a split, no matter how all the other orbits weave globally.

This is the conservation law:

The 4k - 2-step correction word contains k locally forced splits, one per cut edge.
All other steps may be pessimistically treated as merges.

That alone forces:

lean
F' ≥ F + 2.
8. Why this avoids the refuted orbit-label route

The K4-sphere counterexample shows:

lean
oldFaceLift_phi_step

is false globally.

This proof never needs it.

The forced split theorem is only:

lean
SameCycle
  (prefixPerm phiLift W j)
  x
  y

for selected prefixes j and selected local endpoint pairs x,y.

It is a statement about a partial product, not about final phi'2 orbits and not about old-face labels.

So mixing of old faces in final orbits is irrelevant.

9. Why “minus caps form one orbit” is not the right invariant

The observed fact that minus caps often lie in one orbit is useful debugging evidence, but it is not structurally safe enough.

The proof should not use:

lean
all minus caps lie in one phi'2 orbit

nor:

lean
phi'2 never maps a cap to the opposite sign.

Those are stronger-looking but brittle final-orbit statements.

The stable local fact is instead:

lean
∀ i, forced_split_at_edge i

for the fixed correction word.

That is checked directly from the closed forms and survives all genus/cycle-structure variation.

10. Candidate-route assessment under the new target
A. Local induction on k

Still unnecessary. It builds intermediate maps and requires a new delta analysis. The forced-split word theorem gives the lower bound directly from the actual final construction.

B. Old-face orbit bijection

Refuted by the K4-sphere data. Do not use.

C. Riemann-Hurwitz / hypermap inequality

The standard permutation inequality

lean
cycles σ + cycles τ + cycles (στ)
  ≤ n + 2 * components ⟨σ, τ⟩

gives the wrong direction for the desired lower bound unless you also prove an upper bound on the auxiliary genus. That would be more work than the local forced-split certificate.

D. Face-degree double count

Insufficient. It controls total degree, not orbit count.

E. Fixed transposition word plus forced splits

This is the route that closes. It is exactly matched to the weaker target.

11. Dependency-ordered lemma chain

Implement in this order.

Layer 1: permutation and cycle-count API
lean
SameCycle
sameCycle_refl
sameCycle_symm
sameCycle_trans
sameCycle_of_apply_eq

numCycles_mul_swap_delta :
  ((numCycles (p * Equiv.swap x y) : Int)
    - (numCycles p : Int))
  =
  if SameCycle p x y then 1 else -1
Layer 2: transposition word API
lean
Swap
Swap.perm

prefixPerm
prefixPerm_zero
prefixPerm_succ

stepDelta
prefix_step_delta
numCycles_prefix_telescopes

Main generic lower lemma:

lean
sum_stepDelta_lower_of_forced_splits

numCycles_lower_of_forced_splits :
  forced split indices of size s in a word of length m →
  numCycles final ≥ numCycles initial - m + 2*s
Layer 3: face correction word

Define the verified fixed word:

lean
faceCorrWord : Fin (4*k - 2) → Swap Dcut

with:

lean
faceCorrWord_product :
  Finset.prod Finset.univ (fun j => (faceCorrWord j).perm)
    =
  faceCorr2

and:

lean
prefix_full_faceCorrWord :
  prefixPerm phiLift faceCorrWord (4*k - 2)
    =
  phiLift * faceCorr2
Layer 4: forced split indices

Define:

lean
splitIdx : Fin k → Fin (4*k - 2)

with:

lean
splitIdx_injective :
  Function.Injective splitIdx

For each i, define or expose:

lean
closeL i := (faceCorrWord (splitIdx i)).x
closeR i := (faceCorrWord (splitIdx i)).y
Layer 5: closed-form prefix paths

For each i, prove the local path:

lean
forced_split_path_at_edge :
  PermPath
    (prefixPerm phiLift faceCorrWord (splitIdx i).val)
    (closeL i)
    (closeR i)

using only per-class closed forms.

Then:

lean
forced_split_at_edge :
  SameCycle
    (prefixPerm phiLift faceCorrWord (splitIdx i).val)
    (closeL i)
    (closeR i)
Layer 6: lower-bound certificate

Package:

lean
lowerCert : FaceCorrLowerCert

with fields:

lean
m := 4*k - 2
W := faceCorrWord
word_eq := faceCorrWord_product
splitIdx := splitIdx
splitIdx_injective := splitIdx_injective
forced_split := forced_split_at_edge
Layer 7: final lower bound

Use:

lean
phiPrime2_factorization :
  phi'2 = phiLift * faceCorr2

numCycles_phiLift :
  numCycles phiLift = F + 2*k

Then:

lean
theorem numCycles_phiPrime2_ge :
  numCycles phi'2 ≥ F + 2

and hence the weaker requested theorem:

lean
theorem numCycles_phiPrime2_gt :
  numCycles phi'2 ≥ F + 1

by omega.

12. Final contradiction engine

For the Jordan contradiction, assuming the cut map is connected:

lean
chi'_connected_le_two :
  V' - E' + F' ≤ 2

Using proven:

lean
V' = V + k
E' = E + k
V - E + F = 2

you get:

lean
F' ≤ F.

But from the forced-split lower bound:

lean
F' ≥ F + 2.

Contradiction.

So the engine no longer needs exact equality F' = F + 2. It only needs the lower bound, and the forced-split certificate gives that lower bound genus-free.

13. The final invariant in one sentence

The invariant is not an old-face label and not a final cap-orbit statement.

It is:

lean
In the fixed correction transposition word for faceCorr2,
there are k distinguished steps whose endpoints are already
SameCycle in the current prefix product.

Therefore, among the 4k - 2 correction steps, at least k are splits. All other steps may be counted pessimistically as merges, giving:

lean
F'
  ≥ (F + 2k) + k - ((4k - 2) - k)
  = F + 2.

That is the genus-free lower bound needed for the Jordan engine.