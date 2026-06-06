I’ll treat split certification as an algorithmic, proof-carrying scan of the actual word, using a dynamic forest/interval invariant that survives splits instead of fixed split indices.

The final idea is: stop certifying split positions.

The split positions vary because they are not the invariant. The invariant is the amount of possible cycle loss. A transposition word supported on a set of phiLift-orbits can reduce the cycle count by at most the rank of the graph by which that word connects those phiLift-orbits.

So the right proof is:

lean
numCycles (phiLift * faceCorr2)
  ≥ numCycles phiLift - touchRank(phiLift, faceCorr2)

touchRank(phiLift, faceCorr2) ≤ 2*k - 2

numCycles phiLift = F + 2*k

Therefore:

lean
F' = numCycles phi'2
   = numCycles (phiLift * faceCorr2)
   ≥ F + 2*k - (2*k - 2)
   = F + 2.

This bypasses the zero-slack split-position problem entirely. It also explains it: the actual splits are whatever they need to be to prevent the word from losing more than the touch-rank. You certify the rank bound, not the individual split locations.

1. The invariant: touch-rank of the word

Let

lean
p : Equiv.Perm X
W : Fin m → Swap X

and let

lean
q := prefixPerm p W m.

Let POrb p be the quotient of X by SameCycle p:

lean
def POrb (p : Equiv.Perm X) :=
  Quotient (SameCycle.setoid p)

def pOrbOf (p : Equiv.Perm X) (x : X) : POrb p :=
  Quotient.mk _ x

The word touches some p-orbits:

lean
def wordTouchedOrbits
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X) :
    Finset (POrb p) :=
  Finset.univ.bind fun j =>
    {pOrbOf p (W j).x, pOrbOf p (W j).y}

Now build the graph whose vertices are touched p-orbits and whose edges say “some transposition connects these two p-orbits.”

lean
def wordOrbitEdge
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X)
    (u v : POrb p) : Prop :=
  ∃ j : Fin m,
    (u = pOrbOf p (W j).x ∧ v = pOrbOf p (W j).y) ∨
    (u = pOrbOf p (W j).y ∧ v = pOrbOf p (W j).x)

Let wordOrbitConn p W be the reflexive-transitive closure of this edge relation restricted to wordTouchedOrbits.

Then define:

lean
touchRank(p, W)
  :=
card(touched p-orbits)
-
card(connected components of touched p-orbits under wordOrbitConn).

This is the number of initial p-orbits that the word can possibly fuse away. It is independent of the order of the transpositions and independent of where the adaptive split steps occur.

2. Generic theorem: cycle loss is bounded by touch-rank

The key theorem is:

lean
theorem numCycles_prefixPerm_ge_of_touchRank
    [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X) :
  (numCycles (prefixPerm p W m) : Int)
    ≥
  (numCycles p : Int) - (touchRank p W : Int)

This is the replacement for split certification.

Proof idea

Partition X into blocks:

Untouched p-orbits.

Connected components of touched p-orbits under the word-orbit graph.

Every block is invariant under the final permutation

lean
q := prefixPerm p W m.

An untouched p-orbit is completely fixed by every transposition in the word, so on that block:

lean
q = p.

Thus each untouched p-orbit remains one q-cycle.

A touched component is a union of some p-orbits. Every transposition endpoint stays inside the same touched component by construction, and p itself stays inside one p-orbit. Therefore q preserves each touched component. Since each touched component is nonempty and finite, it contains at least one q-cycle.

Hence:

lean
numCycles q
  ≥
#untouched p-orbits + #touched components

But:

lean
#untouched p-orbits
  =
numCycles p - #touched p-orbits.

Therefore:

lean
numCycles q
  ≥
numCycles p - #touched p-orbits + #touched components
  =
numCycles p - touchRank(p,W).

This is the exact conservation law.

No split positions appear.

3. Formal proof of the generic theorem
3.1 Swap word
lean
structure Swap (X : Type*) where
  x : X
  y : X

def Swap.perm [DecidableEq X] (s : Swap X) : Equiv.Perm X :=
  Equiv.swap s.x s.y

Prefix product:

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

At full length:

lean
def wordPerm
    [DecidableEq X]
    {m : Nat}
    (W : Fin m → Swap X) : Equiv.Perm X :=
  Finset.prod Finset.univ fun j : Fin m => (W j).perm

with:

lean
lemma prefixPerm_full_eq
    [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X) :
  prefixPerm p W m = p * wordPerm W

depending on your multiplication convention.

3.2 Touched p-orbits
lean
def POrb (p : Equiv.Perm X) :=
  Quotient (SameCycle.setoid p)

def pOrbOf (p : Equiv.Perm X) (x : X) : POrb p :=
  Quotient.mk _ x

A p-orbit is touched if it contains an endpoint of a word transposition.

lean
def wordTouchedOrbits
    [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X) :
    Finset (POrb p) :=
  Finset.univ.bind fun j : Fin m =>
    {pOrbOf p (W j).x, pOrbOf p (W j).y}

The edge relation:

lean
def wordOrbitEdge
    [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X)
    (u v : POrb p) : Prop :=
  ∃ j : Fin m,
    (u = pOrbOf p (W j).x ∧ v = pOrbOf p (W j).y) ∨
    (u = pOrbOf p (W j).y ∧ v = pOrbOf p (W j).x)

Connectedness:

lean
def wordOrbitConn
    [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X)
    (u v : POrb p) : Prop :=
  Relation.ReflTransGen (wordOrbitEdge p W) u v

Components can be implemented either as a quotient of the subtype of touched orbits, or more Lean-friendly as a coloring certificate. I recommend the coloring version.

4. Coloring certificate version

Instead of constructing connected components directly, use a finite color type.

lean
structure TouchColorCert
    (X : Type*) [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X) where

  Color : Type*
  colorFintype : Fintype Color
  colorDecEq : DecidableEq Color

  color : POrb p → Option Color

  -- Every touched p-orbit receives a color.
  color_some_of_touched :
    ∀ o ∈ wordTouchedOrbits p W, ∃ c, color o = some c

  -- Every color is used by some touched p-orbit.
  color_used :
    ∀ c : Color, ∃ o ∈ wordTouchedOrbits p W, color o = some c

  -- Every transposition connects endpoints of the same color.
  endpoint_color_eq :
    ∀ j : Fin m,
      color (pOrbOf p (W j).x)
        =
      color (pOrbOf p (W j).y)

  -- Rank bound.
  rank_bound :
    (wordTouchedOrbits p W).card - Fintype.card Color ≤ 2*k - 2

For a generic theorem, replace 2*k - 2 by an arbitrary bound B.

lean
structure TouchColorCertBound
    (X : Type*) [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X)
    (B : Nat) where

  Color : Type*
  colorFintype : Fintype Color
  colorDecEq : DecidableEq Color

  color : POrb p → Option Color

  color_some_of_touched :
    ∀ o ∈ wordTouchedOrbits p W, ∃ c, color o = some c

  color_used :
    ∀ c : Color, ∃ o ∈ wordTouchedOrbits p W, color o = some c

  endpoint_color_eq :
    ∀ j : Fin m,
      color (pOrbOf p (W j).x)
        =
      color (pOrbOf p (W j).y)

  rank_bound :
    (wordTouchedOrbits p W).card - Fintype.card Color ≤ B

Then prove:

lean
theorem numCycles_prefixPerm_ge_of_touchColorCert
    [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m B : Nat}
    (W : Fin m → Swap X)
    (C : TouchColorCertBound X p W B) :
  (numCycles (prefixPerm p W m) : Int)
    ≥
  (numCycles p : Int) - (B : Int)

This is the theorem that closes the count.

5. Proof of the coloring theorem

Let:

lean
q := prefixPerm p W m.

Define the block label of an element:

lean
def blockLabel (x : X) : Option C.Color :=
  C.color (pOrbOf p x)

Touched components have labels some c; untouched p-orbits have none.

5.1 The word preserves color

Each swap in the word preserves blockLabel.

lean
lemma swap_preserves_blockLabel
    (j : Fin m)
    (x : X) :
  blockLabel (Swap.perm (W j) x) = blockLabel x := by
  by_cases hx : x = (W j).x
  · subst hx
    simp [Swap.perm, blockLabel, C.endpoint_color_eq j]
  · by_cases hy : x = (W j).y
    · subst hy
      simp [Swap.perm, blockLabel, C.endpoint_color_eq j]
    · simp [Swap.perm, hx, hy, blockLabel]

Since p preserves its own orbit:

lean
lemma p_preserves_blockLabel
    (x : X) :
  blockLabel (p x) = blockLabel x := by
  unfold blockLabel
  congr
  exact Quot.sound (sameCycle_step p x)

Therefore the full prefix permutation preserves the block label:

lean
lemma q_preserves_blockLabel
    (x : X) :
  blockLabel (q x) = blockLabel x := by
  -- induction over prefixPerm;
  -- each step uses swap_preserves_blockLabel,
  -- final left multiplication by p uses p_preserves_blockLabel.

This gives one invariant block per color.

5.2 Untouched p-orbits survive as q-cycles

If a p-orbit is not touched, no endpoint of any transposition lies in it. Therefore every swap fixes every element of that orbit.

lean
lemma prefixPerm_eq_p_on_untouched_orbit
    {o : POrb p}
    (ho : o ∉ wordTouchedOrbits p W)
    {x : X}
    (hx : pOrbOf p x = o) :
  q x = p x

Proof: every swap fixes x, because if x = (W j).x or x = (W j).y, then o would be touched. Extend from one step to the whole word.

Therefore the q-orbit of a representative of an untouched p-orbit is exactly that p-orbit.

So distinct untouched p-orbits give distinct q-orbits.

lean
lemma untouched_orbit_injective :
  Function.Injective
    (fun o : {o : POrb p // o ∉ wordTouchedOrbits p W} =>
      qOrbitOf q (Quotient.out o.val))
5.3 Each used color gives at least one q-orbit

For each color c, use C.color_used c to pick a touched p-orbit with that color, then choose an element in that orbit:

lean
noncomputable def colorAnchor (c : C.Color) : X :=
  Quotient.out (Classical.choose (C.color_used c))

Since q preserves blockLabel, two anchors of distinct colors cannot lie in the same q-orbit.

lean
lemma colorAnchor_injective_on_qOrbits :
  Function.Injective
    (fun c : C.Color => qOrbitOf q (colorAnchor c))
5.4 Untouched q-orbits are distinct from colored q-orbits

An untouched orbit has blockLabel = none.

A colored anchor has blockLabel = some c.

Since q preserves blockLabel, they cannot be in the same q-orbit.

Thus there is an injection:

lean
({o : POrb p // o ∉ wordTouchedOrbits p W} ⊕ C.Color)
  ↪
Quotient (SameCycle.setoid q)

Therefore:

lean
numCycles q
  ≥
card {o : POrb p // o ∉ wordTouchedOrbits p W}
+
card C.Color

Now:

lean
card {o : POrb p // o ∉ touched}
  =
numCycles p - touched.card.

So:

lean
numCycles q
  ≥
numCycles p - touched.card + card C.Color
  =
numCycles p - (touched.card - card C.Color)
  ≥
numCycles p - B.

This proves:

lean
theorem numCycles_prefixPerm_ge_of_touchColorCert
    (C : TouchColorCertBound X p W B) :
  (numCycles (prefixPerm p W m) : Int)
    ≥
  (numCycles p : Int) - (B : Int)

No split positions are used.

6. Where do the colors come from?

Use a small generator graph.

Instead of finding actual connected components of the full word-orbit graph, give a set of at most 2*k - 2 generator edges whose reachability already connects the endpoints of every transposition in the word.

This is the finite certificate:

lean
structure TouchCompressionCert
    (X : Type*) [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X)
    (B : Nat) where

  gen : Fin B → Sym2 (POrb p)

  endpoint_reachable :
    ∀ j : Fin m,
      GenReach gen
        (pOrbOf p (W j).x)
        (pOrbOf p (W j).y)

Here GenReach gen is reflexive-transitive closure of the symmetric generator edges.

Then define:

lean
Color := quotient of touched p-orbits by GenReach.

Every transposition endpoint pair has the same color by endpoint_reachable.

The rank bound is automatic:

lean
card touched - card Color ≤ B.

This is the standard graph fact:

lean
vertices - connectedComponents ≤ edges.

Formal lemma:

lean
lemma graph_rank_le_edges
    (V : Finset α)
    (gen : Fin B → Sym2 α) :
  V.card - card (components of V under GenReach gen) ≤ B

Proof by induction on the generator list:

With no edges, every vertex is its own component, so rank 0.

Adding one edge either connects two already-connected vertices, rank unchanged, or merges two components, rank increases by exactly 1.

Therefore rank never exceeds the number of edges.

Thus:

lean
theorem touchColorCert_of_touchCompressionCert
    (K : TouchCompressionCert X p W B) :
  TouchColorCertBound X p W B

and hence:

lean
theorem numCycles_prefixPerm_ge_of_touchCompressionCert
    (K : TouchCompressionCert X p W B) :
  (numCycles (prefixPerm p W m) : Int)
    ≥
  (numCycles p : Int) - (B : Int)

This is the main abstract theorem.

7. The cut-and-cap certificate

Instantiate with:

lean
X := Dcut
p := phiLift
W := faceCorrWord
B := 2*k - 2

You already have:

lean
faceCorrWord_product :
  wordPerm faceCorrWord = faceCorr2

and therefore:

lean
prefixPerm phiLift faceCorrWord m
  =
phiLift * faceCorr2.

Now define a small generator graph on phiLift-orbits.

lean
def PhiLiftOrb :=
  POrb phiLift

The certificate is:

lean
def bankTouchGen :
  Fin (2*k - 2) → Sym2 PhiLiftOrb

Conceptually, bankTouchGen is the union of two path forests, one along each bank:

lean
plus bank:  k - 1 generator edges
minus bank: k - 1 generator edges

so total:

lean
( k - 1 ) + ( k - 1 ) = 2*k - 2.

These generator edges are not transposition positions. They are orbit-compression witnesses. They say which phiLift-orbits are allowed to be fused by the local cut seam.

The required closed-form lemma is:

lean
lemma faceCorrWord_endpoint_reachable_by_bankTouchGen
    (j : Fin m) :
  GenReach bankTouchGen
    (pOrbOf phiLift (faceCorrWord j).x)
    (pOrbOf phiLift (faceCorrWord j).y)

This is the only cut-specific proof you need.

It is proved by case splitting on the per-class closed forms of faceCorrWord / faceCorr2.

The proof shape is:

lean
lemma faceCorrWord_endpoint_reachable_by_bankTouchGen
    (j : Fin m) :
  GenReach bankTouchGen
    (pOrbOf phiLift (faceCorrWord j).x)
    (pOrbOf phiLift (faceCorrWord j).y) := by
  rcases faceCorrWord_cases j with
    h_plus_local
  | h_minus_local
  | h_cap_turn
  | h_old_seam
  | h_other
  · subst h_plus_local
    exact GenReach.single
      (by simp [bankTouchGen, phiLift_orbit_closed_forms])
  · subst h_minus_local
    exact GenReach.single
      (by simp [bankTouchGen, phiLift_orbit_closed_forms])
  · subst h_cap_turn
    exact GenReach.trans
      (GenReach.single (by simp [bankTouchGen, phiLift_orbit_closed_forms]))
      (GenReach.single (by simp [bankTouchGen, phiLift_orbit_closed_forms]))
  · subst h_old_seam
    exact GenReach.refl
      -- endpoints lie in the same phiLift-orbit
      -- so their pOrbOf values are equal
  · subst h_other
    exact ...

Important: this lemma does not say a given transposition is a split or a merge. It only says its endpoints lie in the same compressed bank component of the phiLift-orbit graph.

Then package:

lean
def faceCorrTouchCompressionCert :
  TouchCompressionCert Dcut phiLift faceCorrWord (2*k - 2) where
  gen := bankTouchGen
  endpoint_reachable := faceCorrWord_endpoint_reachable_by_bankTouchGen
8. Final lower bound

From the generic theorem:

lean
lemma numCycles_phiLift_faceCorr2_ge :
  (numCycles (phiLift * faceCorr2) : Int)
    ≥
  (numCycles phiLift : Int) - ((2*k - 2 : Nat) : Int) := by
  have h :=
    numCycles_prefixPerm_ge_of_touchCompressionCert
      faceCorrTouchCompressionCert

  have hprefix :
      prefixPerm phiLift faceCorrWord m = phiLift * faceCorr2 := by
    rw [prefixPerm_full_eq, faceCorrWord_product]

  simpa [hprefix] using h

Then use:

lean
numCycles_phiLift :
  numCycles phiLift = F + 2*k

and:

lean
phiPrime2_factorization :
  phi'2 = phiLift * faceCorr2

to get:

lean
theorem numCycles_phiPrime2_ge_F_add_two :
  (numCycles phi'2 : Int) ≥ (F : Int) + 2 := by
  have h₁ :
      (numCycles (phiLift * faceCorr2) : Int)
        ≥
      (numCycles phiLift : Int) - ((2*k - 2 : Nat) : Int) :=
    numCycles_phiLift_faceCorr2_ge

  have h₂ :
      (numCycles phiLift : Int) = (F : Int) + 2*(k : Int) := by
    exact_mod_cast numCycles_phiLift

  have h₃ :
      phi'2 = phiLift * faceCorr2 :=
    phiPrime2_factorization

  rw [h₃]
  -- arithmetic:
  -- F + 2k - (2k - 2) = F + 2
  omega

In Nat form:

lean
theorem numCycles_phiPrime2_ge_F_add_two_nat :
  numCycles phi'2 ≥ F + 2 := by
  have hInt := numCycles_phiPrime2_ge_F_add_two
  omega

This is stronger than the required F' ≥ F + 1.

9. Relation to actual splits

If you still want to connect this back to the split-walk machinery, define the actual split set:

lean
def actualSplits
    (p : Equiv.Perm X)
    {m : Nat}
    (W : Fin m → Swap X) :
    Finset (Fin m) :=
  Finset.univ.filter fun j =>
    SameCycle
      (prefixPerm p W j.val)
      (W j).x
      (W j).y

Then:

lean
lemma actualSplits_are_splits
    (j : Fin m)
    (hj : j ∈ actualSplits p W) :
  SameCycle
    (prefixPerm p W j.val)
    (W j).x
    (W j).y := by
  simpa [actualSplits] using hj

The transposition telescoping theorem gives:

lean
(numCycles (prefixPerm p W m) : Int)
  =
(numCycles p : Int)
  - (m : Int)
  + 2*(actualSplits p W).card

Combine this with the touch-rank lower bound:

lean
numCycles (prefixPerm p W m)
  ≥ numCycles p - B

to derive:

lean
lemma actualSplits_card_ge_of_touchCompression
    (K : TouchCompressionCert X p W B) :
  2*((actualSplits p W).card : Int)
    ≥
  (m : Int) - (B : Int)

For cut-and-cap:

lean
B = 2*k - 2.

So:

lean
2 * actualSplitCount ≥ m - (2*k - 2).

This proves that enough split positions exist, but it never names them.

That is exactly what you need when the positions vary by cut.

If your existing one-sided split theorem requires explicit indices, enumerate actualSplits:

lean
noncomputable def actualSplitIdx :
  Fin (actualSplits p W).card → Fin m :=
  fun i => (actualSplits p W).orderIsoOfFin i

Then:

lean
lemma actualSplitIdx_forced :
  ∀ i,
    SameCycle
      (prefixPerm p W (actualSplitIdx i).val)
      (W (actualSplitIdx i)).x
      (W (actualSplitIdx i)).y

and the cardinal lower bound above supplies the needed s.

So the existing split machinery can still be used, but the proof of “there are enough splits” comes from touch-rank, not from a uniform positional rule.

10. Why candidate C almost works, and the correct repair

Candidate C said:

Maintain that the processed support is one prefix-orbit.

That invariant fails after a split. A split cuts one current orbit into two.

The correct local invariant would be:

lean
A_j = the ordered current orbit of the active pivot a_j

not “all processed elements are in one orbit.”

At step j, with pivot pair (a_j, a_{j+1}):

If a_{j+1} ∉ A_j, the step is a merge and the new active orbit is the union of A_j with the orbit of a_{j+1}.

If a_{j+1} ∈ A_j, the step is a split and the new active orbit is the cyclic interval of A_j containing a_{j+1} after swapping successors.

This gives an exact dynamic split-certifier. But it is overkill for the count, and its split positions will still vary.

The touch-rank theorem is the aggregate version of this dynamic invariant. It says:

Regardless of where the splits happen, the word cannot fuse away more initial p-orbits than the rank of the orbit-touch graph.

That is the stable count invariant.

11. Route assessment
A. Invariant-counted single-cycle formulas

There is a classical hypermap formula for two permutations:

lean
cycles(σ) + cycles(τ) + cycles(στ)
  =
|support| + 2*components - 2*genus.

For a single cycle τ, this expresses cycles(σ τ) in terms of the genus of the two-generator dessin. But that genus is exactly the global interleaving complexity you do not want to compute. It is not the clean way to close the lower bound.

A useful corollary is the rank inequality:

lean
cycles(σ τ) ≥ cycles(σ) - rank_touch(σ, τ).

That is the touch-rank theorem above.

B. Redundant word

A redundant word can create more certifiable split opportunities, but it also increases the length m. You then need to prove every redundant pair contributes enough certified splits. That simply recreates the same problem with a longer word.

Do not do this.

C. Processed-support connectivity

The naive invariant fails after splits. The repaired invariant is the active ordered orbit segment, but the aggregate touch-rank proof is simpler and stronger.

D. Robust route

Use the orbit-touch graph compression:

lean
initial p-orbits touched by the word

modulo a small generator graph of size 2*k - 2.

This gives the exact one-sided bound needed.

12. Dependency-ordered lemma chain

Implement in this order.

Layer 1: permutation orbit API
lean
SameCycle
SameCycle.setoid
sameCycle_refl
sameCycle_symm
sameCycle_trans
sameCycle_of_apply_eq

POrb p := Quotient (SameCycle.setoid p)
pOrbOf p x := Quotient.mk _ x

numCycles_eq_card_POrb :
  numCycles p = Fintype.card (POrb p)
Layer 2: word API
lean
Swap
Swap.perm

prefixPerm
wordPerm

prefixPerm_full_eq :
  prefixPerm p W m = p * wordPerm W
Layer 3: touched orbit graph
lean
wordTouchedOrbits :
  Finset (POrb p)

wordOrbitEdge :
  POrb p → POrb p → Prop

wordOrbitConn :
  POrb p → POrb p → Prop

Optional exact component theorem:

lean
touchRank :
  Nat

numCycles_prefixPerm_ge_of_touchRank :
  numCycles (prefixPerm p W m)
    ≥
  numCycles p - touchRank p W
Layer 4: coloring/compression certificate
lean
TouchColorCertBound
TouchCompressionCert

graph_rank_le_edges :
  vertices - components ≤ edges

touchColorCert_of_touchCompressionCert :
  TouchCompressionCert X p W B →
  TouchColorCertBound X p W B

numCycles_prefixPerm_ge_of_touchColorCert :
  TouchColorCertBound X p W B →
  (numCycles (prefixPerm p W m) : Int)
    ≥
  (numCycles p : Int) - (B : Int)

numCycles_prefixPerm_ge_of_touchCompressionCert :
  TouchCompressionCert X p W B →
  (numCycles (prefixPerm p W m) : Int)
    ≥
  (numCycles p : Int) - (B : Int)
Layer 5: cut-and-cap touch compression
lean
faceCorrWord : Fin m → Swap Dcut

faceCorrWord_product :
  wordPerm faceCorrWord = faceCorr2

bankTouchGen :
  Fin (2*k - 2) → Sym2 (POrb phiLift)

faceCorrWord_endpoint_reachable_by_bankTouchGen :
  ∀ j : Fin m,
    GenReach bankTouchGen
      (pOrbOf phiLift (faceCorrWord j).x)
      (pOrbOf phiLift (faceCorrWord j).y)

faceCorrTouchCompressionCert :
  TouchCompressionCert
    Dcut phiLift faceCorrWord (2*k - 2)

The endpoint reachability lemma is the only place that uses the per-class closed forms.

Layer 6: final lower bound
lean
numCycles_phiLift_faceCorr2_ge :
  (numCycles (phiLift * faceCorr2) : Int)
    ≥
  (numCycles phiLift : Int) - ((2*k - 2 : Nat) : Int)

numCycles_phiPrime2_ge_F_add_two :
  (numCycles phi'2 : Int) ≥ (F : Int) + 2

numCycles_phiPrime2_ge_F_add_two_nat :
  numCycles phi'2 ≥ F + 2
Layer 7: contradiction engine

Already proven pieces:

lean
V' = V + k
E' = E + k
V - E + F = 2
chi_connected_le_two :
  connected cutCapMap2 →
  V' - E' + F' ≤ 2

Then:

lean
connected cutCapMap2 → F' ≤ F

But:

lean
F' ≥ F + 2

Contradiction.

13. Final invariant in one sentence

The final invariant is:

lean
A correction word can reduce cycle count only by merging
distinct phiLift-orbits inside the same connected component
of its phiLift-orbit touch graph.

For cutCapMap2, the whole touch graph is compressed by a fixed bank generator graph with only

lean
2*k - 2

edges. Therefore the total loss from

lean
numCycles phiLift = F + 2*k

is at most 2*k - 2, regardless of where the adaptive split steps occur.

So:

lean
F' ≥ F + 2.