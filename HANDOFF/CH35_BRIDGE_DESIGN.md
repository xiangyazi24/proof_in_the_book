Below is the formalization-ready version I would actually implement. The important correction is:

Do not try to prove “entry fragment and exit fragment of the same old face are connected.” That statement is false.
The right theorem is a theorem about a fragment-level dual path, or about a geometric/topological “interior-dual path” that has already been refined to such a fragment-level path. A mere face sequence in the ordinary dual graph is too weak: it can “teleport” across a straddling face.

So the final bridge theorem should be proved in two layers:

lean
banks_connected_of_fragment_dual_path_between_cycle_faces

and, separately, if your current notion of “interior-dual path” is meant geometrically,

lean
fragment_dual_path_of_interior_dual_path_avoiding_cycle

The second lemma is where you prove that consecutive gates through the same old face lie in the same face-fragment. Without that, there is no valid intra-face transfer.

0. Global setup and notation

Let

lean
alpha : D ≃ D
sigma : D ≃ D
phi   : D ≃ D := sigma.trans alpha   -- or phi d = sigma (alpha d), depending convention

I will write

lean
φ d = sigma (alpha d)

as in your convention.

Faces of M are φ-orbits.

The cut map has dart type

lean
Dcut

with maps

lean
alpha' : Dcut ≃ Dcut
sigma' : Dcut ≃ Dcut
phi'   : Dcut ≃ Dcut := sigma' ∘ alpha'

and an embedding of surviving old darts

lean
old : D → Dcut

together with cap/bank darts

lean
cap : Side → Fin k → Dcut

where

lean
inductive Side | plus | minus

The cycle darts are

lean
c : Fin k → D

with cycle edge e_i = {c i, alpha (c i)}.

Define

lean
def IsCycleDart (d : D) : Prop :=
  ∃ i, d = c i ∨ d = alpha (c i)

def IsCycleEdgeDart (d : D) : Prop :=
  ∃ i, d = c i ∨ d = alpha (c i)

The side convention is:

lean
sideOfCycleDart (c i)           = Side.plus
sideOfCycleDart (alpha (c i))   = Side.minus

The two bank representatives for edge i are

lean
bankDart Side.plus  i
bankDart Side.minus i

You already have or should have:

lean
bank_same_side_connected :
  ∀ s i j, CutConn (bankDart s i) (bankDart s j)

and Part A:

lean
partA_reaches_bank :
  ∀ x : Dcut, (∃ i, CutConn x (bankDart Side.plus i)) ∨
              (∃ i, CutConn x (bankDart Side.minus i))

Under the contradiction hypothesis

lean
hsep : ¬ CutConn (bankDart Side.plus i₀) (bankDart Side.minus i₀)

Part A plus same-side bank connectedness gives the two-component dichotomy:

lean
lemma cut_component_dichotomy_of_hsep
  (hsep : ¬ CutConn (bankDart Side.plus i₀) (bankDart Side.minus i₀)) :
  ∀ x : Dcut,
    (∃ i, CutConn x (bankDart Side.plus i)) ∨
    (∃ i, CutConn x (bankDart Side.minus i))

and uniqueness:

lean
lemma not_both_bank_components_of_hsep
  (hsep : ¬ CutConn (bankDart Side.plus i₀) (bankDart Side.minus i₀)) :
  ∀ x : Dcut,
    ¬ ((∃ i, CutConn x (bankDart Side.plus i)) ∧
       (∃ i, CutConn x (bankDart Side.minus i)))

The proof is immediate: if some x reaches both a plus-bank dart and a minus-bank dart, then by transitivity and bank_same_side_connected the chosen bankDart plus i₀ reaches bankDart minus i₀.

1. Face-fragment formalism
1.1 Old faces

Represent an old face as a quotient/orbit, or concretely as a predicate closed under φ.

For formal work, I would use:

lean
def SameOldFace (d e : D) : Prop :=
  Relation.ReflTransGen (fun x y => y = φ x ∨ x = φ y) d e

or the orbit relation of the permutation φ.

Then:

lean
def OldFace := Quotient SameOldFace

with

lean
def faceOf (d : D) : OldFace := Quotient.mk _ d

and

lean
lemma sameOldFace_iff_faceOf_eq :
  SameOldFace d e ↔ faceOf d = faceOf e
1.2 The fragment relation inside one old face

The key relation is not old φ-adjacency. It is old-face adjacency that survives as a φ'-adjacency in the cut map.

For darts d e : D lying in the same old face, define:

lean
def SurvivingFaceStep (f : OldFace) (d e : D) : Prop :=
  faceOf d = f ∧
  faceOf e = f ∧
  (phi' (old d) = old e ∨ phi' (old e) = old d)

Then define same fragment:

lean
def SameFragment (f : OldFace) (d e : D) : Prop :=
  Relation.ReflTransGen (SurvivingFaceStep f) d e

A fragment is the equivalence class of this relation inside one old face:

lean
structure FaceFragment (f : OldFace) where
  carrier : Set D
  nonempty : carrier.Nonempty
  subset_face : ∀ d ∈ carrier, faceOf d = f
  closed :
    ∀ d e, d ∈ carrier → SurvivingFaceStep f d e → e ∈ carrier
  maximal :
    ∀ d e, d ∈ carrier → SameFragment f d e → e ∈ carrier

In practice, use connected components of SurvivingFaceStep f.

The canonical fragment containing a dart is:

lean
def fragOf (f : OldFace) (d : D) (hd : faceOf d = f) : FaceFragment f

with

lean
lemma mem_fragOf :
  d ∈ (fragOf f d hd).carrier

and

lean
lemma sameFragment_iff_same_fragOf :
  SameFragment f d e ↔ fragOf f d hd = fragOf f e he
1.3 Fragment lies in one cut-map component

Because every surviving face step is a φ'-step, and a φ'-step is an alpha' step followed by a sigma' step, every fragment is contained in one cut-map connected component.

lean
lemma cutConn_of_survivingFaceStep
  (h : SurvivingFaceStep f d e) :
  CutConn (old d) (old e)

Proof:

If phi' (old d) = old e, then

lean
old d --alpha'--> alpha' (old d) --sigma'--> phi' (old d) = old e.

If the equality is reversed, use symmetry of CutConn.

Then:

lean
lemma cutConn_of_sameFragment
  (h : SameFragment f d e) :
  CutConn (old d) (old e)

by induction over Relation.ReflTransGen.

Therefore:

lean
lemma fragment_cut_connected
  (F : FaceFragment f)
  (hd : d ∈ F.carrier)
  (he : e ∈ F.carrier) :
  CutConn (old d) (old e)

Proof: use maximality/connected-component characterization to obtain SameFragment f d e, then apply the previous lemma.

This is the only safe “same old face” connectivity statement:

same fragment ⇒ cut-connected.

Not:

same old face ⇒ cut-connected.

2. Boundary/cap facts for fragments

You need the following local facts from the explicit cut construction.

For every cycle index i:

lean
lemma cycle_plus_attached :
  CutConn (old (c i)) (bankDart Side.plus i)

lemma cycle_minus_attached :
  CutConn (old (alpha (c i))) (bankDart Side.minus i)

Usually each is a one-edge alpha' step to the corresponding cap dart, followed by a few sigma' steps along the bank.

Then:

lean
lemma fragment_containing_cycle_plus_lies_plus
  (F : FaceFragment (faceOf (c i)))
  (hmem : c i ∈ F.carrier) :
  ∀ d ∈ F.carrier, CutConn (old d) (bankDart Side.plus i)

Proof:

For d ∈ F, use

lean
CutConn (old d) (old (c i))

from fragment_cut_connected, then compose with cycle_plus_attached.

Similarly:

lean
lemma fragment_containing_cycle_minus_lies_minus
  (F : FaceFragment (faceOf (alpha (c i))))
  (hmem : alpha (c i) ∈ F.carrier) :
  ∀ d ∈ F.carrier, CutConn (old d) (bankDart Side.minus i)

These are your endpoint fragment lemmas.

2.1 The “bounded by cap-diversions” lemma

This is useful diagnostically and for proving the refinement from geometric paths.

A fragment is maximal for φ'-continuation inside the old face. Therefore, if d ∈ F and φ d is in the same old face but not in F, then the old φ-transition from d to φ d was broken by the cut.

Formal statement:

lean
lemma fragment_boundary_is_cut_diversion
  (F : FaceFragment f)
  (hd : d ∈ F.carrier)
  (hface : faceOf (φ d) = f)
  (hnot : φ d ∉ F.carrier) :
  phi' (old d) ≠ old (φ d)

Then from the explicit definition of the cut:

lean
lemma broken_old_face_step_implies_cycle_incidence
  (hface : faceOf (φ d) = faceOf d)
  (hbroken : phi' (old d) ≠ old (φ d)) :
  IsCycleDart d ∨ IsCycleDart (φ d)

Depending on your implementation, the broken transition is usually detected at d, not at φ d, so you may have the sharper version:

lean
lemma broken_old_face_step_iff_cycle_boundary :
  phi' (old d) ≠ old (φ d) ↔ IsCycleDart d

or a version involving the predecessor/successor around the old face.

The point is:

A fragment boundary occurs exactly where the old face traversal tries to pass through the cut cycle and is diverted into a cap/bank.

2.2 Alternation/parity: useful but not the lifting mechanism

You can prove a local side-change lemma around a broken old-face step, but do not use it to move between fragments.

The safe form is:

lean
lemma side_of_adjacent_fragments_across_break
  (hbreak : phi' (old d) ≠ old (φ d))
  (hdcyc : IsCycleDart d) :
  let F₁ := fragOf (faceOf d) d rfl
  let F₂ := fragOf (faceOf (φ d)) (φ d) hface
  FragmentSide F₂ = opposite (BoundaryExitSide d)

The exact side expression depends on your local cut convention. I would avoid baking a global “fragments alternate plus/minus around the face” theorem unless you really need it, because faces can contain maximal blocks of consecutive cycle darts. The robust statement is local:

lean
old φ-step survives        ⇒ same fragment;
old φ-step broken by cut   ⇒ the two adjacent fragments are separated by a cap/bank diversion.

Under hsep, every fragment has a unique side label:

lean
noncomputable def fragmentSide
  (hsep : ¬ CutConn (bankDart Side.plus i₀) (bankDart Side.minus i₀))
  (F : FaceFragment f) : Side

defined by choosing any dart d ∈ F, applying Part A to old d, and using uniqueness from hsep.

Then the local break lemma can be stated as a theorem about fragmentSide.

But the crucial warning is:

lean
-- False:
lemma same_old_face_fragments_connected :
  faceOf d = faceOf e → CutConn (old d) (old e)

and also generally false:

lean
-- False:
lemma all_fragments_of_one_old_face_same_side_under_hsep :
  ...

A straddling face is exactly a counterexample.

3. The corrected lifted dual path

The lifted object is not merely a sequence of old faces.

It must carry fragments.

3.1 Gates

A dual crossing across an uncut edge is represented by a dart a : D such that the face on one side is faceOf a and the face on the other side is faceOf (alpha a).

lean
structure UncutDualGate where
  dart : D
  not_cycle : ¬ IsCycleEdgeDart dart

The cut map preserves the edge join:

lean
lemma alpha'_old_of_not_cycle
  (h : ¬ IsCycleEdgeDart a) :
  alpha' (old a) = old (alpha a)

Hence:

lean
lemma cutConn_across_uncut_dual_gate
  (h : ¬ IsCycleEdgeDart a) :
  CutConn (old a) (old (alpha a))

Proof: one alpha' step.

3.2 Fragment-level dual path

Define a path with n crossings.

lean
structure FragmentDualPath where
  n : Nat

  face : Fin (n + 1) → OldFace
  frag : ∀ j : Fin (n + 1), FaceFragment (face j)

  edge : Fin n → D
  edge_not_cycle : ∀ j, ¬ IsCycleEdgeDart (edge j)

  -- edge j crosses from face j to face j+1
  left_face :
    ∀ j : Fin n, faceOf (edge j) = face (j.castSucc)

  right_face :
    ∀ j : Fin n,
      faceOf (alpha (edge j)) = face (j.succ)

  -- the dart used to leave face j lies in frag j
  left_mem :
    ∀ j : Fin n,
      edge j ∈ (frag j.castSucc).carrier

  -- the dart used to enter face j+1 lies in frag j+1
  right_mem :
    ∀ j : Fin n,
      alpha (edge j) ∈ (frag j.succ).carrier

This already encodes the no-teleport rule: each position has exactly one fragment. If an intermediate face is entered through one dart and exited through another, both darts must be placed in the same frag j.

For ergonomic use, you can add explicit fields:

lean
entry_mem :
  ∀ j : Fin (n+1), 0 < j → alpha (edge (j-1)) ∈ (frag j).carrier

exit_mem :
  ∀ j : Fin (n+1), j < n → edge j ∈ (frag j).carrier

and the single-fragment condition becomes definitional.

3.3 The cycle-side endpoint version

For the Jordan bridge, define:

lean
structure FragmentDualPathBetweenCycleSides (i : Fin k) extends FragmentDualPath where
  start_face :
    face 0 = faceOf (c i)

  end_face :
    face (Fin.last n) = faceOf (alpha (c i))

  start_mem :
    c i ∈ (frag 0).carrier

  end_mem :
    alpha (c i) ∈ (frag (Fin.last n)).carrier

This is the exact object that the bridge theorem needs.

4. The main lifting theorem

The clean theorem is:

lean
theorem banks_connected_of_fragment_dual_path_between_cycle_faces
  (P : FragmentDualPathBetweenCycleSides i) :
  CutConn (bankDart Side.plus i) (bankDart Side.minus i)
Proof

We prove that all fragments along P lie in the same cut-map component.

For each j, choose any representative dart in P.frag j. You do not need a global choice if you state the induction relationally.

Define:

lean
def FragCutConn (F : FaceFragment f) (G : FaceFragment g) : Prop :=
  ∃ d e, d ∈ F.carrier ∧ e ∈ G.carrier ∧ CutConn (old d) (old e)

First prove same-fragment reflexivity:

lean
lemma FragCutConn.refl (F : FaceFragment f) :
  FragCutConn F F

using F.nonempty and reflexivity of CutConn.

Then prove the step lemma:

lean
lemma fragCutConn_step_across_uncut_edge
  (P : FragmentDualPath)
  (j : Fin P.n) :
  FragCutConn (P.frag j.castSucc) (P.frag j.succ)

Proof:

Let

lean
a := P.edge j

Then:

lean
ha_left  : a ∈ (P.frag j.castSucc).carrier
ha_right : alpha a ∈ (P.frag j.succ).carrier

by P.left_mem and P.right_mem.

Since a is not a cycle edge,

lean
CutConn (old a) (old (alpha a))

by cutConn_across_uncut_dual_gate.

Thus the two fragments are connected through the old uncut edge. This proves FragCutConn.

Now chain these steps over j = 0, ..., n-1:

lean
lemma all_path_fragments_cut_connected
  (P : FragmentDualPath) :
  FragCutConn (P.frag 0) (P.frag (Fin.last P.n))

by induction on n.

Finally use the endpoint lemmas.

Start:

lean
P.start_mem : c i ∈ (P.frag 0).carrier

and

lean
cycle_plus_attached :
  CutConn (old (c i)) (bankDart Side.plus i)

so P.frag 0 is in the plus-bank component.

End:

lean
P.end_mem : alpha (c i) ∈ (P.frag (Fin.last P.n)).carrier

and

lean
cycle_minus_attached :
  CutConn (old (alpha (c i))) (bankDart Side.minus i)

so the last fragment is in the minus-bank component.

Since the first and last fragments are connected by the path induction, compose:

lean
bankDart plus i
  ~ old (c i)
  ~ any dart in first fragment
  ~ any dart in last fragment
  ~ old (alpha (c i))
  ~ bankDart minus i

Therefore:

lean
CutConn (bankDart Side.plus i) (bankDart Side.minus i)

This proves the theorem.

5. The contradiction form

The contradiction version is immediate.

lean
theorem no_fragment_dual_path_between_cycle_faces_if_banks_separated
  (hsep : ¬ CutConn (bankDart Side.plus i) (bankDart Side.minus i))
  (P : FragmentDualPathBetweenCycleSides i) :
  False :=
by
  exact hsep (banks_connected_of_fragment_dual_path_between_cycle_faces P)

Or phrased positively:

lean
theorem banks_connected_of_dual_path_between_cycle_faces
  (P : FragmentDualPathBetweenCycleSides i) :
  CutConn (bankDart Side.plus i) (bankDart Side.minus i)

This is the exact bridge needed for Part B.

6. What happens when entry and exit lie in different fragments?

This is the central point.

Suppose the ordinary face path has

lean
f_{j-1} --a_{j-1}--> f_j --a_j--> f_{j+1}

with

lean
alpha (a_{j-1}) : D

the dart by which the path enters f_j, and

lean
a_j : D

the dart by which it exits f_j.

The required condition is:

lean
SameFragment f_j (alpha (a_{j-1})) a_j

Equivalently:

lean
fragOf f_j (alpha (a_{j-1})) = fragOf f_j a_j

If this fails, there is no legal lift through f_j.

Under the contradiction hypothesis, the two fragments have definite side labels, but that does not create a path between them. It only tells you which bank component each fragment belongs to.

So the answer to the straddling question is:

You do not move between different fragments of the same old face.
A valid cut-avoiding interior-dual path must never require such a move.
If your current “dual path” does require it, then it is not a liftable path; it is using the false same-face relay.

This is precisely where the old naive proof failed.

The Lean-side fix is to strengthen the path predicate.

7. Refining an intended geometric interior-dual path

If your book statement says “there is an interior-dual path avoiding the cycle,” the formal version should not be a bare face sequence. It should be one of the following.

Option A: define the path directly at fragment level

This is the cleanest for Lean:

lean
FragmentDualPathBetweenCycleSides i

Then the bridge theorem above is direct.

Option B: keep a geometric path and prove refinement

If you already have a topological/combinatorial notion of an interior-dual path, add a field:

lean
noTeleport :
  ∀ j,
    SameFragment (face j)
      (entryDart j)
      (exitDart j)

For endpoints:

lean
start_noTeleport :
  SameFragment (faceOf (c i)) (c i) (firstExitDart)

end_noTeleport :
  SameFragment (faceOf (alpha (c i))) (lastEntryDart) (alpha (c i))

Then prove:

lean
lemma fragment_dual_path_of_interior_dual_path_avoiding_cycle
  (P : InteriorDualPathAvoidingCycle i) :
  FragmentDualPathBetweenCycleSides i

The proof is by assigning:

lean
frag j := fragOf (face j) (exitDart-or-entryDart j) ...

and using noTeleport to show the other gate dart is in the same fragment.

Option C: ordinary dual path plus a separate compatibility predicate

Define:

lean
structure OrdinaryDualPath where
  n : Nat
  face : Fin (n+1) → OldFace
  edge : Fin n → D
  edge_not_cycle : ∀ j, ¬ IsCycleEdgeDart (edge j)
  left_face : ∀ j, faceOf (edge j) = face j.castSucc
  right_face : ∀ j, faceOf (alpha (edge j)) = face j.succ

Then define:

lean
def FragmentCompatible (P : OrdinaryDualPath) : Prop :=
  -- start endpoint
  SameFragment (P.face 0) (c i) (P.edge 0)
  ∧
  -- intermediate faces
  (∀ j, SameFragment (P.face j)
          (alpha (P.edge (j-1)))
          (P.edge j))
  ∧
  -- end endpoint
  SameFragment (P.face (Fin.last P.n))
    (alpha (P.edge (P.n-1)))
    (alpha (c i))

with the obvious special handling for n = 0.

Then:

lean
lemma fragment_dual_path_of_ordinary_dual_path
  (P : OrdinaryDualPath)
  (hcompat : FragmentCompatible P) :
  FragmentDualPathBetweenCycleSides i

and then:

lean
theorem banks_connected_of_compatible_ordinary_dual_path
  (P : OrdinaryDualPath)
  (hcompat : FragmentCompatible P) :
  CutConn (bankDart Side.plus i) (bankDart Side.minus i)

Do not state the theorem for arbitrary OrdinaryDualPath.

8. Endpoint lemmas in detail
8.1 Start face

Let

lean
F₀ := P.frag 0

The endpoint data gives:

lean
hstart : c i ∈ F₀.carrier

Then for every d ∈ F₀,

lean
CutConn (old d) (old (c i))

by fragment_cut_connected.

Also:

lean
CutConn (old (c i)) (bankDart Side.plus i)

by the local cut construction.

Thus:

lean
lemma start_fragment_in_plus_component
  (P : FragmentDualPathBetweenCycleSides i) :
  ∀ d ∈ (P.frag 0).carrier,
    CutConn (old d) (bankDart Side.plus i)
8.2 End face

Let

lean
Fₙ := P.frag (Fin.last P.n)

The endpoint data gives:

lean
hend : alpha (c i) ∈ Fₙ.carrier

Then for every d ∈ Fₙ,

lean
CutConn (old d) (old (alpha (c i)))

and

lean
CutConn (old (alpha (c i))) (bankDart Side.minus i)

so:

lean
lemma end_fragment_in_minus_component
  (P : FragmentDualPathBetweenCycleSides i) :
  ∀ d ∈ (P.frag (Fin.last P.n)).carrier,
    CutConn (old d) (bankDart Side.minus i)

These are the only endpoint facts needed.

9. Edge cases
9.1 m = 0

There are no uncut edge crossings.

A valid fragment-level path of length zero contains a single face-fragment F with both endpoint darts:

lean
c i ∈ F.carrier
alpha (c i) ∈ F.carrier

Then:

lean
CutConn (old (c i)) (old (alpha (c i)))

by fragment_cut_connected.

Composing with the cap attachments gives:

lean
CutConn (bankDart Side.plus i) (bankDart Side.minus i)

So the theorem works.

But note the important distinction:

lean
faceOf (c i) = faceOf (alpha (c i))

alone is not enough.

For m = 0, the ordinary-dual statement must require:

lean
SameFragment (faceOf (c i)) (c i) (alpha (c i))

Otherwise it is exactly the forbidden teleport across a straddling face.

9.2 A face visited twice

No problem.

The path is indexed by positions, not by face values. If

lean
face j = face ℓ

with j ≠ ℓ, the fragments

lean
frag j : FaceFragment (face j)
frag ℓ : FaceFragment (face ℓ)

may be equal or different. The induction only uses consecutive edge joins.

No global simplicity of the dual path is needed.

9.3 Backtracking across an edge

Also no problem.

If

lean
edge (j+1) = alpha (edge j)

or the path immediately crosses back, the corresponding alpha' joins still prove the consecutive fragments connected. The theorem does not require the path to be reduced.

9.4 A noncycle loop edge whose two darts lie in the same old face

Also fine.

If

lean
faceOf a = faceOf (alpha a)

and a is not a cycle edge, then alpha'_old_of_not_cycle gives:

lean
CutConn (old a) (old (alpha a))

This may connect two different fragments of the same old face. That is allowed because the connection comes from an actual uncut primal edge, not from the false same-face relay.

9.5 Path touches endpoint faces again

Allowed.

The start and end conditions only concern positions 0 and n.

If some intermediate face j equals faceOf (c i) or faceOf (alpha (c i)), nothing special happens. Its fragment is whatever the path data supplies. If the path wants to use the endpoint cycle dart again internally, that would violate edge_not_cycle only if it crosses the cycle edge. Merely being in a face incident to e_i is harmless.

9.6 Path attempts to cross a cycle edge

Forbidden by:

lean
edge_not_cycle : ∀ j, ¬ IsCycleEdgeDart (edge j)

This is essential. Across a cycle edge, alpha' (old (c i)) is no longer old (alpha (c i)); it is a cap dart. Therefore the old dual adjacency does not lift as an alpha' join.

10. Dependency-ordered lemma list

Here is the implementation order I would use.

Layer 1: cut connectedness API
lean
def CutStep (x y : Dcut) : Prop :=
  y = alpha' x ∨ y = sigma' x ∨ x = alpha' y ∨ x = sigma' y

def CutConn : Dcut → Dcut → Prop :=
  Relation.ReflTransGen CutStep

Lemmas:

lean
cutConn_refl
cutConn_symm
cutConn_trans

cutConn_alpha :
  CutConn x (alpha' x)

cutConn_sigma :
  CutConn x (sigma' x)

cutConn_phi :
  CutConn x (phi' x)

Proof of cutConn_phi:

lean
x --alpha'--> alpha' x --sigma'--> sigma' (alpha' x) = phi' x
Layer 2: bank components
lean
bank_same_side_connected :
  ∀ s i j, CutConn (bankDart s i) (bankDart s j)

cycle_plus_attached :
  ∀ i, CutConn (old (c i)) (bankDart Side.plus i)

cycle_minus_attached :
  ∀ i, CutConn (old (alpha (c i))) (bankDart Side.minus i)

Then:

lean
not_both_bank_components_of_hsep
cut_component_dichotomy_of_hsep

using Part A.

Layer 3: old faces and fragments

Definitions:

lean
SameOldFace
OldFace
faceOf
SurvivingFaceStep
SameFragment
FaceFragment
fragOf

Core lemmas:

lean
cutConn_of_survivingFaceStep :
  SurvivingFaceStep f d e →
  CutConn (old d) (old e)

cutConn_of_sameFragment :
  SameFragment f d e →
  CutConn (old d) (old e)

fragment_cut_connected :
  d ∈ F.carrier →
  e ∈ F.carrier →
  CutConn (old d) (old e)

Boundary lemmas:

lean
fragment_boundary_is_cut_diversion :
  d ∈ F.carrier →
  faceOf (φ d) = f →
  φ d ∉ F.carrier →
  phi' (old d) ≠ old (φ d)

broken_old_face_step_implies_cycle_incidence :
  phi' (old d) ≠ old (φ d) →
  IsCycleDart d ∨ IsCycleDart (φ d)

Endpoint component lemmas:

lean
fragment_containing_cycle_plus_lies_plus :
  c i ∈ F.carrier →
  ∀ d ∈ F.carrier,
    CutConn (old d) (bankDart Side.plus i)

fragment_containing_cycle_minus_lies_minus :
  alpha (c i) ∈ F.carrier →
  ∀ d ∈ F.carrier,
    CutConn (old d) (bankDart Side.minus i)
Layer 4: uncut dual gates
lean
alpha'_old_of_not_cycle :
  ¬ IsCycleEdgeDart a →
  alpha' (old a) = old (alpha a)

cutConn_across_uncut_dual_gate :
  ¬ IsCycleEdgeDart a →
  CutConn (old a) (old (alpha a))

Proof: one alpha' step plus rewriting.

Layer 5: fragment dual paths

Definitions:

lean
FragmentDualPath
FragmentDualPathBetweenCycleSides
FragCutConn

Lemmas:

lean
fragCutConn_step_across_uncut_edge :
  ∀ j, FragCutConn (P.frag j.castSucc) (P.frag j.succ)

all_path_fragments_cut_connected :
  FragCutConn (P.frag 0) (P.frag (Fin.last P.n))

Then the main theorem:

lean
banks_connected_of_fragment_dual_path_between_cycle_faces :
  FragmentDualPathBetweenCycleSides i →
  CutConn (bankDart Side.plus i) (bankDart Side.minus i)
Layer 6: contradiction theorem
lean
no_fragment_dual_path_if_banks_separated :
  ¬ CutConn (bankDart Side.plus i) (bankDart Side.minus i) →
  FragmentDualPathBetweenCycleSides i →
  False
Layer 7: optional refinement from ordinary/geometric path

If needed:

lean
OrdinaryDualPath
FragmentCompatible
fragment_dual_path_of_ordinary_dual_path
banks_connected_of_compatible_ordinary_dual_path

or:

lean
InteriorDualPathAvoidingCycle
fragment_dual_path_of_interior_dual_path_avoiding_cycle

This is the correct place to prove that the path does not teleport across straddling faces.

11. Final bridge theorem

The theorem you should expose to the Jordan chapter should be:

lean
theorem banks_connected_of_dual_path_between_cycle_faces
  (P : FragmentDualPathBetweenCycleSides i) :
  CutConn (bankDart Side.plus i) (bankDart Side.minus i) :=
by
  exact banks_connected_of_fragment_dual_path_between_cycle_faces P

If the book-facing statement wants the older name, keep the name but make the hypothesis fragment-compatible.

The essential invariant is:

A lifted dual path is a chain of face-fragments.
Consecutive fragments are connected only across actual uncut primal edges.
Inside one old face, the path may continue only within the same fragment.
Straddling faces are handled by refusing the false same-face relay, not by proving it.

That closes Part B cleanly.