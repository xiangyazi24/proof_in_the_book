═══ BRIDGE pbook | 17b24a74 | 10111 chars 1458 words 359 lines | 260s | prov=? | OK ═══
═══ BRIDGE pbook | 17b24a74 | 10111 chars 1458 words 359 lines | 260s | prov=? | OK ═══
I’ll first isolate the mathematical implication of the bank theorem, then verify whether the current arc data has enough dart-level realization to build the chord∪path₂ cycle.

Your route is mathematically sound, but it closes ArcSideIdentification only after one extra piece of data that the current BoundaryArcSplit substrate does not expose: a dart realization of path₂ as the actual outer-cycle dart run, plus an orientation tie between that run and the chosen chord dart.

The new genus-slack/bank theorem is strong enough to break the path₁/path₂ symmetry. The remaining obstruction is no longer “side connectivity”; it is recovering the directed boundary darts of path₂ and proving they are the ones used in the explicit simple cycle.

1. If C = chord ∪ path₂ is explicit, the bank argument is sound

Assume you have a directed dart run for path₂:

lean
path₂Darts : List D

with these properties:

lean
∀ b ∈ path₂Darts, b ∈ hNT.outerCycle.darts
(path₂Darts.map M.tail) = data.arc.path₂.vertices.dropLast
-- or equivalent indexing: tails are the path₂ vertices except the terminal u
∀ consecutive b b', M.φ b = b'
M.tail path₂Darts.head = v
M.head path₂Darts.getLast = u

Also assume the chord dart is oriented compatibly:

lean
M.tail data.dart = u
M.head data.dart = v

Then define the simple primal cycle

lean
C₂.dart = [data.dart] ++ path₂Darts

so it goes

u --chord--> v --path₂ boundary arc--> u.

At the chord index:

lean
C₂.faceLeft chordIndex  = M.dartFace data.dart       = data.face₁
C₂.faceRight chordIndex = M.dartFace (M.α data.dart) = data.face₂

At a path₂ boundary dart b, since b is an outer-boundary dart,

lean
C₂.faceLeft pathIndex  = M.dartFace b       = hNT.outerFace
C₂.faceRight pathIndex = M.dartFace (M.α b) -- the bounded inner face across that boundary edge

Therefore the right bank of C₂ contains:

lean
data.face₂

and every bounded face across a path₂ boundary edge:

lean
M.dartFace (M.α b)

The generalized bank theorem should give:

lean
right_bank :
  ∀ i j,
    Relation.ReflTransGen (DualAvoidsCycleStep M C₂)
      (C₂.faceRight i) (C₂.faceRight j)

So in particular:

lean
Relation.ReflTransGen (DualAvoidsCycleStep M C₂)
  data.face₂
  (M.dartFace (M.α b))

Now convert this to side₂ membership.

data.side₂ is the ChordSplitAdj-closure from data.face₂; ChordSplitAdj crosses edges that are neither outer-boundary edges nor the chord. It is defined in PlanarMapChordSplitData.lean exactly as “share an edge that is neither a boundary edge nor the chord.” 

PlanarMapChordSplitData

A DualAvoidsCycleStep M C₂ only forbids edges of C₂, i.e. the chord plus the path₂ boundary edges. It does not syntactically forbid the other boundary arc’s edges. But on the data.face₂ bank, the outer face is not reachable; it is on the opposite bank because all path₂ boundary darts have outerFace on the left bank. Thus any path inside the face₂ bank cannot cross a boundary edge, since crossing a boundary edge would touch outerFace.

So prove this bridge:

lean
lemma right_bank_reach_lifts_to_chordSplitAdj
    {f : M.Face}
    (hf_bank :
      Relation.ReflTransGen (DualAvoidsCycleStep M C₂) data.face₂ f)
    (houter_sep :
      ¬ Relation.ReflTransGen (DualAvoidsCycleStep M C₂)
          data.face₂ hNT.outerFace) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₂ f

Then every path₂ boundary-edge inner face is in data.side₂.

Finally, if w is an internal vertex of path₂, pick the outgoing path₂ boundary dart b with

lean
M.tail b = w.

You know

lean
M.dartFace (M.α b) ∈ data.side₂.

But sideRegion₂ needs a kept dart whose tail is w. Use

lean
σ b

because:

lean
M.tail (M.σ b) = M.tail b = w
M.dartFace (M.σ b) = M.dartFace (M.α b)

So:

lean
M.σ b

is a side₂ dart at w, hence:

lean
w ∈ sideRegion₂ data.

This proves the path₂ half of ArcSideIdentification. The path₁ half is symmetric.

2. The construction is blocked by current BoundaryArcSplit

This is the real issue.

The current BoundaryPath structure has:

lean
vertices : List M.Vertex
edges    : List (Sym2 M.Vertex)
starts_at
ends_at
simple

but it does not state that the edges connect consecutive vertices, and it has no dart list. 

PlanarMapBoundary

BoundaryArcSplit stores:

lean
path₁ : BoundaryPath M u v
path₂ : BoundaryPath M v u
path₁_boundary_vertices
path₂_boundary_vertices
boundary_vertices_covered
internally_disjoint
path₁_internal_iff_proper
path₂_internal_iff_proper

but again no dart run and no field saying that path₂.vertices is a contiguous segment of outerCycle.darts.map M.tail. 

PlanarMapBoundary

By contrast, BoundaryCycle itself does expose the real dart list and the φ-successor relation:

lean
darts : List D
vertices = darts.map M.tail
edges = darts.map M.dartEdge
consecutive_phi
consecutive_vertex

PlanarMapBoundary

So the data needed to build C₂ exists in outerCycle, but the current data.arc.path₂ object does not expose its realization as a sub-run of that dart list. You cannot mechanically construct

lean
C₂ : SimplePrimalCycle M

from data.arc.path₂ unless you add a bridge.

This matches your previous obstruction: the substrate can prove only that a path₂-internal vertex is a boundary vertex distinct from the endpoints. The file PlanarMapChordSplit.lean already has the internal-vertex facts and boundary membership facts, but they are vertex-list facts, not dart-run facts. 

PlanarMapChordSplit

 

PlanarMapChordSplit

3. If the dart run exists, ArcSideIdentification is provable

With the explicit C₂, the lemma chain is:

A. Realize the arc as darts
lean
structure BoundaryPathDartRun
    (P : BoundaryPath M a b)
    (C : BoundaryCycle M hNT.outerFace) where
  darts : List D
  darts_sub_outer : ∀ d ∈ darts, d ∈ C.darts
  tails_eq : darts.map M.tail = P.vertices.dropLast
  first_tail : ...
  last_head : ...
  consecutive_phi : ∀ consecutive d e in darts, M.φ d = e
  edges_eq : darts.map M.dartEdge = P.edges

For path₂:

lean
path₂Run : BoundaryPathDartRun data.arc.path₂ hNT.outerCycle
B. Orient the chord

You need one of:

lean
M.tail data.dart = u ∧ M.head data.dart = v

or a case split that chooses the appropriate oriented chord dart and swaps the side labels accordingly.

For the current statement

lean
path₂-internal → sideRegion₂

you need the first orientation. If data.dart is reversed, the same construction puts path₂ on the face₁ bank instead.

This is important: hNT.chordDart is currently chosen from an unordered edge witness:

lean
M.dartEdge (hNT.chordDart h) = s(u, v)

It does not record tail/head orientation. 

PlanarMapChordSplitData

So either normalize chordDart, or state an orientation-dependent theorem.

C. Build the simple cycle
lean
def chordPath₂Cycle
    (hRun : BoundaryPathDartRun data.arc.path₂ hNT.outerCycle)
    (horient : M.tail data.dart = u ∧ M.head data.dart = v) :
    SimplePrimalCycle M

Its darts are:

lean
data.dart :: hRun.darts

The SimplePrimalCycle fields needed are exactly length, darts, tail injectivity, and consecutive incidence. The structure is in PlanarMapCutCap.lean. 

PlanarMapCutCap

D. Apply the generalized bank theorem
lean
have banks := SimpleCycleBankTheorem M C₂

Get:

lean
right_bank_path₂_inner :
  ∀ b ∈ hRun.darts,
    Relation.ReflTransGen (DualAvoidsCycleStep M C₂)
      data.face₂
      (M.dartFace (M.α b))
E. Convert bank reachability to ChordSplitAdj
lean
lemma path₂_inner_face_mem_side₂
    {b : D} (hb : b ∈ hRun.darts) :
    M.dartFace (M.α b) ∈ data.side₂

Proof: right-bank reach + no outer-face in right bank + step conversion to ChordSplitAdj.

Recall:

lean
data.side₂ = hNT.Side u v data.face₂

and Side is ReflTransGen (ChordSplitAdj u v). 

PlanarMapChordSplitData

F. Convert internal path vertices to sideRegion₂

For internal w, find an outgoing dart b ∈ hRun.darts with:

lean
M.tail b = w.

Then:

lean
M.dartFace (M.σ b) = M.dartFace (M.α b)
M.tail (M.σ b) = M.tail b = w

so M.σ b is a side₂ dart at w.

Thus:

lean
lemma path₂_internal_mem_sideRegion₂
    {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices) :
    w ∈ sideRegion₂ data

The path₁ version is symmetric using C₁ = chord ∪ path₁ with the opposite chord orientation/bank.

Then your already-machine-checked confinement proof closes.

4. The single missing lemma

The missing lemma is not another Jordan theorem. It is a dart realization/refinement of BoundaryArcSplit:

lean
lemma boundaryArcSplit_path₂_has_dartRun
    (data : hNT.ChordSplitData u v) :
    BoundaryPathDartRun data.arc.path₂ hNT.outerCycle

and similarly for path₁.

From the current fields of BoundaryArcSplit, this is not provable, because BoundaryPath does not assert that its edges connect consecutive vertices, nor that its vertex list is a contiguous run of the boundary cycle. It is an opaque arc certificate. 

PlanarMapBoundary

 

PlanarMapBoundary

However, it should be provable if you bypass BoundaryArcSplit and construct a new refined arc directly from outerCycle.darts, because BoundaryCycle has the real dart list and consecutive_phi. 

PlanarMapBoundary

So the best residual to add is not ArcSideIdentification as an axiom. It is:

lean
structure BoundaryArcSplitWithDarts ... extends BoundaryArcSplit ... where
  path₁_dartRun : BoundaryPathDartRun path₁ C
  path₂_dartRun : BoundaryPathDartRun path₂ C

or a theorem showing your existing data.arc came from such a refined split.

Final ruling

The chord∪path₂ bank-theorem route is sound and should prove ArcSideIdentification, but only after two explicit orientation/bookkeeping bridges:

lean
BoundaryPathDartRun data.arc.path₂ hNT.outerCycle
M.tail data.dart = u ∧ M.head data.dart = v

or an orientation-aware variant.

Without the dart-run bridge, you cannot build the SimplePrimalCycle C = chord ∪ path₂. Without the chord orientation bridge, the theorem may identify path₂ with side₁ rather than side₂.

So the real remaining residual is:

lean
path₂ has a directed outer-cycle dart realization, and the chosen chord dart is oriented compatibly with the side labels.

Once that is present, the generalized genus-slack bank theorem gives ArcSideIdentification; the old seed residual is unnecessary.
