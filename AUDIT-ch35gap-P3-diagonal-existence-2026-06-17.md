Decisive answer: **do not assume face-boundary simplicity; it is false for simple sphere maps.** The addable-diagonal statement is the right theorem, but it is a substantial “maximal planar iff triangulated” theorem. If you have not proved that theorem, carry a **diagonal-existence contract**, not a face-boundary-simplicity contract.

So:

```lean
IsSphereMap + IsSimpleGraph ⊬ face-boundary-simple
```

but the intended theorem

```lean
faceLen f > 3 → ∃ addable diagonal in f
```

is the standard planar-map maximality theorem. It is not a cheap consequence of the current fields.

The repo’s `CombMap.IsSphereMap` is only `Connected ∧ eulerChar = 2`. fileciteturn123file0L71-L79 `IsSimpleGraph` only rules out dart-loops and parallel edges. fileciteturn127file0L98-L107 Neither says a face boundary has no repeated vertex.

## 1. What is true and what is not

A simple sphere map may have repeated vertices on a face boundary. A plane tree is the standard mental model: it is connected, simple, has Euler characteristic `V - E + F = 2`, and has one face whose boundary walk repeats vertices and edges. So any lemma of the form

```lean
IsSphereMap M → IsSimpleGraph M → every face boundary is a simple cycle
```

is false.

However, for a genuine simple cellular sphere embedding, if a face boundary walk has length `> 3`, there should be an **addable edge inside that face** between two boundary occurrences whose vertices are distinct and not already adjacent. This is the local form of:

```text
A simple plane graph is maximal planar iff every face is triangular.
```

But proving that from your current combinatorial-map primitives is a real theorem. It is not just list arithmetic on `φ.toList`.

The subtle point is that nonconsecutive boundary vertices are **not automatically nonadjacent**. A square face can have one diagonal already drawn through the other side of the embedding; the other diagonal is still missing. So the correct statement is existential:

```text
there exists a missing nonconsecutive pair,
```

not

```text
every nonconsecutive pair is missing.
```

## 2. Minimal honest contract

The minimal non-vacuous contract should be exactly the missing theorem, not stronger face-boundary simplicity.

Define the choice in terms of **two occurrences** on the `φ`-cycle, not merely two vertices:

```lean
structure FaceDiagonalChoice (M : CombMap D) (f : M.Face) where
  root : D
  step : ℕ

  root_face : M.dartFace root = f

  /-- `step` is an honest non-adjacent boundary separation in the face walk. -/
  step_ge_two : 2 ≤ step

  /-- The complementary face arc also has at least two old boundary edges. -/
  step_le : step + 2 ≤ M.faceLen f
  -- equivalently: 2 ≤ M.faceLen f - step

  /-- The endpoint vertices of the proposed diagonal. -/
  endpoints_distinct :
    M.tail root ≠ M.tail ((M.φ ^ step) root)

  /-- The graph does not already contain this edge. -/
  no_old_edge :
    ¬ M.toSimpleGraph.Adj
        (M.tail root)
        (M.tail ((M.φ ^ step) root))
```

Then the actual contract:

```lean
structure FaceDiagonalizable (M : CombMap D) : Prop where
  exists_choice :
    ∀ f : M.Face, 3 < M.faceLen f → Nonempty (FaceDiagonalChoice M f)
```

or, if you want to keep it computational:

```lean
class FaceDiagonalizable (M : CombMap D) : Prop where
  exists_choice :
    ∀ f : M.Face, 3 < M.faceLen f → ∃ c : FaceDiagonalChoice M f, True
```

This is the right §3.3 shape: it is not the conclusion “triangulation exists”; it is the local, checkable addable-diagonal property consumed by the already-proved surgery.

Do **not** use:

```lean
∀ f, (faceDartList root).map M.tail is Nodup
```

as the general contract. It excludes valid simple plane graphs with cut vertices and bridges. It is stronger than necessary and would make your final “general planar graph” theorem too narrow.

## 3. The theorem you would eventually prove

The full non-residual theorem should be:

```lean
theorem faceDiagonalizable_of_simple_sphere
    (hSphere : M.IsSphereMap)
    (hSimple : M.IsSimpleGraph)
    (hNontrivial : 3 ≤ M.V) :
    FaceDiagonalizable M := ...
```

This is the combinatorial-map version of maximal-planar triangulability.

A possible proof strategy is by contradiction:

1. Suppose a face `f` has `faceLen f > 3` and no addable diagonal.
2. Show every eligible nonconsecutive boundary-occurrence pair is already adjacent in `M.toSimpleGraph` or identifies the same vertex.
3. Use sphere separation / Jordan-style arguments to show this forces enough chords to split the face already, contradicting that `f` is one `φ`-orbit of length `> 3`.

That third step is exactly the hard planar-map theorem. It is not present in the current repo infrastructure as a ready lemma.

An alternative global proof is:

```text
If no addable edge exists anywhere, the simple sphere map is maximal.
Maximal simple sphere maps have all faces triangular.
Contradiction.
```

But proving “maximal simple sphere map ⇒ all faces triangular” is the same missing theorem.

## 4. Face-boundary-simple special case

If you temporarily restrict to 2-connected plane maps where every face boundary is a simple cycle, the statement becomes easier but still not automatic for each pair.

A useful special-case theorem is:

```lean
theorem exists_diagonal_of_simple_face_boundary
    (hSphere : M.IsSphereMap)
    (hSimple : M.IsSimpleGraph)
    (hbd : FaceBoundarySimple M f)
    (hlen : 3 < M.faceLen f) :
    Nonempty (FaceDiagonalChoice M f)
```

Here `FaceBoundarySimple M f` can be:

```lean
def FaceBoundarySimple (M : CombMap D) (f : M.Face) : Prop :=
  ∃ root : D,
    M.dartFace root = f ∧
    ((M.faceDartList root).map M.tail).Nodup
```

But even here, the key step is existential. A nonconsecutive boundary pair may already be adjacent elsewhere; you must prove not all such pairs are adjacent. For a simple sphere embedding, that follows from planarity/maximality, but it is still nontrivial.

So `FaceBoundarySimple` is not the minimal contract; it is a helpful lemma target for 2-connected cases.

## 5. Exact Lean skeleton with the carried contract

Assuming your one-step insertion theorem is already proved:

```lean
def faceExcess (M : CombMap D) : ℕ :=
  ∑ f : M.Face, M.faceLen f - 3
```

use the contract like this:

```lean
noncomputable def triangulate
    (M : CombMap D)
    (hSphere : M.IsSphereMap)
    (hSimple : M.IsSimpleGraph)
    (hDiag : FaceDiagonalizable M) :
    TriangulationExtension M :=
by
  classical
  -- recurse on `faceExcess M`
  refine WellFounded.fix (measure_wf faceExcess) ?step M hSphere hSimple hDiag
```

Step:

```lean
-- If all faces are triangular, build NearTriangulation.
by_cases htri : ∀ f : M.Face, M.faceLen f = 3
· exact buildNearTriangulationFromAllFacesTriangular M hSphere hSimple htri

-- Otherwise choose a face with length > 3.
· have hex : ∃ f : M.Face, 3 < M.faceLen f := by
    -- This requires a side lemma ruling out faceLen < 3 as the only obstruction,
    -- or a measure/condition that directly targets non-triangular faces.
    ...

  rcases hex with ⟨f, hf⟩
  rcases (hDiag.exists_choice f hf) with ⟨c⟩

  let M' := addFaceDiagonal M c
  have hSphere' := addFaceDiagonal_sphere M hSphere hSimple c
  have hSimple' := addFaceDiagonal_simple M hSphere hSimple c
  have hDiag' : FaceDiagonalizable M' := by
    -- If `FaceDiagonalizable` is a global external contract, you need it for each
    -- intermediate map too. Better package the recursion contract as a supplier:
    -- `∀ M in extension chain, FaceDiagonalizable M`.
    ...

  have hdecrease : faceExcess M' < faceExcess M :=
    addFaceDiagonal_faceExcess_decrease M c

  exact recurse M' hSphere' hSimple' hDiag' hdecrease
```

Important: if you carry `FaceDiagonalizable` only for the original `M`, you still need it for the maps after adding diagonals. So the contract should be part of a **triangulation supplier** closed under insertion, or stated as a theorem for all simple sphere maps:

```lean
structure FaceDiagonalSupplier : Type where
  exists_choice :
    ∀ {D} [Fintype D] [DecidableEq D] (M : CombMap D),
      M.IsSphereMap → M.IsSimpleGraph →
      ∀ f : M.Face, 3 < M.faceLen f → Nonempty (FaceDiagonalChoice M f)
```

Then after insertion you just call the supplier again on `M'`.

This mirrors your Ch35 residual discipline: the supplier is uniform, so it is not a one-map vacuity trap.

## 6. Non-vacuity examples

### Triangle

For a triangular near-triangulation, the supplier is vacuous at each face because no face satisfies `3 < faceLen f`.

```lean
def triangleFaceDiagonalizable (M : CombMap D)
    (htri : ∀ f : M.Face, M.faceLen f = 3) :
    FaceDiagonalizable M where
  exists_choice := by
    intro f hf
    exfalso
    rw [htri f] at hf
    omega
```

This is useful for checking that the contract is not contradictory.

### Square

For a square sphere map, each face has length `4`. A concrete choice is:

```lean
root := dart 0→1
step := 2
target := φ^[2] root   -- tail is vertex 2
```

Then:

```lean
step_ge_two : 2 ≤ 2
step_le : 2 + 2 ≤ 4
endpoints_distinct : v0 ≠ v2
no_old_edge : ¬ Adj v0 v2
```

After inserting diagonal `0-2` in one face, the opposite quadrilateral still has a valid diagonal `1-3`. This demonstrates that the contract is satisfiable in the first nontrivial case.

For Lean, I would make the square witness a tiny finite explicit `CombMap` and close the facts by `decide`/enumeration if your project allows computational witnesses; otherwise prove by finite cases on `Fin 4`.

## 7. Answer to each question

1. **Face-boundary simplicity is not provable** from `IsSphereMap + IsSimpleGraph`; repeated face vertices occur in simple sphere maps with cut vertices. The addable-diagonal theorem is mathematically true for simple plane maps but is a substantial maximal-planar theorem, not a local consequence already available.

2. The minimal honest extra hypothesis is **not** face-boundary simplicity. It is a uniform `FaceDiagonalSupplier` / `FaceDiagonalizable` contract giving an addable diagonal for every face with `faceLen > 3`. This is non-vacuous: triangles satisfy it vacuously; squares satisfy it by an explicit missing diagonal.

3. For a simple face boundary, non-adjacency is **not automatic** for a particular nonconsecutive pair. A square may already have one diagonal. The correct theorem is existential: at least one suitable nonconsecutive pair is missing. In a full simple sphere map, proving that is equivalent to the usual maximal-planar triangulation theorem.

4. Clean Lean path: carry

```lean
FaceDiagonalSupplier
```

uniformly through the triangulation recursion, use your proven one-step insertion and faceExcess decrease, and separately build concrete non-vacuity witnesses. If you want the fully unconditional general theorem, the remaining theorem to prove is precisely:

```lean
faceDiagonalSupplier_of_simple_sphere :
  FaceDiagonalSupplier
```

This keeps the current final theorem honest: without that theorem, the general Five Color Theorem carries a triangulability residual; with it, the theorem closes unconditionally.
