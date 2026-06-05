# Separation reply: `ProofsInTheBook/PlanarMapSeparation.lean`

Status: **verified clean** on uisai1
(`lake env lean ProofsInTheBook/PlanarMapSeparation.lean` → exit 0, 0 errors,
0 warnings). 0 `sorry`/`axiom`/`admit`/`native_decide`. `#print axioms` on all
six headline declarations reports only `[propext, Classical.choice, Quot.sound]`.

Owns only the new file (263 lines). Imports `ProofsInTheBook.PlanarMapChordSplit`
(transitively files 5/4 and the NearTriangulation/Euler stack). Touches no other
file.

## Honest verdict

The target `separates_of_nearTriangulation : ... → Separates data` is **NOT
discharged unconditionally.** After sustained independent analysis I confirm the
file-5, file-6, and design-review verdict: the genus-0 chord separation is the
irreducible combinatorial Jordan/Euler input. It is equivalent to the per-side
Euler count `F₁ + F₂ = F + 1`, which needs the side sub-maps' Euler characteristic,
whose well-definedness (the kept set's α-closure) already needs separation —
circular at the CombMap API level (`IsSphereMap = Connected ∧ eulerChar = 2`).

I independently traced **Route B (bridge duality)** to its real conclusion: the
chord is a non-bridge of the FULL dual (it is not a primal loop, endpoints u≠v),
so it lies on some full-dual cycle — but that says nothing about the INTERIOR dual
(avoiding boundary edges + chord), which is the actual claim. The "any chord cycle
must use the outer face/a boundary edge" step IS planarity (Jordan) and has no
orbit-count shortcut. **Route A** (global Euler) hits the same wall: V, E, F are
global orbit counts that do not "see" the chord cycle without a side construction.

Per the task's explicit sanction, I therefore (a) proved the strongest
unconditional partial results, and (b) isolated the remainder as ONE named Prop
with exact statement, conditional theorem proved from it, no faking.

## Unconditional results (genuinely new vs files 5/6)

* `chordSplitAdj_source_not_outer`, `chordSplitAdj_endpoints_not_outer`,
  `chordSplitAdj_endpoints_faceLen_three` — every face on a `ChordSplitAdj` step
  is a non-outer triangle (file 5 only had the *target*; source via symmetry).
* `side₁_subset_triangles` / `side₂_subset_triangles` — every side face is a
  triangle.
* `not_separates_iff_face₂_mem`, `not_separates_sides_eq` — `¬ Separates`
  collapses the two reachability closures into one (`side₁ = side₂`).
* `chord_joins_faces_except_chord` — the chord's two darts join `face₁`/`face₂`
  across a non-boundary edge; the ONLY failed `ChordSplitAdj` clause is the chord
  exclusion. So the chord is the unique seam.
* `not_separates_iff_reachable_avoiding_chord` — `¬ Separates` is exactly a
  chord-avoiding dual path between the two chord faces, i.e. the chord is a
  non-bridge of the interior dual. This is the sharp reformulation of the gap.

## The one isolated input + conditional theorem

* `SphereChordSeparation h` (def, NearTriangulation level):
  `¬ ReflTransGen (ChordSplitAdj u v) face₁ face₂` — the interior-dual non-bridge
  / separating-cycle statement.
* `separates_of_nearTriangulation (data) (hsep : SphereChordSeparation data.chord)
  : data.Separates` — the conditional separation theorem.
* `sidesDisjoint_of_nearTriangulation` — discharges file-5's `SidesDisjoint` from
  the same input (via `separates_iff_sidesDisjoint`), the downstream payload.

**No overclaim:** `sphereChordSeparation_iff_separates` proves explicitly that the
isolated input is *equivalent to* `Separates` (definitionally the same content at
the interior-dual level), NOT a strictly higher-level Euler hypothesis. So this is
an honest single-point isolation + repackaging, not a vacuous/strengthened
conditional. The conditional theorem is non-vacuous: the input is exactly as
satisfiable as the true (and true) Jordan separation.

## For downstream (file 10 / Thomassen)

When a real producer of `SphereChordSeparation` (or `Separates`) becomes available
— the genuine route is a NEW CombMap-level Jordan/Euler lemma (sphere map ⇒ a
chord+arc cycle separates faces), or the full bidirectional side-map Euler count
`V₁+V₂=V+2, E₁+E₂=E+1, F₁+F₂=F+1 ⇒ chi₁+chi₂=4` with per-side `chi ≤ 2` forcing
the partition — it plugs straight in via `separates_of_nearTriangulation` /
`sidesDisjoint_of_nearTriangulation`, then file 6's `sideMap₁/₂` become genuine
CombMaps with valid α/σ.
