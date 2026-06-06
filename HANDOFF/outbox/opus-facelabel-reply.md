# opus-facelabel reply — genus-free F-count orbit-label layer (Ch35)

## Status: DESIGN ROUTE REFUTED (Lean-verified). Core NOT closed unconditionally.

`ProofsInTheBook/CutFaceLabel.lean` written, builds clean on **uisai2**
(`lake env lean ProofsInTheBook/CutFaceLabel.lean`, exit 0, no errors, no warnings,
no `sorry`/`axiom`/`admit`/`native_decide`). But the deliverable is **not** a closed
`NumCyclesCutPhi2` — because the prescribed design route is mathematically
**unrealizable**, not merely hard, and I verified that inside Lean.

## The finding

The genus-free design (route B) wants the proven engine `OrbitLabelCert` instantiated
at `β = OldFace(φ) ⊕ Side` with a label `cutFaceLabel : CutDart → OldFace(φ) ⊕ Side`
that is (a) `φ'₂`-invariant and (b) sends `inl d ↦ Sum.inl (faceOf d)`. Both required
structural fields (`cutFaceLabel_phi'2` + the `faceOf` form; and Layer-6
`oldFaceLift_phi_step`) **have no instance**, because they assert a `φ'₂`-orbit
structure that contradicts the actual `φ'₂`-orbits.

Verified in actual Lean on the repo's own computable mirror (`SeamInstEval`), K₄
**sphere** cut A→B→D (F=4, F'=6):

- old φ-faces: `{0,8,5} {1,2,7} {3,4,11} {6,10,9}`
- φ'₂-orbits: `{0,8,5} {1,4,9} {2,7,c0+} {3,c2+,11} {6,10,c1+} {c0-,c1-,c2-}`

Two fatal facts:
1. φ'₂-orbit `{1,4,9}` **mixes three distinct old faces** (1∈{1,2,7}, 4∈{3,4,11},
   9∈{6,10,9}). A φ'₂-invariant label is constant on orbits ⇒ it would have to give
   1,4,9 one single old face. Impossible ⇒ `cutFaceLabel_phi'2` + `faceOf`-form is
   **unsatisfiable**.
2. Old face `{1,2,7}` **splits across two φ'₂-orbits** (1∈{1,4,9}; 2,7∈{2,7,c0+}).
   `oldFaceLift_phi_step` for d=1 (φ1=2) needs `SameCycle φ'₂ (lift 1)(lift 2)`, but
   they sit in different φ'₂-orbits ⇒ **no lift can repair it** (cannot merge two
   genuinely distinct orbits).

This is the same obstruction `PlanarMapCutCap2F.lean` already records in prose ("old
faces do not survive intact; the naive face-survival bijection is false as stated"),
now pinned to the exact failing certificate fields with a Lean-checked witness. The
COUNT `F' = F+2` is TRUE across genus (kernel-confirmed: triangle 2→4, K4-sphere 4→6,
K4-torus 2→4); it is the *route* that is false. φ'₂ genuinely reorganises darts;
its orbits are not "old faces (rerouted) + 2 caps".

No genus-uniform, closed-form φ'₂-invariant label onto a type of independent
cardinality F+2 exists (the only natural such target the design named, OldFace⊕Side,
is the refuted one).

## What the file delivers (all unconditional, genus-free, building)

- `Side` (Fintype/DecidableEq), `OldFace M`, `faceOf`, `faceOf_phi`, `faceOf_eq_iff`
- `CutFaceLabel := OldFace ⊕ Side`; **`card_cutFaceLabel : card CutFaceLabel = M.F+2`**
  (the true counting content the engine would consume after a valid label)
- `plusAnchor`/`minusAnchor` (the two cap-face anchors)
- `numCyclesCutPhi2_of_orbitLabelCert`: an honest **conditional** bridge — *any*
  `OrbitLabelCert φ'₂ CutFaceLabel` discharges `NumCyclesCutPhi2` (via the proven
  engine + the card bridge). It carries the certificate as an explicit hypothesis
  precisely because no such certificate exists for the design's label; it is NOT a
  closed proof of the core, just a faithful statement of the route's remaining
  obligation. No false lemma, no unsatisfiable-hypothesis theorem, no sorry.
- Two reproducible `#eval` Lean anchors printing the orbits/faces above.

I deliberately did NOT construct a fake `cutFaceLabelCert` / false `oldFaceLift_phi_step`
/ sorry'd core — that would require an unsatisfiable field or `sorry`, which the repo
forbids and the playbook (§3.3) flags as the worst failure mode (vacuous/impostor).

## Bottom line for `NumCyclesCutPhi2`

The strongest honest result for the core remains the already-formalised **conditional**
`SeamInst.SeamDecomposition.numCyclesCutPhi2` (genus-0; provably fails at genus-1). A
genus-free unconditional closing of `NumCyclesCutPhi2` does **not** go through the
OldFace⊕Side orbit-label as designed. If the chapter wants it unconditionally, it needs
a different φ'₂-invariant labelling whose target has independently-computable
cardinality F+2 — currently unknown, and the natural candidate is refuted here.

## Verification

uisai2: `cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH &&
lake env lean ProofsInTheBook/CutFaceLabel.lean` → exit 0, prints only the two #eval
anchors. Dep oleans (OrbitLabelCert, PlanarMapCutCap2FWalk, PlanarMapSeamInst) already
present. NEVER built locally (kernel-panic rule respected). No commits, branch
untouched.
