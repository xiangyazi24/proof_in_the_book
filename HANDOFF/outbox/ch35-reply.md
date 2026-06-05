## Ch35 vertex-deletion reply

Created `ProofsInTheBook/PlanarMapDelete.lean`.

Verified:

```bash
/data/home/xhuan5/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake env lean ProofsInTheBook/PlanarMapDelete.lean
```

Result: passes.  The plain `lake` executable is not in PATH in this shell, so I used the Lake binary matching `lean-toolchain` (`leanprover/lean4:v4.30.0-rc2`).  The check emits only one linter warning about an unused section variable `[DecidableEq D]` in `exists_pos_pow_notMem`; no errors.

No `sorry`, `axiom`, or `native_decide` in the new file.

Implemented:

- `Equiv.Perm.deleteSet (p : Equiv.Perm D) (S : Finset D) : Equiv.Perm {d : D // d ∉ S}` using the first positive `p`-iterate outside `S`.
- `Equiv.Perm.sameCycle_deleteSet_iff`: deleted permutation cycles are exactly original `p`-cycles restricted to surviving points.
- `CombMap.vertexDarts`, `dartVertexDegree`, `deleteVertexSet`.
- `CombMap.deleteVertex`: deletes the closed dart star `vertexDarts v ∪ α '' vertexDarts v`; `α` is restricted and `σ` is `Perm.deleteSet` over that deleted set.
- `deleteVertex` proves the restricted `α` is an involution and fixed-point-free through the `CombMap` fields.
- `deleteVertex_E`: edge count under `NoLoopAt v`, `(M.deleteVertex v).E = M.E - M.dartVertexDegree v`.
- `deleteVertex_V_of_orbitEquiv`: vertex count factored through the exact remaining orbit-equivalence hypothesis.

Blockers / design notes:

1. `HANDOFF/EULER_DESIGN_r3.md` is not present in this checkout.  I used `HANDOFF/TASK_Ch35.md` plus the existing `PlanarMap.lean`/`PlanarMapEuler.lean`.
2. The task text says delete the `σ`-orbit of `v` and restrict `α`.  That set is not generally `α`-stable: if `d` is at `v`, `α d` is usually at the neighboring vertex.  Restricting `α` to the complement of only `vertexDarts v` is therefore ill-typed/false in general.
3. I used closed-star deletion (`vertexDarts v ∪ α '' vertexDarts v`) so `α` really restricts.  With this choice, `V' = V - 1` is not automatic: deleting opposite darts can delete all darts of a neighboring vertex (for example a degree-1 neighbor in the dart-only model).  The file exposes the exact quotient equivalence needed as `deleteVertex_V_of_orbitEquiv`.
4. `E' = E - deg(v)` needs `NoLoopAt v`; otherwise a loop at `v` contributes two darts to `dartVertexDegree` but removes one edge.
5. Face-count change and Euler preservation were not attempted beyond these blockers; they still need the deleted-star boundary/orbit lemma.
