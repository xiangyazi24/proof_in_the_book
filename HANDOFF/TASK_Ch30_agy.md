# TASK Ch30: Upgrade chapter30 from Tier 1 (BadInvolutionCertificate hypothesis) to Tier 2 (concrete construction)

## Background

`Chapter30.lean` already has the Tier 1 statement:
```lean
theorem chapter30 {n : ℕ} {R : Type*} [CommRing R] [IsAddTorsionFree R]
    (M : Matrix (Fin n) (Fin n) R)
    (cert : BadInvolutionCertificate (Equiv.Perm (Fin n)) R)
    (h_weight : ∀ σ, cert.signedWeight σ = Equiv.Perm.sign σ • ∏ i, M (σ i) i) :
    M.det = ∑ σ ∈ Finset.univ.filter (fun σ => ¬ cert.bad σ),
      Equiv.Perm.sign σ • ∏ i, M (σ i) i := ...
```

The `BadInvolutionCertificate` structure (line 134) packages:
- `bad : Family → Prop` (which families are "intersecting")
- `tauBad : {F // bad F} ≃ {F // bad F}` (the involution)
- `signedWeight : Family → R`
- `sign_reverse : signedWeight (tauBad F).1 = -signedWeight F.1`

For Tier 2, we need a CONSTRUCTION: given concrete lattice paths in a grid, build this certificate. The mathematical content is the standard LGV swap.

## Tier 2 task (simplified scope)

Construct, in `Chapter30.lean`, a concrete `BadInvolutionCertificate` for the
**lattice-path setting on ℤ²** at an abstract combinatorial level. You do NOT
need to handle full geometric lattice paths; instead define a combinatorial
abstraction that captures the involution structure.

### Step 1: Define the family type

A "path family" of size n with vertices in a vertex type V:
```lean
structure LatticePathFamily (n : ℕ) (V : Type*) [DecidableEq V] where
  perm : Equiv.Perm (Fin n)
  paths : Fin n → List V  -- ordered list of vertices
```

A family is "bad" if two paths share a vertex (intersecting):
```lean
def LatticePathFamily.bad {n V} [DecidableEq V] (F : LatticePathFamily n V) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ ((F.paths i).toFinset ∩ (F.paths j).toFinset).Nonempty
```

### Step 2: Define the involution

For a bad family, find the earliest pair (i, j) (lex order on Fin n × Fin n)
with i < j and shared vertex. Find the first vertex shared. Swap the tails of
paths i and j at that vertex. Update the permutation by composing with
swap i j.

This gives a self-inverse map on bad families. Prove it's an involution.

Helper:
```lean
def LatticePathFamily.swapAt {n V} [DecidableEq V] (F : LatticePathFamily n V)
    (i j : Fin n) (v : V) : LatticePathFamily n V :=
  -- find position p in (F.paths i) where p = v (use List.indexOf)
  -- find position q in (F.paths j) where q = v
  -- new paths i = take p (F.paths i) ++ drop q (F.paths j)
  -- new paths j = take q (F.paths j) ++ drop p (F.paths i)
  -- new perm = F.perm * swap i j (using Equiv.Perm.swap or Equiv.swap on Fin n)
  sorry
```

### Step 3: Define signedWeight and prove sign_reverse

```lean
def LatticePathFamily.signedWeight {n V R} [DecidableEq V] [CommRing R]
    (weight : V → R) (F : LatticePathFamily n V) : R :=
  Equiv.Perm.sign F.perm • ∏ i, (F.paths i).map weight |>.prod
```

For `sign_reverse`: after swap, perm changed by `swap i j` so sign flips. The
product of weights: the multiset of vertices visited by the swap is the same
(same vertices, just redistributed between two paths). So the product is
unchanged.

→ signedWeight changes by exactly `-1` factor. Done.

### Step 4: Package as `BadInvolutionCertificate`

```lean
def latticeLGV_certificate {n : ℕ} {V : Type*} {R : Type*} [DecidableEq V]
    [CommRing R] [IsAddTorsionFree R] [Fintype (LatticePathFamily n V)]
    (weight : V → R) :
    BadInvolutionCertificate (LatticePathFamily n V) R where
  bad F := F.bad
  bad_decidable := ... (decidable from finite check)
  tauBad := ... (the involution from Step 2)
  signedWeight := LatticePathFamily.signedWeight weight
  sign_reverse F := ... (from Step 3)
```

### Step 5: Apply to chapter30 to drop the hypothesis

Build a NEW theorem `chapter30_concrete` that USES this certificate. The
existing `chapter30` (hypothesis form) can stay for now — add `chapter30_concrete`
alongside.

```lean
theorem chapter30_concrete {n : ℕ} {V R : Type*} [DecidableEq V]
    [CommRing R] [IsAddTorsionFree R] [Fintype V]
    [Fintype (LatticePathFamily n V)] [DecidableEq (LatticePathFamily n V)]
    (weight : V → R) (M : Matrix (Fin n) (Fin n) R)
    (h_M_eq : ∀ i j, M i j = sorry /- "weighted count of paths" condition -/) :
    M.det = ∑ F ∈ (Finset.univ.filter (fun F : LatticePathFamily n V => ¬ F.bad)),
      LatticePathFamily.signedWeight weight F := by
  -- use latticeLGV_certificate and lgv_lemma_of_certificate
  sorry
```

## Honest scope

- Step 1 (~10 LOC): straightforward structure.
- Step 2 (~40 LOC): swapAt + involution proof; need to handle `List.indexOf`
  carefully (use `WellFoundedRecursion` or just `List.findIdx`).
- Step 3 (~30 LOC): show product unchanged (multiset equality).
- Step 4 (~10 LOC): bundle it.
- Step 5 (~20 LOC): tie to chapter30 via lgv_lemma_of_certificate.

Total ~100-150 LOC.

## Constraints

- 0 sorry, 0 axiom, 0 admit when done.
- All builds remote: `bash ~/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book --file ProofsInTheBook/Chapter30.lean`
- File oracle questions to `HANDOFF/oracle/QUESTION_30_NN_agy.md` if blocked on Mathlib API.

## What you should NOT do

- Do NOT add Prop hypotheses to `chapter30` that hide the work.
- Do NOT use axiom.
- Do NOT keep `cert : BadInvolutionCertificate ...` as input for `chapter30_concrete`.

Go. Read this file, then start with Step 1. Build remotely after each step
to catch errors early.
