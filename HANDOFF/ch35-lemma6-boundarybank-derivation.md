═══ BRIDGE pbook | 55bc0049 | 12271 chars 2232 words 589 lines | 269s | prov=network | OK ═══
═══ BRIDGE pbook | 55bc0049 | 12271 chars 2232 words 589 lines | 269s | prov=network | OK ═══
The boundary-bank count is true, and the proof is **pure orbit algebra** once you expose the two boundary darts at each boundary vertex. No fan-incidence theorem is needed.

I’ll use the following notation. Let

```text
qᵢ := outerDart i        -- the i-th dart of the outer face, in φ-order
rᵢ := α qᵢ              -- the reverse boundary dart
vᵢ := tail qᵢ           -- the i-th boundary vertex
next i := i+1 mod B
prev i := i-1 mod B
```

The outer boundary data gives

```text
φ qᵢ = qₙₑₓₜᵢ
```

because `BoundaryCycle.consecutive_phi` says consecutive boundary darts agree with `φ`. The boundary cycle structure exposes `darts`, `vertices`, `edges`, `vertices_eq`, `edges_eq`, and `consecutive_phi`; `NearTriangulation` additionally stores `outer_simple` and `outer_len`. fileciteturn104file0L121-L154 fileciteturn100file0L20-L31

Since

```text
φ = σ ∘ α,
```

we get the two key identities:

```text
σ rᵢ = σ (α qᵢ) = φ qᵢ = qₙₑₓₜᵢ       (1)

σ rₚᵣₑᵥᵢ = qᵢ                         (1')
```

Now define

```text
OuterDel = {qᵢ | i} ∪ {rᵢ | i}
αout d  = d     if d ∈ OuterDel
        = α d   otherwise
P       = φ ∘ αout
```

The raw restricted involution `rawAlpha` in `SubmapPlanar.lean` is exactly this operation: it fixes deleted darts and equals `M.α` off the deleted set. The file proves the fixed/deleted and kept/outside equations as `rawAlpha_eq_self_of_mem` and `rawAlpha_eq_alpha_of_notMem`. fileciteturn128file0L116-L154

So:

```text
if d ∉ OuterDel,     P d = φ (α d) = σ d
if d = qᵢ,           P qᵢ = φ qᵢ = qₙₑₓₜᵢ
if d = rᵢ = α qᵢ,   P rᵢ = φ rᵢ = σ qᵢ
```

The last equality is because `α rᵢ = qᵢ`.

---

## 1. Which σ-cycles are disrupted?

Exactly the `B` boundary-vertex σ-cycles are disrupted. All other σ-cycles survive unchanged as `P`-cycles.

First, `qᵢ` lies in the σ-cycle of `vᵢ` by definition:

```text
tail qᵢ = vᵢ.
```

Also `rₚᵣₑᵥᵢ` lies in the same σ-cycle because

```text
σ rₚᵣₑᵥᵢ = qᵢ.
```

Thus at boundary vertex `vᵢ`, the two deleted darts in its σ-cycle are

```text
qᵢ       -- outgoing boundary dart
rₚᵣₑᵥᵢ  -- incoming reverse boundary dart
```

and `rₚᵣₑᵥᵢ` is the immediate σ-predecessor of `qᵢ`.

There are no other deleted darts in that σ-cycle. If `qⱼ` lies in the σ-cycle of `qᵢ`, then

```text
tail qⱼ = tail qᵢ,
```

so `vⱼ = vᵢ`, and `outer_simple` gives `j = i`. If `rⱼ = α qⱼ` lies in the σ-cycle of `qᵢ`, then

```text
tail rⱼ = head qⱼ = tail qₙₑₓₜⱼ = vₙₑₓₜⱼ.
```

So `vₙₑₓₜⱼ = vᵢ`, hence `next j = i`, so `j = prev i`.

Therefore:

```text
OuterDel ∩ σOrbit(qᵢ) = {qᵢ, rₚᵣₑᵥᵢ}.
```

Every dart of `OuterDel` is in one of these boundary σ-cycles:

```text
qᵢ ∈ σOrbit(qᵢ),
rᵢ ∈ σOrbit(qₙₑₓₜᵢ), because σ rᵢ = qₙₑₓₜᵢ.
```

So the touched σ-cycles are exactly the `B` boundary vertex cycles. Since the outer boundary vertex list is simple, these `B` σ-cycles are distinct. Hence the remaining

```text
V - B
```

σ-cycles are untouched.

If a σ-cycle is untouched, then no dart in it lies in `OuterDel`, and `P = σ` on every dart in that cycle. Therefore each untouched σ-cycle is literally one unchanged `P`-cycle.

So we already have

```text
V - B
```

surviving `P`-cycles.

---

## 2. The disrupted boundary region becomes exactly two P-cycles

Let

```text
Q := {qᵢ | i}
R := (⋃ᵢ σOrbit(qᵢ)) \ Q.
```

The whole disrupted region is

```text
Q ⊔ R.
```

I will prove:

```text
Q is one P-cycle,
R is one P-cycle.
```

### 2.1. The forward outer cycle `Q`

For every `i`,

```text
P qᵢ = φ qᵢ = qₙₑₓₜᵢ.
```

Since the outer dart list is cyclic and has no duplicates, the darts `qᵢ` form one `P`-cycle of length `B`.

No dart outside `Q` maps into `Q`.

Suppose `d ∉ OuterDel`. Then `P d = σ d`. If `P d = qᵢ`, then `σ d = qᵢ`, so

```text
d = σ⁻¹ qᵢ = rₚᵣₑᵥᵢ,
```

by `(1')`, contradicting `d ∉ OuterDel`.

If `d = rⱼ`, then

```text
P rⱼ = σ qⱼ,
```

which cannot be a boundary dart `qᵢ`: if `σ qⱼ = qᵢ`, then `qᵢ` lies in the same boundary vertex σ-cycle as `qⱼ`, hence `i = j`; then `σ qⱼ = qⱼ`, impossible for a boundary dart in this near-triangulation. The repo already proves boundary darts have nontrivial σ-orbit via `boundary_dart_sigma_ne`. fileciteturn100file0L157-L193

Thus `Q` is a closed `P`-cycle and is not joined to the other boundary-region darts.

### 2.2. The second bank cycle `R`

For each boundary vertex `vᵢ`, define the σ-segment

```text
Sᵢ := [σ qᵢ, σ² qᵢ, ..., rₚᵣₑᵥᵢ]
```

where `rₚᵣₑᵥᵢ` is the first deleted dart encountered after `qᵢ` in the σ-cycle. This segment is nonempty because `rₚᵣₑᵥᵢ` is in the same σ-cycle as `qᵢ`.

In Lean, the clean way is to get this segment from `M.σ.toList qᵢ`. You have:

```text
M.σ.toList qᵢ = [qᵢ] ++ Sᵢ
```

up to the standard cyclic-list representation, with the last element of `Sᵢ` equal to `rₚᵣₑᵥᵢ`.

The crucial local facts are:

```text
Sᵢ contains every dart of σOrbit(qᵢ) except qᵢ.
Sᵢ ends at rₚᵣₑᵥᵢ.
All elements of Sᵢ except its last are not in OuterDel.
```

The last point follows from the calculation in §1: the only deleted darts in the σ-cycle of `qᵢ` are `qᵢ` and `rₚᵣₑᵥᵢ`.

Now trace `P`.

Let

```text
Sᵢ = [aᵢ,₀, aᵢ,₁, ..., aᵢ,tᵢ]
```

with

```text
aᵢ,₀ = σ qᵢ,
aᵢ,tᵢ = rₚᵣₑᵥᵢ.
```

For `k < tᵢ`, the dart `aᵢ,k` is not in `OuterDel`, so

```text
P aᵢ,k = σ aᵢ,k = aᵢ,k+1.
```

At the final dart,

```text
aᵢ,tᵢ = rₚᵣₑᵥᵢ = α qₚᵣₑᵥᵢ,
```

so

```text
P aᵢ,tᵢ
  = P rₚᵣₑᵥᵢ
  = φ rₚᵣₑᵥᵢ
  = σ qₚᵣₑᵥᵢ
  = aₚᵣₑᵥᵢ,0.
```

Thus `P` runs through the segment at vertex `vᵢ`, then jumps to the first segment dart at the previous boundary vertex:

```text
Sᵢ → Sₚᵣₑᵥᵢ → Sₚᵣₑᵥ²ᵢ → ... → Sᵢ.
```

Because the boundary indices form one cyclic orbit under `prev`, this concatenation is one single cycle:

```text
Sᵢ ++ Sₚᵣₑᵥᵢ ++ Sₚᵣᵉᵛ²ᵢ ++ ... ++ Sₙₑₓₜᵢ.
```

This cycle contains every dart in every boundary σ-cycle except the forward boundary darts `qᵢ`. Hence it is exactly `R`.

This is the heart of the proof:

```text
P threads the boundary vertex stars by σ-segments,
and the reverse boundary dart at the end of one segment jumps to the start of the previous segment.
```

It does **not** split into `B` separate cycles because the terminal reverse dart of `Sᵢ` is not sent back into `Sᵢ`; it is sent to `Sₚᵣₑᵥᵢ`:

```text
P rₚᵣₑᵥᵢ = σ qₚᵣₑᵥᵢ.
```

That is the exact closure mechanism.

Notice this uses only:

```text
φ qᵢ = qₙₑₓₜᵢ,
φ = σ ∘ α,
α² = 1,
outer boundary vertices are distinct.
```

It does **not** use a fan incidence/orientation certificate.

---

## 3. Formal cycle-count statement

The full decomposition is:

```text
P-cycles =
  { untouched interior σ-cycles }             -- V - B cycles
  ∪ { forward outer boundary cycle Q }        -- 1 cycle
  ∪ { reverse/interior boundary bank cycle R }-- 1 cycle
```

Therefore

```text
numCycles P = (V - B) + 2.
```

Lean-targetable version:

```lean
def BoundaryVertexOrbit (i : Fin B) : Quotient (cycleSetoid M.σ) :=
  Quotient.mk _ (q i)

def IsBoundaryVertexOrbit (Q : Quotient (cycleSetoid M.σ)) : Prop :=
  ∃ i : Fin B, Q = BoundaryVertexOrbit i
```

Prove:

```lean
lemma boundaryVertexOrbit_injective :
  Function.Injective BoundaryVertexOrbit
```

from `outer_simple`.

Then:

```lean
lemma numInteriorSigmaCycles :
  Fintype.card {Q : Quotient (cycleSetoid M.σ) // ¬ IsBoundaryVertexOrbit Q}
    = M.V - B
```

Then build the quotient equivalence:

```lean
Quotient (cycleSetoid P)
  ≃
({Q : Quotient (cycleSetoid M.σ) // ¬ IsBoundaryVertexOrbit Q} ⊕ Fin 2)
```

where:

* `Sum.inl Q` = an untouched interior σ-cycle;
* `Sum.inr 0` = the forward outer dart cycle `{qᵢ}`;
* `Sum.inr 1` = the second bank cycle `R`.

This equivalence is the cleanest way to prove:

```lean
theorem numCycles_boundaryBank :
  numCycles P = M.V - B + 2
```

The proof obligations of the equivalence are exactly the three invariance/transitivity facts above.

---

## 4. Suggested Lean lemma package

Here is the package I would implement, in dependency order.

### Basic boundary dart notation

```lean
def q (i : Fin B) : D := outerDart i
def r (i : Fin B) : D := M.α (q i)
def prev (i : Fin B) : Fin B := ...
def next (i : Fin B) : Fin B := ...
```

### Outer-cycle equations

```lean
lemma phi_q (i : Fin B) :
  M.φ (q i) = q (next i)

lemma sigma_r (i : Fin B) :
  M.σ (r i) = q (next i) := by
  simpa [r, CombMap.φ, Equiv.Perm.mul_apply] using phi_q i

lemma sigma_r_prev (i : Fin B) :
  M.σ (r (prev i)) = q i := by
  simpa using sigma_r (prev i)
```

### Deleted-dart classification inside a boundary vertex

```lean
lemma outerDel_inter_sigmaOrbit_q
    (i : Fin B) {d : D} :
  M.σ.SameCycle (q i) d →
  d ∈ OuterDel hNT ↔ d = q i ∨ d = r (prev i)
```

This is the key local classifier. It uses boundary vertex injectivity:

```lean
tail q i = tail q j → i = j
tail (r j) = tail q i → next j = i
```

The second equality uses:

```text
tail (r j) = head q j = tail q (next j).
```

### `P` equations

```lean
lemma P_eq_sigma_of_not_outerDel {d : D}
    (hd : d ∉ OuterDel hNT) :
  P d = M.σ d

lemma P_q (i : Fin B) :
  P (q i) = q (next i)

lemma P_r (i : Fin B) :
  P (r i) = M.σ (q i)
```

### Segment facts

Define `seg i` as the non-`qᵢ` part of the σ-cycle at `qᵢ`, ending at `r (prev i)`.

You can avoid a custom segment API by proving all facts in `SameCycle` form:

```lean
lemma sameCycleP_bank_of_boundary_non_q
    {i : Fin B} {d : D}
    (hdσ : M.σ.SameCycle (q i) d)
    (hdq : d ≠ q i) :
  P.SameCycle d (r (prev i))
```

and

```lean
lemma P_bank_jump (i : Fin B) :
  P (r (prev i)) = M.σ (q (prev i))
```

Then:

```lean
lemma sameCycleP_bank_prev
    (i : Fin B) :
  P.SameCycle (r (prev i)) (r (prev (prev i)))
```

Finally, since `prev` is a single cycle on `Fin B`:

```lean
lemma all_bank_darts_sameCycleP
    {i j : Fin B} :
  P.SameCycle (r i) (r j)
```

and more generally:

```lean
lemma boundary_non_q_same_bank
    {d e : D}
    (hd : ∃ i, M.σ.SameCycle (q i) d ∧ d ≠ q i)
    (he : ∃ i, M.σ.SameCycle (q i) e ∧ e ≠ q i) :
  P.SameCycle d e
```

### Forward cycle facts

```lean
lemma all_q_sameCycleP {i j : Fin B} :
  P.SameCycle (q i) (q j)

lemma q_not_sameCycleP_bank {i j : Fin B} :
  ¬ P.SameCycle (q i) (r j)
```

For the second lemma, use the invariant:

```lean
def IsForwardBoundaryDart (d : D) : Prop := ∃ i, d = q i
```

and prove it is `P`-invariant both forward and backward on the forward cycle, while `r j` is not forward. More directly: classify all preimages into `Q` as above; no non-`Q` dart maps into `Q`.

### Unchanged interior cycles

```lean
lemma P_sameCycle_iff_sigma_sameCycle_of_interior
    {d e : D}
    (hd : ∀ i, ¬ M.σ.SameCycle (q i) d)
    (he : ∀ i, ¬ M.σ.SameCycle (q i) e) :
  P.SameCycle d e ↔ M.σ.SameCycle d e
```

This follows because `P = σ` on the whole σ-orbit.

### Final quotient equivalence

```lean
noncomputable def PcycleEquiv :
  Quotient (cycleSetoid P) ≃
    ({Q : Quotient (cycleSetoid M.σ) // ¬ IsBoundaryVertexOrbit Q} ⊕ Fin 2)
```

Then:

```lean
theorem numCycles_P :
  numCycles P = M.V - B + 2 := by
  rw [← Fintype.card_congr PcycleEquiv]
  -- card of RHS = (V - B) + 2
```

---

## 5. Euler/slack arithmetic cross-check

Let

```text
c := numComponents(M.φ, αout).
```

The landed slack equation is:

```text
genusSlack(M.φ, αout)
  = 2c - numCycles(M.φ) + Ehalf(αout) - numCycles(M.φ * αout).
```

The relevant values are:

```text
numCycles(M.φ)       = F
Ehalf(αout)          = E - B
numCycles(M.φ*αout)  = V - B + 2
genusSlack           = 0
```

So:

```text
0 = 2c - F + (E - B) - (V - B + 2)
  = 2c - F + E - V - 2.
```

Euler gives:

```text
V - E + F = 2
```

so

```text
E - F - V = -2.
```

Thus:

```text
0 = 2c - 4,
```

hence:

```text
c = 2.
```

This arithmetic is perfect.

One caution: `genusSlack = 0` plus `c ≥ 2` alone does **not** force

```text
numCycles(P) = V - B + 2.
```

It gives

```text
numCycles(P) = V - B - 2 + 2c.
```

So if all you know is `c ≥ 2`, then `numCycles(P) ≥ V - B + 2`. The boundary-bank decomposition proves the missing upper/equality statement by showing the disrupted boundary region contributes exactly two cycles. Once that is proved, the slack arithmetic forces `c = 2`.

So the boundary-bank count is not merely cosmetic; it is exactly the topological “two boundary banks” fact in orbit form. The good news is that its proof is local and mechanical from the outer `φ`-cycle and σ-orbits, not a fan theorem.
