# Bounded crux: component count under adding one symmetric edge

GOAL: prove these lemmas in a NEW standalone file
`ProofsInTheBook/RelationComponentCount.lean`. Import `Mathlib` only.
STRICT: no sorry, no axiom, no admit, no native_decide. Verify with
`lake env lean ProofsInTheBook/RelationComponentCount.lean`.

Let `V` be a `Fintype`. Given a relation `r : V -> V -> Prop`, the connected
components are the classes of its reflexive-transitive-symmetric closure. Use the
equivalence closure `Relation.EqvGen r` (an `Equivalence` when... it always is an
Equivalence: `Relation.EqvGen.is_equivalence`). Build the setoid and count:

```
def compSetoid (r : V -> V -> Prop) : Setoid V := ⟨Relation.EqvGen r, Relation.EqvGen.is_equivalence r⟩
noncomputable def numComp (r : V -> V -> Prop) : ℕ :=
  Fintype.card (Quotient (compSetoid r))    -- need Fintype instance via Quotient.fintype + DecidableRel; you may need `open Classical` / `Classical.dec` to get the Fintype (Quotient _) instance. Use `Fintype.ofFinite` if cleaner: `Nat.card` may be easier than `Fintype.card`. Prefer `Nat.card (Quotient (compSetoid r))` to dodge Decidable instances.
```

Define the "edge-added" relation:
```
def addEdge (r : V -> V -> Prop) (a b : V) : V -> V -> Prop :=
  fun x y => r x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)
```

Prove (with `numComp` defined via `Nat.card (Quotient (compSetoid r))`):

```
theorem numComp_addEdge_of_eqvGen (r : V -> V -> Prop) {a b : V}
    (h : Relation.EqvGen r a b) :
    numComp (addEdge r a b) = numComp r
-- adding an edge inside an existing component does not change the count

theorem numComp_addEdge_of_not_eqvGen (r : V -> V -> Prop) {a b : V}
    (h : ¬ Relation.EqvGen r a b) :
    numComp (addEdge r a b) + 1 = numComp r
-- adding an edge across two distinct components merges them: count drops by 1
```

MATH: `EqvGen (addEdge r a b)` equals `EqvGen r` with the classes of `a` and `b`
identified. If a,b already EqvGen-related, no change. Otherwise exactly two
classes fuse into one, dropping the count by 1.

ROUTE HINT: First prove the key relational identity
  `Relation.EqvGen (addEdge r a b) x y  <->
     Relation.EqvGen r x y
     ∨ (Relation.EqvGen r x a ∧ Relation.EqvGen r y b)
     ∨ (Relation.EqvGen r x b ∧ Relation.EqvGen r y a)`
(forward by induction on EqvGen; backward by closure properties).
Then for the count: the quotient by `compSetoid (addEdge r a b)` is the quotient
of `Quotient (compSetoid r)` by identifying `⟦a⟧` and `⟦b⟧`. Build an explicit
surjection `Quotient (compSetoid r) → Quotient (compSetoid (addEdge r a b))`
(it is `Quotient.map id` since EqvGen r → EqvGen (addEdge ...)). For the
not-related case, show this surjection is exactly "2-to-1 on {⟦a⟧,⟦b⟧}, injective
elsewhere", giving card drop of 1, e.g. via
`Nat.card` of a quotient-of-quotient = `Nat.card (Quotient s) - 1` when exactly
two distinct points are merged (use `Setoid.comap` / a bijection with a subtype,
or count fibers). You may instead use `Finset`/`Fintype` and
`Fintype.card_quotient...`. Pick whatever closes it.

Whatever route: deliver the two theorems fully proved, file type-checks clean.
Put findings in HANDOFF/outbox/crux-comp-reply.md: status + load-bearing lemma names.
