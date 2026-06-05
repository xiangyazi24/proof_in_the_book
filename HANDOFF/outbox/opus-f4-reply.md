# File 4 reply: `ProofsInTheBook/PlanarMapFilteredRotation.lean`

Status: **complete, verified clean** on uisai1 (`lake env lean` 0 errors, 0 sorry/axiom/admit/native_decide).
`#print axioms` on the headline definitions/lemmas reports only `{propext, Classical.choice, Quot.sound}`.

Generic permutation-surgery toolkit for files 5-8. No chord-specific or fan-specific content.

## Conventions

A surgery is parametrized by the **deleted** finite set `Del : Finset D`; the **kept**
darts are the subtype `{d : D // d ∉ Del}`. This matches `PlanarMapDelete`
(`CombMap.deleteVertex` sets the new `σ := σ.deleteSet (deleteVertexSet v)`).
Everything lives in `namespace ProofsInTheBook.PlanarMap.FilteredRotation`.

## Part 1 — Filtered cyclic rotation (wraps `Equiv.Perm.deleteSet`)

```lean
noncomputable def filteredRotation (σ : Equiv.Perm D) (Del : Finset D) :
    Equiv.Perm {d : D // d ∉ Del}                              -- := σ.deleteSet Del

@[simp] lemma filteredRotation_apply_coe (σ) (Del) (x) :
    ((filteredRotation σ Del x : _) : D) = (σ ^ DeleteSet.firstOutside σ Del x) x.1

lemma firstOutside_eq_one_of_next_notMem (σ) (Del) (x) (h : σ x.1 ∉ Del) :
    Equiv.Perm.DeleteSet.firstOutside σ Del x = 1

-- consecutive-successor fact: on a run of kept darts the filtered map IS σ
lemma filteredRotation_apply_of_next_kept (σ) (Del) (x) (h : σ x.1 ∉ Del) :
    (filteredRotation σ Del x).1 = σ x.1

lemma filteredRotation_apply_eq (σ) (Del) (x y) (h : σ x.1 ∉ Del) (hy : (y:D) = σ x.1) :
    filteredRotation σ Del x = y
```

## Part 2 — Orbit / cycle behavior (orbit trace)

```lean
lemma filteredRotation_sameCycle_iff (σ) (Del) (x y) :
    (filteredRotation σ Del).SameCycle x y ↔ σ.SameCycle x.1 y.1

lemma filteredRotation_sameCycle_of_pow (σ) (Del) (x y) {m : ℕ} (h : (σ^m) x.1 = y.1) :
    (filteredRotation σ Del).SameCycle x y
```

## Part 3 — THE CONTIGUITY LEMMA

Contiguity of the kept darts of one σ-cycle is packaged as `Fin n`-indexed data
(avoids `List.get` index juggling, directly usable from a boundary cycle's dart
enumeration). `step` says σ sends `seq i` to `seq (i+1 mod n)` and `kept` says all
interval darts survive.

```lean
structure ContiguousInterval (σ : Equiv.Perm D) (Del : Finset D) (n : ℕ) where
  seq  : Fin n → D
  kept : ∀ i, seq i ∉ Del
  step : ∀ i, σ (seq i) = seq ⟨(i.1+1) % n, _⟩

namespace ContiguousInterval
  def keptElt  (I) (i : Fin n) : {d // d ∉ Del}      -- ⟨seq i, kept i⟩
  def nextIdx  (I) (i : Fin n) : Fin n               -- ⟨(i+1) % n, _⟩

  -- one filtered step follows the interval
  lemma filteredRotation_keptElt (I) (i) :
      filteredRotation σ Del (I.keptElt i) = I.keptElt (I.nextIdx i)

  -- interval-shift / iterate form (the review's named requirement)
  lemma filteredRotation_iterate_keptElt (I) (i) (k : ℕ) :
      (filteredRotation σ Del)^[k] (I.keptElt i) = I.keptElt (I.nextIdx^[k] i)

  lemma filteredRotation_iterate_first (I) (hn : 0 < n) (k : ℕ) :
      (filteredRotation σ Del)^[k] (I.keptElt ⟨0,hn⟩) = I.keptElt ⟨k % n, _⟩

  -- filteredRotation^[i] of the first element hits exactly seq i, in order
  lemma keptElt_mem_filteredRotation_orbit (I) (hn : 0 < n) (i : Fin n) :
      (filteredRotation σ Del)^[i.1] (I.keptElt ⟨0,hn⟩) = I.keptElt i

  lemma nextIdx_iterate (I) (i) (k) : (I.nextIdx^[k] i).1 = (i.1 + k) % n
```

## Part 4 — Fresh-dart adjunction (`K ⊕ Fin 2`)

`K = {d // d ∉ Del}` (the kept type), `β` = filtered α, `ρ` = filtered σ, fresh darts
`c₀ = Sum.inr 0`, `c₁ = Sum.inr 1`. Splice anchors `a₀ a₁ : K` (distinct).

```lean
def freshAlpha (β : Equiv.Perm K) : Equiv.Perm (K ⊕ Fin 2)   -- sumCongr β (swap 0 1)
@[simp] freshAlpha_inl / freshAlpha_inr
lemma freshAlpha_involutive (β) (hβ : β*β = 1) : freshAlpha β * freshAlpha β = 1
lemma freshAlpha_no_fixed  (β) (hβ : ∀ k, β k ≠ k) : ∀ x, freshAlpha β x ≠ x

def freshSigmaFun / freshSigmaInv (ρ a₀ a₁) : K ⊕ Fin 2 → K ⊕ Fin 2
def freshSigma (ρ a₀ a₁) (hne : a₀ ≠ a₁) : Equiv.Perm (K ⊕ Fin 2)
@[simp] freshSigma_apply
@[simp] freshSigma_anchor_zero : freshSigma .. (Sum.inl a₀) = Sum.inr 0
@[simp] freshSigma_anchor_one  : freshSigma .. (Sum.inl a₁) = Sum.inr 1
@[simp] freshSigma_fresh_zero  : freshSigma .. (Sum.inr 0)  = Sum.inl (ρ a₀)
@[simp] freshSigma_fresh_one   : freshSigma .. (Sum.inr 1)  = Sum.inl (ρ a₁)
lemma   freshSigma_other (h0 : k ≠ a₀) (h1 : k ≠ a₁) :
          freshSigma .. (Sum.inl k) = Sum.inl (ρ k)

-- the assembled CombMap on K ⊕ Fin 2
def freshMap (β ρ : Equiv.Perm K) (hβinv : β*β = 1) (hβfix : ∀ k, β k ≠ k)
    (a₀ a₁ : K) (hne : a₀ ≠ a₁) : CombMap (K ⊕ Fin 2)
@[simp] freshMap_alpha / freshMap_sigma
```

The orbit step lemmas fully characterize the spliced rotation: `... → a₀ → c₀ → ρ(a₀) → ...`
(the new cycle through `c₀` visits `c₀` then the old cycle segment), symmetric for `c₁`/`a₁`,
and `ρ` unchanged elsewhere. `freshMap` packages it as a `CombMap` whose `α` is a
fixed-point-free involution and whose `σ` is the spliced permutation.

## Usage notes for files 5-8

- For a chord split, instantiate `freshMap` with `K = {d // d ∉ Del}` for each side's
  deleted-dart set, `β = alphaDeleteVertex`-style restriction, `ρ = filteredRotation`,
  and `a₀, a₁` = the chord-endpoint darts whose rotations receive the fresh chord dart.
- `ContiguousInterval` is the hypothesis to discharge from
  `chordSplit_side_darts_contiguous_at_vertex`: build the `Fin n` enumeration from the
  side's kept darts at a vertex, then `filteredRotation_iterate_first` /
  `keptElt_mem_filteredRotation_orbit` give "the side maps' faces are what we claim".
