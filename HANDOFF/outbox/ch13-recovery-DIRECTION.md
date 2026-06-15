Commit to **(b), but in a sharpened form**:

> Do **not** try to prove `CloseStrict + FinalStrict` for `openedWBS`.  
> Prove instead:  
> **weak cyclic support + strict consecutive turns + exactly one nonincident support zero** imply the suffix nondegeneracy consumed by `core_of_nondeg`.

This is non-circular and fits the actual `openedWBS` structure. The strict-support theorem was a useful sufficient condition for a strictly convex chain, but it is too strong for support-stuck WBS.

---

# 1. Does suffix nondegeneracy require global strict supports?

No. It requires two weaker facts:

\[
s_k := Q_n-Q_k\ne0
\]

and

\[
b_k := (\theta_{n-1}-\theta_k)-a_k\ne\pi.
\]

`CloseStrict + FinalStrict` is one way to get these, but not the right way for `openedWBS`.

For `openedWBS`, the right source is:

\[
\textbf{there is exactly one nonincident support equality, and all other nonincident supports are strict.}
\]

This is much weaker than global strict support and is compatible with the single WBS stuck tangency.

In Lean, introduce a cyclic planar support package:

```lean
def NonIncidentEdgeVertex (n : ℕ) : Type :=
  {c : Fin (n + 1) × Fin (n + 1) //
    c.2 ≠ c.1 ∧ c.2 ≠ c.1 + 1}

def supportVal {n : ℕ} (Q : Fin (n + 1) → E3)
    (c : NonIncidentEdgeVertex n) : ℝ :=
  det3 (Q c.1.1) (Q (c.1.1 + 1)) (Q c.1.2)

def SingleStuckSupport {n : ℕ} (Q : Fin (n + 1) → E3) : Prop :=
  ∃ c₀ : NonIncidentEdgeVertex n,
    supportVal Q c₀ = 0 ∧
    ∀ c : NonIncidentEdgeVertex n,
      c ≠ c₀ → 0 < supportVal Q c
```

You also keep weak support for all pairs:

```lean
hweak : ∀ i j : Fin (n + 1),
  0 ≤ det3 (Q i) (Q (i + 1)) (Q j)
```

This matches the monitored-support setup: `NonIncident` is already defined as the edge–vertex pairs with `j ≠ i` and `j ≠ i+1`, and `supportConstraint` unfolds to the opened-arm orientation of exactly such a triple. fileciteturn34file0L123-L151 The current support-stuck extraction gives existence of a vanished nonincident support; the thing you need to strengthen/formalize for WBS is uniqueness/strictness away from that pair. fileciteturn29file0L31-L44

---

# 2. Is `chord_k ≠ 0` equivalent to the no-collision goal?

Analytically, yes:

\[
\operatorname{chord}_k
=
\sum_{i=k}^{n-1}\rho_i e^{i\theta_i}
\]

is the planar coordinate form of

\[
Q_n-Q_k.
\]

So

\[
\operatorname{chord}_k\ne0
\quad\Longleftrightarrow\quad
Q_n\ne Q_k.
\]

This is an endpoint no-collision statement. For cross-piece prefix indices \(k<K\), it is indeed a special endpoint case of the final `ProperCrossPieceNoCollisionAtSup`.

But it is **not circular** if you prove it from `SingleStuckSupport`. Here is the direct argument.

Suppose \(1\le k\le n-1\) and \(Q_k=Q_n\).

If \(k=n-1\), this contradicts the nonzero final edge \(Q_{n-1}\ne Q_n\), which follows from short edges / positive edge length.

If \(k\le n-2\), then there are at least two distinct nonincident support zeros.

First, edge \(k\), vertex \(n\):

\[
\det(Q_k,Q_{k+1},Q_n)=0
\]

because \(Q_n=Q_k\). The pair \((k,n)\) is nonincident since \(n\ne k\) and \(n\ne k+1\).

Second, final edge \(n-1\), vertex \(k\):

\[
\det(Q_{n-1},Q_n,Q_k)=0
\]

because \(Q_k=Q_n\). The pair \((n-1,k)\) is nonincident since \(k\le n-2\).

These are distinct nonincident pairs, contradicting uniqueness of the stuck support.

So `chord_k ≠ 0` is obtained non-circularly from the single-stuck support structure.

Lean skeleton:

```lean
lemma chord_ne_of_singleStuck
    {n : ℕ} {Q : Fin (n + 1) → E3}
    (hweak : ∀ i j : Fin (n + 1),
      0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hsingle : SingleStuckSupport Q)
    (hedge : ∀ i : Fin (n + 1), Q i ≠ Q (i + 1))
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) :
    Q ⟨k, by omega⟩ ≠ Q ⟨n, by omega⟩ := by
  intro hEq
  by_cases hk_last : k = n - 1
  · subst hk_last
    exact hedge ⟨n - 1, by omega⟩ hEq
  · have hk_le : k ≤ n - 2 := by omega

    -- zero #1: edge k, vertex n
    let c1 : NonIncidentEdgeVertex n :=
      ⟨(⟨k, by omega⟩, ⟨n, by omega⟩), by
        constructor
        · intro h; have := congrArg Fin.val h; omega
        · intro h; have := congrArg Fin.val h; omega⟩
    have hzero1 : supportVal Q c1 = 0 := by
      unfold supportVal
      -- Q n = Q k
      rw [hEq]
      -- det3 (Q k) (Q (k+1)) (Q k) = 0
      exact det3_self_right _ _

    -- zero #2: edge n-1, vertex k
    let c2 : NonIncidentEdgeVertex n :=
      ⟨(⟨n - 1, by omega⟩, ⟨k, by omega⟩), by
        constructor
        · intro h; have := congrArg Fin.val h; omega
        · intro h; have := congrArg Fin.val h; omega⟩
    have hzero2 : supportVal Q c2 = 0 := by
      unfold supportVal
      -- Q k = Q n
      rw [hEq]
      -- det3 (Q (n-1)) (Q n) (Q n) = 0
      exact det3_self_mid _ _

    -- c1 ≠ c2, but SingleStuckSupport allows only one nonincident zero.
    obtain ⟨c0, hc0zero, hstrict_else⟩ := hsingle
    have hc1_eq : c1 = c0 := by
      by_contra hne
      have hpos := hstrict_else c1 hne
      linarith
    have hc2_eq : c2 = c0 := by
      by_contra hne
      have hpos := hstrict_else c2 hne
      linarith
    have hc12 : c1 = c2 := by rw [hc1_eq, hc2_eq]
    -- contradiction from different edge indices
    have hval := congrArg (fun c : NonIncidentEdgeVertex n => c.1.1) hc12
    simp [c1, c2] at hval
    omega
```

The exact determinant-zero lemma names may differ; the repo already uses determinant self-zero facts such as `det3_self_right` and `det3_self_mid` in similar support proofs. fileciteturn28file0L31-L36

---

# 3. Does the single stuck contact avoid closing/final edges?

Do **not** rely on that. There is no structural guarantee from the current monitored-family definition.

The monitored support family includes **all** nonincident edge–vertex pairs:

```lean
def NonIncident (n : ℕ) :=
  {c : Fin (n + 1) × Fin (n + 1) // c.2 ≠ c.1 ∧ c.2 ≠ c.1 + 1}
```

and the support constraint is exactly

```lean
sOrient (openTail A K θ c.i)
        (openTail A K θ (c.i+1))
        (openTail A K θ c.j)
```

fileciteturn34file0L123-L151

Therefore the stuck pair can, in principle, be:

* a closing-edge pair \((n,j)\),
* a final-edge pair \((n-1,j)\),
* a first-edge pair,
* or any other nonincident pair.

The `supportStuck` extraction only gives an arbitrary vanished nonincident support; it does not exclude boundary edges. fileciteturn29file0L31-L44

So the answer to question 2 is:

> No, do not assume the stuck pair avoids the closing edge or final edge unless you add and prove a WBS-specific lemma saying so. The current structure does not give that exclusion.

Fortunately, you do **not** need that exclusion.

---

# 4. Handling `b_k ≠ π` without `FinalStrict`

This is the second half of suffix nondegeneracy.

Recall:

\[
b_k
=
(\theta_{n-1}-\theta_k)-a_k.
\]

Geometrically,

\[
b_k=\pi
\]

means the suffix vector

\[
s_k=Q_n-Q_k
\]

points exactly opposite to the final edge direction. Since \(s_k\ne0\), this means

\[
Q_k=Q_n+\lambda (Q_n-Q_{n-1})
\qquad\text{for some }\lambda>0.
\]

So \(Q_k\) lies beyond \(Q_n\) on the final-edge ray.

This condition produces **two** nonincident support zeros under weak cyclic support:

1. final edge \((Q_{n-1},Q_n)\) at vertex \(Q_k\);
2. closing edge \((Q_n,Q_0)\) at vertex \(Q_{n-1}\).

That contradicts `SingleStuckSupport`.

Here is the exact determinant argument.

Let

\[
f=Q_n-Q_{n-1},
\qquad
c=Q_0-Q_n.
\]

Assume

\[
Q_k=Q_n+\lambda f,\qquad \lambda>0.
\]

Then

\[
Q_k-Q_n=\lambda f,
\qquad
Q_{n-1}-Q_n=-f.
\]

Weak support for the closing edge \(Q_n\to Q_0\) gives:

\[
0\le \det(c,Q_k-Q_n)=\lambda\det(c,f),
\]

so

\[
0\le\det(c,f).
\]

It also gives:

\[
0\le \det(c,Q_{n-1}-Q_n)=\det(c,-f)=-\det(c,f),
\]

so

\[
\det(c,f)\le0.
\]

Therefore

\[
\det(c,f)=0.
\]

Thus

\[
\det(Q_n,Q_0,Q_{n-1})=0.
\]

The pair \((n,n-1)\), i.e. closing edge at vertex \(n-1\), is nonincident because the closing edge’s endpoints are \(n\) and \(0\), and \(n-1\ne n,0\) for \(n\ge2\).

Also, from \(Q_k\) lying on the final-edge line,

\[
\det(Q_{n-1},Q_n,Q_k)=0.
\]

For \(1\le k\le n-2\), the pair \((n-1,k)\) is nonincident.

These are two distinct nonincident zeros, contradiction.

So `b_k = π` is impossible under weak cyclic support plus unique stuck support.

Lean-level structure:

```lean
lemma b_ne_pi_of_singleStuck
    {n : ℕ} {Q : Fin (n + 1) → E3}
    (hplane : ∀ i : Fin (n + 1), (⟪h, Q i⟫ : ℝ) = 1)
    (hweak : ∀ i j : Fin (n + 1),
      0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hsingle : SingleStuckSupport Q)
    (hchord_ne : ∀ k, 1 ≤ k → k ≤ n - 1 →
      chord θ ρ n k ≠ 0)
    (hedge_eq : -- Q_{m+1}-Q_m = ρ_m d(θ_m), already in ZinanFFCT106
      ...)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) :
    (θ (n - 1) - θ k) - aang θ ρ n k ≠ Real.pi := by
  intro hb

  by_cases hk_last : k = n - 1
  · subst hk_last
    have ha : aang θ ρ n (n - 1) = 0 :=
      aang_last θ ρ n (by omega) (hpos (n - 1))
    rw [ha, sub_self, zero_sub] at hb
    nlinarith [Real.pi_pos]

  · have hk_le_n2 : k ≤ n - 2 := by omega

    -- Step A. Convert hb = π into the ray identity:
    -- Q k = Q n + λ • (Q n - Q (n-1)), λ > 0.
    obtain ⟨λ, hλpos, hray⟩ :=
      final_ray_of_b_eq_pi
        (θ := θ) (ρ := ρ) (n := n) (k := k)
        hchord_ne hb hedge_eq

    -- Step B. final-edge support zero at k.
    let cFinal : NonIncidentEdgeVertex n :=
      ⟨(⟨n - 1, by omega⟩, ⟨k, by omega⟩), by
        constructor <;> intro h <;> have := congrArg Fin.val h <;> omega⟩

    have hzeroFinal : supportVal Q cFinal = 0 := by
      unfold supportVal
      -- use hray: Q k - Q (n-1) = (1+λ) • (Q n - Q (n-1))
      -- determinant of collinear vectors is zero
      -- det3_plane_eq or affine det-linearity lemma
      exact det_final_collinear_zero hray

    -- Step C. closing-edge support zero at n-1.
    let cClose : NonIncidentEdgeVertex n :=
      ⟨(⟨n, by omega⟩, ⟨n - 1, by omega⟩), by
        constructor <;> intro h <;> have := congrArg Fin.val h <;> omega⟩

    have hzeroClose : supportVal Q cClose = 0 := by
      -- weak support at closing edge for vertex k
      have hkweak :
          0 ≤ det3 (Q ⟨n, by omega⟩) (Q 0) (Q ⟨k, by omega⟩) :=
        hweak ⟨n, by omega⟩ ⟨k, by omega⟩

      -- weak support at closing edge for vertex n-1
      have hn1weak :
          0 ≤ det3 (Q ⟨n, by omega⟩) (Q 0) (Q ⟨n - 1, by omega⟩) :=
        hweak ⟨n, by omega⟩ ⟨n - 1, by omega⟩

      -- Using hray:
      -- Q k - Q n = λ • (Q n - Q (n-1))
      -- Q (n-1) - Q n = -1 • (Q n - Q (n-1))
      -- these inequalities force det(closing, finalDir)=0.
      exact closing_zero_from_opposite_weak_supports hray hλpos hkweak hn1weak

    -- Step D. contradiction with uniqueness.
    exact two_distinct_nonincident_zeros_contradict_singleStuck
      hsingle cFinal cClose hzeroFinal hzeroClose
      (by -- edge index n-1 ≠ n
        intro h; have := congrArg (fun c : NonIncidentEdgeVertex n => c.1.1) h
        simp [cFinal, cClose] at this
        omega)
```

The only new analytic bridge is:

```lean
lemma final_ray_of_b_eq_pi :
  chord θ ρ n k ≠ 0 →
  (θ (n - 1) - θ k) - aang θ ρ n k = Real.pi →
  ∃ λ : ℝ, 0 < λ ∧
    Q k = Q n + λ • (Q n - Q (n - 1))
```

This is just the real/complex meaning of `b_k = π`. You already have the needed complex pieces:

* `chord`, `wrot`, `aang` are defined in `ZinanFFCT108`; fileciteturn10file0L97-L100
* `im_end_chord` identifies the end-frame imaginary part as \(-‖s_k‖\sin b_k\); fileciteturn11file0L1-L15
* add the analogous real-part lemma to get \(-‖s_k‖\cos b_k\) or directly reconstruct the complex equality.

A direct complex proof is shortest:

\[
e^{-i\theta_{n-1}}s_k
=
\|s_k\|e^{-ib_k}.
\]

If \(b_k=\pi\), then

\[
e^{-i\theta_{n-1}}s_k=-\|s_k\|.
\]

Thus

\[
s_k=-\|s_k\|e^{i\theta_{n-1}}.
\]

But

\[
s_k=Q_n-Q_k,
\qquad
Q_n-Q_{n-1}=\rho_{n-1}e^{i\theta_{n-1}}.
\]

Hence

\[
Q_n-Q_k
=
-\frac{\|s_k\|}{\rho_{n-1}}(Q_n-Q_{n-1}),
\]

so

\[
Q_k
=
Q_n+
\frac{\|s_k\|}{\rho_{n-1}}(Q_n-Q_{n-1}),
\]

with positive coefficient because \(\|s_k\|>0\) and \(\rho_{n-1}>0\).

---

# 5. What if the single stuck pair is final-edge or closing-edge?

That is fine.

You do **not** need to prove it avoids those edges.

If the stuck pair is final-edge \((n-1,k)\), then

\[
\det(Q_{n-1},Q_n,Q_k)=0.
\]

This is allowed.

But the bad suffix condition \(b_k=\pi\) is a **stronger** statement: it says \(Q_k\) lies beyond \(Q_n\) on the final ray. That stronger statement would force an additional closing-edge zero, as shown above. Therefore uniqueness rules out the bad case.

So the stuck contact may be final-edge tangency, but it must be a harmless tangency, not the final-ray degeneracy that breaks the suffix proof.

Similarly, a closing-edge stuck contact is harmless unless it participates in a collision or final-ray degeneracy; those would again create a second nonincident zero.

This is the clean non-circular handling of the one stuck pair.

---

# 6. The theorem to prove for `openedWBS`

Do **not** prove `CloseStrict + FinalStrict`.

The right theorem is:

```lean
theorem openedWBS_suffix_nondeg_of_singleStuck
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A)
    ...
    (hweak : ∀ i j : Fin (n + 1),
      0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hsingle : SingleStuckSupport Q)
    (hedge : ∀ i : Fin (n + 1), Q i ≠ Q (i + 1))
    (hθρbridge : -- edge coordinate bridge from ZinanFFCT106
      ...)
    :
    ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 →
      chord θ ρ n k ≠ 0 ∧
      (θ (n - 1) - θ k) - aang θ ρ n k ≠ Real.pi
```

Then feed it directly into:

```lean
core_of_nondeg n θ ρ hn hmono hgap hpos hfwd hbwd hnd
```

`core_of_nondeg` is exactly the suffix-lift theorem already present: it proves the total turn `< 2π` from the usual open sine supports plus the suffix nondegeneracy. fileciteturn12file0L42-L49

So the WBS route becomes:

```text
openedWBS weak cyclic support
+ exactly one nonincident stuck support, strict elsewhere
+ nonzero edges
        ↓
suffix nondegeneracy hnd
        ↓
core_of_nondeg
        ↓
one_wind < 2π
        ↓
PlanarLiftedTurnSpan
        ↓
planar no-repeat
        ↓
ProperCrossPieceNoCollisionAtSup
```

This is non-circular because the only no-collision-like fact used before one-wind is derived from **uniqueness of support tangency**, not from the final no-repeat theorem.

---

# 7. Does `openedWBS` currently supply `SingleStuckSupport`?

From the files we inspected, the current proved payload is weaker.

`openedWBS_gnomonicSingleWind` derives weak planar support and strict consecutive turns for the opened WBS arm. fileciteturn14file0L111-L123 The support-stuck extraction gives existence of a vanished nonincident support. fileciteturn29file0L31-L44

But the files shown do **not** yet prove uniqueness of the stuck support or strictness of every other nonincident pair in the stuck branch. In the REACH/`¬ Stuck` branch, the repo proves all nonincident supports are strictly positive at the supremum. fileciteturn35file0L13-L21 In the STUCK branch, uniqueness/strict-elsewhere is a WBS-specific strengthening you need to formalize.

So the honest new spherical lemma should be:

```lean
theorem openedWBS_singleStuckSupport
    ... :
    SingleStuckSupport
      (fun i : Fin (n + 1) => gproj h (openedWBS A B k i))
```

or, if uniqueness is too strong globally:

```lean
theorem openedWBS_atMostOneNonincidentZero
    ... :
    ∀ c₁ c₂ : NonIncidentEdgeVertex n,
      supportVal Q c₁ = 0 →
      supportVal Q c₂ = 0 →
      c₁ = c₂
```

plus existence of the stuck support if needed.

For suffix nondegeneracy, **at most one** nonincident zero is enough. You do not actually need to know which pair is stuck.

---

# 8. Final recommendation

Commit to this direction:

## Prove a “single weak tangency” suffix-nondeg bridge

```lean
weak cyclic supports
+ nonzero edges
+ at most one nonincident support equality
+ θ/ρ coordinate bridge
⇒ suffix nondegeneracy hnd
```

Then use the already-built `core_of_nondeg`.

This is cleaner and more faithful to `openedWBS` than `CloseStrict + FinalStrict`.

Do **not** spend effort proving that the stuck pair avoids final/closing edges. It may not. The uniqueness argument handles those cases.

Do **not** use `ProperCrossPieceNoCollisionAtSup` to prove `chord_k ≠ 0`. Instead prove endpoint noncollision as a consequence of “a collision would create at least two nonincident zero supports,” contradicting the single-stuck structure.

The core slogan for the Lean proof is:

> A collision or a bad final-ray suffix is not merely a tangency; it forces **two distinct nonincident support zeros**.  
> `openedWBS` has only one.  
> Therefore suffix nondegeneracy is non-circular.
