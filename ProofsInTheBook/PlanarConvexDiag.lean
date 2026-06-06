import ProofsInTheBook.SphericalGnomonic

/-!
# `PlanarConvexDiag` — the planar convex-position diagonal positivity primitive

This module discharges the single planar residue isolated by the gnomonic round
(`HANDOFF/outbox/opus-gnomonic-reply.md`): the purely two-dimensional convex-position fact

> `PlanarConvexDiagPos` : a strictly convex planar polygon (edge-support form) has every
> increasing triple `i < j < k` positively oriented.

## The algebraic engine: a Grassmann–Plücker relation for shared-apex `det3`

The prior round confirmed four obstructions to a single-file algebraic proof from the *first-order*
supports (no nonnegative-coefficient certificate, sign-indefinite cocycle, same-gap `gp`, circular
ear-removal).  None of those refutes the *quadratic* Grassmann–Plücker relation among five points
sharing an apex, which is the genuine engine here:

* **`det3_apex_plucker`** — the pure polynomial identity (provable by `ring` on coordinates)
  `det3 A P Q · det3 A E M = det3 A M Q · det3 A E P + det3 A P M · det3 A E Q`.
  This is the `3×3` shared-apex Plücker (Grassmann–Plücker) syzygy.

With apex `A = f i` and reference edge endpoint `E = f (i+1)`, the three `det3 A E ·` factors are
exactly the **edge supports** of the cyclic edge `(f i, f (i+1))` (strictly positive on the
non-incident vertices).  The relation then expresses the diagonal `det3 (f i)(f p)(f q)` as a
*positive* combination of strictly smaller-gap diagonals divided by a strictly positive edge support:

  `det3 A P Q = (det3 A (Q-1) Q · det3 A E P + det3 A P (Q-1) · det3 A E Q) / det3 A E (Q-1)`.

This founds a clean strong induction on the gap `q - p`, with the consecutive base
`det3 (f i)(f t)(f (t+1)) > 0` (a cyclic rotation of the edge support of edge `(t, t+1)`) — exactly
the "monotone polar order from the apex inside the half-plane" the handoff flagged, now realised
purely on `det3` with the Plücker syzygy as the algebraic carrier of the angular ordering.

## Result

* **`planarConvexDiagPos_holds : PlanarConvexDiagPos`** — the residue, proved unconditionally.
* The downstream spherical results of `SphericalGnomonic` become unconditional in the cut branch:
  `cyclicTriplePos_unconditional`, and the clean arm lemmas
  `spherical_arm_mono_cut_unconditional` / `_strict_cut_unconditional` (conditional now only on the
  opening primitive `SZStepGeom`, the convex-position input fully discharged).

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalArm ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalGnomonic

namespace ProofsInTheBook.PlanarConvexDiag

/-! ## Block A — the algebraic engine (pure `ring` identities on `det3`) -/

/-- **Shared-apex Grassmann–Plücker syzygy.**  For any five vectors in `E3`, the `det3`'s sharing the
apex `A` satisfy `det3 A P Q · det3 A E M = det3 A M Q · det3 A E P + det3 A P M · det3 A E Q`.
A pure polynomial identity (`ring`), the quadratic engine of the convex-position induction. -/
theorem det3_apex_plucker (A E P M Q : E3) :
    det3 A P Q * det3 A E M = det3 A M Q * det3 A E P + det3 A P M * det3 A E Q := by
  simp only [det3]; ring

/-- `det3` is invariant under cyclic rotation of its three arguments (`ring`). -/
theorem det3_cyclic (a b c : E3) : det3 a b c = det3 b c a := by
  simp only [det3]; ring

/-! ## Block B — the natural-number-indexed core induction

We phrase the heart of the argument over `ℕ` indices via an arbitrary point family `g : ℕ → E3`,
assuming exactly the two `det3`-positivity facts the convex polygon supplies in a window `[i, n)`:

* `hbase` — the consecutive base `0 < det3 (g i) (g t) (g (t+1))` for `i < t` (monotone turning);
* `hedge` — the strict edge supports `0 < det3 (g i) (g (i+1)) (g t)` for `i+1 < t` (half-plane).

These are *exactly* what the cyclic edge `(f i, f (i+1))` and the rotated edge supports furnish.  The
conclusion is the all-pairs diagonal positivity `0 < det3 (g i) (g p) (g q)` for `i < p < q`. -/

/-- The core planar induction, on natural-number indices, in a window `[i, N)`.  From the consecutive
turning base and the strict half-plane edge supports (only needed inside the window), every increasing
triple `i < p < q < N` is positively oriented. -/
theorem det3_diag_pos_nat (g : ℕ → E3) (i N : ℕ)
    (hbase : ∀ t : ℕ, i < t → t + 1 < N → 0 < det3 (g i) (g t) (g (t + 1)))
    (hedge : ∀ t : ℕ, i + 1 < t → t < N → 0 < det3 (g i) (g (i + 1)) (g t)) :
    ∀ q p : ℕ, i < p → p < q → q < N → 0 < det3 (g i) (g p) (g q) := by
  intro q
  -- strong induction on the larger index `q`
  induction q using Nat.strong_induction_on with
  | _ q IH =>
    intro p hip hpq hqN
    -- Case split on whether `p` is the reference endpoint `i+1`.
    rcases Nat.lt_or_ge (i + 1) p with hp2 | hple
    · -- `p ≥ i+2`: use the Plücker syzygy with pivot `m = q-1`.
      -- First, `q ≥ p+1 ≥ i+3`, so `q-1 ≥ i+2` and `q ≥ i+2`.
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      -- pivot m = q' (= q-1)
      have hq'p : p ≤ q' := by omega
      rcases Nat.lt_or_ge p q' with hlt | hge
      · -- p < q' : recurse
        -- positivity of the three edge-support factors and the two recursive diagonals
        have e_p : 0 < det3 (g i) (g (i + 1)) (g p) := hedge p hp2 (by omega)
        have e_q : 0 < det3 (g i) (g (i + 1)) (g (q' + 1)) := hedge (q' + 1) (by omega) (by omega)
        have e_m : 0 < det3 (g i) (g (i + 1)) (g q') := hedge q' (by omega) (by omega)
        -- D(i, q', q'+1) consecutive base
        have d_consec : 0 < det3 (g i) (g q') (g (q' + 1)) := hbase q' (by omega) (by omega)
        -- D(i, p, q') smaller q (= q' < q'+1)
        have d_rec : 0 < det3 (g i) (g p) (g q') := IH q' (by omega) p hip hlt (by omega)
        -- Plücker: D(i,p,q'+1) * e_m = D(i,q',q'+1) * e_p + D(i,p,q') * e_q
        have hpl := det3_apex_plucker (g i) (g (i + 1)) (g p) (g q') (g (q' + 1))
        -- hpl : det3 (g i)(g p)(g (q'+1)) * det3 (g i)(g (i+1))(g q')
        --      = det3 (g i)(g q')(g (q'+1)) * det3 (g i)(g (i+1))(g p)
        --      + det3 (g i)(g p)(g q') * det3 (g i)(g (i+1))(g (q'+1))
        nlinarith [mul_pos d_consec e_p, mul_pos d_rec e_q, e_m,
          mul_pos (mul_pos d_consec e_p) e_m]
      · -- p = q' : then the triple is the consecutive base D(i, q', q'+1)
        have : p = q' := le_antisymm hq'p hge
        subst this
        exact hbase p hip (by omega)
    · -- `p ≤ i+1`, and `i < p`, so `p = i+1`: direct strict edge support
      have : p = i + 1 := by omega
      subst this
      exact hedge q (by omega) hqN

/-! ## Block C — transporting the `Fin n` hypotheses to the `ℕ` core

The target `PlanarConvexDiagPos` quantifies over `f : Fin n → E3` with `Fin`-cyclic `+1`.  Inside the
window relevant to a fixed `i < j < k`, the cyclic successor is the linear one, so the `ℕ` core
applies after one `Fin`-arithmetic conversion. -/

/-- For `i : Fin n` with `i.val + 1 < n`, the `Fin`-cyclic successor coincides with the linear one. -/
theorem fin_succ_val {n : ℕ} [NeZero n] {i : Fin n} (h : i.val + 1 < n) :
    (i + 1 : Fin n).val = i.val + 1 := by
  have hn : 2 ≤ n := by omega
  rw [Fin.add_def]
  have h1 : (1 : Fin n).val = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  rw [h1]
  exact Nat.mod_eq_of_lt h

/-! ## Block D — the headline planar primitive (unconditional) -/

/-- **`PlanarConvexDiagPos`, proved.**  A strictly convex planar polygon (edge-support form) has every
increasing triple `i < j < k` positively oriented.  We lift `f` to a `ℕ`-indexed family `g` (agreeing
with `f` inside the window `[0, n)`), translate the cyclic edge supports into the consecutive turning
base (`hbase`, via the cyclic rotation `det3_cyclic`) and the strict half-plane supports (`hedge`),
and invoke the Plücker-driven core induction `det3_diag_pos_nat`. -/
theorem planarConvexDiagPos_holds : PlanarConvexDiagPos := by
  intro n _ h _hh f _hplane hedge_nn hstrict i j k hij hjk
  -- `g : ℕ → E3` agreeing with `f` on `[0, n)`
  set g : ℕ → E3 := fun t => f ⟨t % n, Nat.mod_lt t (NeZero.pos n)⟩ with hg
  have g_eq : ∀ t (ht : t < n), g t = f ⟨t, ht⟩ := by
    intro t ht; simp only [hg, Nat.mod_eq_of_lt ht]
  -- consecutive turning base
  have hbase : ∀ t : ℕ, i.val < t → t + 1 < n → 0 < det3 (g i.val) (g t) (g (t + 1)) := by
    intro t hit ht1
    have ht : t < n := by omega
    rw [g_eq i.val i.isLt, g_eq t ht, g_eq (t + 1) ht1]
    -- det3 (f i)(f ⟨t⟩)(f ⟨t+1⟩) = det3 (f ⟨t⟩)(f ⟨t+1⟩)(f i)  (cyclic)
    rw [det3_cyclic]
    -- f ⟨t+1⟩ = f (⟨t⟩ + 1)
    have hsucc : (⟨t, ht⟩ + 1 : Fin n) = ⟨t + 1, ht1⟩ := by
      apply Fin.ext; rw [fin_succ_val (by simpa using ht1)]
    rw [show (⟨t + 1, ht1⟩ : Fin n) = (⟨t, ht⟩ + 1 : Fin n) from hsucc.symm]
    -- strict edge support of edge (⟨t⟩, ⟨t⟩+1) on i
    refine hstrict ⟨t, ht⟩ i ?_ ?_
    · exact fun hc => by simp only [Fin.ext_iff] at hc; omega
    · exact fun hc => by
        simp only [Fin.ext_iff, hsucc] at hc; omega
  -- strict half-plane edge supports
  have hedge : ∀ t : ℕ, i.val + 1 < t → t < n → 0 < det3 (g i.val) (g (i.val + 1)) (g t) := by
    intro t hit ht
    have hi1 : i.val + 1 < n := by omega
    rw [g_eq i.val i.isLt, g_eq (i.val + 1) hi1, g_eq t ht]
    have hsucc : (i + 1 : Fin n) = ⟨i.val + 1, hi1⟩ := by
      apply Fin.ext; exact fin_succ_val hi1
    rw [show (⟨i.val + 1, hi1⟩ : Fin n) = (i + 1 : Fin n) from hsucc.symm]
    refine hstrict i ⟨t, ht⟩ ?_ ?_
    · exact fun hc => by simp only [Fin.ext_iff] at hc; omega
    · exact fun hc => by
        rw [hsucc] at hc; simp only [Fin.ext_iff] at hc; omega
  -- apply the core and identify `g` with `f` on the window
  have hcore := det3_diag_pos_nat g i.val n hbase hedge k.val j.val
    (by exact_mod_cast hij) (by exact_mod_cast hjk) k.isLt
  rwa [g_eq i.val i.isLt, g_eq j.val j.isLt, g_eq k.val k.isLt,
    Fin.eta, Fin.eta, Fin.eta] at hcore

/-! ## Block E — the now-unconditional cut-branch spherical results

With `planarConvexDiagPos_holds` proved, every result of `SphericalGnomonic` that was conditional on
`PlanarConvexDiagPos` becomes unconditional.  We state the clean unconditional cut-branch outputs. -/

/-- **HINGE Lemma 2.3 (`CyclicTriplePos`), unconditional.**  Every strictly convex spherical polygon
has all `i < j < k` diagonals positively oriented — the convex-position residue fully discharged. -/
theorem cyclicTriplePos_unconditional {n : ℕ} [NeZero n] {P : Fin n → S2}
    (h : StrictConvexSphPolygon P) : CyclicTriplePos P :=
  cyclicTriplePos_holds planarConvexDiagPos_holds h

/-- **Clean spherical arm lemma (weak), unconditional in the cut branch (modulo `SZStepGeom`).**  The
convex-position input is now fully furnished by `planarConvexDiagPos_holds`; the only remaining
hypothesis is the opening primitive `SZStepGeom`. -/
theorem spherical_arm_mono_cut_unconditional (hcut : SZStepGeom)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_cut_holds planarConvexDiagPos_holds hcut hn A B hA hB hside hangle

/-- **Clean spherical arm lemma (strict), unconditional in the cut branch (modulo `SZStepGeom`).** -/
theorem spherical_arm_mono_strict_cut_unconditional (hcut : SZStepGeom)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict_cut_holds planarConvexDiagPos_holds hcut hn A B hA hB hside hangle hstrict

end ProofsInTheBook.PlanarConvexDiag
