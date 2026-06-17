[intro]
I’ll pull FFCT25/23/18 signatures for the exact theorem names around boundary classification, coefficient degeneracy, and `FoldedFlatCutTransportPlus`, then I’ll give the discharge plan.

[answer]
1. **What the old splice residuals assert**

`SpliceBodyDiagMono` is **not** an IH-shaped `MainPlus` theorem. It asserts a one-side-monotone splice-body comparison where one side, the splice diagonal, is only `≤`, all other sides are equal, and the body joints are compared:

```lean
def SpliceBodyDiagMono : Prop :=
  ∀ m : ℕ, ∀ Ab Bb : Fin (m + 1) → S2,
    WeakConvexSphArm Ab → StrictConvexSphArm Bb →
    ∀ s : Fin m, sideLen Ab s ≤ sideLen Bb s →
    (∀ t : Fin m, t ≠ s → sideLen Ab t = sideLen Bb t) →
    (∀ r : Fin (m - 1), jointAngle Ab r ≤ jointAngle Bb r) →
    endpt Ab ≤ endpt Bb
```

The file explicitly says `Main` does **not** apply because `SameSides` fails at the splice edge and the splice joints are not inherited; it also records that the generic side-monotone lemma is false. filecite`SpliceStructuralData` asserts the structural CUT payload: from a weak arm with a vanishing nonincident support, produce cut indices, weak/strict splice bodies, the diagonal inequality, and body joint comparison:

```lean
def SpliceStructuralData : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2,
    WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    (∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (A i) (A (i + 1)) (A j) = 0) →
    ∃ (i j : ℕ) (hij : i < j) (hj : j ≤ n),
      WeakConvexSphArm (spliceArm A i j hij hj) ∧
      StrictConvexSphArm (spliceArm B i j hij hj) ∧
      sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩)
        ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, by omega⟩) ∧
      (∀ r : Fin (i + (n - j) + 1 - 1),
        jointAngle (spliceArm A i j hij hj) r ≤ jointAngle (spliceArm B i j hij hj) r)
```

filecite these should not be discharged directly**

Do **not** prove `SpliceBodyDiagMono` globally. Its own file documents the counterexample mechanism: one-side side-length monotonicity is false in general, and the only reason the real CUT closes is the specific folded-flat geometry. fileciteturn B1/B5 line is the right replacement: convert a support-zero event into a true folded-flat datum, use betweenness and boundary classification, and close by boundary endpoint arithmetic. So `SpliceBodyDiagMono` and `SpliceStructuralData` should be **superseded**, not proved.

3. **Exact FFCTPlus surface**

`FoldedFlatCutTransportPlus` already has the honest modern shape: it assumes `WeakConvexSphArm A`, `PositiveJoints A`, `StrictConvexSphArm B`, `SameSides`, `JointLe`, an IH `∀ m < n, MainPlus m`, explicit betweenness

```lean
(A i : E3) ∈ span≥0 {(A (i+1) : E3), (A j : E3)}
```

and diagonal inequality

```lean
sDist (A i) (A j) ≤ sDist (B i) (B j)
```

then concludes `endpt A ≤ endpt B`. fileciteturn92file0**

FFCT25’s boundary classification needs `NoNonadjacentRepeat A`:

```lean
theorem far_fold_boundary_classification_final ...
  (hnr : NoNonadjacentRepeat A)
  ...
  (hnd : ∃ a b : ℝ≥0, 0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧ ...)
  : i = 0 ∧ (j = n ∨ j = n - 1)
```

fileciteturn151file0lean
def NoNonadjacentRepeat {n : ℕ} (A : Fin (n + 1) → S2) : Prop :=
  ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1), r + 2 ≤ s →
    A ⟨r, hr⟩ ≠ A ⟨s, hs⟩
```

and explicitly says deriving it from `PositiveJoints` alone is the audited global gap. fileciteturn` statement cannot be proved via FFCT25 unless either `NoNonadjacentRepeat` is derived or threaded. Honest recommendation: replace it by:

```lean
def FoldedFlatCutTransportPlusNR : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ m : ℕ, m < n → MainPlus m) →
    ∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
      StrictConvexSphArm B → SameSides A B → JointLe A B →
      ∀ i j : ℕ, j ≠ i → j ≠ i + 1 →
        ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        (A ⟨i, by omega⟩ : E3) ∈
          Submodule.span NNReal ({(A ⟨i + 1, hi1⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3) →
        sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩)
          ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) →
        endpt A ≤ endpt B
```

5. **Degenerate coefficient dispatch**

Use FFCT23’s coefficient pipeline:

```lean
theorem far_fold_nondeg_datum_of_no_repeat ...
  (hcol : A i ∈ span≥0 {A(i+1), A j}) :
  ∃ a b : ℝ≥0, 0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧
    (a : ℝ) • A(i+1) + (b : ℝ) • A j = A i
```

Here `b > 0` comes from the short edge and `a > 0` from `NoNonadjacentRepeat`. fileciteturn152file0_adjacent_contradiction
    {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hpos : PositiveJoints A)
    (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hijfar : i + 2 < j) (hj : j < n + 1)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3)) :
    ∃ a b : ℝ≥0, 0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧
      (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3)
        + (b : ℝ) • (A ⟨j, hj⟩ : E3)
        = (A ⟨i, by omega⟩ : E3)
```

Classification: **worker**, 10–20 lines, direct FFCT23 call.

6. **Forward-index normalization**

FFCT25 requires `i + 2 < j`. The FFCTPlus statement only assumes `j ≠ i`, `j ≠ i+1`.

Add:

```lean
theorem foldedFlat_forward_or_boundary_dispatch
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hji : j ≠ i) (hji1 : j ≠ i + 1)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal ({(A ⟨i + 1, hi1⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3)) :
    i + 2 < j ∨ FoldedFlatCutTransportPlusNR_boundary_or_contradiction A B i j
```

Sketch: adjacent `j = i+2` gives a local joint angle `0`, contradicting `PositiveJoints`. Backward `j < i` needs either cyclic reindexing or should be excluded by the actual support-stuck normalizer. If the consuming support data is `NonIncident` from the monitored family, normalize there to forward edge order before calling FFCTPlusNR.

Classification: **master/needs-care**, 120–220 lines.

7. **Boundary case `(i,j)=(0,n)`**

This case closes cleanly.

```lean
theorem foldedFlat_boundary_j_eq_n
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (ih : ∀ m, m < n → MainPlus m)
    (hA : WeakConvexSphArm A) (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (hcol : (A 0 : E3) ∈
      Submodule.span NNReal ({(A ⟨1, by omega⟩ : E3), (A (Fin.last n) : E3)} : Set E3)) :
    endpt A ≤ endpt B
```

Sketch: betweenness gives

```lean
sDist (A 1) (A n) = sDist (A 1) (A 0) + endpt A
```

using `sDist_betweenness_of_collinear`. fileciteturn157file0L109 arms `[1..n]`. The interval API gives endpoint, side, and joint inheritance; `intervalArm_sameSides` and `intervalArm_jointLe` are banked. fileciteturn155file0L
sDist (B 1) (B n) ≤ sDist (B 1) (B 0) + endpt B
```

and `SameSides` gives `sDist (A 1) (A 0) = sDist (B 1) (B 0)`. Finish by `linarith`.

Classification: **needs-care**, 120–180 lines.

8. **Boundary case `(i,j)=(0,n-1)`**

This case does **not** close by the same algebra. The naive chain

```lean
endpt A ≤ sDist(A0,A(n-1)) + side_last
```

and

```lean
sDist(A0,A(n-1)) ≤ sDist(B0,B(n-1))
```

does not imply `endpt A ≤ endpt B`; the triangle inequality on `B` goes the wrong way.

Use FFCT18’s landed endpoint arithmetic instead:

```lean
theorem endpoint_le_of_tail_fold
    (hflatTail : sDist A0 An1 = sDist A0 An + sDist An An1)
    (hdiag : sDist A0 An1 ≤ sDist B0 Bn1)
    (hsideLast : sDist An An1 = sDist Bn Bn1) :
    sDist A0 An ≤ sDist B0 Bn
```

fileciteturn92file0Flat_boundary_j_eq_n_minus_one_tail_fold
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hpos : PositiveJoints A)
    (hnr : NoNonadjacentRepeat A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    (hcol : (A 0 : E3) ∈
      Submodule.span NNReal ({(A ⟨1, by omega⟩ : E3),
        (A ⟨n - 1, by omega⟩ : E3)} : Set E3)) :
    sDist (A 0) (A ⟨n - 1, by omega⟩)
      =
    endpt A + sDist (A (Fin.last n)) (A ⟨n - 1, by omega⟩)
```

Sketch: use weak supports of the two boundary edges and the positive-coefficient fold datum to force the last vertex onto the same folded ray; then convert cone membership to distance additivity. This is the real hard endpoint of the `j=n-1` boundary branch.

Classification: **master**, 250–450 lines.

9. **Boundary `(0,n-1)` transport**

Once the previous brick is available:

```lean
theorem foldedFlat_boundary_j_eq_n_minus_one
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hA : WeakConvexSphArm A) (hpos : PositiveJoints A)
    (hnr : NoNonadjacentRepeat A)
    (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (hcol : (A 0 : E3) ∈
      Submodule.span NNReal ({(A ⟨1, by omega⟩ : E3),
        (A ⟨n - 1, by omega⟩ : E3)} : Set E3))
    (hdiag :
      sDist (A 0) (A ⟨n - 1, by omega⟩)
        ≤ sDist (B 0) (B ⟨n - 1, by omega⟩)) :
    endpt A ≤ endpt B
```

Proof: call `foldedFlat_boundary_j_eq_n_minus_one_tail_fold`, then `endpoint_le_of_tail_fold`, and use `SameSides` for the last side.

Classification: **worker after master**, 40–80 lines.

10. **Main FFCTPlusNR proof**

```lean
theorem foldedFlatCutTransportPlusNR_holds :
    FoldedFlatCutTransportPlusNR
```

Proof structure:

1. Normalize to the forward far-fold case `i + 2 < j`; adjacent fold contradicts `PositiveJoints`.
2. Extract nondegenerate coefficients using `far_fold_nondeg_datum_of_no_repeat`.
3. Apply `far_fold_boundary_classification_final` to get `i=0 ∧ (j=n ∨ j=n-1)`. fileciteturn151file0L126j=n-1`, call `foldedFlat_boundary_j_eq_n_minus_one`.

Classification: **master wrapper**, 180–300 lines after boundary bricks.

11. **How to connect to the CUT branch**

Replace the old CUT consumer:

```lean
cut_step hcore hstruct ...
```

with:

```lean
theorem cut_step_plus
    (hffct : FoldedFlatCutTransportPlusNR)
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (ih : ∀ m, m < n → MainPlus m)
    (hA : WeakConvexSphArm A) (hpos : PositiveJoints A)
    (hnr : NoNonadjacentRepeat A)
    (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (hcut : CutReadyPlus A B) :
    endpt A ≤ endpt B
```

`CutReadyPlus` should supply the normalized support, betweenness, and diagonal inequality from the B1/B5 line. This deletes `SpliceBodyDiagMono` and `SpliceStructuralData`.

Classification: **needs-care**, 80–140 lines.

12. **Final honest headline after this wave**

If `NoNonadjacentRepeat` is accepted as a top-level invariant:

```lean
theorem mainPlus_headline_no_splice_residuals
    (hffct : FoldedFlatCutTransportPlusNR)
    (houtcome : InteriorOpeningOutcomePlusNR) :
    ∀ n, 2 ≤ n → MainPlus n
```

If the chapter headline is only for strict arms, state the final theorem without exposing `MainPlus`:

```lean
theorem spherical_arm_mono_final
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (hnr_produced :
      ∀ A' produced in the CUT path, NoNonadjacentRepeat A') :
    endpt A ≤ endpt B
```

Best final form is cleaner if the opening/CUT outcome carries:

```lean
NoNonadjacentRepeat A'
```

in its STUCK branch, so the public strict-arm theorem has no explicit `NoNonadjacentRepeat` assumption.

13. **Degenerate audit**

`n=2`: boundary `j=n` and `j=n-1` can overlap with adjacency. The `j=n-1=1` case is excluded by `j ≠ i+1` when `i=0`.

`a=0`: FFCT23 reduces to a nonadjacent repeat; killed only by `NoNonadjacentRepeat`.

`b=0`: killed by the short edge `A i`–`A(i+1)` via `coeff_b_pos_of_edge_short`.

`j=i+2`: adjacent folded ray forces the local joint to `0`; contradicted by `PositiveJoints`.

Backward `j<i`: must be normalized before FFCT25 or ruled out by the B1 support normalizer; do not leave it implicit.

14. **Ordered brick list**

1. `FoldedFlatCutTransportPlusNR` definition — worker, 20 lines.  
2. `foldedFlat_forward_or_boundary_dispatch` — master/needs-care, 120–220 lines.  
3. `foldedFlat_boundary_j_eq_n` — needs-care, 120–180 lines.  
4. `foldedFlat_boundary_j_eq_n_minus_one_tail_fold` — master, 250–450 lines.  
5. `foldedFlat_boundary_j_eq_n_minus_one` — worker, 40–80 lines.  
6. `foldedFlatCutTransportPlusNR_holds` — master wrapper, 180–300 lines.  
7. `cut_step_plus` replacing `cut_step` — needs-care, 80–140 lines.  
8. `open_step_plus` / `mainPlus` rethread removing `SpliceBodyDiagMono` and `SpliceStructuralData` — needs-care, 150–250 lines.

Final warning: the exact FFCT18 `FoldedFlatCutTransportPlus` without `NoNonadjacentRepeat` is not reachable from FFCT25. Either prove `NoNonadjacentRepeat` for the produced CUT arm, or honestly replace FFCTPlus by the `NR` version on the critical path.
