[intro]
I’ll quote the splice residual definitions directly and then separate what is pure recursion/IH from what is still structural geometry.

[answer]
1. **Exact legacy residuals**

`SpliceBodyDiagMono` is the isolated one-side-monotone splice-body comparison:

```lean
def SpliceBodyDiagMono : Prop :=
  ∀ m : ℕ, ∀ Ab Bb : Fin (m + 1) → S2,
    WeakConvexSphArm Ab → StrictConvexSphArm Bb →
    ∀ s : Fin m, sideLen Ab s ≤ sideLen Bb s →
    (∀ t : Fin m, t ≠ s → sideLen Ab t = sideLen Bb t) →
    (∀ r : Fin (m - 1), jointAngle Ab r ≤ jointAngle Bb r) →
    endpt Ab ≤ endpt Bb
```

The file explicitly says this is **not** a `Main` instance: the splice side is only `≤`, not equal, and the two splice joints are not controlled by parent `JointLe`. It also records the critical audit: the general one-side-monotone statement is false in a 2-edge limit, so it cannot be discharged as a generic theorem. fileciteturn146file0 payload:

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

It bundles body convexity preservation, diagonal inequality, and body joint comparison. fileciteturn148file0L11 is:

```lean
theorem cut_step
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    ...
    (hvanish : ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (A i) (A (i + 1)) (A j) = 0) :
    endpt A ≤ endpt B
```

It obtains the structural data and calls:

```lean
splice_transport_of_diag_le hcore hij hj hAb hBb hside hdiag hjoint
```

fileciteturn148file0L24 currently stated**

It is **not** just an application of `MainPlus` IH. `SpliceBodyDiagMono` is deliberately stronger/different than `MainPlus`: unequal splice side, unmatched splice joints. The file’s own audit says the generic lemma is false. fileciteturnliceBodyDiagMono` globally. The correct move is to **retire the legacy splice-body residual** and replace the CUT consumer by the landed B1/B5 cut route.

4. **What B1/B5 should replace**

The modern CUT payload is not “some support vanishes”; it is a **stuck datum with Gram signs**:

```lean
StuckAtKData A B i j
```

Then:

```lean
stuckAtK_betweenness
```

gives the folded-flat betweenness, the ear comparison gives the diagonal inequality, and `FoldedFlatCutTransportPlus` / FFCT25 boundary classification closes the endpoint.

So the replacement consumer should be:

```lean
theorem cut_step_from_stuckAtK_plus
    (hffct : FoldedFlatCutTransportPlus)
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (ihdim : ∀ m : ℕ, m < n → MainPlus m)
    (hA : WeakConvexSphArm A) (hApos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    {i j : ℕ}
    (hsk : StuckAtKData A B i j)
    (hAe : WeakConvexSphArm (intervalArm A (i + 1) (j - (i + 1)) (by omega)))
    (hBe : StrictConvexSphArm (intervalArm B (i + 1) (j - (i + 1)) (by omega))) :
    endpt A ≤ endpt B
```

Sketch: use `stuckAtK_diag_le_plus` to get `hdiag`; use `stuckAtK_betweenness` for `hcol`; call `FoldedFlatCutTransportPlus`. This deletes both `SpliceStructuralData` and `SpliceBodyDiagMono` from the CUT path.

Classification: **needs-care wrapper**, 80–140 lines.

5. **Modern opening outcome should output cut-ready data**

Current `InteriorOpeningOutcome` only outputs:

```lean
WeakConvexSphArm A' ∧
∃ i j, j ≠ i ∧ j ≠ i+1 ∧ sOrient (A' i) (A' (i+1)) (A' j) = 0
```

fileciteturn148file0L5 line. Replace with:

```lean
structure CutReadyPlus {n : ℕ}
    (A B : Fin (n + 1) → S2) : Prop where
  i j : ℕ
  hsk : StuckAtKData A B i j
  hAe : WeakConvexSphArm (intervalArm A (i + 1) (j - (i + 1)) (by omega))
  hBe : StrictConvexSphArm (intervalArm B (i + 1) (j - (i + 1)) (by omega))
```

Then define:

```lean
def InteriorOpeningOutcomePlus : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2,
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∃ A' : Fin (n + 1) → S2,
      endpt A ≤ endpt A' ∧ SameSides A' B ∧ JointLe A' B ∧ PositiveJoints A' ∧
      ((StrictConvexSphArm A' ∧ deficitCount A' B < deficitCount A B) ∨
       (WeakConvexSphArm A' ∧ CutReadyPlus A' B))
```

Classification: **master refactor**, 150–250 lines.

6. **Bridge from landed B1 to `CutReadyPlus`**

For the WB/WBS support-stuck branch, B1 should produce:

```lean
theorem CutReadyPlus_of_supportStuckWB
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    {k : Fin (n - 1)} {h₀ : E3}
    (hside : SameSides (openTailW A (openingAxis k) (monitoredSupWB A B k h₀)) B)
    (hangle : JointLe (openTailW A (openingAxis k) (monitoredSupWB A B k h₀)) B)
    (hpos : PositiveJoints (openTailW A (openingAxis k) (monitoredSupWB A B k h₀)))
    (hstuck : ∃ c : NonIncident n,
      supportConstraint A (openingAxis k) c (-(monitoredSupWB A B k h₀)) = 0) :
    CutReadyPlus (openTailW A (openingAxis k) (monitoredSupWB A B k h₀)) B
```

Sketch: normalize `c : NonIncident n` to the edge `(i,i+1)` and vertex `j`. Use B1 Gram-sign extraction to build `StuckAtKData`. Ear interval convexity comes from the existing interval-arm API plus positivity/strictness of sub-arms.

Classification: **master**, 200–350 lines if B1 normalization is already landed; otherwise larger.

7. **Generic weak-entry CUT branch**

The old `strict_or_vanishing` branch also handles a weak input `A` that already has a vanishing support before any opening. For the repaired `MainPlus` proof, this branch must not consume bare `hsupp`; it needs `CutReadyPlus`.

So replace:

```lean
strict_or_vanishing : ... → vanish ∨ StrictConvexSphArm A
```

with:

```lean
def CutReadyOrStrictPlus : Prop :=
  ∀ n A B,
    WeakConvexSphArm A → PositiveJoints A →
    StrictConvexSphArm B → SameSides A B → JointLe A B →
    CutReadyPlus A B ∨ StrictConvexSphArm A
```

But this is a real theorem, not routine. It asks: if `A` is weak positive and not strict, can we extract Gram signs? B1 derivative does not apply to arbitrary weak `A`.

Recommended honest alternative: **do not prove full `MainPlus` for arbitrary weak-positive arms via this branch**. Prove the chapter headline for strict-left arms using the opening-produced `CutReadyPlus`. If the theorem name `MainPlus` remains, this is another predicate-scope issue.

Classification: **critical design choice**.

8. **If full `MainPlus` is required**

Then you need a new residual:

```lean
def WeakPositiveCutReady : Prop :=
  ∀ n A B,
    WeakConvexSphArm A → PositiveJoints A →
    StrictConvexSphArm B → SameSides A B → JointLe A B →
    (∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (A i) (A (i + 1)) (A j) = 0) →
    CutReadyPlus A B
```

This is **not** supplied by B1. It is exactly the arbitrary-weak analogue of Gram-sign extraction and may be false without a reachability/closure certificate.

Classification: **master/open**, 500+ lines or predicate repair.

9. **Recommended final architecture**

Do not discharge `SpliceBodyDiagMono`. Delete it from the final route.

New assembly theorem:

```lean
theorem open_step_plus
    (hffct : FoldedFlatCutTransportPlus)
    (houtcome : InteriorOpeningOutcomePlus)
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (ihdim : ∀ m, m < n → MainPlus m)
    (ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B')
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k) :
    endpt A ≤ endpt B
```

REACH branch: same `ihdef`.  
CUT branch: `cut_step_from_stuckAtK_plus`.

Classification: **needs-care**, 120–200 lines.

10. **Strong induction wrapper**

The banked shape already exists in the old assembly: `open_step` takes

```lean
ihdef : ∀ A' B' : Fin (n + 1) → S2,
  WeakConvexSphArm A' → StrictConvexSphArm B' →
  SameSides A' B' → JointLe A' B' →
  deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B'
```

fileciteturn148file0L The outer induction is still strong induction on `n`; the inner induction is strong induction on `deficitCount`. This part is (a): the REACH branch genuinely dissolves into same-level deficit IH.

CUT branch should **not** use splice body IH; it uses dimension IH only for the ear comparison inside `stuckAtK_diag_le_plus`, then specialized FFCTPlus for endpoint.

11. **Final unconditional theorem shape**

If you keep full `MainPlus`:

```lean
theorem mainPlus_all_final
    (hweakCut : WeakPositiveCutReady)
    (hffct : FoldedFlatCutTransportPlus)
    (houtcome : InteriorOpeningOutcomePlus) :
    ∀ n : ℕ, 2 ≤ n → MainPlus n
```

But if `InteriorOpeningOutcomePlus` is fully landed and the only input arms in the final headline are strict, the honest chapter headline should be:

```lean
theorem spherical_arm_mono_final
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B) :
    endpt A ≤ endpt B
```

with no `SpliceBodyDiagMono` or `SpliceStructuralData`.

12. **Ordered bricks**

1. `CutReadyPlus` structure — worker, 30–50 lines.  
2. `cut_step_from_stuckAtK_plus` — needs-care, 80–140 lines.  
3. `CutReadyPlus_of_supportStuckWB/WBS` — master, 200–350 lines.  
4. `InteriorOpeningOutcomePlus` replacing bare vanish payload — master refactor, 150–250 lines.  
5. `open_step_plus` — needs-care, 120–200 lines.  
6. `mainPlus_at_level_plus` / `mainPlus_all_final` — routine/needs-care, 100–180 lines.  
7. Optional but dangerous: `WeakPositiveCutReady` if full weak-left `MainPlus` must be retained — master/open, 500+ lines.

13. **Bottom line**

`SpliceBodyDiagMono` is not a theorem to prove; it is a false overgeneralized legacy residual. `SpliceStructuralData` is also the wrong payload level now. The landed B1/B5 line should replace the CUT branch with a `StuckAtKData`/`CutReadyPlus` consumer, after which the final chapter headline can be unconditional for strict arms.
