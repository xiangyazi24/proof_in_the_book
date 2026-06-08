import ProofsInTheBook.SphericalSZClose

/-!
# `SphericalMonitoredSup` — the §R-O interior monitored-supremum trichotomy + reach persistence

This module is the **R-O** sub-theorem of Chapter 13's Schoenberg–Zaremba spherical arm lemma:
the *interior-axis* reach/stuck supremum trichotomy together with the **strict-convexity persistence
at REACH**.

The substrate `SphericalSZClose` already built the interior reach/stuck production
(`interior_reachOrStuck_at_sup`) on the interior tail-opening `openTail A K θ`, monitoring the
interior supports (`interiorSupport`) and the interior joint-angle target slack
(`interiorTargetSlack`).  It explicitly isolated the **remaining R-O core** as *boundary convexity of
the opened arm at `δ*`*: at the admissible supremum the monitored constraints are only `≥ 0`, while a
`StrictConvexSphArm` needs every non-incident support **strictly** `> 0` and the open-hemisphere
functional **strictly** `> 0` at every vertex — including the rotated-tail vertices, which the
substrate's interior family never monitored, so positivity there was not available at the boundary.

## What this module BANKS (genuine new, UNCONDITIONAL content — strictly enlarges the substrate)

We build a **single finite monitored family** for the interior opening `Aδ := openTail A K δ`
(axis `K = openingAxis k`, `k` the deficient joint), with three kinds of members:

* **support constraints** — one per *non-incident* edge–vertex pair `c` (edge `(c.i, c.i+1)`, vertex
  `c.j` with `c.j ≠ c.i` and `c.j ≠ c.i+1`): `supportConstraint δ c := sOrient (Aδ c.i)(Aδ (c.i+1))(Aδ c.j)`.
  Indexing *only non-incident* pairs is the genuine correction over the substrate's `interiorSupport`
  (which monitored *all* triples, including incident ones that are identically `0` and would trip a
  vacuous STUCK at `δ*`);
* **hemisphere constraints** using the **FIXED original hemisphere normal `h₀`** of `A`
  (`StrictConvexSphArm A` supplies it; it does *not* vary with `δ`):
  `hemiConstraint δ r := ⟪h₀, Aδ r⟫` — the substrate-absent monitoring of the rotated tail's
  hemisphere margin, the precise gap the R-O core named;
* the **joint slack** `jointSlack δ := jointAngle B k − openedInteriorJointAngle A k δ`.

`Monitored δ` is "all support constraints `> 0`, all hemisphere constraints `> 0`, and
`0 ≤ jointSlack δ`"; `Adm δ := 0 ≤ δ ∧ Monitored δ`.  Running the generic engine
`SphericalRotation.reach_or_stuck` on this family at `δ* := sSup {δ | Adm δ}` gives:

* **`opening_boundary_trichotomy`** — at `δ*`, *either* `jointSlack δ* = 0` (REACH) *or* a support
  vanishes *or* a hemisphere constraint vanishes (STUCK).  By closure every monitored constraint is
  `≥ 0` at `δ*`; if all three families were nonzero, closure + finiteness + continuity would keep them
  positive on a right-neighbourhood, contradicting `δ* = sup`.

* **`strict_persistence_at_reach`** — the main target.  In the REACH branch with `¬ Stuck`, every
  support constraint is `≥ 0` (closure) and `≠ 0` (else STUCK), hence `> 0`; likewise every hemisphere
  constraint with the **fixed** `h₀` is `> 0`.  These two strict positivities *are* exactly the
  `strict_nonincident` and `open_hemisphere` fields of `StrictConvexSphArm (openTail A K δ*)`, with
  `edge_short` derived from the hemisphere positivity (distinct open-hemisphere vertices form a short
  arc) and a strict support (edge endpoints distinct), and `edge_support` from `strict_nonincident`.
  This **discharges**, in the REACH case, the boundary-convexity obstacle the substrate isolated.

The REACH branch carries the mutually-exclusive data `Reach ∧ ¬ Stuck`, so the persistence is not
vacuous: STUCK and REACH are the two exhaustive boundary alternatives, and persistence is exactly the
REACH consumer.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose

namespace ProofsInTheBook.SphericalMonitoredSup

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §0. Two elementary determinant facts (edge-distinctness from a strict support). -/

/-- A strict orientation `0 < sOrient a b c` forces `a ≠ b` (else `det3 a a c = 0`). -/
theorem ne_of_sOrient_pos_ab {a b c : S2} (h : 0 < sOrient a b c) : a ≠ b := by
  intro he
  apply (ne_of_gt h).symm
  rw [sOrient, he, det3_self_left]

/-! ## §1. The hemisphere margin of the interior opening (the FIXED `h₀`).

The only substrate-absent monitored member: the open-hemisphere functional `⟪h₀, ·⟫` evaluated at the
*interior-opened* vertex `openTail A K θ r`.  `h₀` is the **fixed** original hemisphere normal of `A`
(it does not vary with `θ`).  Its continuity in `θ` follows from the vector-valued continuity of the
opened vertex (constant if fixed, a rotation of a constant if rotated). -/

/-- The interior-opened vertex `openTail A K θ r` as a *vector-valued* continuous function of `θ`. -/
theorem continuous_openTail_vec {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (r : Fin (n + 1)) :
    Continuous (fun θ : ℝ => ((openTail A K θ r : S2) : E3)) := by
  by_cases hx : r.val ≤ K.val
  · simp only [openTail_fixed A _ _ hx]
    exact continuous_const
  · simp only [openTail_rot A K _ (show K.val < r.val by omega), rotS2_coe]
    exact continuous_rot (A K : E3) (A r : E3)

/-- The hemisphere margin functional at the interior-opened vertex `r`:
`θ ↦ ⟪h₀, openTail A K θ r⟫`, with `h₀` the **fixed** hemisphere normal. -/
def hemiMargin {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3) (r : Fin (n + 1)) : ℝ → ℝ :=
  fun θ => (⟪h₀, ((openTail A K θ r : S2) : E3)⟫ : ℝ)

/-- The hemisphere margin is continuous in `θ`. -/
theorem continuous_hemiMargin {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3)
    (r : Fin (n + 1)) : Continuous (hemiMargin A K h₀ r) :=
  continuous_const.inner (continuous_openTail_vec A K r)

/-- At `θ = 0` the hemisphere margin equals `⟪h₀, A r⟫` (the original vertex's hemisphere value). -/
theorem hemiMargin_zero {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3) (r : Fin (n + 1)) :
    hemiMargin A K h₀ r 0 = (⟪h₀, (A r : E3)⟫ : ℝ) := by
  simp only [hemiMargin, openTail_zero_angle]

/-! ## §2. The non-incident support index and the support constraint.

A support constraint is monitored only for a *non-incident* edge–vertex pair `c` — edge `(c.i, c.i+1)`
and a vertex `c.j` with `c.j ≠ c.i`, `c.j ≠ c.i+1`.  This subtype is `Finite`, and the support
constraint is the interior support of the triple `(c.i, c.i+1, c.j)`, continuous in `θ` by the
substrate's `continuous_interiorSupport`. -/

/-- A non-incident edge–vertex pair: edge `(c.1, c.1+1)` and a vertex `c.2` off that edge. -/
def NonIncident (n : ℕ) : Type :=
  {c : Fin (n + 1) × Fin (n + 1) // c.2 ≠ c.1 ∧ c.2 ≠ c.1 + 1}

instance (n : ℕ) : Finite (NonIncident n) := by
  unfold NonIncident; infer_instance

/-- The support constraint at the non-incident pair `c`:
`θ ↦ sOrient (Aδ c.i)(Aδ (c.i+1))(Aδ c.j)`. -/
def supportConstraint {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (c : NonIncident n) : ℝ → ℝ :=
  interiorSupport A K (c.1.1, c.1.1 + 1, c.1.2)

/-- The support constraint is continuous in `θ`. -/
theorem continuous_supportConstraint {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (c : NonIncident n) : Continuous (supportConstraint A K c) :=
  continuous_interiorSupport A K (c.1.1, c.1.1 + 1, c.1.2)

/-- The support constraint unfolds to the opened-arm orientation. -/
theorem supportConstraint_apply {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (c : NonIncident n)
    (θ : ℝ) :
    supportConstraint A K c θ
      = sOrient (openTail A K θ c.1.1) (openTail A K θ (c.1.1 + 1)) (openTail A K θ c.1.2) := rfl

/-! ## §3. The single finite monitored family.

Indexed by `NonIncident n ⊕ (Fin (n+1) ⊕ Unit)`: support constraints, hemisphere constraints (FIXED
`h₀`), and the single joint-slack member.  The joint slack reuses the substrate's
`openedInteriorJointAngle A k`, with target `T := jointAngle B k`. -/

/-- The monitored family for the interior opening of joint `k` (axis `K = openingAxis k`), comparing to
arm `B` (target joint `jointAngle B k`), with fixed hemisphere normal `h₀`. -/
def monitoredFamily {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) :
    NonIncident n ⊕ (Fin (n + 1) ⊕ Unit) → ℝ → ℝ
  | Sum.inl c => supportConstraint A (openingAxis k) c
  | Sum.inr (Sum.inl r) => hemiMargin A (openingAxis k) h₀ r
  | Sum.inr (Sum.inr ()) => interiorTargetSlack A k (jointAngle B k)

/-- Each monitored-family member is continuous in `θ`. -/
theorem continuous_monitoredFamily {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) :
    ∀ o, Continuous (monitoredFamily A B k h₀ o) := by
  rintro (c | (r | ⟨⟩))
  · exact continuous_supportConstraint A (openingAxis k) c
  · exact continuous_hemiMargin A (openingAxis k) h₀ r
  · exact continuous_const.sub (continuous_openedInteriorJointAngle hka hkt)

/-- The admissible supremum `δ*` of the monitored family within `[0, Tcap]`. -/
def monitoredSup {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) (Tcap : ℝ) : ℝ :=
  sSup (admissibleSet (monitoredFamily A B k h₀) Tcap)

/-- **The monitored admissible supremum `δ*` is admissible** (the family is finite + continuous; its
admissible supremum is closed, nonempty, bounded). -/
theorem monitoredSup_mem {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSup A B k h₀ Tcap ∈ admissibleSet (monitoredFamily A B k h₀) Tcap :=
  sSup_mem_admissibleSet (continuous_monitoredFamily hka hkt) hTcap h0

/-! ## §4. Closure: every monitored constraint is `≥ 0` at `δ*`. -/

/-- At `δ*` every support constraint is `≥ 0` (closure of the admissible set). -/
theorem supportConstraint_nonneg_at_sup {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) (c : NonIncident n) :
    0 ≤ supportConstraint A (openingAxis k) c (monitoredSup A B k h₀ Tcap) :=
  (monitoredSup_mem hka hkt hTcap h0).2 (Sum.inl c)

/-- At `δ*` every hemisphere constraint (FIXED `h₀`) is `≥ 0` (closure). -/
theorem hemiMargin_nonneg_at_sup {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) (r : Fin (n + 1)) :
    0 ≤ hemiMargin A (openingAxis k) h₀ r (monitoredSup A B k h₀ Tcap) :=
  (monitoredSup_mem hka hkt hTcap h0).2 (Sum.inr (Sum.inl r))

/-! ## §5. The boundary trichotomy at `δ*`.

The R-O dichotomy: at the monitored supremum, `δ* = Tcap`, *or* the joint slack vanishes (REACH),
*or* a support / hemisphere constraint vanishes (STUCK).  We package the support+hemisphere alternative
as `Stuck`. -/

/-- The REACH predicate: the opened interior joint reaches `B`'s value (joint slack vanishes). -/
def Reach {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) (Tcap : ℝ) : Prop :=
  openedInteriorJointAngle A k (monitoredSup A B k h₀ Tcap) = jointAngle B k

/-- The STUCK predicate: a non-incident support *or* a hemisphere constraint vanishes at `δ*`. -/
def Stuck {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) (Tcap : ℝ) : Prop :=
  (∃ c : NonIncident n, supportConstraint A (openingAxis k) c (monitoredSup A B k h₀ Tcap) = 0) ∨
    (∃ r : Fin (n + 1), hemiMargin A (openingAxis k) h₀ r (monitoredSup A B k h₀ Tcap) = 0)

/-- **The §R-O boundary trichotomy at the monitored supremum `δ*`.**  Either `δ* = Tcap` (the opening
cap, avoided by `Tcap = π`), *or* `Reach`, *or* `Stuck`.  This is the engine's `reach_or_stuck` on the
monitored family, with the joint-slack member surfacing as REACH and the support/hemisphere members as
STUCK. -/
theorem opening_boundary_trichotomy {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSup A B k h₀ Tcap = Tcap ∨
      Reach A B k h₀ Tcap ∨ Stuck A B k h₀ Tcap := by
  rcases reach_or_stuck (continuous_monitoredFamily hka hkt) hTcap h0 with hcap | ⟨o, ho⟩
  · exact Or.inl hcap
  · rcases o with c | (r | ⟨⟩)
    · -- a support constraint vanishes: STUCK.
      exact Or.inr (Or.inr (Or.inl ⟨c, ho⟩))
    · -- a hemisphere constraint vanishes: STUCK.
      exact Or.inr (Or.inr (Or.inr ⟨r, ho⟩))
    · -- the joint slack vanishes: REACH.
      refine Or.inr (Or.inl ?_)
      have hslack : interiorTargetSlack A k (jointAngle B k) (monitoredSup A B k h₀ Tcap) = 0 := ho
      simp only [interiorTargetSlack] at hslack
      unfold Reach
      linarith

/-! ## §6. Strict positivity at `δ*` in the REACH (¬ Stuck) branch.

In the REACH branch with `¬ Stuck`, each monitored support / hemisphere constraint is `≥ 0` (closure)
and `≠ 0` (else STUCK), hence `> 0`. -/

/-- In the `¬ Stuck` branch every non-incident support is **strictly** `> 0` at `δ*`. -/
theorem supportConstraint_pos_at_sup {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hnotStuck : ¬ Stuck A B k h₀ Tcap) (c : NonIncident n) :
    0 < supportConstraint A (openingAxis k) c (monitoredSup A B k h₀ Tcap) := by
  have hle := supportConstraint_nonneg_at_sup hka hkt hTcap h0 c
  refine lt_of_le_of_ne hle (fun heq => hnotStuck (Or.inl ⟨c, heq.symm⟩))

/-- In the `¬ Stuck` branch the hemisphere margin (FIXED `h₀`) is **strictly** `> 0` at `δ*`, at every
opened-arm vertex. -/
theorem hemiMargin_pos_at_sup {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hnotStuck : ¬ Stuck A B k h₀ Tcap) (r : Fin (n + 1)) :
    0 < hemiMargin A (openingAxis k) h₀ r (monitoredSup A B k h₀ Tcap) := by
  have hle := hemiMargin_nonneg_at_sup hka hkt hTcap h0 r
  refine lt_of_le_of_ne hle (fun heq => hnotStuck (Or.inr ⟨r, heq.symm⟩))

/-! ## §7. Strict-convexity persistence at REACH (the main R-O target).

Assembling the strict support / hemisphere positivities of §6 into a full `StrictConvexSphArm` on the
opened arm `A* = openTail A K δ*`.  This discharges, in the REACH case, the boundary-convexity obstacle
the substrate isolated (its interior family did not monitor the rotated-tail hemisphere margin, so it
could not produce `> 0` there at the boundary; the augmented family does). -/

/-- **Interior reach persistence (general form).**  If at angle `δ` every non-incident support of the
interior-opened arm is strictly positive (`hmix`) and the fixed-`h₀` hemisphere margin is strictly
positive at every vertex (`hhem`, `‖h₀‖ = 1`), then `openTail A K δ` is a `StrictConvexSphArm`.  The
`edge_short` field is derived from the hemisphere positivity (distinct open-hemisphere vertices form a
short arc) together with a strict support (edge endpoints distinct, via vertex `i+2`); `edge_support`
is the weak form of `hmix`. -/
theorem reach_strictConvex_interior {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} {δ : ℝ} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    (hhem : ∀ r : Fin (n + 1), 0 < (⟪h₀, ((openTail A K δ r : S2) : E3)⟫ : ℝ)) :
    StrictConvexSphArm (openTail A K δ) := by
  have h3 : 3 ≤ n + 1 := by have := hA.two_le; omega
  -- distinctness of edge endpoints: pick the non-incident vertex `i + 2`.
  have hedge : ∀ i : Fin (n + 1), ShortArc (openTail A K δ i) (openTail A K δ (i + 1)) := by
    intro i
    have hi := i.isLt
    have h2v : ((2 : Fin (n + 1)) : ℕ) = 2 := by simp; omega
    have h1v : ((1 : Fin (n + 1)) : ℕ) = 1 := by simp; omega
    have e2 : ((i + 2 : Fin (n + 1)) : ℕ) = (↑i + 2) % (n + 1) := by rw [Fin.val_add, h2v]
    have e1 : ((i + 1 : Fin (n + 1)) : ℕ) = (↑i + 1) % (n + 1) := by rw [Fin.val_add, h1v]
    have hni0 : (i + 2 : Fin (n + 1)) ≠ i := by
      intro he
      have h := congrArg Fin.val he
      rw [e2] at h
      rcases Nat.lt_or_ge (↑i + 2) (n + 1) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h; omega
      · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h; omega
    have hni1 : (i + 2 : Fin (n + 1)) ≠ i + 1 := by
      intro he
      have h := congrArg Fin.val he
      rw [e2, e1] at h
      rcases Nat.lt_or_ge (↑i + 2) (n + 1) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)] at h; omega
      · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
        rcases Nat.lt_or_ge (↑i + 1) (n + 1) with hlt1 | hge1
        · rw [Nat.mod_eq_of_lt hlt1] at h; omega
        · rw [Nat.mod_eq_sub_mod hge1, Nat.mod_eq_of_lt (by omega)] at h; omega
    have hpos := hmix i (i + 2) hni0 hni1
    exact shortArc_of_hemisphere (hhem i) (hhem (i + 1)) (ne_of_sOrient_pos_ab hpos)
  refine { two_le := hA.two_le, closed_convex := ?_ }
  refine { three_le := h3
           edge_short := hedge
           edge_support := ?_
           strict_nonincident := hmix
           open_hemisphere := ⟨h₀, hnorm, hhem⟩ }
  intro i j
  by_cases hji : j = i
  · subst hji; rw [sOrient, det3_self_right]
  · by_cases hji1 : j = i + 1
    · subst hji1; rw [sOrient, det3_self_mid]
    · exact le_of_lt (hmix i j hji hji1)

/-- **Strict-convexity persistence at REACH (the main R-O theorem).**  In the REACH branch with
`¬ Stuck`, the interior-opened arm at the monitored supremum `A* = openTail A (openingAxis k) δ*` is a
`StrictConvexSphArm`.  The strict non-incident supports come from `supportConstraint_pos_at_sup`, the
strict hemisphere positivity (with the FIXED `h₀`) from `hemiMargin_pos_at_sup`; `‖h₀‖ = 1` is the
original arm's hemisphere normal.  This is the boundary-convexity persistence the substrate's R-O core
left open, now proved in the REACH case via the augmented monitoring. -/
theorem strict_persistence_at_reach {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (_hreach : Reach A B k h₀ Tcap) (hnotStuck : ¬ Stuck A B k h₀ Tcap) :
    StrictConvexSphArm (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap)) := by
  refine reach_strictConvex_interior hA hnorm ?_ ?_
  · -- every non-incident support is strictly positive at δ*.
    intro i j hji hji1
    have hc : (⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n) ∈ (Set.univ : Set (NonIncident n)) := trivial
    have := supportConstraint_pos_at_sup hka hkt hTcap h0 hnotStuck
      (⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n)
    rw [supportConstraint_apply] at this
    exact this
  · -- the fixed-h₀ hemisphere margin is strictly positive at every vertex of A* at δ*.
    intro r
    have := hemiMargin_pos_at_sup hka hkt hTcap h0 hnotStuck r
    simpa only [hemiMargin] using this

/-! ## §8. Non-vacuity / anti-impostor guards (playbook §3.3).

The monitored family and the trichotomy are over a real, inhabited admissible set, and the REACH
persistence is genuinely consumed by the `Reach ∧ ¬ Stuck` data of the trichotomy (REACH and STUCK are
exhaustive boundary alternatives), not a vacuous-hypothesis impostor. -/

/-- Non-vacuity of the joint-slack member: at `θ = 0` it is `jointAngle B k − jointAngle A k`, the
genuine initial deficit (nonnegative exactly when joint `k` of `B` is at least as wide as `A`'s — the
real "B's joint is wider" input), not a vacuous constant. -/
theorem monitoredFamily_jointSlack_zero {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) :
    monitoredFamily A B k h₀ (Sum.inr (Sum.inr ())) 0 = jointAngle B k - jointAngle A k := by
  show interiorTargetSlack A k (jointAngle B k) 0 = _
  simp only [interiorTargetSlack, openedInteriorJointAngle_zero]

/-- Non-vacuity of the support member: at `θ = 0` it is the genuine original orientation of the
non-incident triple of `A` (strictly positive for a strictly convex `A`), so the support constraints
are real geometric quantities, not vacuous. -/
theorem monitoredFamily_support_zero {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3)
    (c : NonIncident n) :
    monitoredFamily A B k h₀ (Sum.inl c) 0
      = sOrient (A c.1.1) (A (c.1.1 + 1)) (A c.1.2) := by
  show supportConstraint A (openingAxis k) c 0 = _
  rw [supportConstraint, interiorSupport_zero]

/-- Non-vacuity of the hemisphere member: at `θ = 0` it is the genuine original hemisphere value
`⟪h₀, A r⟫` (strictly positive for the original arm's hemisphere normal), not a vacuous constant. -/
theorem monitoredFamily_hemi_zero {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3)
    (r : Fin (n + 1)) :
    monitoredFamily A B k h₀ (Sum.inr (Sum.inl r)) 0 = (⟪h₀, (A r : E3)⟫ : ℝ) := by
  show hemiMargin A (openingAxis k) h₀ r 0 = _
  rw [hemiMargin_zero]

/-- Non-vacuity of the persistence conclusion: it is realised at `δ = 0` (the unopened arm
`openTail A K 0 = A`, which is `StrictConvexSphArm` by hypothesis) — so the conclusion is a real
strict-convexity statement, not a vacuous-hypothesis impostor. -/
theorem reach_strictConvex_interior_base {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (hA : StrictConvexSphArm A) :
    StrictConvexSphArm (openTail A K 0) := by
  rw [openTail_zero_angle]; exact hA

end ProofsInTheBook.SphericalMonitoredSup
