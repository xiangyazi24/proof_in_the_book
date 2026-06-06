I’ll develop the genus-free count as a quotient-level orbit certificate for phi'2, using only its closed-form successor table. The key is classifying phi'2-orbits by labels, not by faceCorr2 cycles or old-dart projection.

The closing route is B, but with one important refinement:

Do not try to construct a semiconjugacy from phi'2 to phi, and do not try to preserve old face orbits as sets.
Construct an orbit-label certificate: a finite label type with exactly F + 2 labels, a label function constant on phi'2-orbits, and a proof that each label fiber is one phi'2-orbit.

The genus-free invariant is:

lean
phi'2-orbits are exactly the fibers of a label
  cutFaceLabel : Dcut → OldFace(phi) ⊕ Side

where

lean
Side = {plusCapFace, minusCapFace}.

Then:

lean
numCycles phi'2
  = card (OldFace(phi) ⊕ Side)
  = numCycles phi + 2
  = F + 2.

This proof uses only the per-class closed forms of phi'2. It ignores faceCorr2’s cycle structure entirely, which is exactly what the K4-torus evidence says we must do.

1. Candidate route assessment
A. Local induction on k

This is possible in principle but not the cleanest route. It creates intermediate permutations/maps that are not natural cut-cap maps. You then need to prove their face-count deltas by a new transposition-walk analysis. That may work, but it reintroduces adaptivity of SameCycle pivots in a less canonical setting.

I would not use it for the chapter.

B. phi'2-orbit bijection

This is the route that closes.

The correct theorem is:

lean
Quotient (SameCycle.setoid phi'2)
  ≃
Quotient (SameCycle.setoid phi) ⊕ Side

or, equivalently:

lean
numCycles phi'2 = numCycles phi + 2.

This is not a projection semiconjugacy. It is a classification of final phi'2-orbits by labels.

C. Euler via components/genus

Skip. It imports genus theory or an equivalent classification theorem.

D. Face-degree double count

Insufficient. Degree sums do not determine the number of face orbits.

E. Conservation law for the transposition walk

There may be a hidden conservation law, but once faceCorr2 can become one combined cycle threading both signs, the conservation law is not naturally a two-chain telescoping fact. The clean conservation law is the orbit-label certificate for phi'2.

So the proof should be:

lean
closed forms of phi'2
  ⇒ orbit-label certificate
  ⇒ quotient equivalence
  ⇒ F' = F + 2.
2. Pure permutation theorem: orbit-label certificates

First prove a generic theorem independent of maps.

Let q : Equiv.Perm X. Suppose there is a finite label type Λ, a label function, and an anchor for each label:

lean
label  : X → Λ
anchor : Λ → X

such that:

lean
label_anchor :
  ∀ ℓ, label (anchor ℓ) = ℓ

label_invariant :
  ∀ x, label (q x) = label x

same_anchor :
  ∀ x, SameCycle q x (anchor (label x))

Then:

lean
numCycles q = Fintype.card Λ.

This is the abstract engine.

2.1 Lean structure
lean
structure OrbitLabelCert
    (X Λ : Type*)
    [Fintype X] [DecidableEq X]
    [Fintype Λ] [DecidableEq Λ]
    (q : Equiv.Perm X) where
  label : X → Λ
  anchor : Λ → X

  label_anchor :
    ∀ ℓ, label (anchor ℓ) = ℓ

  label_invariant :
    ∀ x, label (q x) = label x

  same_anchor :
    ∀ x, SameCycle q x (anchor (label x))
2.2 Label is constant on same-cycle classes
lean
lemma label_eq_of_sameCycle
    {X Λ : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Λ] [DecidableEq Λ]
    {q : Equiv.Perm X}
    (C : OrbitLabelCert X Λ q)
    {x y : X}
    (h : SameCycle q x y) :
  C.label x = C.label y

Proof idea:

label_invariant gives constancy under one forward step:

lean
C.label (q x) = C.label x

It also gives constancy under one backward step:

lean
C.label (q.symm x) = C.label x

because:

lean
C.label (q (q.symm x)) = C.label (q.symm x)

and q (q.symm x) = x.

So the label is constant along the undirected orbit graph of q.

Lean skeleton:

lean
lemma label_eq_of_step_forward
    (C : OrbitLabelCert X Λ q) :
  C.label (q x) = C.label x :=
C.label_invariant x

lemma label_eq_of_step_backward
    (C : OrbitLabelCert X Λ q) :
  C.label (q.symm x) = C.label x := by
  have h := C.label_invariant (q.symm x)
  simpa using h.symm

Then induct over your definition of SameCycle.

If SameCycle q x y is defined by integer powers, prove:

lean
lemma label_zpow :
  ∀ n : ℤ, C.label ((q ^ n) x) = C.label x

and use the witness.

2.3 Equal labels imply same cycle
lean
lemma sameCycle_of_label_eq
    (C : OrbitLabelCert X Λ q)
    {x y : X}
    (h : C.label x = C.label y) :
  SameCycle q x y := by
  exact SameCycle.trans
    (C.same_anchor x)
    (SameCycle.symm (by
      simpa [h] using C.same_anchor y))

The idea is:

x ~ anchor(label x)
  = anchor(label y)
  ~ y.
2.4 Quotient equivalence

Define:

lean
def orbitLabelEquiv
    (C : OrbitLabelCert X Λ q) :
  Quotient (SameCycle.setoid q) ≃ Λ

by:

lean
toFun    := fun Q => Quot.lift C.label
              (by intro x y h; exact label_eq_of_sameCycle C h) Q
invFun   := fun ℓ => Quotient.mk _ (C.anchor ℓ)
left_inv := by
  intro Q
  refine Quot.induction_on Q ?_
  intro x
  apply Quot.sound
  exact C.same_anchor x
right_inv := by
  intro ℓ
  exact C.label_anchor ℓ

Then:

lean
theorem numCycles_eq_card_of_orbitLabelCert
    (C : OrbitLabelCert X Λ q) :
  numCycles q = Fintype.card Λ := by
  -- depending on your definition of numCycles:
  -- numCycles q = card of orbit quotient
  rw [numCycles_eq_card_orbitQuotient q]
  exact Fintype.card_congr (orbitLabelEquiv C)

This theorem is the reusable count engine.

3. The label type for cutCapMap2

Let:

lean
OldFace := Quotient (SameCycle.setoid phi)

with:

lean
def faceOf (d : D) : OldFace :=
  Quotient.mk _ d

and:

lean
inductive Side
| plus
| minus
deriving DecidableEq, Fintype

Define:

lean
abbrev CutFaceLabel := OldFace ⊕ Side

The final goal is to build:

lean
cutFaceLabelCert :
  OrbitLabelCert Dcut CutFaceLabel phi'2

Then:

lean
numCycles phi'2
  = Fintype.card CutFaceLabel
  = Fintype.card OldFace + Fintype.card Side
  = numCycles phi + 2.
4. What cutFaceLabel must encode

The label function is:

lean
cutFaceLabel : Dcut → OldFace ⊕ Side

It assigns each cut dart to one of:

lean
Sum.inl f          -- transported old face f
Sum.inr Side.plus  -- new plus cap face
Sum.inr Side.minus -- new minus cap face

This is not a projection to a dart of D. It is a classification of final phi'2-face orbits.

You define it by the same per-class partition already used for the closed forms of phi'2.

A typical shape:

lean
def cutFaceLabel : Dcut → OldFace ⊕ Side
| old d =>
    if h₁ : IsPlusNewFaceDart d then
      Sum.inr Side.plus
    else if h₂ : IsMinusNewFaceDart d then
      Sum.inr Side.minus
    else
      Sum.inl (faceOf (oldLabelRep d))
| cap Side.plus i =>
    Sum.inr Side.plus
| cap Side.minus i =>
    Sum.inr Side.minus

The exact predicates and oldLabelRep depend on your cutCapMap2 dart constructors. The point is that each branch should line up with a closed-form theorem for phi'2.

If some cap dart belongs to a transported old face in your convention, then label it by Sum.inl .... If all caps are on the two capped faces, label caps by side. The certificate is robust: only the closed-form lemmas decide the branches.

The required facts are:

lean
cutFaceLabel_phi'2 :
  ∀ x, cutFaceLabel (phi'2 x) = cutFaceLabel x

and:

lean
cutFaceLabel_fiber_connected :
  ∀ x y,
    cutFaceLabel x = cutFaceLabel y →
    SameCycle phi'2 x y.

The OrbitLabelCert packages the second condition via anchors.

5. Anchors

Define an anchor for every label.

For side labels:

lean
plusAnchor  : Dcut := cap Side.plus 0
minusAnchor : Dcut := cap Side.minus 0

or whichever cap representatives are known to lie in the two new face orbits.

For old labels, choose a representative old dart:

lean
noncomputable def oldFaceRep : OldFace → D :=
  Quotient.out

Then choose a canonical cut dart representing that old face:

lean
oldFaceLift : D → Dcut

In many implementations:

lean
oldFaceLift d = old d

but if seam darts have multiple cut-side incarnations, choose the one whose closed forms are easiest.

Required label lemma:

lean
oldFaceLift_label :
  ∀ d, cutFaceLabel (oldFaceLift d) = Sum.inl (faceOf d)

Define:

lean
noncomputable def cutFaceAnchor : CutFaceLabel → Dcut
| Sum.inl f =>
    oldFaceLift (oldFaceRep f)
| Sum.inr Side.plus =>
    plusAnchor
| Sum.inr Side.minus =>
    minusAnchor

Then prove:

lean
lemma cutFaceLabel_anchor :
  ∀ ℓ, cutFaceLabel (cutFaceAnchor ℓ) = ℓ := by
  intro ℓ
  cases ℓ with
  | inl f =>
      unfold cutFaceAnchor oldFaceRep
      rw [oldFaceLift_label]
      exact congrArg Sum.inl (Quotient.out_eq f)
  | inr s =>
      cases s
      · exact plusAnchor_label
      · exact minusAnchor_label

where:

lean
plusAnchor_label :
  cutFaceLabel plusAnchor = Sum.inr Side.plus

minusAnchor_label :
  cutFaceLabel minusAnchor = Sum.inr Side.minus
6. Label invariance under phi'2

This is the most local part and should use only your per-class closed forms.

Prove:

lean
lemma cutFaceLabel_phi'2 :
  ∀ x, cutFaceLabel (phi'2 x) = cutFaceLabel x

Lean skeleton:

lean
lemma cutFaceLabel_phi'2 :
  ∀ x : Dcut, cutFaceLabel (phi'2 x) = cutFaceLabel x := by
  intro x
  rcases cutDart_cases x with
    h_old_regular
  | h_old_plus_seam
  | h_old_minus_seam
  | h_cap_plus
  | h_cap_minus
  | h_boundary_case_1
  | h_boundary_case_2
  | ...
  · subst x
    simp [
      cutFaceLabel,
      phi'2_apply_old_regular,
      faceOf_phi
    ]
  · subst x
    simp [
      cutFaceLabel,
      phi'2_apply_old_plus_seam,
      faceOf_phi,
      cycle_index_simp
    ]
  · subst x
    simp [
      cutFaceLabel,
      phi'2_apply_old_minus_seam,
      faceOf_phi,
      cycle_index_simp
    ]
  · subst x
    simp [
      cutFaceLabel,
      phi'2_apply_plus_cap,
      cycle_index_simp
    ]
  · subst x
    simp [
      cutFaceLabel,
      phi'2_apply_minus_cap,
      cycle_index_simp
    ]
  · ...

The only old-face identity needed is:

lean
lemma faceOf_phi (d : D) :
  faceOf (phi d) = faceOf d := by
  exact Quot.sound (sameCycle_step phi d)

If some closed-form branch sends a seam dart to a cap or from a cap to an old dart, the two branches of cutFaceLabel must have been defined so both sides have the same label. That is the design constraint.

This is why cutFaceLabel should be defined from the closed-form partition, not from a naive projection.

7. Connectivity of each label fiber

Now prove every dart is in the same phi'2-orbit as its anchor:

lean
lemma cutFaceLabel_same_anchor :
  ∀ x, SameCycle phi'2 x (cutFaceAnchor (cutFaceLabel x))

This is the second certificate field.

The proof is split by label.

7.1 Old-face labels

First prove that old phi steps lift to phi'2-same-cycle paths.

lean
lemma oldFaceLift_phi_step :
  ∀ d : D,
    SameCycle phi'2
      (oldFaceLift d)
      (oldFaceLift (phi d))

This is not a semiconjugacy. It only says the two chosen lifts lie in the same phi'2-orbit.

For regular darts, it is a one-step proof:

lean
phi'2 (oldFaceLift d) = oldFaceLift (phi d)

For seam darts, it is a finite closed-form path through the local surgery gadgets.

Lean skeleton:

lean
lemma oldFaceLift_phi_step :
  ∀ d : D,
    SameCycle phi'2
      (oldFaceLift d)
      (oldFaceLift (phi d)) := by
  intro d
  rcases oldDart_cases d with h_regular | h_cycle_plus | h_cycle_minus | ...
  · subst d
    apply sameCycle_of_apply_eq
    simp [oldFaceLift, phi'2_apply_regular]
  · subst d
    exact sameCycle_path phi'2
      [ by simp [phi'2_apply_cycle_plus_1]
      , by simp [phi'2_apply_cycle_plus_2]
      , by simp [phi'2_apply_cycle_plus_3]
      ]
  · subst d
    exact sameCycle_path phi'2
      [ by simp [phi'2_apply_cycle_minus_1]
      , by simp [phi'2_apply_cycle_minus_2]
      , by simp [phi'2_apply_cycle_minus_3]
      ]
  · ...

Here sameCycle_path is a utility lemma:

lean
lemma sameCycle_path
    {q : Equiv.Perm X}
    {x y : X}
    (path : List X)
    (hpath : PathBy q x path y) :
  SameCycle q x y

or use repeated SameCycle.trans from equations of the form q a = b.

Then extend from one step to an arbitrary old face orbit:

lean
lemma oldFaceLift_same_old_face
    {d e : D}
    (h : SameCycle phi d e) :
  SameCycle phi'2 (oldFaceLift d) (oldFaceLift e)

Proof:

lean
-- if SameCycle is generated by phi-steps:
induction h with
| refl =>
    exact SameCycle.refl _
| step h ih =>
    exact SameCycle.trans ih (oldFaceLift_phi_step _)
| symm h ih =>
    exact SameCycle.symm ih
| trans h1 h2 ih1 ih2 =>
    exact SameCycle.trans ih1 ih2

If your SameCycle is integer-power based, prove by induction on n : ℤ, using oldFaceLift_phi_step and its symmetric version.

Now prove every old-labeled cut dart reaches some old lift.

lean
lemma oldLabel_to_oldFaceLift :
  ∀ x d,
    cutFaceLabel x = Sum.inl (faceOf d) →
    SameCycle phi'2 x (oldFaceLift d)

This is a closed-form case split on x.

Typical branches:

If x = oldFaceLift e and its label is faceOf e, then from the hypothesis faceOf e = faceOf d, use oldFaceLift_same_old_face.

If x is a local seam/cap dart labeled by an old face, the closed forms give a bounded phi'2 path from x to oldFaceLift e, then use oldFaceLift_same_old_face.

Skeleton:

lean
lemma oldLabel_to_oldFaceLift :
  ∀ x d,
    cutFaceLabel x = Sum.inl (faceOf d) →
    SameCycle phi'2 x (oldFaceLift d) := by
  intro x d hx
  rcases cutDart_cases x with h_regular | h_seam1 | h_seam2 | h_cap_old | ...
  · subst x
    simp [cutFaceLabel] at hx
    -- hx : faceOf e = faceOf d
    apply oldFaceLift_same_old_face
    exact sameCycle_of_faceOf_eq hx
  · subst x
    simp [cutFaceLabel] at hx
    exact SameCycle.trans
      (sameCycle_path phi'2 seam1_to_oldFaceLift_path)
      (oldFaceLift_same_old_face (sameCycle_of_faceOf_eq hx))
  · ...

The helper:

lean
lemma sameCycle_of_faceOf_eq
    {d e : D}
    (h : faceOf d = faceOf e) :
  SameCycle phi d e

comes from quotient equality.

Finally connect old lifts to their old-label anchors:

lean
lemma oldFaceLift_to_anchor
    (d : D) :
  SameCycle phi'2
    (oldFaceLift d)
    (cutFaceAnchor (Sum.inl (faceOf d))) := by
  unfold cutFaceAnchor
  apply oldFaceLift_same_old_face
  exact sameCycle_quotient_out d

where:

lean
lemma sameCycle_quotient_out
    (d : D) :
  SameCycle phi d (oldFaceRep (faceOf d))

is Quotient.out_eq.

Then:

lean
lemma oldLabel_to_anchor
    {x : Dcut} {d : D}
    (hx : cutFaceLabel x = Sum.inl (faceOf d)) :
  SameCycle phi'2
    x
    (cutFaceAnchor (Sum.inl (faceOf d))) := by
  exact SameCycle.trans
    (oldLabel_to_oldFaceLift x d hx)
    (oldFaceLift_to_anchor d)
7.2 Plus and minus new-face labels

Prove:

lean
lemma plusLabel_to_anchor :
  ∀ x,
    cutFaceLabel x = Sum.inr Side.plus →
    SameCycle phi'2 x plusAnchor

and:

lean
lemma minusLabel_to_anchor :
  ∀ x,
    cutFaceLabel x = Sum.inr Side.minus →
    SameCycle phi'2 x minusAnchor

Again, these are closed-form orbit traces.

They should not mention faceCorr2 chains. They should prove connectivity under the final face permutation phi'2.

Skeleton:

lean
lemma plusLabel_to_anchor :
  ∀ x,
    cutFaceLabel x = Sum.inr Side.plus →
    SameCycle phi'2 x plusAnchor := by
  intro x hx
  rcases cutDart_cases x with h_regular | h_seam | h_plusCap | h_minusCap | ...
  · subst x
    simp [cutFaceLabel] at hx
  · subst x
    simp [cutFaceLabel] at hx
    exact sameCycle_path phi'2
      [ by simp [phi'2_apply_plus_new_1]
      , by simp [phi'2_apply_plus_new_2]
      , ...
      ]
  · subst x
    simp [cutFaceLabel] at hx
    exact sameCycle_path phi'2 plusCap_to_anchor_path
  · subst x
    simp [cutFaceLabel] at hx
  · ...

Branches whose label is not Side.plus are discharged by contradiction from simp [cutFaceLabel] at hx.

Analogously for minus.

Then:

lean
lemma sideLabel_to_anchor :
  ∀ x s,
    cutFaceLabel x = Sum.inr s →
    SameCycle phi'2 x (cutFaceAnchor (Sum.inr s)) := by
  intro x s hx
  cases s
  · simpa [cutFaceAnchor] using plusLabel_to_anchor x hx
  · simpa [cutFaceAnchor] using minusLabel_to_anchor x hx
7.3 Assemble same-anchor proof
lean
lemma cutFaceLabel_same_anchor :
  ∀ x, SameCycle phi'2 x (cutFaceAnchor (cutFaceLabel x)) := by
  intro x
  cases h : cutFaceLabel x with
  | inl f =>
      let d := oldFaceRep f
      have hf : faceOf d = f := by
        exact Quotient.out_eq f
      have hx : cutFaceLabel x = Sum.inl (faceOf d) := by
        simpa [d, hf] using h
      exact SameCycle.trans
        (oldLabel_to_oldFaceLift x d hx)
        (oldFaceLift_to_anchor d)
  | inr s =>
      exact sideLabel_to_anchor x s h

This is the connectivity half of the certificate.

8. Build the certificate and count
lean
noncomputable def cutFaceLabelCert :
  OrbitLabelCert Dcut CutFaceLabel phi'2 where
  label := cutFaceLabel
  anchor := cutFaceAnchor
  label_anchor := cutFaceLabel_anchor
  label_invariant := cutFaceLabel_phi'2
  same_anchor := cutFaceLabel_same_anchor

Then:

lean
theorem numCycles_phi'2_eq_numCycles_phi_add_two :
  numCycles phi'2 = numCycles phi + 2 := by
  have hcert :
      numCycles phi'2 = Fintype.card CutFaceLabel := by
    exact numCycles_eq_card_of_orbitLabelCert cutFaceLabelCert

  calc
    numCycles phi'2
        = Fintype.card CutFaceLabel := hcert
    _   = Fintype.card (OldFace ⊕ Side) := rfl
    _   = Fintype.card OldFace + Fintype.card Side := by
            simp
    _   = numCycles phi + 2 := by
            simp [oldFace_card_eq_numCycles, Side]

If your chapter notation is:

lean
F  := numCycles phi
F' := numCycles phi'2

then:

lean
theorem cutCapMap2_faces :
  F' = F + 2 := by
  unfold F' F
  exact numCycles_phi'2_eq_numCycles_phi_add_two

This is the final genus-free count.

9. Optional stronger form: quotient equivalence theorem

It may be cleaner to expose the proof as an actual equivalence.

lean
noncomputable def phiPrimeFaceQuotEquiv :
  Quotient (SameCycle.setoid phi'2)
    ≃
  OldFace ⊕ Side :=
orbitLabelEquiv cutFaceLabelCert

Then:

lean
theorem numFaces_cutCapMap2 :
  numCycles phi'2 = numCycles phi + 2 := by
  have hcard :=
    Fintype.card_congr phiPrimeFaceQuotEquiv
  -- rewrite quotient-card to numCycles
  ...

This is the best chapter-level statement:

lean
Faces(cutCapMap2 M C) ≃ Faces(M) ⊕ {plusCapFace, minusCapFace}.

It is clear, genus-free, and independent of the internal cycle structure of faceCorr2.

10. Why the proof survives the K4-torus counterexample

In the K4-torus case, faceCorr2 may be one combined cycle threading both signs. That only says faceCorr2 is not the object whose cycles classify final faces.

The final face permutation is:

lean
phi'2 = phiLift * faceCorr2.

The product may have orbits classified by OldFace ⊕ Side even when faceCorr2 alone has a completely different cycle structure.

The proof works because the certificate checks:

lean
cutFaceLabel (phi'2 x) = cutFaceLabel x

and:

lean
SameCycle phi'2 x (cutFaceAnchor (cutFaceLabel x)).

Both are statements about phi'2 itself, using its closed forms.

So this proof is not refuted by variation in faceCorr2. It is designed to ignore it.

11. The final dependency-ordered lemma chain

Here is the implementation order I would use.

Layer 1: orbit quotient and cycle count
lean
SameCycle
SameCycle.setoid
sameCycle_refl
sameCycle_symm
sameCycle_trans
sameCycle_step
sameCycle_step_inv

numCycles_eq_card_orbitQuotient :
  numCycles q = Fintype.card (Quotient (SameCycle.setoid q))
Layer 2: old faces
lean
OldFace := Quotient (SameCycle.setoid phi)

faceOf : D → OldFace

faceOf_phi :
  faceOf (phi d) = faceOf d

sameCycle_of_faceOf_eq :
  faceOf d = faceOf e → SameCycle phi d e

oldFace_card_eq_numCycles :
  Fintype.card OldFace = numCycles phi
Layer 3: generic label certificate theorem
lean
OrbitLabelCert

label_eq_of_sameCycle
sameCycle_of_label_eq

orbitLabelEquiv :
  OrbitLabelCert X Λ q →
  Quotient (SameCycle.setoid q) ≃ Λ

numCycles_eq_card_of_orbitLabelCert :
  OrbitLabelCert X Λ q →
  numCycles q = Fintype.card Λ
Layer 4: cut labels
lean
Side
CutFaceLabel := OldFace ⊕ Side

cutFaceLabel : Dcut → CutFaceLabel
oldFaceLift : D → Dcut
plusAnchor : Dcut
minusAnchor : Dcut
cutFaceAnchor : CutFaceLabel → Dcut

oldFaceLift_label :
  cutFaceLabel (oldFaceLift d) = Sum.inl (faceOf d)

plusAnchor_label :
  cutFaceLabel plusAnchor = Sum.inr Side.plus

minusAnchor_label :
  cutFaceLabel minusAnchor = Sum.inr Side.minus

cutFaceLabel_anchor :
  cutFaceLabel (cutFaceAnchor ℓ) = ℓ
Layer 5: label invariance

Using per-class closed forms:

lean
cutFaceLabel_phi'2 :
  cutFaceLabel (phi'2 x) = cutFaceLabel x
Layer 6: old-label connectivity
lean
oldFaceLift_phi_step :
  SameCycle phi'2
    (oldFaceLift d)
    (oldFaceLift (phi d))

oldFaceLift_same_old_face :
  SameCycle phi d e →
  SameCycle phi'2 (oldFaceLift d) (oldFaceLift e)

oldFaceLift_to_anchor :
  SameCycle phi'2
    (oldFaceLift d)
    (cutFaceAnchor (Sum.inl (faceOf d)))

oldLabel_to_oldFaceLift :
  cutFaceLabel x = Sum.inl (faceOf d) →
  SameCycle phi'2 x (oldFaceLift d)

oldLabel_to_anchor :
  cutFaceLabel x = Sum.inl (faceOf d) →
  SameCycle phi'2 x
    (cutFaceAnchor (Sum.inl (faceOf d)))
Layer 7: side-label connectivity

Using per-class closed forms:

lean
plusLabel_to_anchor :
  cutFaceLabel x = Sum.inr Side.plus →
  SameCycle phi'2 x plusAnchor

minusLabel_to_anchor :
  cutFaceLabel x = Sum.inr Side.minus →
  SameCycle phi'2 x minusAnchor

sideLabel_to_anchor :
  cutFaceLabel x = Sum.inr s →
  SameCycle phi'2 x (cutFaceAnchor (Sum.inr s))
Layer 8: certificate assembly
lean
cutFaceLabel_same_anchor :
  SameCycle phi'2 x (cutFaceAnchor (cutFaceLabel x))

cutFaceLabelCert :
  OrbitLabelCert Dcut CutFaceLabel phi'2
Layer 9: final face count
lean
phiPrimeFaceQuotEquiv :
  Quotient (SameCycle.setoid phi'2) ≃ OldFace ⊕ Side

numCycles_phi'2_eq_numCycles_phi_add_two :
  numCycles phi'2 = numCycles phi + 2

cutCapMap2_faces :
  F' = F + 2
12. The invariant in one sentence

The genus-free invariant is:

lean
cutFaceLabel : Dcut → OldFace(phi) ⊕ Side

such that:

lean
cutFaceLabel (phi'2 x) = cutFaceLabel x

and every label fiber is connected under phi'2.

Therefore the final faces are not obtained by reading cycles of faceCorr2; they are obtained by quotienting Dcut by phi'2, and those quotient classes are exactly:

lean
old faces of M  +  two cap faces.

Hence:

lean
F' = F + 2.