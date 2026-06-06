The route that closes genus-free is B: the phi'-orbit bijection done at the quotient/label level, not a semiconjugacy and not a decomposition of faceCorr2.

The right invariant is:

lean
Every `phi'2`-orbit has a unique label in
  OldFace(phi) ⊕ Side,
and every label fiber is exactly one `phi'2`-orbit.

So you prove

lean
numCycles phi'2 = Fintype.card (OldFace phi ⊕ Side)
                = numCycles phi + 2
                = F + 2.

This proof is genus-free because it never uses the cycle structure of faceCorr2. It uses only the closed forms for phi'2 itself.

0. Why the two-chain route failed, and what replaces it

The false assumption was:

lean
faceCorr2 = plusChain * minusChain

with two independently telescoping seam chains. Kernel data refutes that at positive genus and even shows shape variation at genus zero.

The replacement is not to understand faceCorr2 as a product. Instead, ignore faceCorr2 after the factorization has given you the closed forms of

lean
phi'2 : Perm Dcut.

Then prove directly that the orbits of phi'2 are classified by:

lean
OldFace(phi) ⊕ Side

where:

lean
OldFace(phi) := quotient/orbit type of phi on D
Side := plus | minus

The two Side labels are the two newly capped faces. The OldFace(phi) labels are the old faces transported through the surgery.

This avoids all genus dependence. The old face orbits may be rearranged as sets of darts, and faceCorr2 may have any cycle structure, but the phi'2-orbits are still counted by these labels.

1. Generic permutation theorem: orbit labels count cycles

First prove a pure permutation theorem.

Let q : Equiv.Perm X and let β be a finite label type. Suppose we have:

lean
label  : X → β
anchor : β → X

such that:

lean
label_anchor :
  ∀ b, label (anchor b) = b

label_invariant :
  ∀ x, label (q x) = label x

same_anchor :
  ∀ x, SameCycle q x (anchor (label x))

Then:

lean
numCycles q = Fintype.card β.

This is the central abstract theorem.

1.1 Lean statement
lean
structure OrbitLabelCert
    (X β : Type*) [Fintype X] [DecidableEq X]
    [Fintype β] [DecidableEq β]
    (q : Equiv.Perm X) where
  label : X → β
  anchor : β → X

  label_anchor :
    ∀ b, label (anchor b) = b

  label_invariant :
    ∀ x, label (q x) = label x

  same_anchor :
    ∀ x, SameCycle q x (anchor (label x))

Then:

lean
theorem numCycles_eq_card_of_orbitLabelCert
    {X β : Type*} [Fintype X] [DecidableEq X]
    [Fintype β] [DecidableEq β]
    (q : Equiv.Perm X)
    (C : OrbitLabelCert X β q) :
  numCycles q = Fintype.card β
1.2 Proof

You prove that SameCycle q x y is equivalent to C.label x = C.label y.

First direction:

lean
lemma label_eq_of_sameCycle
    (h : SameCycle q x y) :
  C.label x = C.label y

Proof: label_invariant says the label is constant under one forward q step. Since q is a permutation, it is also constant under backward steps:

lean
have h_inv_back : ∀ x, C.label (q.symm x) = C.label x := by
  intro x
  have h := C.label_invariant (q.symm x)
  simpa using h

Then induct over the orbit relation.

Second direction:

lean
lemma sameCycle_of_label_eq
    (h : C.label x = C.label y) :
  SameCycle q x y

Proof:

lean
x ~ anchor (label x)
  = anchor (label y)
  ~ y.

In Lean:

lean
exact SameCycle.trans
  (C.same_anchor x)
  (SameCycle.symm (by simpa [h] using C.same_anchor y))

Thus the quotient of X by SameCycle q is equivalent to β.

Define:

lean
def orbitLabelEquiv :
  Quotient (SameCycle.setoid q) ≃ β

by:

lean
toFun [x] := C.label x
invFun b := Quotient.mk _ (C.anchor b)

Well-definedness uses label_eq_of_sameCycle. The inverse proofs use label_anchor and same_anchor.

Then:

lean
numCycles q
= Fintype.card (Quotient (SameCycle.setoid q))
= Fintype.card β.

This theorem is completely independent of maps, genus, chains, and faceCorr2.

2. Apply the theorem with label type OldFace(phi) ⊕ Side

For the cut-and-cap map, set:

lean
X := Dcut
q := phi'2
β := OldFace(phi) ⊕ Side

where:

lean
inductive Side
| plus
| minus

and:

lean
OldFace(phi) := Quotient (SameCycle.setoid phi)

with:

lean
faceOf : D → OldFace(phi)
faceOf d := Quotient.mk _ d

The target certificate is:

lean
def cutFaceLabelCert :
  OrbitLabelCert Dcut (OldFace(phi) ⊕ Side) phi'2

Once this is built:

lean
calc
  numCycles phi'2
      = Fintype.card (OldFace(phi) ⊕ Side) := by
          exact numCycles_eq_card_of_orbitLabelCert phi'2 cutFaceLabelCert
  _   = Fintype.card (OldFace(phi)) + Fintype.card Side := by
          simp
  _   = numCycles phi + 2 := by
          simp [OldFace_card_eq_numCycles_phi, Side]
  _   = F + 2 := by
          rw [hF]

This is the full genus-free count.

3. What the label means

The label is not a projection semiconjugacy. It is an orbit classifier.

A cut dart is labeled either by:

lean
Sum.inl f

meaning “this dart lies on the transported old face f,” or by:

lean
Sum.inr Side.plus
Sum.inr Side.minus

meaning “this dart lies on one of the two new capped faces.”

So define:

lean
def FaceLabel := OldFace(phi) ⊕ Side

Then define:

lean
cutLabel : Dcut → FaceLabel

by a case table generated from the closed forms of phi'2.

This is the crucial point: cutLabel is not required to satisfy

lean
cutLabel (phi'2 x) = mapSomething (cutLabel x)

for an old dart-level projection. It only satisfies the much weaker and correct invariant:

lean
cutLabel (phi'2 x) = cutLabel x.

That is exactly what orbit counting needs.

4. The concrete certificate fields

You need:

lean
cutLabel : Dcut → OldFace(phi) ⊕ Side
cutAnchor : OldFace(phi) ⊕ Side → Dcut

with:

lean
cutLabel_anchor :
  ∀ b, cutLabel (cutAnchor b) = b

cutLabel_phi'2 :
  ∀ x, cutLabel (phi'2 x) = cutLabel x

cut_same_anchor :
  ∀ x, SameCycle phi'2 x (cutAnchor (cutLabel x))

These three facts close the count.

4.1 The anchors

For the two new faces:

lean
cutAnchor (Sum.inr Side.plus)  := plusCapAnchor
cutAnchor (Sum.inr Side.minus) := minusCapAnchor

Usually:

lean
plusCapAnchor  := cap Side.plus  0
minusCapAnchor := cap Side.minus 0

or whichever representatives your closed forms make convenient.

For old faces, choose a representative old dart:

lean
noncomputable def oldFaceRep : OldFace(phi) → D :=
  Quotient.out

Then:

lean
cutAnchor (Sum.inl f) := oldFaceLift (oldFaceRep f)

where:

lean
oldFaceLift : D → Dcut

is the cut dart representing the old face corner of d.

In the simplest cases:

lean
oldFaceLift d = Sum.inl d

but do not require that globally. At seam/cycle darts, oldFaceLift should be the representative selected by your phi'2 closed-form table.

The required anchor label lemma is:

lean
lemma cutLabel_oldFaceLift :
  ∀ d, cutLabel (oldFaceLift d) = Sum.inl (faceOf d)

Then:

lean
lemma cutLabel_anchor_old :
  ∀ f, cutLabel (cutAnchor (Sum.inl f)) = Sum.inl f := by
  intro f
  unfold cutAnchor
  rw [cutLabel_oldFaceLift]
  exact Quotient.out_eq f

and for sides:

lean
lemma cutLabel_plusCapAnchor :
  cutLabel plusCapAnchor = Sum.inr Side.plus

lemma cutLabel_minusCapAnchor :
  cutLabel minusCapAnchor = Sum.inr Side.minus

Together:

lean
lemma cutLabel_anchor :
  ∀ b, cutLabel (cutAnchor b) = b := by
  intro b
  cases b with
  | inl f =>
      exact cutLabel_anchor_old f
  | inr s =>
      cases s <;> simp [cutAnchor, cutLabel_plusCapAnchor, cutLabel_minusCapAnchor]
5. How to define cutLabel from closed forms

Do not define cutLabel by guessing from faceCorr2.

Define it from the closed forms of phi'2.

You already have symbolic theorems of the shape:

lean
phi'2_apply_old_nonseam
phi'2_apply_old_plus_seam
phi'2_apply_old_minus_seam
phi'2_apply_cap_plus
phi'2_apply_cap_minus
...

Use the same partition of Dcut to define:

lean
def cutLabel : Dcut → OldFace(phi) ⊕ Side

The table should satisfy these two local principles.

5.1 Old-face labels

For every old face corner represented by d : D:

lean
cutLabel (oldFaceLift d) = Sum.inl (faceOf d)

and if a phi'2 step represents an old phi step, its labels agree because:

lean
faceOf (phi d) = faceOf d.

So typical proofs look like:

lean
simp [cutLabel, phi'2_apply_*, faceOf_phi]

where:

lean
lemma faceOf_phi (d : D) :
  faceOf (phi d) = faceOf d
5.2 New-face labels

For the two capped faces, every dart in the plus capped trace receives:

lean
Sum.inr Side.plus

and every dart in the minus capped trace receives:

lean
Sum.inr Side.minus.

Then the closed forms give:

lean
cutLabel (phi'2 x) = cutLabel x

by direct rewriting.

In Lean, the invariant proof should be a single case split over the closed-form classes:

lean
lemma cutLabel_phi'2 :
  ∀ x, cutLabel (phi'2 x) = cutLabel x := by
  intro x
  rcases classify_cut_dart x with h | h | h | h | ...
  · subst h
    simp [cutLabel, phi'2_apply_old_nonseam, faceOf_phi]
  · subst h
    simp [cutLabel, phi'2_apply_old_plus_seam, faceOf_phi, cycle_index_identities]
  · subst h
    simp [cutLabel, phi'2_apply_old_minus_seam, faceOf_phi, cycle_index_identities]
  · subst h
    simp [cutLabel, phi'2_apply_cap_plus]
  · subst h
    simp [cutLabel, phi'2_apply_cap_minus]

This proof is genus-free because it is purely local.

6. The hard-looking part: one orbit per label

The only nontrivial certificate field is:

lean
cut_same_anchor :
  ∀ x, SameCycle phi'2 x (cutAnchor (cutLabel x))

This says every label fiber is connected under phi'2.

Prove it in two pieces.

6.1 Old labels are connected to old-face anchors

First prove a local lift of every old phi step.

lean
lemma oldFaceLift_phi_step :
  ∀ d : D,
    SameCycle phi'2
      (oldFaceLift d)
      (oldFaceLift (phi d))

This is not a semiconjugacy. It does not say:

lean
phi'2 (oldFaceLift d) = oldFaceLift (phi d)

It only says they are in the same phi'2 orbit.

In most nonseam cases the proof is one step:

lean
phi'2 (oldFaceLift d) = oldFaceLift (phi d)

At seam cases, the proof is a bounded closed-form path through the local cut/cap darts:

lean
oldFaceLift d
  --phi'2--> local seam dart 1
  --phi'2--> local seam dart 2
  ...
  --phi'2--> oldFaceLift (phi d)

So the Lean proof is:

lean
lemma oldFaceLift_phi_step :
  ∀ d : D,
    SameCycle phi'2
      (oldFaceLift d)
      (oldFaceLift (phi d)) := by
  intro d
  by_cases h : IsSeamDart d
  · rcases seam_cases d h with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ...
    · exact sameCycle_of_phi'2_path
        [phi'2_apply_seam_1, phi'2_apply_seam_2, ...]
    · exact sameCycle_of_phi'2_path
        [phi'2_apply_seam_1, phi'2_apply_seam_2, ...]
  · exact sameCycle_of_apply_eq
      (by simp [oldFaceLift, phi'2_apply_old_nonseam, h])

Then extend from one old phi step to an entire old face orbit.

lean
lemma oldFaceLift_same_old_face
    {d e : D}
    (h : SameCycle phi d e) :
  SameCycle phi'2 (oldFaceLift d) (oldFaceLift e)

Proof: induction over the SameCycle phi path, using oldFaceLift_phi_step and symmetry.

Now for an old face label:

lean
lemma oldFaceLift_to_anchor
    (d : D) :
  SameCycle phi'2
    (oldFaceLift d)
    (cutAnchor (Sum.inl (faceOf d))) := by
  unfold cutAnchor
  exact oldFaceLift_same_old_face
    (sameCycle_faceOf_out d)

where:

lean
sameCycle_faceOf_out :
  SameCycle phi d (oldFaceRep (faceOf d))

comes from Quotient.out_eq.

6.2 Every dart with old label reaches its old lift

Next prove:

lean
lemma cutDart_oldLabel_to_lift :
  ∀ x d,
    cutLabel x = Sum.inl (faceOf d) →
    SameCycle phi'2 x (oldFaceLift d)

Again, this is a finite case split using closed forms.

For an old nonseam dart, this is usually immediate:

lean
x = oldFaceLift d

or one local path to it.

For a seam/cap dart that belongs to an old transported face, the closed forms give a bounded path from that dart to the corresponding oldFaceLift d.

Lean skeleton:

lean
lemma cutDart_oldLabel_to_lift :
  ∀ x d,
    cutLabel x = Sum.inl (faceOf d) →
    SameCycle phi'2 x (oldFaceLift d) := by
  intro x d hx
  rcases classify_cut_dart x with h | h | h | h | ...
  · subst h
    simp [cutLabel] at hx
    -- reduce to oldFaceLift_same_old_face
    exact oldFaceLift_same_old_face (by simpa using hx)
  · subst h
    simp [cutLabel] at hx
    exact sameCycle_trans
      (sameCycle_of_phi'2_path [phi'2_apply_*, ...])
      (oldFaceLift_same_old_face (by simpa using hx))
  · ...

This proof is where your per-class symbolic phi'2 equations are used.

6.3 New labels are connected to side anchors

For the plus new face:

lean
lemma plusLabel_to_anchor :
  ∀ x,
    cutLabel x = Sum.inr Side.plus →
    SameCycle phi'2 x plusCapAnchor

For the minus new face:

lean
lemma minusLabel_to_anchor :
  ∀ x,
    cutLabel x = Sum.inr Side.minus →
    SameCycle phi'2 x minusCapAnchor

These are also direct finite closed-form orbit traces.

The capped-face traces may be pure cap cycles in some maps and mixed in others. That does not matter. The trace is not faceCorr2’s trace. It is the phi'2 trace. Your closed forms identify the phi'2 successor of every dart, so the proof is a finite local path around the capped boundary.

Lean skeleton:

lean
lemma sideLabel_to_anchor :
  ∀ x s,
    cutLabel x = Sum.inr s →
    SameCycle phi'2 x (cutAnchor (Sum.inr s)) := by
  intro x s hx
  cases s
  · exact plusLabel_to_anchor x hx
  · exact minusLabel_to_anchor x hx
6.4 Assemble cut_same_anchor
lean
lemma cut_same_anchor :
  ∀ x, SameCycle phi'2 x (cutAnchor (cutLabel x)) := by
  intro x
  cases h : cutLabel x with
  | inl f =>
      -- choose old representative of f
      let d := oldFaceRep f
      have hf : faceOf d = f := by
        exact Quotient.out_eq f
      have hx :
          cutLabel x = Sum.inl (faceOf d) := by
        simpa [d, hf] using h
      exact cutDart_oldLabel_to_lift_then_anchor x d hx
  | inr s =>
      exact sideLabel_to_anchor x s h

where:

lean
lemma cutDart_oldLabel_to_lift_then_anchor
    (x : Dcut) (d : D)
    (hx : cutLabel x = Sum.inl (faceOf d)) :
  SameCycle phi'2 x (cutAnchor (Sum.inl (faceOf d))) := by
  exact SameCycle.trans
    (cutDart_oldLabel_to_lift x d hx)
    (oldFaceLift_to_anchor d)

This completes the certificate.

7. The genus-free theorem

Now define:

lean
def cutFaceLabelCert :
  OrbitLabelCert Dcut (OldFace(phi) ⊕ Side) phi'2 where
  label := cutLabel
  anchor := cutAnchor
  label_anchor := cutLabel_anchor
  label_invariant := cutLabel_phi'2
  same_anchor := cut_same_anchor

Then:

lean
theorem numCycles_phi'2_eq :
  numCycles phi'2 = numCycles phi + 2 := by
  have h :=
    numCycles_eq_card_of_orbitLabelCert
      phi'2 cutFaceLabelCert
  calc
    numCycles phi'2
        = Fintype.card (OldFace(phi) ⊕ Side) := h
    _   = Fintype.card (OldFace(phi)) + Fintype.card Side := by
            simp
    _   = numCycles phi + 2 := by
            simp [OldFace_card_eq_numCycles, Side]

Using your existing theorem:

lean
numCycles_phiLift = F + 2*k

is no longer needed for this proof, except as consistency evidence. The direct phi'2 orbit-label proof gives the target immediately.

If you want to keep the already-established notation:

lean
F := numCycles phi
F' := numCycles phi'2

then:

lean
theorem face_count_cutCapMap2 :
  F' = F + 2 := by
  unfold F' F
  exact numCycles_phi'2_eq
8. Why this is not a forbidden semiconjugacy

The kernel refuted a projection semiconjugacy of the form:

lean
π (phi'2 x) = phi (π x)

or similar.

This proof does not need one.

It only proves:

lean
cutLabel (phi'2 x) = cutLabel x.

That is an invariant label, not a dynamics-preserving projection.

For old labels, cutLabel x = Sum.inl f means “the cut dart x lies in the transported old face f.” Since a face label is already a quotient by phi, it is constant under old phi steps. Therefore it is reasonable and provable that it is also constant under the corresponding cut-face walk.

The old face may be represented by a very different set of darts after surgery. That is fine. The theorem counts orbit labels, not preserved orbit supports.

9. Why this handles the K4 torus evidence

In the K4 torus case, faceCorr2 may be one combined cycle threading both cap signs.

This proof never asks about:

lean
numCycles faceCorr2

or about any chain decomposition of faceCorr2.

It asks only:

lean
cutLabel (phi'2 x) = cutLabel x

and

lean
SameCycle phi'2 x (cutAnchor (cutLabel x)).

The first is a closed-form one-step check. The second is a closed-form orbit-trace check. Both are local to phi'2.

So even if faceCorr2 has one combined cycle, the actual face permutation phi'2 still has exactly one orbit per label in:

lean
OldFace(phi) ⊕ Side.

Hence:

lean
F' = F + 2

without any planarity or genus assumption.

10. Dependency-ordered Lean implementation plan
Layer 1: orbit and cycle-count API

You likely already have these, but the label theorem needs them cleanly.

lean
def SameCycle (p : Equiv.Perm X) (x y : X) : Prop := ...

Lemmas:

lean
sameCycle_refl :
  SameCycle p x x

sameCycle_symm :
  SameCycle p x y → SameCycle p y x

sameCycle_trans :
  SameCycle p x y → SameCycle p y z → SameCycle p x z

sameCycle_step :
  SameCycle p x (p x)

sameCycle_step_inv :
  SameCycle p x (p.symm x)

Also:

lean
OldFace := Quotient (SameCycle.setoid phi)

faceOf : D → OldFace
faceOf d := Quotient.mk _ d

faceOf_phi :
  faceOf (phi d) = faceOf d

oldFace_card_eq_numCycles :
  Fintype.card OldFace = numCycles phi
Layer 2: generic orbit-label count theorem

Define:

lean
structure OrbitLabelCert
    (X β : Type*) [Fintype X] [DecidableEq X]
    [Fintype β] [DecidableEq β]
    (q : Equiv.Perm X) where
  label : X → β
  anchor : β → X
  label_anchor :
    ∀ b, label (anchor b) = b
  label_invariant :
    ∀ x, label (q x) = label x
  same_anchor :
    ∀ x, SameCycle q x (anchor (label x))

Prove:

lean
lemma label_eq_of_sameCycle
    (C : OrbitLabelCert X β q)
    (h : SameCycle q x y) :
  C.label x = C.label y

Prove:

lean
lemma sameCycle_of_label_eq
    (C : OrbitLabelCert X β q)
    (h : C.label x = C.label y) :
  SameCycle q x y

Then:

lean
def orbitLabelEquiv
    (C : OrbitLabelCert X β q) :
  Quotient (SameCycle.setoid q) ≃ β

Finally:

lean
theorem numCycles_eq_card_of_orbitLabelCert
    (C : OrbitLabelCert X β q) :
  numCycles q = Fintype.card β

This layer is pure permutation theory.

Layer 3: define the cut face label type
lean
inductive Side
| plus
| minus
deriving DecidableEq, Fintype

abbrev CutFaceLabel :=
  OldFace(phi) ⊕ Side

Then:

lean
def cutLabel : Dcut → CutFaceLabel

Use the same classifier you use for the closed forms of phi'2.

Do not try to define it from faceCorr2.

Layer 4: define old-face lifts and anchors
lean
def oldFaceLift : D → Dcut

with:

lean
lemma cutLabel_oldFaceLift :
  ∀ d, cutLabel (oldFaceLift d) = Sum.inl (faceOf d)

Define:

lean
def plusCapAnchor : Dcut := ...
def minusCapAnchor : Dcut := ...

with:

lean
lemma cutLabel_plusCapAnchor :
  cutLabel plusCapAnchor = Sum.inr Side.plus

lemma cutLabel_minusCapAnchor :
  cutLabel minusCapAnchor = Sum.inr Side.minus

Define:

lean
noncomputable def oldFaceRep : OldFace(phi) → D :=
  Quotient.out

noncomputable def cutAnchor : CutFaceLabel → Dcut
| Sum.inl f => oldFaceLift (oldFaceRep f)
| Sum.inr Side.plus => plusCapAnchor
| Sum.inr Side.minus => minusCapAnchor

Prove:

lean
lemma cutLabel_anchor :
  ∀ b, cutLabel (cutAnchor b) = b
Layer 5: label invariance under phi'2

This is a direct closed-form proof.

lean
lemma cutLabel_phi'2 :
  ∀ x, cutLabel (phi'2 x) = cutLabel x := by
  intro x
  cases x using cutDartClosedFormCases
  all_goals
    simp [
      cutLabel,
      phi'2_apply_closed_form_1,
      phi'2_apply_closed_form_2,
      phi'2_apply_closed_form_3,
      faceOf_phi,
      index_simp
    ]

The exact closed-form lemmas are your existing per-class symbolic equations.

This is the local invariant.

Layer 6: old-face lift connectivity

First, one old phi step lifts to a phi'2 orbit path:

lean
lemma oldFaceLift_phi_step :
  ∀ d : D,
    SameCycle phi'2
      (oldFaceLift d)
      (oldFaceLift (phi d))

Proof by closed-form cases:

lean
lemma oldFaceLift_phi_step :
  ∀ d : D,
    SameCycle phi'2
      (oldFaceLift d)
      (oldFaceLift (phi d)) := by
  intro d
  cases d using oldDartClosedFormCases
  · exact sameCycle_of_apply_eq
      (by simp [oldFaceLift, phi'2_apply_closed_form])
  · exact sameCycle_path
      [by simp [phi'2_apply_closed_form_1],
       by simp [phi'2_apply_closed_form_2],
       by simp [phi'2_apply_closed_form_3]]
  · ...

Then extend to old face orbits:

lean
lemma oldFaceLift_same_old_face
    {d e : D}
    (h : SameCycle phi d e) :
  SameCycle phi'2 (oldFaceLift d) (oldFaceLift e) := by
  induction h with
  | refl =>
      exact sameCycle_refl
  | step h ih =>
      exact SameCycle.trans ih (oldFaceLift_phi_step _)
  | symm h ih =>
      exact SameCycle.symm ih
  | trans h1 h2 ih1 ih2 =>
      exact SameCycle.trans ih1 ih2

Adapt the induction shape to your SameCycle definition.

Then:

lean
lemma oldFaceLift_to_anchor
    (d : D) :
  SameCycle phi'2
    (oldFaceLift d)
    (cutAnchor (Sum.inl (faceOf d))) := by
  unfold cutAnchor oldFaceRep
  apply oldFaceLift_same_old_face
  exact sameCycle_quotient_out d

where:

lean
sameCycle_quotient_out :
  SameCycle phi d (Quotient.out (faceOf d))
Layer 7: every dart reaches the anchor of its label

Prove old-label darts reach their old lift:

lean
lemma cutDart_oldLabel_to_lift :
  ∀ x d,
    cutLabel x = Sum.inl (faceOf d) →
    SameCycle phi'2 x (oldFaceLift d)

Proof by closed-form cases on x.

For a dart whose label is an old face, the closed forms either identify it with the lift or give a bounded path to the lift. If the local representative is a different old dart e in the same old face, use:

lean
oldFaceLift_same_old_face :
  SameCycle phi e d → SameCycle phi'2 (oldFaceLift e) (oldFaceLift d)

For plus and minus labels:

lean
lemma plusLabel_to_anchor :
  ∀ x,
    cutLabel x = Sum.inr Side.plus →
    SameCycle phi'2 x plusCapAnchor
lean
lemma minusLabel_to_anchor :
  ∀ x,
    cutLabel x = Sum.inr Side.minus →
    SameCycle phi'2 x minusCapAnchor

Again, these are closed-form orbit traces under phi'2, not faceCorr2.

Then:

lean
lemma cut_same_anchor :
  ∀ x, SameCycle phi'2 x (cutAnchor (cutLabel x)) := by
  intro x
  cases h : cutLabel x with
  | inl f =>
      let d := oldFaceRep f
      have hf : faceOf d = f := by
        exact Quotient.out_eq f
      have hx : cutLabel x = Sum.inl (faceOf d) := by
        simpa [d, hf] using h
      exact SameCycle.trans
        (cutDart_oldLabel_to_lift x d hx)
        (oldFaceLift_to_anchor d)
  | inr s =>
      cases s
      · simpa [cutAnchor] using plusLabel_to_anchor x h
      · simpa [cutAnchor] using minusLabel_to_anchor x h
Layer 8: build the certificate
lean
def cutFaceLabelCert :
  OrbitLabelCert Dcut CutFaceLabel phi'2 where
  label := cutLabel
  anchor := cutAnchor
  label_anchor := cutLabel_anchor
  label_invariant := cutLabel_phi'2
  same_anchor := cut_same_anchor

Then:

lean
theorem numCycles_phi'2_eq_numCycles_phi_add_two :
  numCycles phi'2 = numCycles phi + 2 := by
  have h :=
    numCycles_eq_card_of_orbitLabelCert
      (q := phi'2)
      cutFaceLabelCert
  calc
    numCycles phi'2
        = Fintype.card CutFaceLabel := h
    _   = Fintype.card (OldFace(phi) ⊕ Side) := rfl
    _   = Fintype.card (OldFace(phi)) + Fintype.card Side := by
            simp
    _   = numCycles phi + 2 := by
            simp [oldFace_card_eq_numCycles, Side]

Finally:

lean
theorem F'_eq_F_add_two :
  F' = F + 2 := by
  unfold F' F
  exact numCycles_phi'2_eq_numCycles_phi_add_two
11. Candidate-route assessment
A. Local induction on k

This can work, but it creates unnecessary intermediate maps that are not natural cut-cap maps. You would have to design partial surgeries, prove their permutations are valid combinatorial maps, and prove a delta theorem for each partial operation. That is a lot of infrastructure for a count that can be read directly from phi'2.

B. Orbit-label bijection

This is the route that closes cleanly.

It uses exactly the data you have: closed forms for phi'2.

It does not require:

lean
faceCorr2

to have any stable cycle structure.

It does not require:

lean
phi'2

to semiconjugate to phi.

It proves directly:

lean
Orbits(phi'2) ≃ Orbits(phi) ⊕ Side.
C. Euler via components/genus

Skip. It imports genus theory or an equivalent Euler-characteristic classification theorem.

D. Face-degree double count

Insufficient alone. Degree sums do not determine the number of cycles.

E. Conservation law for transposition walks

There may be such a law, but it would effectively reconstruct the same orbit-label invariant in a less direct language. The kernel evidence says the adaptive same/different-cycle statuses vary with genus and map structure. The stable object is not the faceCorr2 transposition walk; it is the phi'2 orbit labeling.

12. Final theorem shape for the chapter

The chapter-facing theorem should not mention faceCorr2 chains.

Use:

lean
theorem cutCapMap2_numFaces
    (M : CombMap)
    (C : SimplePrimalCycle M)
    (hcut : cutCapMap2 M C = M') :
  numFaces M' = numFaces M + 2

and internally prove:

lean
phi'2_orbit_label_equiv :
  Quotient (SameCycle.setoid phi'2)
    ≃
  Quotient (SameCycle.setoid phi) ⊕ Side

Then the count is immediate by cardinality.

The invariant to remember is:

lean
cutLabel : Dcut → OldFace(phi) ⊕ Side

with:

lean
cutLabel (phi'2 x) = cutLabel x

and:

lean
∀ x, SameCycle phi'2 x (cutAnchor (cutLabel x)).

Those two facts say exactly:

lean
phi'2-orbits are the fibers of cutLabel.

Since the label type has F + 2 elements, the face count is:

lean
F' = F + 2.

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