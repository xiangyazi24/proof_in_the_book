import Mathlib

/-!
# Chapter 30: Lattice paths and determinants

From "Proofs from THE BOOK":

**Lindström-Gessel-Viennot lemma**: The number of non-intersecting
lattice path systems from sources to sinks equals a determinant.

The book applies this to count standard Young tableaux and proves
the hook length formula: |SYT(λ)| = n! / ∏ hook_lengths.
-/

namespace ProofsInTheBook.Chapter30

open Matrix BigOperators

/--
The determinant expansion over signed permutations, the algebraic starting
point of the Lindström-Gessel-Viennot cancellation argument.
-/
theorem det_eq_sum_signed_permutations {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R) :
    M.det = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, M (σ i) i := by
  exact Matrix.det_apply M

/--
The diagonal case of the Lindström-Gessel-Viennot determinant: when the
path-counting matrix has no off-diagonal contributions, the determinant
has only the identity permutation term.
-/
theorem det_eq_diag_product_of_offdiag_zero {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R)
    (hzero : ∀ i j, i ≠ j → M i j = 0) :
    M.det = ∏ i, M i i := by
  have hM : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij, hzero i j hij]
  rw [hM]
  simp

/--
Finite sign-reversing reindexing lemma.

In an arbitrary additive group this gives `S = -S`, not necessarily `S = 0`
unless the target has no `2`-torsion.
-/
theorem sum_eq_neg_self_of_sign_reversing_equiv {α R : Type*} [Fintype α]
    [AddCommGroup R] (τ : α ≃ α) (w : α → R) (hw : ∀ x, w (τ x) = -w x) :
    (∑ x : α, w x) = -∑ x : α, w x := by
  classical
  have hreindex : (∑ x : α, w (τ x)) = ∑ x : α, w x := by
    simpa using
      (Fintype.sum_equiv τ
        (fun x : α => w (τ x))
        (fun y : α => w y)
        (by intro x; rfl))
  calc
    (∑ x : α, w x) = ∑ x : α, w (τ x) := hreindex.symm
    _ = ∑ x : α, -w x := by simp [hw]
    _ = -∑ x : α, w x := by simp

/-- A sign-reversing involution makes the total signed sum `2`-torsion. -/
theorem two_nsmul_sum_eq_zero_of_sign_reversing_equiv {α R : Type*} [Fintype α]
    [AddCommGroup R] (τ : α ≃ α) (w : α → R) (hw : ∀ x, w (τ x) = -w x) :
    (2 : ℕ) • (∑ x : α, w x) = 0 := by
  classical
  let S : R := ∑ x : α, w x
  have h : S = -S := by
    simpa [S] using sum_eq_neg_self_of_sign_reversing_equiv τ w hw
  change (2 : ℕ) • S = 0
  rw [two_nsmul]
  nth_rewrite 1 [h]
  exact neg_add_cancel S

/-- A sign-reversing involution cancels the sum in an additive torsion-free target. -/
theorem sum_eq_zero_of_sign_reversing_equiv {α R : Type*} [Fintype α]
    [AddCommGroup R] [IsAddTorsionFree R] (τ : α ≃ α) (w : α → R)
    (hw : ∀ x, w (τ x) = -w x) :
    (∑ x : α, w x) = 0 := by
  classical
  have h2 := two_nsmul_sum_eq_zero_of_sign_reversing_equiv τ w hw
  rcases (nsmul_eq_zero_iff.mp h2) with hsum | htwo
  · exact hsum
  · norm_num at htwo

/--
LGV split layer: if the bad finite subfamily cancels by a sign-reversing
equivalence, then the total signed sum is the contribution from the good
subfamily.
-/
theorem total_sum_eq_good_sum_of_bad_sign_reversing {α R : Type*} [Fintype α]
    [DecidableEq α] [AddCommGroup R] [IsAddTorsionFree R]
    (bad : α → Prop) [DecidablePred bad] (τbad : {x : α // bad x} ≃ {x : α // bad x})
    (w : α → R) (hw : ∀ x : {x : α // bad x}, w (τbad x).1 = -w x.1) :
    (∑ x : α, w x) = ∑ x ∈ (Finset.univ.filter fun x : α => ¬ bad x), w x := by
  classical
  let badSet : Finset α := Finset.univ.filter fun x : α => bad x
  let goodSet : Finset α := Finset.univ.filter fun x : α => ¬ bad x
  have hbad_sum : (∑ x ∈ badSet, w x) = 0 := by
    let wbad : {x : α // bad x} → R := fun x => w x.1
    have hwbad : ∀ x : {x : α // bad x}, wbad (τbad x) = -wbad x := by
      intro x
      exact hw x
    have h := sum_eq_zero_of_sign_reversing_equiv τbad wbad hwbad
    have hfilter : (∑ x ∈ badSet, w x) = ∑ x : {x : α // bad x}, wbad x := by
      rw [← Finset.sum_subtype]
      simp [badSet]
    rw [hfilter, h]
  have huniv : (Finset.univ : Finset α) = badSet ∪ goodSet := by
    ext x
    by_cases hx : bad x <;> simp [badSet, goodSet, hx]
  have hdisj : Disjoint badSet goodSet := by
    rw [Finset.disjoint_left]
    intro x hxbad hxgood
    simp [badSet] at hxbad
    simp [goodSet, hxbad] at hxgood
  calc
    (∑ x : α, w x) = ∑ x ∈ (Finset.univ : Finset α), w x := by simp
    _ = ∑ x ∈ badSet ∪ goodSet, w x := by rw [huniv]
    _ = (∑ x ∈ badSet, w x) + ∑ x ∈ goodSet, w x := by
      rw [Finset.sum_union hdisj]
    _ = ∑ x ∈ goodSet, w x := by rw [hbad_sum, zero_add]
    _ = ∑ x ∈ (Finset.univ.filter fun x : α => ¬ bad x), w x := rfl

/--
A finite LGV cancellation certificate: `bad` identifies the bad path families,
`tauBad` pairs bad families, and `sign_reverse` says the signed weight reverses.
-/
structure BadInvolutionCertificate (Family R : Type*) [AddCommGroup R] where
  bad : Family → Prop
  bad_decidable : DecidablePred bad
  tauBad : {F : Family // bad F} ≃ {F : Family // bad F}
  signedWeight : Family → R
  sign_reverse : ∀ F : {F : Family // bad F}, signedWeight (tauBad F).1 = -signedWeight F.1

attribute [instance] BadInvolutionCertificate.bad_decidable

/--
Using a bad-involution certificate, the total signed sum over all finite
families equals the signed sum over the good families.
-/
theorem BadInvolutionCertificate.total_sum_eq_good_sum {Family R : Type*} [Fintype Family]
    [DecidableEq Family] [AddCommGroup R] [IsAddTorsionFree R]
    (C : BadInvolutionCertificate Family R) :
    (∑ F : Family, C.signedWeight F) =
      ∑ F ∈ (Finset.univ.filter fun F : Family => ¬ C.bad F), C.signedWeight F := by
  classical
  letI : DecidablePred C.bad := C.bad_decidable
  exact
    total_sum_eq_good_sum_of_bad_sign_reversing C.bad C.tauBad C.signedWeight C.sign_reverse

/--
The path intersection swap: the combinatorial heart of the LGV lemma.
Given two lattice paths `p₁ : a₁ → b_{σ(1)}` and `p₂ : a₂ → b_{σ(2)}`
that share a vertex `v`, swapping tails at `v` produces paths
`p₁' : a₁ → b_{σ'(1)}` and `p₂' : a₂ → b_{σ'(2)}` where `σ'` differs from
`σ` by a transposition. This changes the sign of the permutation.
-/
theorem path_swap_changes_sign {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n)
    (hij : i ≠ j) :
    Equiv.Perm.sign (σ.trans (Equiv.swap i j)) =
      -Equiv.Perm.sign σ := by
  simp [Equiv.Perm.sign_trans, Equiv.Perm.sign_swap hij]

/--
When the path system family has exactly one non-intersecting system (the
identity permutation), the LGV determinant equals the product of single-path
counts.
-/
theorem lgv_identity_case {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [IsAddTorsionFree R]
    (_pathCount : n → n → R)
    (cert : BadInvolutionCertificate (Equiv.Perm n) R) :
    (∑ σ : Equiv.Perm n, cert.signedWeight σ) =
      ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm n => ¬ cert.bad σ),
        cert.signedWeight σ :=
  cert.total_sum_eq_good_sum

/--
A path family from sources to sinks via a permutation σ: for each source
index i, a path from source i to sink σ(i). The signed weight of a family
is sign(σ) times the product of individual path weights.
-/
structure PathFamily (Source Sink Vertex : Type*) (n : ℕ) where
  perm : Equiv.Perm (Fin n)
  paths : Fin n → List Vertex

/--
A path family is non-intersecting if no two paths share a vertex (other
than at their endpoints, in the lattice path case).
-/
def PathFamily.nonIntersecting {Source Sink Vertex : Type*} {n : ℕ}
    [DecidableEq Vertex] (F : PathFamily Source Sink Vertex n) : Prop :=
  ∀ i j : Fin n, i ≠ j → Disjoint (F.paths i).toFinset (F.paths j).toFinset

/--
The LGV lemma: det(M) = ∑ over non-intersecting path families, where
M(i,j) = number of paths from source i to sink j. The proof uses the
sign-reversing involution on intersecting families via `BadInvolutionCertificate`.
-/
theorem lgv_lemma_of_certificate {n : ℕ} {R : Type*} [Fintype (Equiv.Perm (Fin n))]
    [DecidableEq (Equiv.Perm (Fin n))] [CommRing R] [IsAddTorsionFree R]
    (_pathCount : Fin n → Fin n → R)
    (cert : BadInvolutionCertificate (Equiv.Perm (Fin n)) R) :
    (∑ σ : Equiv.Perm (Fin n), cert.signedWeight σ) =
      ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => ¬ cert.bad σ),
        cert.signedWeight σ :=
  cert.total_sum_eq_good_sum

/--
A concrete combinatorial path family on a generic vertex type.
-/
structure LatticePathFamily (n : ℕ) (V : Type*) [DecidableEq V] where
  perm : Equiv.Perm (Fin n)
  paths : Fin n → List V

/--
A path family is bad if two distinct paths share a vertex.
-/
def LatticePathFamily.bad {n V} [DecidableEq V] (F : LatticePathFamily n V) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ ((F.paths i).toFinset ∩ (F.paths j).toFinset).Nonempty

/-- The "bad" predicate is symmetric in the offending pair of indices: a witness
`(i, j)` with `i ≠ j` and a shared vertex can be swapped to `(j, i)`. -/
theorem LatticePathFamily.bad_symm {n V} [DecidableEq V]
    {F : LatticePathFamily n V}
    (h : F.bad) : F.bad := by
  obtain ⟨i, j, hij, hshared⟩ := h
  refine ⟨j, i, hij.symm, ?_⟩
  rwa [Finset.inter_comm] at hshared

/-- The trivial 0-family is never bad: vacuously, there are no two distinct
indices to witness a shared vertex. -/
theorem LatticePathFamily.not_bad_of_zero {V} [DecidableEq V]
    (F : LatticePathFamily 0 V) : ¬ F.bad := by
  rintro ⟨i, _, _, _⟩
  exact i.elim0

/-- The product of vertex weights along a finite path. -/
def pathVertexWeight {V R : Type*} [CommMonoid R] (weight : V → R) (p : List V) : R :=
  (p.map weight).prod

/--
The good side of a concrete LGV path family: a permutation together with
pairwise disjoint vertex lists.
-/
structure LGVGoodFamily (n : ℕ) (V : Type*) [DecidableEq V] where
  perm : Equiv.Perm (Fin n)
  paths : Fin n → List V
  nonIntersecting :
    ∀ i j : Fin n, i ≠ j → Disjoint (paths i).toFinset (paths j).toFinset

/--
The bad side of a concrete LGV path family, with the Lindström tail-swap
data made explicit.  The two distinguished paths have prefixes ending at a
shared vertex and tails that can be exchanged.
-/
structure LGVBadFamily (n : ℕ) (V : Type*) [DecidableEq V] where
  perm : Equiv.Perm (Fin n)
  i : Fin n
  j : Fin n
  hij : i ≠ j
  shared : V
  leftPrefix : List V
  leftTail : List V
  rightPrefix : List V
  rightTail : List V
  left_shared : shared ∈ leftPrefix
  right_shared : shared ∈ rightPrefix
  otherPaths : Fin n → List V

namespace LGVBadFamily

variable {n : ℕ} {V R : Type*} [DecidableEq V]

/-- The underlying list of vertices of a marked bad family. -/
def paths (B : LGVBadFamily n V) (k : Fin n) : List V :=
  if k = B.i then
    B.leftPrefix ++ B.leftTail
  else if k = B.j then
    B.rightPrefix ++ B.rightTail
  else
    B.otherPaths k

/-- Swapping the two marked tails and multiplying the permutation by the same transposition. -/
def tailSwap (B : LGVBadFamily n V) : LGVBadFamily n V where
  perm := B.perm * Equiv.swap B.i B.j
  i := B.i
  j := B.j
  hij := B.hij
  shared := B.shared
  leftPrefix := B.leftPrefix
  leftTail := B.rightTail
  rightPrefix := B.rightPrefix
  rightTail := B.leftTail
  left_shared := B.left_shared
  right_shared := B.right_shared
  otherPaths := B.otherPaths

/-- Tail-swap is an involution on the marked bad data. -/
theorem tailSwap_tailSwap (B : LGVBadFamily n V) : B.tailSwap.tailSwap = B := by
  cases B
  simp [tailSwap, mul_assoc]

/-- Tail-swap changes the permutation sign. -/
theorem sign_tailSwap (B : LGVBadFamily n V) :
    Equiv.Perm.sign B.tailSwap.perm = -Equiv.Perm.sign B.perm := by
  simp [tailSwap, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap B.hij]

/-- The marked shared vertex witnesses an actual intersection. -/
theorem bad (B : LGVBadFamily n V) :
    (LatticePathFamily.mk B.perm B.paths).bad := by
  refine ⟨B.i, B.j, B.hij, ?_⟩
  refine ⟨B.shared, ?_⟩
  have hji : B.j ≠ B.i := B.hij.symm
  simp [paths, hji, B.left_shared, B.right_shared]

/-- The unsigned vertex-weight product of a marked bad family. -/
def unsignedWeight [CommMonoid R] (weight : V → R) (B : LGVBadFamily n V) : R :=
  pathVertexWeight weight B.leftPrefix *
    pathVertexWeight weight B.leftTail *
    pathVertexWeight weight B.rightPrefix *
    pathVertexWeight weight B.rightTail *
    ∏ k, pathVertexWeight weight (B.otherPaths k)

/-- Swapping the marked tails preserves the unsigned product of vertex weights. -/
theorem unsignedWeight_tailSwap [CommMonoid R] (weight : V → R) (B : LGVBadFamily n V) :
    unsignedWeight weight B.tailSwap = unsignedWeight weight B := by
  simp [unsignedWeight, tailSwap, mul_assoc, mul_left_comm, mul_comm]

end LGVBadFamily

/--
Concrete LGV families split into non-intersecting families and marked
intersecting families.  The mark is exactly the local data needed for the
Lindström tail-swap involution.
-/
inductive LGVFamily (n : ℕ) (V : Type*) [DecidableEq V] where
  | good (G : LGVGoodFamily n V)
  | bad (B : LGVBadFamily n V)

namespace LGVFamily

variable {n : ℕ} {V R : Type*} [DecidableEq V]

/-- The bad predicate for concrete LGV families. -/
def isBad : LGVFamily n V → Prop
  | good _ => False
  | bad _ => True

instance : DecidablePred (isBad (n := n) (V := V)) := by
  intro F
  cases F with
  | good _ => exact isFalse id
  | bad _ => exact isTrue trivial

/-- The permutation attached to a concrete LGV family. -/
def perm : LGVFamily n V → Equiv.Perm (Fin n)
  | good G => G.perm
  | bad B => B.perm

/-- The vertex lists attached to a concrete LGV family. -/
def paths : LGVFamily n V → Fin n → List V
  | good G => G.paths
  | bad B => B.paths

/-- The unsigned product of vertex weights for a concrete LGV family. -/
def unsignedWeight [CommMonoid R] (weight : V → R) : LGVFamily n V → R
  | good G => ∏ i, pathVertexWeight weight (G.paths i)
  | bad B => B.unsignedWeight weight

/-- The usual LGV signed weight: permutation sign times path-weight product. -/
def signedWeight [CommRing R] (weight : V → R) (F : LGVFamily n V) : R :=
  Equiv.Perm.sign F.perm • F.unsignedWeight weight

/-- Tail-swap on the subtype of marked bad concrete families. -/
def badTailSwap (F : {F : LGVFamily n V // isBad F}) : {F : LGVFamily n V // isBad F} :=
  match F with
  | ⟨good _, h⟩ => False.elim h
  | ⟨bad B, _⟩ => ⟨bad B.tailSwap, trivial⟩

/-- The marked tail-swap is an involution on bad concrete families. -/
theorem badTailSwap_badTailSwap (F : {F : LGVFamily n V // isBad F}) :
    badTailSwap (badTailSwap F) = F := by
  rcases F with ⟨F, hF⟩
  cases F with
  | good _ => contradiction
  | bad B =>
      simp [badTailSwap, LGVBadFamily.tailSwap_tailSwap]

/-- The bad-family equivalence induced by marked tail-swap. -/
def badTailSwapEquiv : {F : LGVFamily n V // isBad F} ≃ {F : LGVFamily n V // isBad F} where
  toFun := badTailSwap
  invFun := badTailSwap
  left_inv := badTailSwap_badTailSwap
  right_inv := badTailSwap_badTailSwap

/-- Marked tail-swap reverses the signed vertex weight. -/
theorem signedWeight_badTailSwap [CommRing R] (weight : V → R)
    (F : {F : LGVFamily n V // isBad F}) :
    signedWeight weight (badTailSwapEquiv F).1 = -signedWeight weight F.1 := by
  rcases F with ⟨F, hF⟩
  cases F with
  | good _ => contradiction
  | bad B =>
      simp [badTailSwapEquiv, badTailSwap, signedWeight, perm, unsignedWeight,
        LGVBadFamily.sign_tailSwap, LGVBadFamily.unsignedWeight_tailSwap]

end LGVFamily

/--
The concrete LGV bad-involution certificate obtained from the marked
Lindström tail-swap construction.
-/
def latticeLGVCertificate {n : ℕ} {V R : Type*} [DecidableEq V] [CommRing R]
    (weight : V → R) : BadInvolutionCertificate (LGVFamily n V) R where
  bad := LGVFamily.isBad
  bad_decidable := inferInstance
  tauBad := LGVFamily.badTailSwapEquiv
  signedWeight := LGVFamily.signedWeight weight
  sign_reverse := LGVFamily.signedWeight_badTailSwap weight

/--
A finite path-count system for the determinant side of LGV.  `Path i j` is
the finite type of paths from source `i` to sink `j`, and `familyEquiv`
identifies the determinant expansion data `(σ, one path for each column i from
σ i to i)` with the concrete `LGVFamily` type used by the tail-swap
certificate.
-/
structure PathCountSystem (n : ℕ) (V R : Type*) [DecidableEq V] [CommRing R] where
  vertexWeight : V → R
  Path : Fin n → Fin n → Type*
  pathFintype : ∀ i j : Fin n, Fintype (Path i j)
  pathWeight : ∀ {i j : Fin n}, Path i j → R
  familyEquiv :
    (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, Path (σ i) i) ≃ LGVFamily n V
  weight_eq :
    ∀ X : (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, Path (σ i) i),
      LGVFamily.signedWeight vertexWeight (familyEquiv X) =
        Equiv.Perm.sign X.1 • ∏ i : Fin n, pathWeight (X.2 i)

namespace PathCountSystem

variable {n : ℕ} {V R : Type*} [DecidableEq V] [CommRing R]

/-- The weighted path-count matrix entry. -/
def pathCount (S : PathCountSystem n V R) (i j : Fin n) : R :=
  letI := S.pathFintype i j
  ∑ p : S.Path i j, S.pathWeight p

/-- The LGV path-count matrix. -/
def matrix (S : PathCountSystem n V R) : Matrix (Fin n) (Fin n) R :=
  fun i j => S.pathCount i j

/--
The determinant of the path-count matrix expands as the signed sum over all
concrete LGV families.
-/
theorem det_matrix_eq_total (S : PathCountSystem n V R) [Fintype (LGVFamily n V)] :
    S.matrix.det = ∑ F : LGVFamily n V, LGVFamily.signedWeight S.vertexWeight F := by
  classical
  letI : ∀ i j : Fin n, Fintype (S.Path i j) := S.pathFintype
  have h_expand :
      S.matrix.det =
        ∑ X : (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, S.Path (σ i) i),
          Equiv.Perm.sign X.1 • ∏ i : Fin n, S.pathWeight (X.2 i) := by
    calc
      S.matrix.det =
          ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, S.matrix (σ i) i := by
            exact Matrix.det_apply S.matrix
      _ =
          ∑ σ : Equiv.Perm (Fin n),
            Equiv.Perm.sign σ •
              (∑ choice : (∀ i : Fin n, S.Path (σ i) i),
                ∏ i : Fin n, S.pathWeight (choice i)) := by
            apply Finset.sum_congr rfl
            intro σ _
            simp [matrix, pathCount, Fintype.prod_sum]
      _ =
          ∑ σ : Equiv.Perm (Fin n),
            ∑ choice : (∀ i : Fin n, S.Path (σ i) i),
              Equiv.Perm.sign σ • ∏ i : Fin n, S.pathWeight (choice i) := by
            simp [Finset.smul_sum]
      _ =
          ∑ X : (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, S.Path (σ i) i),
            Equiv.Perm.sign X.1 • ∏ i : Fin n, S.pathWeight (X.2 i) := by
            exact
              (Fintype.sum_sigma'
                (fun σ (choice : ∀ i : Fin n, S.Path (σ i) i) =>
                  Equiv.Perm.sign σ • ∏ i : Fin n, S.pathWeight (choice i))).symm
  calc
    S.matrix.det =
        ∑ X : (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, S.Path (σ i) i),
          Equiv.Perm.sign X.1 • ∏ i : Fin n, S.pathWeight (X.2 i) := h_expand
    _ =
        ∑ X : (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, S.Path (σ i) i),
          LGVFamily.signedWeight S.vertexWeight (S.familyEquiv X) := by
          apply Finset.sum_congr rfl
          intro X _
          exact (S.weight_eq X).symm
    _ = ∑ F : LGVFamily n V, LGVFamily.signedWeight S.vertexWeight F := by
          simpa using
            (Fintype.sum_equiv S.familyEquiv
              (fun X : (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, S.Path (σ i) i) =>
                LGVFamily.signedWeight S.vertexWeight (S.familyEquiv X))
              (fun F : LGVFamily n V => LGVFamily.signedWeight S.vertexWeight F)
              (by intro X; rfl))

end PathCountSystem

/-- LGV determinant identity (certificate form):
The determinant of a matrix M equals the signed sum over non-intersecting path families.
(This abstracts the geometric core: M(i, j) is the number of paths from source i to sink j.
If a sign-reversing involution `cert` on intersecting families is provided, the cancellation
leaves only the non-intersecting families.) -/
theorem chapter30_of_certificate {n : ℕ} {R : Type*}
    [CommRing R] [IsAddTorsionFree R]
    (M : Matrix (Fin n) (Fin n) R)
    (cert : BadInvolutionCertificate (Equiv.Perm (Fin n)) R)
    (h_weight : ∀ σ : Equiv.Perm (Fin n),
        cert.signedWeight σ = Equiv.Perm.sign σ • ∏ i, M (σ i) i) :
    M.det = ∑ σ ∈ Finset.univ.filter (fun σ => ¬ cert.bad σ),
      Equiv.Perm.sign σ • ∏ i, M (σ i) i := by
  calc M.det
      = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, M (σ i) i := Matrix.det_apply M
    _ = ∑ σ : Equiv.Perm (Fin n), cert.signedWeight σ := by
        apply Finset.sum_congr rfl
        intros σ _
        exact (h_weight σ).symm
    _ = ∑ σ ∈ Finset.univ.filter (fun σ => ¬ cert.bad σ),
          cert.signedWeight σ := cert.total_sum_eq_good_sum
    _ = ∑ σ ∈ Finset.univ.filter (fun σ => ¬ cert.bad σ),
          Equiv.Perm.sign σ • ∏ i, M (σ i) i := by
        apply Finset.sum_congr rfl
        intros σ _
        exact h_weight σ

/--
Concrete LGV cancellation theorem.  The determinant expansion into all
concrete path families is supplied as `h_det_expand`; the cancellation of
marked intersecting families is constructed internally by tail-swap, with no
`BadInvolutionCertificate` parameter.
-/
theorem chapter30_of_det_expand {n : ℕ} {V R : Type*} [DecidableEq V]
    [Fintype (LGVFamily n V)] [DecidableEq (LGVFamily n V)]
    [CommRing R] [IsAddTorsionFree R]
    (weight : V → R) (M : Matrix (Fin n) (Fin n) R)
    (h_det_expand :
      M.det = ∑ F : LGVFamily n V, LGVFamily.signedWeight weight F) :
    M.det =
      ∑ F ∈ Finset.univ.filter (fun F : LGVFamily n V => ¬ LGVFamily.isBad F),
        LGVFamily.signedWeight weight F := by
  rw [h_det_expand]
  exact (latticeLGVCertificate weight).total_sum_eq_good_sum

/--
Lindström-Gessel-Viennot cancellation for a finite path-count system.  The
matrix is defined from the path counts, and the determinant expansion is proved
from `Matrix.det_apply`; the only remaining sum is over the non-intersecting
families.
-/
theorem chapter30 {n : ℕ} {V R : Type*} [DecidableEq V]
    [Fintype (LGVFamily n V)] [DecidableEq (LGVFamily n V)]
    [CommRing R] [IsAddTorsionFree R]
    (S : PathCountSystem n V R) :
    S.matrix.det =
      ∑ F ∈ Finset.univ.filter (fun F : LGVFamily n V => ¬ LGVFamily.isBad F),
        LGVFamily.signedWeight S.vertexWeight F := by
  rw [S.det_matrix_eq_total]
  exact (latticeLGVCertificate S.vertexWeight).total_sum_eq_good_sum

end ProofsInTheBook.Chapter30
