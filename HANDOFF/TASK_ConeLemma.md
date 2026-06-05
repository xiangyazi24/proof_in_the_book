# TASK: ConeLemma.lean — the Ch09 cone lemma (queued; dispatch when a codex slot frees)

Create ProofsInTheBook/ConeLemma.lean (you own ONLY this file). Prove the book ch9 Cone Lemma:

theorem cone_lemma {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℚ)
    (x : Fin N → ℝ)
    (hsol : (A.map ((↑) : ℚ → ℝ)).mulVec x = 0)
    (hpos : ∀ j, 0 < x j) :
    ∃ z : Fin N → ℤ, (∀ j, 0 < z j) ∧ A.mulVec (fun j => (z j : ℚ)) = 0

Design (HANDOFF/CH09_PEARL_ROUTE.md): (a) rational kernel dense in real kernel for rational A —
NOTE Mathlib has NO Matrix.rank field-map invariance lemma (checked); choose between
(i) Module.Flat.ker_lTensor_eq (RingTheory/Flat/Equalizer.lean) + TensorProduct pi-equivalences,
(ii) proving rank invariance yourself via det-of-submatrix characterization + RingHom.map_det,
(iii) a direct argument: extend a ℚ-basis of ker(A_ℚ) to ℝ-independent set and dimension-count
via rank-nullity (Matrix.rank_eq... + LinearMap.finrank_range_add_finrank_ker).
(b) approximate the real coordinates in the rational-kernel basis expansion of x by rationals
(positivity is an open condition; use sup-norm continuity). (c) clear denominators
(common multiple of the q j denominators) for the integer point.
No sorry/axiom. lake env lean ProofsInTheBook/ConeLemma.lean. Append HANDOFF/outbox/conelemma-reply.md.
