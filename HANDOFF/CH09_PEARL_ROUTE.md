# CH09 PEARL/CONE ROUTE — design note (book ch9 verbatim: HANDOFF/BOOK_CH09_HILBERT3.txt)

The book proof (Kagan/Benko modernization) has three layers:
  1. CONE LEMMA (pure linear algebra, NO geometry): an integer/rational homogeneous linear
     system with a positive REAL solution has a positive INTEGER solution.
  2. PEARL LEMMA: in equidecompositions P = ⋃Pi, Q = ⋃Qi, assign positive integers to the
     SEGMENTS so corresponding edges of Pi/Qi carry equal pearl counts. Proof: the constraint
     system is rational-homogeneous and the real segment LENGTHS solve it; apply 1.
     (For equicomplementability: same with extra balance constraints — the proof allows them.)
  3. BRICARD'S CONDITION via the Σ-double-count of dihedral angles at pearls (the geometric
     bookkeeping: pearl in edge of P → interior angle α_j; in facet interior → π; interior of
     P → 2π or π). Then the examples (cube vs T0/T1/T2) via the PROVEN arccos irrationality.

## Step 1 Lean spec (self-contained brick, dispatch when a codex slot frees)
File: ProofsInTheBook/ConeLemma.lean (new, single writer)
  theorem cone_lemma {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℚ)
      (x : Fin N → ℝ) (hsol : (A.map (Rat.cast : ℚ → ℝ)).mulVec x = 0)
      (hpos : ∀ j, 0 < x j) :
      ∃ z : Fin N → ℤ, (∀ j, 0 < z j) ∧ (A.map (Int.cast ∘ ... )).mulVec ... = 0
  (state the conclusion over ℚ via (z j : ℚ) to dodge cast noise; integerize by common
   denominator of a rational solution.)
Design (NOT the book's Fourier-Motzkin — a cleaner density route):
  (a) Rational kernel is dense in real kernel for rational A. Tools, in preference order:
      - Module.Flat.ker_lTensor_eq (RingTheory/Flat/Equalizer.lean) with ℝ flat over ℚ
        (free → flat), transferring along TensorProduct.piScalarRight / finite-pi equivalences;
      - or rank/dimension count: ℚ-basis b₁..b_k of ker(A_ℚ) stays independent over ℝ and
        spans ker(A_ℝ) (dim = N − rank, rank preserved under field map — if a ready rank-map
        lemma is missing, prove spanning directly via the flat-base-change kernel identity).
  (b) x = Σ c_i b_i (c_i real); pick rationals q_i close to c_i; q = Σ q_i b_i is a rational
      kernel point, sup-close to x, hence still componentwise positive (x's positivity is open).
  (c) multiply by the common denominator → positive integer solution.
Acceptance: 0 sorry, lake env lean clean, #print axioms ⊆ {propext, Classical.choice, Quot.sound}.

## Step 2-3 (heavier geometry — design with pbook AFTER ch35 round)
Substrate decisions to iterate before any dispatch:
  - decomposition := finite family of convex polytopes with pairwise disjoint interiors whose
    union is P (Mathlib `Equidecomp` in MeasureTheory is about measurable equidecomposability —
    NOT the polytope notion; check what Chapter09 already uses for the arithmetic obstruction).
  - segments: the 1-skeleton refinement — the hard formalization object (interior points of a
    segment belong to a fixed set of piece-edges). Consider replacing pointwise "segments" by
    the abstract finite incidence data the Σ-argument needs (edge of piece → its dihedral angle;
    a pearl assignment is any positive integer weighting satisfying the matching constraints) —
    the Bricard double count only consumes: (i) each piece-edge's angle, (ii) the grouping of
    collinear segment-pieces into P-edges/facet-lines/interior-lines with angle sums α_j/π/2π·π.
    A faithful axiom-free version still needs the geometric realization of (ii) — this is THE
    wall; bring it to ChatGPT with the explicit question of the weakest geometric lemmas needed.
