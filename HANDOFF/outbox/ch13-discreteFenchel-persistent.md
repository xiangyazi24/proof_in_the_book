# Discrete Fenchel core — persistent session notes (UPDATED)

GOAL: `discreteFenchelCore_holds : ZinanFFCT106.DiscreteFenchelCore` (last Ch13 residue).
Edit ONLY `ProofsInTheBook/ZinanFFCT108.lean`. NO sorry/axiom/admit/native_decide.

## CURRENT STATE (committed 501662a, builds clean 8556 jobs, clean-3 axioms)
FFCT108 now contains the COMPLETE verified analytic core of discrete Fenchel via the
**suffix argument-lift**, reduced to ONE clean geometric non-degeneracy residue.

Key theorem: `core_of_nondeg (premises) (hnd : nondeg) : θ(n-1)-θ0 < 2π`  (STRICT, open+closed cases).
Wrapper: `discreteFenchelCore_of_nondeg (h : DiscreteFenchelNondeg) : DiscreteFenchelCore`.

VERIFIED machinery (all clean-3, no sorry):
- `cone_arg` : arg(ρ + r·e^{iφ}) ∈ [0,φ] for ρ,r≥0, φ∈(0,π].  THE WORKHORSE.
- `edge/chord/wrot/aang` defs; `chord_succ`, `chord_last`, `chord_last_ne`, `norm_wrot`, `chord_polar`.
- `im_rot_chord` : Im(exp(-θa I)·chord) = ∑ ρ_i sin(θ_i-θ_a)  [forward support bridge]
- `im_end_chord` : Im(exp(-θ(n-1) I)·chord_j) = -‖chord_j‖·sin(b_j)  [backward support bridge]
- `wrot_succ` : wrot(j) = ρ_j + ‖chord(j+1)‖·exp((δ_j+a_{j+1})I)
- `step` : the inductive step — given H(j+1) with b_{j+1}<π strict, forward+backward supports,
  chord(j)≠0, chord(j+1)≠0, produces H(j): a_j∈[0,π], a_j≤Δ_j, b_j≤π, a_j≤δ_j+a_{j+1}, δ_j+a_{j+1}≤π.
  Corner b_j=2π excluded because b_j≤b_{j+1}+π and b_{j+1}<π ⟹ b_j<2π.
- `aux_inv` : downward induction (on d, k+d=n-1) establishing H(k) for 1≤k≤n-1, GIVEN the residue
  (which supplies chord(k)≠0 and b_k≠π, the latter upgrading step's b_k≤π to b_k<π for chaining).
- `core_of_nondeg` : open case via step at j=0 (+ strict: a_0=b_0=π ⟹ φ_0=π ⟹ b_1=π contra residue);
  closed case s_0=0 via chord(1)=-e_0, a_1=π-δ_0, b_1=T-π<π.

## THE RESIDUE (the ONLY remaining gap)  — `DiscreteFenchelNondeg`
For 1≤k≤n-1:  `chord θ ρ n k ≠ 0`  AND  `(θ(n-1)-θ k) - aang θ ρ n k ≠ π`.
i.e. (A) no proper suffix sub-arc closes (V_n ≠ V_k); (B) interior suffix chord not exactly
antiparallel to the final edge (b_k ≠ π).
TRUE + non-vacuous: 40k+ feasible MC — interior chord_k never 0; closed sub-suffix violates a
backward support 2000/2000; interior b_k ≤ 3.134 < π; regular-polygon arcs realise premises.
Both are MEASURE-ZERO geometric degeneracies the supports exclude.

## HOW TO CLOSE THE RESIDUE (next target)
(B) follows from (A) + strong induction: the suffix [k,n] is a size-(n-k) DFC instance; if its
core is strengthened to also output "chord(0)≠0 → b_0 < π", then (A) gives b_k<π so b_k≠π.
So the IRREDUCIBLE kernel is (A): **chord(k)≠0 for 1≤k≤n-1** (no proper sub-suffix closes).

(A) proof sketch (discrete convexity / no-sub-loop, needs prefix-suffix interaction — NOT capturable
by suffix-only induction since a closed convex sub-polygon satisfies its own supports):
  chord(k)=0 ⟹ V_n=V_k ⟹ closed convex polygon P=[V_k..V_n]. Prefix vertex V_{k-1}=V_k-e_{k-1} is
  LEFT of every edge of P (backward support a∈[k,n) vtx k-1), i.e. inside P. But V_{k-1} sits across
  edge (k-1) which has direction θ_{k-1}<θ_k (the outgoing edge at V_k) — contradiction with the
  convex cone at vertex V_k. Concretely: backward a=n-1 vtx (k-1) gives ρ_{k-1} sin(θ_{n-1}-θ_{k-1})≥0
  and backward a=k vtx (k-1) gives ρ_{k-1} sin(θ_k - θ_{k-1})>0; combine with the closed-ness
  (V_n=V_k) and the partial-sum sign structure of the forward supports a=k (∑_{[k,m)} ρ sin(θ_i-θ_k)
  ≥0, total =0 since chord(k)=0). The clean contradiction likely: with all directions θ_k..θ_{n-1}
  and ∑ e_i=0, the forward partial sums (≥0, returning to 0) force a direction-balance that the
  prefix vertex's "left of all edges" + strict gaps make impossible. ~150-300 lines, real convexity.
  Alternative: strong induction on n proving (A) for chord(2..n-1) from suffix [1,n], leaving only
  chord(1)≠0 (the "remove first edge" boundary case) to handle directly.

## DESIGN VALIDATION (numerics, all confirmed)
- forward supports ALONE allow T≈4π (max 12.37); backward ESSENTIAL.
- single suffix lift Ω_j=θ_j+arg(exp(-iθ_j)s_j) satisfies (PRINCIPAL def, 0 violations / 150k):
  A: θ_j≤Ω_j≤θ_j+π;  B: Ω_j≥θ(n-1)-π (i.e. b_j≤π);  C: Ω_j≤Ω_{j+1}.
- s_0=0 (closed regular n-gon) IS feasible, T=2π-2π/n; only s_0 can vanish.
- max b_0 → π (regular arcs), max interior b_k ≈ 3.134 < π.

## DEAD ENDS (confirmed, don't repeat)
- nlinarith/fixed Farkas family: no universal certificate (prior agent).
- two independent lifts (suffix + prefix): circular winding-consistency. SINGLE suffix lift escapes.
- repo PolygonUmlaufsatz: itself unproved (ExtAngleRealSumPm2Pi) + needs StrictSimplePolygon. No reuse.
- last/first-vertex peeling: only <3π. Need exposed-vertex or the lift.
- Re(wrot j)=∑ρcos(θ_i-θj) can be very negative (-8.9): nonzero NOT free that way.

Verified machinery archived at HANDOFF/outbox/ch13-step-machinery.lean (early) ; live file is FFCT108.
