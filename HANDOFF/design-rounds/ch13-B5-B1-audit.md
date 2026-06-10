(pbook2 wave-3, 2026-06-10, via tab paste) B5 AUDIT: sketch incomplete, statement likely true.
Two gaps: (1) coefficient degeneracies — the predecessor kill needs 0 < a AND 0 < b; b > 0 from
edge-short (b = 0 ⟹ p = v coincidence); a > 0 needs no_repeat_of_positiveJoints (nonadjacent
repeated vertex forces an interior flat joint — master, 180-300 lines); (2) the tail side (j ≤ n−2)
is NOT a mirror — needs OnFoldRay cone propagation forward along the tail (master, 250-450).
Corrected predecessor algebra: det3 u p v = −b·det3 u v w, det3 u p w = a·det3 u v w; both weak
supports ≥ 0 with a,b > 0 ⟹ det3 u v w = 0 ⟹ the ADJACENT triple at vertex A i (joint index i−1)
vanishes ⟹ jointAngle ∈ {0, π} ⟹ PositiveJoints + jointAngle_lt_pi kill. Fallback milestone:
far_fold_boundary_classification_of_nondeg (takes nondegenerate coeffs as hypothesis).
B1 AUDIT: support-zero alone CANNOT give the Gram signs (branch ambiguity — this is why StuckAtKData
stores them) — needs the one-sided derivative at the admissible supremum (f'(δ*) = −hβ shape) +
witness normalization to a genuine edge-support triple + companion sign. 500-900 lines master.
Dependency order: B5-nondeg → no-repeat → B1 derivative → B1 normalization → B1 full → A2 → wrappers.
