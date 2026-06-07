# Ch13: THE book-faithful discharge of DeficientReachStep (from BOOK_CH13_CAUCHY.txt lines 86-125)

## The book proof is the design (bridge-independent)
Arm lemma (Schoenberg→Zaremba letter, valid planar AND spherical): arms A,B, equal sides,
jointAngle A i ≤ jointAngle B i (2≤i≤n-1) ⟹ endpt A ≤ endpt B. Induction on n:
- n=3: spherical hinge (cos c = cos a cos b + sin a sin b cos γ; opening γ increases c). BANKED
  (spherical_hinge_mono/_strict).
- n≥4, SOME joint i EQUAL (αi=α'i): cut vertex i via diagonal q(i-1)q(i+1); by SAS (n=3 with EQUAL
  angle) the diagonal is EQUAL (diag_len_eq), giving an equal-side (n-1)-arm → IH. *Cut is ALWAYS at
  an EQUAL joint (equal diagonal); NEVER a deficient/folded one.* So cut_diag_le (≤-diagonal),
  FoldedFlatCutTransport, SpliceBodyDiagMono are the WRONG architecture.
- n≥4, ALL joints deficient: open the LAST joint α(n-1) to sup α*(n-1) ≤ α'(n-1) keeping convex:
  - REACH (reach α'(n-1) keeping convex): endpt A < endpt A* (n=3 hinge, eq before (1)) then
    endpt A* ≤ endpt B (cut the now-EQUAL last joint, IH).
  - STUCK (q2,q1,q*n collinear, eq(2): q2q1+q1q*n=q2q*n; eq(1): q1q*n>q1qn): DIRECT bound
        endpt B = q'1q'n ≥ q'2q'n - q'1q'2     [(∗) sphere triangle inequality on B]
                ≥ q2q*n - q1q2                  [(3) IH on the PLAIN sub-arm q2..q*n vs q'2..q'n]
                = q1q*n                          [(2) collinearity, q'1q'2=q1q2 equal sides]
                > q1qn = endpt A                 [(1) partial-opening gain]
    NOT a contradiction — a DIRECT proof of endpt A ≤ endpt B (strict). Uses a PLAIN shift sub-arm
    (drop q1=A 0), NOT the substrate frontCut's matched-sides machinery (which the original round got
    stuck on).

## Why this closes DeficientReachStep (SphericalArmFinish's single residue)
The two documented obstacles in SphericalArmFinish §51-84 are resolved:
1. REACH strict-positivity at δ*: by_cases on Stuck (augmented_reachOrStuck_at_sup dichotomy). In
   ¬Stuck, no monitored support/hemisphere vanished ⟹ hmix,hhem >0 ⟹ reach_strictConvex_at_sup ⟹
   A♯ strict. (Reach/stuck need NOT be mutually exclusive — by_cases handles both.)
2. STUCK matched two-piece cut: NOT needed. Use the plain sub-arm (drop A 0) + SZComparison IH +
   sDist triangle inequality + the stuck collinearity (q2,q1,q*n) + reach_endpoint_mono (eq 1).
   The stuck support that binds the last-joint opening IS the (q2,q1,q*n) det (q1=A 0 collinear).

## Banked pieces (all confirmed present)
spherical_hinge_mono/_strict (SphericalArm); diag_len_eq (SphericalSZChain/CyclicTriple);
augmented_reachOrStuck_at_sup, reach_endpoint_mono, reach_strictConvex_at_sup (SphericalAdmissibleSup);
sDist triangle inequality (SphericalArmDone/SphericalArm); the recursion driver
spherical_arm_mono_of_deficientReachStep (SphericalArmFinish). Target: discharge DeficientReachStep
⟹ spherical_arm_mono UNCONDITIONAL. The recent InteriorOpenAndSpliceStep / interior-openTail /
splice / OpeningGlue campaign is a more-fragmented detour and is SUPERSEDED by this.
