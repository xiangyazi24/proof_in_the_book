# Chapter 39 — Fully finite mod-2 Fan / Freund–Todd pivot proof (AUTHORITATIVE blueprint)

Source: bridge answer, master-verified. This is the exact structure for the remaining gap
`∀ d≥1, KyFanUnorderedParityStatement d`. KEY: the local deletion lemma is for a GENERAL
increasing index set a_1<...<a_k ≤ m (NOT the fixed diagonal A), and Fan parity needs m≥r.

## 1. Complexes K_r and positive hemisphere B_r^+
K_r = order complex of nonzero signed subsets of [r]; vertices X∈{-1,0,1}^r\{0}; simplices = strict chains.
Facet = maximal chain of length r = signed permutation of [r]. K_{r-1}⊂K_r = signed subsets with coord r = 0.
B_r^+ = full subcomplex on X with X_r ≠ -1. ∂B_r^+ = K_{r-1}.
HEMISPHERE INCIDENCE: a codim-1 face τ of B_r^+ lies in 1 or 2 facets; in exactly 1 iff τ⊂K_{r-1}
(boundary ridge). (Missing intermediate rank → 2 insertions; missing top rank → 1 iff missing coord is r,
since only +r allowed in B_r^+.)

## 2. Alternating simplices (GENERAL index set — this is the generalization)
Label range {±1,...,±m}. For a simplex σ with k vertices: Alt_k^+(σ) iff labels have distinct abs values
and, sorted by abs value, are  +a_1, -a_2, +a_3, ..., (-1)^{k-1} a_k  with  1≤a_1<a_2<...<a_k≤m.
Alt_k^-(σ): sorted labels  -a_1, +a_2, ..., (-1)^k a_k.   N_k^±(S) = # (k-1)-simplices σ⊂S with Alt_k^±(σ).

## 3. Local deletion lemma  (`local_deletion_parity`)  — THE crux, full case analysis
Assume σ has NO two vertices with opposite labels +a,-a. For a (k+1)-vertex σ:
  d_+(σ) := #{v∈σ : Alt_k^+(σ\{v})}.
LEMMA:  d_+(σ) ≡ 1 (mod 2)  iff  Alt_{k+1}^+(σ) ∨ Alt_{k+1}^-(σ);  else d_+(σ) even; and d_+(σ)>0 ⇒ d_+(σ)∈{1,2}.
PROOF. Suppose d_+(σ)>0; pick a +-alternating k-face τ⊂σ with labels +a_1,-a_2,...,(-1)^{k-1}a_k (a_1<...<a_k).
Let v = extra vertex, label η·b, η∈{±1}.
 • b = a_i for some i: no complementary pair ⇒ η = (-1)^{i-1} (same sign as existing). Then exactly TWO +-alt
   k-faces (delete extra copy of a_i, or original copy) ⇒ d_+(σ)=2.
 • b ∉ {a_i}: let p = #{i : a_i < b} (b inserted between a_p, a_{p+1}; p=0 or p=k allowed). τ (delete v) is always
   one +-alt k-face. Other +-alt faces keep v, delete one old vertex (forced):
     0<p<k: delete a_p works iff η=(-1)^{p-1}; delete a_{p+1} works iff η=(-1)^p. Opposite signs ⇒ exactly one works.
            ⇒ d_+(σ)=2.
     p=0: only candidate is delete a_1, works iff η=+1 ⇒ d_+=2. If η=-1: no replacement; full list
          -b,+a_1,-a_2,...,(-1)^{k-1}a_k = Alt_{k+1}^-(σ) ⇒ d_+=1.
     p=k: only candidate delete a_k, works iff η=(-1)^{k-1} ⇒ d_+=2. If η=(-1)^k: no replacement; full list
          +a_1,...,(-1)^{k-1}a_k,(-1)^k b = Alt_{k+1}^+(σ) ⇒ d_+=1.
 So d_+=1 exactly in the two full-alternating cases, else 2. ∎

## 4. Ball parity lemma  (`ball_parity`)
Apply local lemma in B_r^+, k=r-1. Incidence set I = {(τ,σ): τ⊂σ, σ facet of B_r^+, τ codim-1 face, Alt_{r-1}^+(τ)}.
By ridges: interior ridge → 2 facets (0 mod 2), boundary ridge → 1 facet (1 mod 2). So |I| ≡ N_{r-1}^+(∂B_r^+) =
N_{r-1}^+(K_{r-1}). By facets: contribution of σ = d_+(σ) ≡ 1 iff Alt_r^±(σ). So |I| ≡ N_r^+(B_r^+)+N_r^-(B_r^+).
  ⇒  N_{r-1}^+(K_{r-1}) ≡ N_r^+(B_r^+) + N_r^-(B_r^+)  (mod 2).    (Ball)

## 5. Fan parity on K_r  (`fan_sphere_parity`)  — induction on r, NEEDS m≥r
THM: m≥r, λ: V(K_r)→{±1,...,±m} antipodal, no complementary comparable pair ⇒ N_r^+(K_r) ≡ 1 (mod 2).
PROOF by induction on r.
 r=1: two antipodal vertices, labels a, -a; exactly one positive ⇒ N_1^+=1.
 r-1 ⇒ r: by IH N_{r-1}^+(K_{r-1}) ≡ 1. Ball ⇒ N_r^+(B_r^+)+N_r^-(B_r^+) ≡ 1. Antipodal map sends B_r^+→B_r^-
   bijectively and Alt_r^- → Alt_r^+, so N_r^-(B_r^+)=N_r^+(B_r^-). Facets of K_r split disjointly into B_r^+ and
   B_r^- (by sign of top coord r), so N_r^+(K_r) = N_r^+(B_r^+)+N_r^+(B_r^-) = N_r^+(B_r^+)+N_r^-(B_r^+) ≡ 1. ∎

## 6. Reduction (the Tucker step) — CLEANER than the prior framing
n≥2, label range {±1,...,±(n-1)} (m=n-1). Suppose NO complementary comparable pair (no edge of K_n with
opposite labels). Restrict λ to equator K_{n-1}⊂K_n: still antipodal, no complementary edge, m=n-1=r.
 Fan parity (r=n-1): N_{n-1}^+(K_{n-1}) ≡ 1.
 Ball parity at B_n^+: N_{n-1}^+(K_{n-1}) ≡ N_n^+(B_n^+)+N_n^-(B_n^+). But N_n^±(B_n^+)=0 (an Alt_n^± facet needs
 n distinct abs indices, only n-1 exist). ⇒ N_{n-1}^+(K_{n-1}) ≡ 0. CONTRADICTION with ≡1.
 So a comparable pair X≺Y with λ(X)=-λ(Y) exists; extend to a maximal chain (X coords, then Y\X, then rest with
 arbitrary signs) ⇒ chain C_0≺...≺C_{n-1} with i<j, λ(C_i)=-λ(C_j). That is the reduction step.

## Lean lemma list (the formal targets)
local_deletion_parity ; hemisphere_incidence ; ball_parity ; fan_sphere_parity (induction, m≥r) ;
then §6 contradiction. The §6 route may bypass the heavy ActualHemisphere restructuring: it only needs
Fan parity at the equator (m=r) + ball parity at B_n^+ with the "no length-n alternating facet" triviality.

---

## ADDENDUM (round 19 reframing) — dissolve the local deletion lemma via SIGN SEQUENCES

The `idx` machinery is a red herring for the local deletion lemma. Reduce to pure sign combinatorics.

### Incidence correction (from pbook task 41fd9654)
The dichotomy is purely: #{facets of B_r^+ containing ridge τ} = 1 if τ⊆K_{r-1}, else 2. ("missing the top
rank" alone does NOT give 1 — e.g. r=2, τ={2↦+} misses top rank, not in K_1, lies in BOTH {2+}≺{1+,2+} and
{2+}≺{1-,2+}; it's 1 iff the missing support coord is r, i.e. iff τ⊆K_{r-1}.)

### Local deletion lemma — sign-sequence reduction
σ has k+1 vertices, NO opposite-label pair (so each absolute value occurs with a single common sign).
d_+(σ) := #{v∈σ : IsAltPos (σ\{v})}.

CASE A — σ has a repeated absolute value. Then NOT IsAltPos σ and NOT IsAltNeg σ (both need distinct abs).
  Sub-argument: with no opposite pair, a repeated abs value a means ≥2 equal labels. Any σ\{v} with distinct
  abs values must delete down to multiplicity 1 everywhere; if exactly one value has multiplicity 2 (rest 1),
  the only deletions giving distinct-abs are the TWO copies, and both yield the SAME k-label multiset (hence
  same IsAltPos truth value) ⇒ d_+∈{0,2}. If any value has multiplicity ≥3, or ≥2 values have multiplicity 2,
  no single deletion gives distinct abs ⇒ d_+=0. Either way d_+ even. ✓ (matches lemma RHS false.)

CASE B — σ has all DISTINCT absolute values. Sort the k+1 vertices by |label|; extract the SIGN SEQUENCE
  s : Fin(k+1)→{±1} (s_t = sign of the t-th smallest abs value). Deleting the vertex of the i-th smallest abs
  value leaves the sign subsequence (s with position i removed). IsAltPos(σ\{v_i}) ⟺ that subsequence equals
  +,-,+,...  So d_+(σ) = D(s) where:

  SIGN-SEQUENCE DELETION PARITY LEMMA. For s:Fin(k+1)→{±1}, D(s):=#{i : (s delete i) = (+,-,+,...) length k}.
  Then D(s) is ODD iff s = (+,-,+,...) (alt-start-+) OR s = (-,+,-,...) (alt-start-−).
  And IsAltPos σ ⟺ s=alt-start-+ ; IsAltNeg σ ⟺ s=alt-start-−. So d_+(σ)≡1 ⟺ IsAltPos σ ∨ IsAltNeg σ. ∎(B)

### PROOF of the sign-sequence deletion parity lemma (DOOR characterization — fully finite)
Define door(i) for i∈{0,...,k}:  door(i) :⟺ (∀ j<i, s_j=(-1)^j) ∧ (∀ j>i, s_j=(-1)^{j-1}).
CLAIM: deleting position i yields (+,-,+,...) iff door(i). [The kept prefix s_0..s_{i-1} must be +,-,+,... ⟹
  s_j=(-1)^j for j<i; the kept suffix s_{i+1}..s_k, reindexed to follow position i-1, must continue the
  alternation ⟹ s_j=(-1)^{j-1} for j>i. s_i is dropped, hence free.]
KEY FACTS:
 (1) prefix-cond is downward closed in i, suffix-cond is upward closed ⇒ each is an interval condition.
 (2) NO THREE DOORS, and two doors must be ADJACENT: if i<i' both doors, every j with i<j<i' satisfies both
     s_j=(-1)^{j-1} (door i suffix) and s_j=(-1)^j (door i' prefix) — contradiction unless no such j, i.e.
     i'=i+1. Three doors i<i+1<i+2 would put i,i+2 non-adjacent ⇒ impossible. So D(s)∈{0,1,2}.
 (3) For 0<i<k, door(i) forces EXACTLY ONE neighbor door: door(i+1)⟺s_i=(-1)^i ; door(i-1)⟺s_i=(-1)^{i-1};
     s_i is one of these, so a door at an interior i always has a partner ⇒ D≥2. Hence a UNIQUE door (D=1)
     sits at i=0 or i=k.
 (4) Unique door at i=k: uniqueness kills door(k-1) ⟹ s_k=(-1)^k, combined with prefix ⟹ s=alt-start-+.
     Unique door at i=0: uniqueness kills door(1) ⟹ s_0=-, combined with suffix ⟹ s=alt-start-−.
 (5) Conversely s=alt-start-+ ⇒ only door is i=k (any suffix-cond at i<k fails since (-1)^j≠(-1)^{j-1});
     s=alt-start-− ⇒ only door is i=0. So D=1 in exactly these two cases; otherwise D∈{0,2}, even.
 Therefore D(s) odd ⟺ s alternating-±.  ∎

This is the entire crux. No idx summation, no fixed-A specialization — pure {±1}-sequence combinatorics,
ideal for Lean (Finset.filter over Fin(k+1), the door predicate is Decidable, the parity falls out of (2)-(5)).
