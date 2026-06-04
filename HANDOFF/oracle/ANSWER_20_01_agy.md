# ANSWER_20_01_agy — Ch20 Monsky Tier 1

## Recommended Tier 1

The book's Ch20 = Monsky's theorem: a unit square CANNOT be divided into an
odd number of triangles of equal area. The proof uses 2-adic coloring of ℝ²
(via Hahn series extension, NOT in Mathlib) + Sperner-style parity.

You already have:
- `sperner_parity_abstract` — abstract Sperner parity claim
- `exists_trichromatic_of_odd_boundary` — odd boundary ⇒ ∃ trichromatic triangle

Tier 1 takes the 2-adic-coloring + double-counting result as hypothesis:

```lean
/-- Certificate for Monsky's theorem: a 2-adic-style coloring of triangle
vertices together with the double-counting witness that boundary red-green
edge count is odd. This is the part that requires 2-adic extension to ℝ
(via transcendence basis / Hahn series, not in Mathlib). -/
structure MonskyCertificate (n : ℕ) where
  /-- The triangle colorings induced by a (hypothetical) equal-area
      odd-triangulation of the unit square. -/
  triangleColors : Fin n → MonskyColor × MonskyColor × MonskyColor
  /-- The boundary red-green edge count (from the square's edge contour). -/
  boundaryRGCount : ℕ
  /-- Total RG edge count summed over all triangles. -/
  totalRG : ℕ
  /-- Total = sum of triangle-local RG counts (double-counting bookkeeping). -/
  htotal : totalRG = ∑ i : Fin n,
    ((if RedGreenEdge (triangleColors i).1 (triangleColors i).2.1 then 1 else 0) +
     (if RedGreenEdge (triangleColors i).2.1 (triangleColors i).2.2 then 1 else 0) +
     (if RedGreenEdge (triangleColors i).2.2 (triangleColors i).1 then 1 else 0))
  /-- 2-adic constraint: parity of total RG = parity of boundary RG. -/
  hparity : totalRG % 2 = boundaryRGCount % 2
  /-- Crux of Monsky's argument: boundary RG count is ODD (from the unit
      square's specific 2-adic coloring at corners). -/
  hodd : Odd boundaryRGCount

/-- Chapter 20 (Monsky's theorem, Tier 1 conditional):
Given a Monsky 2-adic coloring certificate (which packages the 2-adic
extension construction + the double-counting parity result + the odd-boundary
witness), there exists a trichromatic triangle — corresponding to the
contradiction that closes the proof (such a triangle has area with 2-adic
valuation incompatible with 1/(odd integer)).

Tier 2 (construct MonskyCertificate from a hypothetical equal-area odd
triangulation, using 2-adic extension to ℝ via Hahn series / transcendence
basis, which is NOT in Mathlib) is deferred. -/
theorem chapter20 {n : ℕ} (cert : MonskyCertificate n) :
    ∃ i : Fin n,
      TrichromaticTriangle (cert.triangleColors i).1
        (cert.triangleColors i).2.1 (cert.triangleColors i).2.2 :=
  exists_trichromatic_of_odd_boundary n cert.triangleColors
    cert.boundaryRGCount cert.totalRG cert.htotal cert.hparity cert.hodd
```

## Notes

- The certificate bundles the 4 hypotheses needed by
  `exists_trichromatic_of_odd_boundary` (already proved in your file).
- `chapter20` literally calls that lemma with certificate fields.
- The contradictory content of Monsky's theorem (existence of trichromatic
  triangle ⇒ area is non-dyadic-fraction ⇒ contradicts equal-area-with-odd-count)
  is captured by the Tier 2 caller's job: they'd build the certificate ONLY
  IF such a triangulation existed, then derive `False` from the chapter20
  conclusion via area-valuation analysis.

## Tier 2 docstring

```lean
/- Tier 2 work (deferred): given a hypothetical equal-area triangulation of
the unit square into an ODD number of triangles, construct a MonskyCertificate
by:
1. Using Hahn series / transcendence basis to extend the 2-adic valuation
   v₂ : ℚ → ℤ to v₂' : ℝ → ℤ.
2. Color each point (x, y) ∈ ℝ² by:
   - red if v₂'(x) > 0 ∧ v₂'(y) > 0
   - green if v₂'(x) ≤ 0 ∧ v₂'(x) ≤ v₂'(y)
   - blue if v₂'(y) < 0 ∧ v₂'(y) < v₂'(x)
3. Verify the unit square corners (0,0), (1,0), (0,1), (1,1) get 3 distinct
   colors with odd boundary RG count.
4. The "total RG = boundary RG mod 2" identity follows from double-counting
   per Sperner.
The 2-adic extension to ℝ is non-trivial in Lean — likely needs Mathlib's
HahnSeries / WellOrderedExtension machinery. -/
```

## Build + commit

~40 LOC (structure + theorem + docstring). Should build clean since
the proof body is just `exists_trichromatic_of_odd_boundary` invocation.

Go.
