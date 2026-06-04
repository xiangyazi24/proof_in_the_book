import ProofsInTheBook.Chapter20DissectionEngine
import ProofsInTheBook.Chapter20Colors
import ProofsInTheBook.Chapter20AtomicCount
import ProofsInTheBook.Chapter20SideGeom
import ProofsInTheBook.Chapter20DissectionSperner
import ProofsInTheBook.Chapter20E2Boundary

/-!
# Chapter 20 (Monsky) — final assembly

Wires the verified combinatorial layer to the geometric core (E2):
* per-side E3 bridge: along each subdivided triangle side the red-green atomic
  count has the parity of the side's endpoint colours (collinear ⇒ ≤2 colours);
* per-triangle: `listEdgeRGCount (triAtomicEdges i) ≡ triangleLocalRGCount` (mod 2);
* the atomic double-count + E2 turn the summed corner parity into the
  square-boundary atomic parity;
* the boundary organization (odd) + the Sperner spine close the chapter.

`monsky_dissection` is `False`-from-an-odd-equal-area-dissection, conditional only
on the geometric E2 (proved in the engine) and the boundary organization lemma.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

variable (D : SquareDissection)

/-- **Per-side E3 bridge.** The number of red-green atomic segments along side
`(p,q)` is odd iff the two endpoint colours form a red-green pair. -/
theorem odd_side_listEdgeRGCount_iff (p q : D.vtx) :
    Odd (listEdgeRGCount (sideAtomicEdges D p q) (realTwoAdicColor ∘ D.coord)) ↔
      RedGreenEdge (realTwoAdicColor (D.coord p)) (realTwoAdicColor (D.coord q)) := by
  rw [sideAtomicEdges, consecutiveEdges_RGCount_eq_listRGTransitionCount_map,
    show (p :: sideInteriorChain D p q ++ [q]).map (realTwoAdicColor ∘ D.coord)
        = realTwoAdicColor (D.coord p)
          :: ((sideInteriorChain D p q).map D.coord).map realTwoAdicColor
          ++ [realTwoAdicColor (D.coord q)] by
      simp [List.map_append, List.map_cons, List.map_map, Function.comp]]
  refine odd_sideRG_iff_endpoints_of_collinear
    ((p :: sideInteriorChain D p q ++ [q]).map D.coord)
    ((sideInteriorChain D p q).map D.coord) (D.coord p) (D.coord q)
    (by simp [List.map_append, List.map_cons]) ?_
  intro x hx y hy z hz
  obtain ⟨wx, hwx, rfl⟩ := List.mem_map.mp hx
  obtain ⟨wy, hwy, rfl⟩ := List.mem_map.mp hy
  obtain ⟨wz, hwz, rfl⟩ := List.mem_map.mp hz
  exact doubleArea_eq_zero_of_wbtw (onSide_of_mem_sideChain D hwx)
    (onSide_of_mem_sideChain D hwy) (onSide_of_mem_sideChain D hwz)

/-- Mod 2, a side's red-green atomic count equals its endpoint red-green indicator. -/
theorem side_listEdgeRGCount_mod_two (p q : D.vtx) :
    listEdgeRGCount (sideAtomicEdges D p q) (realTwoAdicColor ∘ D.coord) % 2 =
      (if RedGreenEdge (realTwoAdicColor (D.coord p)) (realTwoAdicColor (D.coord q))
        then 1 else 0) := by
  by_cases h : RedGreenEdge (realTwoAdicColor (D.coord p)) (realTwoAdicColor (D.coord q))
  · simp only [h, if_true]
    exact Nat.odd_iff.mp ((odd_side_listEdgeRGCount_iff D p q).mpr h)
  · simp only [h, if_false]
    rcases Nat.even_or_odd (listEdgeRGCount (sideAtomicEdges D p q)
      (realTwoAdicColor ∘ D.coord)) with he | ho
    · exact Nat.even_iff.mp he
    · exact absurd ((odd_side_listEdgeRGCount_iff D p q).mp ho) h

/-- **Per-triangle bridge.** The red-green atomic boundary count of triangle `i`
agrees mod 2 with its corner-colour `triangleLocalRGCount`. -/
theorem triangle_listEdgeRGCount_mod_two (i : Fin D.n) :
    listEdgeRGCount (triAtomicEdges D i) (realTwoAdicColor ∘ D.coord) % 2 =
      triangleLocalRGCount (realTwoAdicColor (D.coord (D.tri i).1),
        realTwoAdicColor (D.coord (D.tri i).2.1),
        realTwoAdicColor (D.coord (D.tri i).2.2)) % 2 := by
  rw [triAtomicEdges, listEdgeRGCount_append, listEdgeRGCount_append]
  have h1 := side_listEdgeRGCount_mod_two D (D.tri i).1 (D.tri i).2.1
  have h2 := side_listEdgeRGCount_mod_two D (D.tri i).2.1 (D.tri i).2.2
  have h3 := side_listEdgeRGCount_mod_two D (D.tri i).2.2 (D.tri i).1
  simp only [triangleLocalRGCount]
  omega

/-- `atomicMult` is exactly the family multiplicity of the atomic-edge lists. -/
theorem atomicMult_eq_familyEdgeMult (e : Sym2 D.vtx) :
    atomicMult D e = familyEdgeMult (triAtomicEdges D) e := rfl

/-- Summing the per-triangle bridge: the total corner `triangleLocalRGCount`
agrees mod 2 with the red-green count of odd-multiplicity atomic edges. -/
theorem sum_triangleLocalRGCount_mod_two_eq_oddAtomic :
    (∑ i : Fin D.n, triangleLocalRGCount
        (realTwoAdicColor (D.coord (D.tri i).1),
         realTwoAdicColor (D.coord (D.tri i).2.1),
         realTwoAdicColor (D.coord (D.tri i).2.2))) % 2 =
      (Finset.univ.filter fun e : Sym2 D.vtx =>
        edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧
          Odd (atomicMult D e)).card % 2 := by
  classical
  -- step 1: sum of per-triangle parities (bridge), backwards
  have hstep1 : (∑ i : Fin D.n, triangleLocalRGCount
        (realTwoAdicColor (D.coord (D.tri i).1),
         realTwoAdicColor (D.coord (D.tri i).2.1),
         realTwoAdicColor (D.coord (D.tri i).2.2))) % 2 =
      (∑ i : Fin D.n, listEdgeRGCount (triAtomicEdges D i)
        (realTwoAdicColor ∘ D.coord)) % 2 := by
    rw [Finset.sum_nat_mod, Finset.sum_nat_mod
      (f := fun i => listEdgeRGCount (triAtomicEdges D i) (realTwoAdicColor ∘ D.coord))]
    congr 1
    exact Finset.sum_congr rfl fun i _ => (triangle_listEdgeRGCount_mod_two D i).symm
  rw [hstep1, sum_listEdgeRGCount_mod_two (triAtomicEdges D) (realTwoAdicColor ∘ D.coord)]
  -- familyEdgeMult (triAtomicEdges D) = atomicMult D, definitionally
  rfl

/-- **Monsky's theorem (faithful dissection form).** No dissection of the unit
square into an odd number of equal-area triangles exists. Conditional only on the
geometric boundary-organization lemma `oddAtomicRG_card_odd` (which in turn rests
on the proved E2 incidence lemmas). -/
theorem monsky_dissection (hn : Odd D.n) : False := by
  refine monsky_false_of_odd_corner_parity hn
    (fun i => (D.coord (D.tri i).1, D.coord (D.tri i).2.1, D.coord (D.tri i).2.2))
    D.equalArea ?_
  rw [Nat.odd_iff, sum_triangleLocalRGCount_mod_two_eq_oddAtomic D,
    ← Nat.odd_iff]
  exact oddAtomicRG_card_odd D

end ProofsInTheBook.Chapter20
