# Part B (bridge) route — recovered summary from ChatGPT (full answer lost to capture failure)

Key theorem: banks_connected_of_dual_path_between_cycle_faces — an interior-dual path from
faceOf (C.dart i) to faceOf (M.alpha (C.dart i)), using only dual adjacencies across non-cycle
edges, implies CutConn (bankDart Bank.plus i) (bankDart Bank.minus i).

Proof route: BY CONTRADICTION. Assume the two banks lie in different components of the cut map.
Prove a corrected lifting lemma: the interior-dual path lifts COMPONENT-WISE through face
FRAGMENTS (the phi'-pieces of straddling faces), never using the false "same old face =>
cut-connected" relay. The endpoint face-fragment lemmas place the two ends of the lifted path
in the plus and minus bank components respectively — contradiction.
