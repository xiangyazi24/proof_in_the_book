I have implemented the skeleton for `tailSwap` exactly as you suggested and it typechecks perfectly. Now I need the proofs for the 4 lemmas in the chain:
1. `Path.swapTailAt_swapTailAt`
2. `PathFamily.tailSwap_firstBadPair`
3. `PathFamily.tailSwap_tailSwap`
4. `PathFamily.tailSwap_sign`

Since `firstBadPair_tailSwap` is the hardest and involves many List and Finset manipulations, could you provide the complete proofs for these 4 lemmas (or the hardest ones) so I don't hit the > 80 LOC limit and get stuck in list indexing hell? My definitions for `splitAtFirst` and `swapTailAt` are:

```lean
def Path.splitAtFirst (p : List V) (v : V) : List V × List V :=
  let idx := p.idxOf v
  (p.take (idx + 1), p.drop (idx + 1))

def Path.swapTailAt (pi pj : List V) (v : V) : List V × List V :=
  let (pi_head, pi_tail) := Path.splitAtFirst pi v
  let (pj_head, pj_tail) := Path.splitAtFirst pj v
  (pi_head ++ pj_tail, pj_head ++ pi_tail)
```
