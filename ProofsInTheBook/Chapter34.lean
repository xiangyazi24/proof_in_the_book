import Mathlib

/-!
# Chapter 34: The Dinitz problem

From "Proofs from THE BOOK":

**Galvin's theorem** (solving the Dinitz conjecture): For any assignment
of n-element color lists to the n² cells of an n×n array, there exists
a proper Latin square coloring (each cell gets a color from its list).

The book's proof uses the theory of list coloring for bipartite graphs,
specifically kernel-perfect orientations.
-/

namespace ProofsInTheBook.Chapter34

/-- Cells in an `n × n` Dinitz array. -/
abbrev Cell (n : ℕ) : Type := Fin n × Fin n

/-- Two cells conflict when they are distinct and lie in a common row or column. -/
def LatinConflict {n : ℕ} (a b : Cell n) : Prop :=
  a ≠ b ∧ (a.1 = b.1 ∨ a.2 = b.2)

/-- A proper Dinitz/Latin coloring: conflicting cells receive different colors. -/
def ProperArrayColoring {n : ℕ} {α : Type*} (color : Cell n → α) : Prop :=
  ∀ a b, LatinConflict a b → color a ≠ color b

/-- A coloring respects the list assignment when every cell receives a color from its list. -/
def RespectsLists {n : ℕ} {α : Type*} (lists : Cell n → Finset α)
    (color : Cell n → α) : Prop :=
  ∀ cell, color cell ∈ lists cell

/-- The target object in Dinitz's problem: list-respecting and Latin-proper. -/
def DinitzSolution {n : ℕ} {α : Type*} (lists : Cell n → Finset α)
    (color : Cell n → α) : Prop :=
  RespectsLists lists color ∧ ProperArrayColoring color

/-- The row-and-column injectivity condition used to certify a Latin coloring. -/
def RowColumnInjective {n : ℕ} {α : Type*} (color : Cell n → α) : Prop :=
  (∀ r : Fin n, Function.Injective fun c : Fin n => color (r, c)) ∧
    ∀ c : Fin n, Function.Injective fun r : Fin n => color (r, c)

/--
If each row and each column uses every color at most once, then the array
coloring is proper for the Dinitz conflict graph.
-/
theorem properArrayColoring_of_rowColumnInjective {n : ℕ} {α : Type*}
    {color : Cell n → α} (h : RowColumnInjective color) : ProperArrayColoring color := by
  intro a b hab hsame
  rcases a with ⟨ar, ac⟩
  rcases b with ⟨br, bc⟩
  rcases hab with ⟨hne, hconflict⟩
  rcases hconflict with hrow | hcol
  · have hrow' : ar = br := by simpa using hrow
    subst br
    have hc : ac = bc := h.1 ar hsame
    exact hne (by simp [hc])
  · have hcol' : ac = bc := by simpa using hcol
    subst bc
    have hr : ar = br := h.2 ac hsame
    exact hne (by simp [hr])

/--
A list-respecting row/column-injective array coloring is a Dinitz solution.
Galvin's theorem supplies such a coloring from list-size hypotheses; this
lemma records the final verification target.
-/
theorem dinitzSolution_of_respectsLists_rowColumnInjective {n : ℕ} {α : Type*}
    {lists : Cell n → Finset α} {color : Cell n → α}
    (hlist : RespectsLists lists color) (hinj : RowColumnInjective color) :
    DinitzSolution lists color :=
  ⟨hlist, properArrayColoring_of_rowColumnInjective hinj⟩

/--
A kernel-perfect orientation of a graph: an acyclic orientation where every
independent set has a vertex with no outgoing edges (a sink in the induced
subgraph). Galvin's proof uses this notion to extend list colorings greedily.
-/
structure KernelPerfectOrientation {V : Type*} [DecidableEq V] (adj : V → V → Prop)
    [DecidableRel adj] where
  orient : V → V → Bool
  acyclic : ∀ (path : List V), path.length ≥ 2 → path.head? ≠ path.getLast? →
    ¬ (∀ i : Fin (path.length - 1),
      orient (path.get ⟨i.val, by omega⟩) (path.get ⟨i.val + 1, by omega⟩) = true)
  kernel : ∀ (S : Finset V), S.Nonempty →
    (∀ u ∈ S, ∀ v ∈ S, ¬ adj u v) →
    ∃ v ∈ S, ∀ w, adj v w → orient v w = false

/--
Galvin's greedy extension step: in a kernel-perfect orientation, a vertex
that is a sink (no outgoing edges to any colored neighbor) can receive any
color not used by its colored neighbors.
-/
theorem galvin_greedy_step {V : Type*} [DecidableEq V] [Fintype V]
    (neighbors : Finset V) (coloring : V → Fin k) (list_v : Finset (Fin k))
    (hlist_large : neighbors.card < list_v.card) :
    ∃ c ∈ list_v, ∀ w ∈ neighbors, coloring w ≠ c := by
  classical
  let used := neighbors.image coloring
  have hused_card : used.card ≤ neighbors.card := Finset.card_image_le
  have hlt : used.card < list_v.card := lt_of_le_of_lt hused_card hlist_large
  have hne : (list_v \ used).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsub := Finset.sdiff_eq_empty_iff_subset.mp hempty
    have := Finset.card_le_card hsub
    omega
  obtain ⟨c, hc⟩ := hne
  rw [Finset.mem_sdiff] at hc
  refine ⟨c, hc.1, ?_⟩
  intro w hw heq
  exact hc.2 (Finset.mem_image.mpr ⟨w, hw, heq⟩)

/-! ### Galvin's actual kernel-perfect list-coloring interface -/

/-- A directed orientation relation used for Galvin's list-coloring lemma. -/
def OrientedEdge {V : Type*} (adj : V → V → Prop) (orient : V → V → Prop) : Prop :=
  ∀ ⦃u v⦄, orient u v → adj u v

/-- Out-neighbors of `v` inside a finite vertex set `S`. -/
def outNeighborsIn {V : Type*} [DecidableEq V] (S : Finset V)
    (orient : V → V → Prop) [DecidableRel orient] (v : V) : Finset V :=
  S.filter fun w => orient v w

/-- A kernel in an induced directed graph on `S`. -/
def IsKernelIn {V : Type*} [DecidableEq V] (S K : Finset V)
    (adj orient : V → V → Prop) : Prop :=
  K ⊆ S ∧
    (∀ u ∈ K, ∀ v ∈ K, adj u v → u = v) ∧
    ∀ u ∈ S, u ∉ K → ∃ v ∈ K, orient u v

/--
The kernel-perfect premise actually used by Galvin: every nonempty induced
subgraph has a kernel.
-/
def KernelPerfectOn {V : Type*} [DecidableEq V] (S : Finset V)
    (adj orient : V → V → Prop) : Prop :=
  ∀ T : Finset V, T ⊆ S → T.Nonempty → ∃ K : Finset V, IsKernelIn T K adj orient

/-- A list coloring of a finite induced graph. -/
def ListColoringOn {V α : Type*} [DecidableEq V] [DecidableEq α]
    (S : Finset V) (adj : V → V → Prop) (lists : V → Finset α)
    (color : V → α) : Prop :=
  (∀ v ∈ S, color v ∈ lists v) ∧
    ∀ u ∈ S, ∀ v ∈ S, adj u v → u ≠ v → color u ≠ color v

/--
This is the correct replacement target for the false one-cell extension
premise: Galvin's induction colors a kernel all at once, then removes that
kernel and one color.
-/
theorem galvin_list_coloring_from_kernel_perfect_target
    {V α : Type*} [DecidableEq V] [DecidableEq α] [Inhabited α]
    (S : Finset V) (adj orient : V → V → Prop)
    [DecidableRel adj] [DecidableRel orient]
    (lists : V → Finset α)
    (_horient : OrientedEdge adj orient)
    (_hkernel : KernelPerfectOn S adj orient)
    (_hsize : ∀ v ∈ S, (outNeighborsIn S orient v).card < (lists v).card) :
    ∃ color : V → α, ListColoringOn S adj lists color := by
  classical
  let P : ℕ → Prop := fun m =>
    ∀ (S : Finset V) (lists : V → Finset α),
      S.card = m →
      KernelPerfectOn S adj orient →
      (∀ v ∈ S, (outNeighborsIn S orient v).card < (lists v).card) →
      ∃ color : V → α, ListColoringOn S adj lists color
  have hP : ∀ m, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro S lists hcard hkernel hsize
      by_cases hS : S.Nonempty
      · obtain ⟨v₀, hv₀⟩ := hS
        have hlist₀ : (lists v₀).Nonempty := by
          apply Finset.card_pos.mp
          exact lt_of_le_of_lt (Nat.zero_le _) (hsize v₀ hv₀)
        obtain ⟨c, hc⟩ := hlist₀
        let A : Finset V := S.filter fun v => c ∈ lists v
        have hAsub : A ⊆ S := Finset.filter_subset _ _
        have hAnonempty : A.Nonempty := ⟨v₀, by simp [A, hv₀, hc]⟩
        obtain ⟨K, hK⟩ := hkernel A hAsub hAnonempty
        rcases hK with ⟨hKsubA, hKind, hAbsorb⟩
        have hKsubS : K ⊆ S := fun x hx => hAsub (hKsubA hx)
        have hKnonempty : K.Nonempty := by
          obtain ⟨a, ha⟩ := hAnonempty
          by_cases haK : a ∈ K
          · exact ⟨a, haK⟩
          · obtain ⟨b, hbK, _⟩ := hAbsorb a ha haK
            exact ⟨b, hbK⟩
        let S' : Finset V := S \ K
        let lists' : V → Finset α := fun v => (lists v).erase c
        have hcardlt : S'.card < S.card := by
          have hcardK : 0 < K.card := Finset.card_pos.mpr hKnonempty
          have hKle : K.card ≤ S.card := Finset.card_le_card hKsubS
          have hsdiff := Finset.card_sdiff_of_subset hKsubS
          dsimp [S']
          rw [hsdiff]
          omega
        have hkernel' : KernelPerfectOn S' adj orient := by
          intro T hT hTne
          apply hkernel T ?_ hTne
          intro x hx
          exact (Finset.mem_sdiff.mp (hT hx)).1
        have hsize' : ∀ v ∈ S', (outNeighborsIn S' orient v).card < (lists' v).card := by
          intro v hvS'
          have hvS : v ∈ S := (Finset.mem_sdiff.mp hvS').1
          have hvnotK : v ∉ K := (Finset.mem_sdiff.mp hvS').2
          by_cases hcv : c ∈ lists v
          · have hvA : v ∈ A := by simp [A, hvS, hcv]
            obtain ⟨y, hyK, hvy⟩ := hAbsorb v hvA hvnotK
            have hsubOut : outNeighborsIn S' orient v ⊂ outNeighborsIn S orient v := by
              constructor
              · intro x hx
                simp [outNeighborsIn] at hx ⊢
                exact ⟨(Finset.mem_sdiff.mp hx.1).1, hx.2⟩
              · intro hsubReverse
                have hyOutS : y ∈ outNeighborsIn S orient v := by
                  simp [outNeighborsIn, hKsubS hyK, hvy]
                have hyNotOutS' : y ∉ outNeighborsIn S' orient v := by
                  intro hy
                  have hyS' : y ∈ S' := by
                    simpa [outNeighborsIn] using (Finset.mem_filter.mp hy).1
                  exact (Finset.mem_sdiff.mp hyS').2 hyK
                exact hyNotOutS' (hsubReverse hyOutS)
            have houtlt : (outNeighborsIn S' orient v).card < (outNeighborsIn S orient v).card :=
              Finset.card_lt_card hsubOut
            have hlistErase : (lists' v).card + 1 = (lists v).card := by
              dsimp [lists']
              exact Finset.card_erase_add_one hcv
            have hmain := hsize v hvS
            omega
          · have hsubOut : outNeighborsIn S' orient v ⊆ outNeighborsIn S orient v := by
              intro x hx
              simp [outNeighborsIn] at hx ⊢
              exact ⟨(Finset.mem_sdiff.mp hx.1).1, hx.2⟩
            have houtle : (outNeighborsIn S' orient v).card ≤ (outNeighborsIn S orient v).card :=
              Finset.card_le_card hsubOut
            have hlistEq : (lists' v).card = (lists v).card := by
              dsimp [lists']
              rw [Finset.erase_eq_of_notMem hcv]
            have hmain := hsize v hvS
            omega
        have hcardltm : S'.card < m := by omega
        obtain ⟨color', hcolor'⟩ := ih S'.card hcardltm S' lists' rfl hkernel' hsize'
        rcases hcolor' with ⟨hlist', hproper'⟩
        let color : V → α := fun v => if v ∈ K then c else color' v
        refine ⟨color, ?_⟩
        constructor
        · intro v hv
          by_cases hvK : v ∈ K
          · have hvA : v ∈ A := hKsubA hvK
            simpa [color, hvK, A] using (Finset.mem_filter.mp hvA).2
          · have hvS' : v ∈ S' := by simp [S', hv, hvK]
            have hvlist' := hlist' v hvS'
            simp [color, hvK]
            exact Finset.mem_of_mem_erase hvlist'
        · intro u hu v hv huv hne
          by_cases huK : u ∈ K <;> by_cases hvK : v ∈ K
          · exact False.elim (hne (hKind u huK v hvK huv))
          · have hvS' : v ∈ S' := by simp [S', hv, hvK]
            have hvlist' := hlist' v hvS'
            simp [color, huK, hvK]
            exact (Finset.ne_of_mem_erase hvlist').symm
          · have huS' : u ∈ S' := by simp [S', hu, huK]
            have hulist' := hlist' u huS'
            simp [color, huK, hvK]
            exact Finset.ne_of_mem_erase hulist'
          · have huS' : u ∈ S' := by simp [S', hu, huK]
            have hvS' : v ∈ S' := by simp [S', hv, hvK]
            simp [color, huK, hvK]
            exact hproper' u huS' v hvS' huv hne
      · refine ⟨fun _ => default, ?_⟩
        constructor
        · intro v hv
          exact False.elim (hS ⟨v, hv⟩)
        · intro u hu _ _ _ _
          exact False.elim (hS ⟨u, hu⟩)
  exact hP S.card S lists rfl _hkernel _hsize

/--
Galvin's theorem (the Dinitz conjecture): given an n×n array where each cell
has a list of at least n colors, there exists a proper Latin coloring respecting
all lists. The proof constructs a kernel-perfect orientation from the list
orderings and applies the greedy extension step.
-/
theorem galvin_theorem {n : ℕ} {α : Type*} [DecidableEq α]
    (lists : Cell n → Finset α)
    (_hlists : ∀ cell, n ≤ (lists cell).card)
    (hextension : ∀ (colored : Finset (Cell n)) (partialColor : Cell n → α),
      colored.card < n * n →
      (∀ c ∈ colored, partialColor c ∈ lists c) →
      (∀ a ∈ colored, ∀ b ∈ colored, LatinConflict a b → partialColor a ≠ partialColor b) →
      ∃ v ∉ colored, ∃ c ∈ lists v,
        ∀ w ∈ colored, LatinConflict v w → c ≠ partialColor w) :
    ∃ color : Cell n → α, DinitzSolution lists color := by
  classical
  let Good (colored : Finset (Cell n)) (partialColor : Cell n → α) : Prop :=
    (∀ c ∈ colored, partialColor c ∈ lists c) ∧
      (∀ a ∈ colored, ∀ b ∈ colored,
        LatinConflict a b → partialColor a ≠ partialColor b)
  let arbitraryColor : Cell n → α := fun cell => by
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le cell.1.val) cell.1.isLt
    have hcard_pos : 0 < (lists cell).card := lt_of_lt_of_le hnpos (_hlists cell)
    exact Classical.choose (Finset.card_pos.mp hcard_pos)
  have hconf_sym : ∀ a b : Cell n, LatinConflict a b → LatinConflict b a := by
    intro a b h; unfold LatinConflict at h ⊢; rcases h with ⟨hne, hrc⟩
    exact ⟨fun hba => hne hba.symm, hrc.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
  have exists_good : ∀ k, k ≤ n * n →
      ∃ colored : Finset (Cell n), ∃ partialColor : Cell n → α,
        colored.card = k ∧ Good colored partialColor := by
    intro k; induction k with
    | zero => intro _; refine ⟨∅, arbitraryColor, by simp, ?_⟩; simp [Good]
    | succ k ih =>
      intro hk
      obtain ⟨colored, partialColor, hcard, hgood⟩ := ih (Nat.le_of_succ_le hk)
      change (∀ c ∈ colored, partialColor c ∈ lists c) ∧
        (∀ a ∈ colored, ∀ b ∈ colored, LatinConflict a b → partialColor a ≠ partialColor b) at hgood
      rcases hgood with ⟨hlist_colored, hproper_colored⟩
      have hlt : colored.card < n * n := by rw [hcard]; exact Nat.lt_of_succ_le hk
      obtain ⟨v, hvnot, c, hcin, havoid⟩ :=
        hextension colored partialColor hlt hlist_colored hproper_colored
      refine ⟨insert v colored, Function.update partialColor v c, ?_, ?_⟩
      · simpa [hcard, Nat.succ_eq_add_one] using Finset.card_insert_of_notMem hvnot
      · change (∀ x ∈ insert v colored,
            Function.update partialColor v c x ∈ lists x) ∧
          (∀ a ∈ insert v colored, ∀ b ∈ insert v colored,
            LatinConflict a b →
              Function.update partialColor v c a ≠ Function.update partialColor v c b)
        constructor
        · intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
          · rw [Function.update_self]; exact hcin
          · rw [Function.update_of_ne (fun h => hvnot (by rwa [← h]))]; exact hlist_colored x hx
        · intro a ha b hb hab
          rcases Finset.mem_insert.mp ha with rfl | ha <;>
            rcases Finset.mem_insert.mp hb with rfl | hb
          · exact absurd rfl hab.1
          · rw [Function.update_self, Function.update_of_ne (fun h => hvnot (by rwa [← h]))]
            exact havoid b hb hab
          · rw [Function.update_of_ne (fun h => hvnot (by rwa [← h])), Function.update_self]
            have ha' : a ∈ colored := by rcases Finset.mem_insert.mp ha with rfl | h; exact absurd rfl hab.1; exact h
            intro h; exact havoid a ha' (hconf_sym _ _ hab) h.symm
          · rw [Function.update_of_ne (fun h => hvnot (by rwa [← h])),
                 Function.update_of_ne (fun h => hvnot (by rwa [← h]))]
            exact hproper_colored a ha b hb hab
  obtain ⟨colored, color, hcard, hgood⟩ := exists_good (n * n) le_rfl
  change (∀ c ∈ colored, color c ∈ lists c) ∧
    (∀ a ∈ colored, ∀ b ∈ colored, LatinConflict a b → color a ≠ color b) at hgood
  rcases hgood with ⟨hlist_colored, hproper_colored⟩
  have huniv : colored = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [Cell, hcard])
  exact ⟨color, fun cell => hlist_colored cell (by rw [huniv]; exact Finset.mem_univ cell),
    fun a b hab => hproper_colored a (by rw [huniv]; exact Finset.mem_univ a)
      b (by rw [huniv]; exact Finset.mem_univ b) hab⟩

theorem chapter34 {n : ℕ} {α : Type*} {lists : Cell n → Finset α} {color : Cell n → α}
    (hlist : RespectsLists lists color) (hinj : RowColumnInjective color) :
    DinitzSolution lists color :=
  dinitzSolution_of_respectsLists_rowColumnInjective hlist hinj

end ProofsInTheBook.Chapter34
