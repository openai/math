import OAI.Computability.VPVNP.PairTraversalHistory

/-!
# Storing placement-fiber rows for the depth-first traversal

In Section 13 and Appendix E of *VP and VNP differ over every field*, each
position has a bounded row listing its immediate old positions. Here the
first two words of a row store its child-list address and count. The remaining
cells hold the actual older descriptor addresses in the reader's order.
Successive layers occupy disjoint intervals, and every row fits in the same
fixed stride, regardless of the wire widths or the chosen branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel Compression

variable {R : Type*}

/-- The actual numerical order of sites at the output of each selected term. -/
def ChainOrders {N Y : Network} : TermChain R N Y → Type
  | .done _ => PUnit
  | .more t _ tail => Order t.output.Site × ChainOrders tail

/-- Site numbers at each stage come from that state's base and lane coordinates. -/
noncomputable def branchOrders [CommSemiring R] {a g b n : ℕ} {X : State a g}
    (E : StateExecution R b n X) (data : E.Records) (z : E.Choices) :
    ChainOrders (E.termChain data z) := by
  induction E with
  | done => exact PUnit.unit
  | more p tail ih =>
    let e := p.output_eq z.1
    let c := (tail z.1).termChain (data.2 z.1) z.2
    have transport {N M Y : Network} (h : N = M) (c : TermChain R M Y) (r : ChainOrders c) :
        ChainOrders (h.symm ▸ c : TermChain R N Y) := by cases h; exact r
    exact ⟨e.symm ▸ siteOrder (p.next z.1), transport e c (ih z.1 (data.2 z.1) z.2)⟩

end PairSimulation.LocalHistory

namespace PairSimulation.TraversalRows

open BurstRAM BurstRAM.PrivateRAM NetworkKernel LocalHistory Compression
open scoped Fin.CommRing

/-- A layer in numerical site order. Child identifiers refer to the preceding
layer's site numbers, before translation to absolute word addresses. -/
structure Layer where
  /-- Number of site rows in a single DFS layer. -/
  count : ℕ
  /-- The list of old-site child ordinals for each row of this layer. -/
  ids : Fin count → List ℕ

/-- Absolute address of a site's DFS row given the layer base and its capacity-plus-two word
pitch. -/
def address (cap base id : ℕ) : ℕ := base + (cap + 2) * id

/-- Exclusive end of a layer's DFS rows, obtained from its site count and fixed row pitch. -/
def endPos (cap base : ℕ) (L : Layer) : ℕ := address cap base L.count

/-- Child identifiers have the exact order in which the local history reader
visits the placement fiber. -/
def stepLayer {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}
    {N : Network} {t : Term A N} (old : Order N.Site) (next : Order t.output.Site)
    (r : TermParsers κ t) : Layer :=
  ⟨next.length, fun i => List.ofFn fun j =>
    (old.entries.symm (((r.order.children (next.entries i)).entries j).val)).val⟩

/-- The initial cursor layer with one childless DFS row per site in the chosen initial order. -/
def leafLayer {I : Type} (initial : Order I) : Layer := ⟨initial.length, fun _ => []⟩

theorem stepLayer_ids_lt {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}
    {N : Network} {t : Term A N} (old : Order N.Site) (next : Order t.output.Site)
    (r : TermParsers κ t) (i : Fin next.length) :
    ∀ j ∈ (stepLayer old next r).ids i, j < old.length := by
  intro j hj
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hj
  exact (old.entries.symm (((r.order.children (next.entries i)).entries l).val)).isLt

variable {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}
variable {N Y : Network}

/-- The chronological output DFS layers of the selected term chain, using each pass's placement
fibers and site order. -/
def stepLayers {N Y : Network} (c : TermChain A N Y) (r : ChainParsers κ c) (ords : ChainOrders c)
    (initial : Order N.Site) : List Layer :=
  match c with
  | .done _ => []
  | .more _ _ tail => stepLayer initial ords.1 r.1 :: stepLayers tail r.2 ords.2 ords.1

/-- The complete selected row layout formed by prepending the initial cursor leaf layer to the
pass output layers. -/
def chainLayers (c : TermChain A N Y) (r : ChainParsers κ c) (ords : ChainOrders c)
    (initial : Order N.Site) : List Layer := leafLayer initial :: stepLayers c r ords initial

/-- The substep record limit bounds the number of stored words in every
child list, including on branches with parallel arcs or empty placement fibers. -/
theorem stepLayers_capacity (c : TermChain A N Y) (r : ChainParsers κ c) (ords : ChainOrders c)
    (initial : Order N.Site) {cap W : ℕ} (hb : c.Bounded cap W) :
    ∀ L ∈ stepLayers c r ords initial, ∀ i, (L.ids i).length ≤ cap := by
  classical
  induction c generalizing W with
  | done => simp [stepLayers]
  | more t data tail ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | ht
    · intro i
      let v := ords.1.entries i
      have hs := Fintype.card_congr (r.1.order.children v).entries
      rw [Fintype.card_fin] at hs
      change (List.ofFn _).length ≤ cap
      rw [List.length_ofFn]
      exact hs.trans_le ((Nat.le_add_left _ _).trans (hb.1 v))
    · exact ih r.2 ords.2 ords.1 hb.2.2 L ht

theorem chainLayers_capacity (c : TermChain A N Y) (r : ChainParsers κ c) (ords : ChainOrders c)
    (initial : Order N.Site) {cap W : ℕ} (hb : c.Bounded cap W) :
    ∀ L ∈ chainLayers c r ords initial, ∀ i, (L.ids i).length ≤ cap := by
  intro L hL
  rcases List.mem_cons.mp hL with rfl | ht
  · exact fun _ => Nat.zero_le _
  · exact stepLayers_capacity c r ords initial hb _ ht

variable {w : ℕ}

/-- The finite list of absolute child descriptor addresses. -/
def childWords (w cap previous : ℕ) (L : Layer) (i : Fin L.count) : List (Word w) :=
  (L.ids i).map fun j => (address cap previous j : Word w)

/-- Memory contains each site's row header and its child addresses at the designated
fixed-pitch location, with the header address representable as a word. -/
def Layer.Rows (L : Layer) (w : ℕ) (m : Memory w) (cap previous base : ℕ) : Prop :=
  ∀ i : Fin L.count, let node := address cap base i.val
    node < 2 ^ w ∧ DFS.Row m node (node + 2) (childWords w cap previous L i)

/-- Populate the header and live children. Unused reserved cells retain
their original contents. -/
private def cell (cap previous base : ℕ) (L : Layer) (i : Fin L.count) (other : Word w) :
    ℕ → Word w
  | 0 => ((address cap base i.val + 2 : ℕ) : Word w)
  | 1 => ((L.ids i).length : Word w)
  | j + 2 => ((childWords w cap previous L i)[j]?).getD other

/-- The memory image of one layer over arbitrary contents at other addresses. -/
def writeLayer (cap previous base : ℕ) (L : Layer) (m : Memory w) : Memory w := fun x =>
  if h : base ≤ x ∧ (x - base) / (cap + 2) < L.count then
    cell cap previous base L ⟨_, h.2⟩ (m x) ((x - base) % (cap + 2))
  else m x

private theorem layer_at (cap previous base : ℕ) (L : Layer) (m : Memory w) (i : Fin L.count)
    (slot : ℕ) (hs : slot < cap + 2) :
    writeLayer cap previous base L m (address cap base i.val + slot) =
      cell cap previous base L i (m (address cap base i.val + slot)) slot := by
  have hsub : address cap base i.val + slot - base = slot + (cap + 2) * i.val := by
    unfold address
    omega
  have hdiv : (slot + (cap + 2) * i.val) / (cap + 2) = i.val := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hs, Nat.zero_add]
  have hmod : (slot + (cap + 2) * i.val) % (cap + 2) = slot := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  have hbase : base ≤ address cap base i.val + slot := by unfold address; omega
  simp only [writeLayer, hsub, hdiv, hmod, hbase, i.isLt, and_self, ↓reduceDIte]

/-- A word belongs to a live header or payload of this layer. Reserved padding
and cells outside the layer are excluded. -/
def Layer.Live (L : Layer) (cap base x : ℕ) : Prop :=
  ∃ i : Fin L.count, address cap base i.val ≤ x ∧ x < address cap base i.val + 2 + (L.ids i).length

theorem writeLayer_unchanged (cap previous base : ℕ) (L : Layer) (m : Memory w) (x : ℕ)
    (h : ¬ L.Live cap base x) : writeLayer cap previous base L m x = m x := by
  unfold writeLayer
  split
  · rename_i hi
    let i : Fin L.count := ⟨_, hi.2⟩
    let off := (x - base) % (cap + 2)
    change cell cap previous base L i (m x) off = m x
    have hreconstruct : address cap base i.val + off = x := by
      change base + (cap + 2) * ((x - base) / (cap + 2)) + off = x
      have he := Nat.div_add_mod (x - base) (cap + 2)
      dsimp only [off] at *
      omega
    have hpad : 2 + (L.ids i).length ≤ off := by
      by_contra! hlt
      exact h ⟨i, by omega, by omega⟩
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ off)
    have hlen : (childWords w cap previous L i).length ≤ j := by
      simpa [childWords] using (show (L.ids i).length ≤ j by omega)
    rw [hj, Nat.add_comm 2 j]
    simp [cell, List.getElem?_eq_none hlen]
  · rfl

private theorem row_end_le (cap base : ℕ) (L : Layer) (i : Fin L.count) :
    address cap base i.val + (cap + 2) ≤ endPos cap base L := by
  have h := Nat.mul_le_mul_left (cap + 2) i.isLt
  rw [Nat.mul_succ] at h
  unfold endPos address
  omega

/-- A complete row, including the exclusive-end bound required by the
native child-copy loop. -/
theorem writeLayer_rows (cap previous base : ℕ) (L : Layer) (m : Memory w)
    (hc : ∀ i, (L.ids i).length ≤ cap) (fit : endPos cap base L < 2 ^ w) :
    L.Rows w (writeLayer cap previous base L m) cap previous base := by
  intro i
  let node := address cap base i.val
  have hrow : node + (cap + 2) ≤ endPos cap base L := row_end_le _ _ _ _
  have hlen : (childWords w cap previous L i).length ≤ cap := by simpa [childWords] using hc i
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
  · exact layer_at cap previous base L m i 0 (by omega)
  · simpa only [cell, childWords, List.length_map] using
      layer_at cap previous base L m i 1 (by omega)
  · intro j
    have hj := j.isLt
    have he := layer_at cap previous base L m i (j.val + 2) (by omega)
    change writeLayer cap previous base L m (node + 2 + j.val) = _
    rw [show node + 2 + j.val = address cap base i.val + (j.val + 2) by dsimp [node]; omega]
    simpa only [cell, List.getElem?_eq_getElem hj, Option.getD_some] using he

/-- Total row storage has a fixed number of words per position at each layer. -/
def words (cap : ℕ) (layers : List Layer) : ℕ := (cap + 2) * (layers.map Layer.count).sum

/-- Build all layers in increasing stage order, preserving older rows. -/
def build (cap previous base : ℕ) : List Layer → Memory w → Memory w
  | [], m => m
  | L :: ls, m => build cap base (endPos cap base L) ls (writeLayer cap previous base L m)

/-- Consecutive layers satisfy the row memory predicate with each new layer starting at the
exclusive end of the preceding layer. -/
def AllRows (w : ℕ) (m : Memory w) (cap previous base : ℕ) : List Layer → Prop
  | [] => True
  | L :: ls => L.Rows w m cap previous base ∧ AllRows w m cap base (endPos cap base L) ls

private theorem build_below (ls : List Layer) (cap previous base : ℕ) (m : Memory w)
    {x : ℕ} (hx : x < base) : build cap previous base ls m x = m x := by
  induction ls generalizing previous base m with
  | nil => rfl
  | cons L ls ih =>
    have he : x < endPos cap base L := hx.trans_le (Nat.le_add_right _ _)
    exact (ih base (endPos cap base L) _ he).trans (dite_eq_right (fun h => hx.not_ge h.1))

theorem build_rows (ls : List Layer) (cap previous base : ℕ) (m : Memory w)
    (hc : ∀ L ∈ ls, ∀ i, (L.ids i).length ≤ cap) (fit : base + words cap ls < 2 ^ w) :
    AllRows w (build cap previous base ls m) cap previous base ls := by
  induction ls generalizing previous base m with
  | nil => trivial
  | cons L ls ih =>
    let old := writeLayer cap previous base L m
    let next := endPos cap base L
    have hf : next + words cap ls < 2 ^ w := by simpa [next, endPos, address, words, Nat.mul_add,
      Nat.add_assoc] using fit
    have hcap i := hc L List.mem_cons_self i
    have hgood := writeLayer_rows cap previous base L m hcap ((Nat.le_add_right _ _).trans_lt hf)
    refine ⟨?_, ih base next old (fun L hL => hc L (List.mem_cons_of_mem _ hL)) hf⟩
    intro i
    let node := address cap base i.val
    have he : node + (cap + 2) ≤ next := row_end_le cap base L i
    obtain ⟨hn, hn1, hs, h0, h1, hj⟩ := hgood i
    refine ⟨hn, hn1, hs, ?_, ?_, ?_⟩
    · exact (build_below ls cap base next old (by omega : node < next)).trans h0
    · exact (build_below ls cap base next old (by omega : node + 1 < next)).trans h1
    · intro j
      have hlen : (childWords w cap previous L i).length ≤ cap := by simpa [childWords] using hcap i
      have hj' := j.isLt
      exact (build_below ls cap base next old (by omega : node + 2 + j.val < next)).trans (hj j)

/-- Base pointer and child-list pointer of a site in a specified layer. -/
def sitePointers {I : Type} (cap base : ℕ) (ord : Order I) (v : I) : ℕ × ℕ :=
  let node := address cap base (ord.entries.symm v).val
  (node, node + 2)

/-- Pointers to every output site of a selected term. The argument `base` is
where the first output layer starts, immediately after the input layer. -/
def chainPointers (cap : ℕ) {N Y : Network} (c : TermChain A N Y) (ords : ChainOrders c)
    (base : ℕ) : RowPointers c :=
  match c with
  | .done _ => PUnit.unit
  | .more _ _ tail => ⟨sitePointers cap base ords.1,
    chainPointers cap tail ords.2 (address cap base ords.1.length)⟩

/-- The table representation agrees with the descriptor row read by the native
traversal, including the ordering of the children. -/
theorem chainPointers_rowsAt (c : TermChain A N Y) (r : ChainParsers κ c) (ords : ChainOrders c)
    (initial : Order N.Site) (cap previous base : ℕ) (m : Memory w)
    (hrows : AllRows w m cap previous base (stepLayers c r ords initial)) :
    rowsAt c r (chainPointers cap c ords base) m
      (fun v => (sitePointers cap previous initial v).1) := by
  induction c generalizing previous base with
  | done => trivial
  | more t data tail ih =>
    refine ⟨fun v => ?_, ih r.2 ords.2 ords.1 base (address cap base ords.1.length) hrows.2⟩
    obtain ⟨i, rfl⟩ := ords.1.entries.surjective v
    have hv := hrows.1 i
    simpa only [chainPointers, sitePointers, childWords, stepLayer, List.map_ofFn,
      Function.comp_def,
      Equiv.symm_apply_apply] using hv

/-- Initial leaf headers and all later descriptors are simultaneously present
in the same memory, built on any initial contents. -/
theorem chain_memory_rows (c : TermChain A N Y) (r : ChainParsers κ c) (ords : ChainOrders c)
    (initial : Order N.Site) (cap base : ℕ) (m : Memory w) {W : ℕ} (hb : c.Bounded cap W)
    (fit : base + words cap (chainLayers c r ords initial) < 2 ^ w) :
    let image := build cap base base (chainLayers c r ords initial) m
    let leaf := sitePointers cap base initial
    (∀ v, (leaf v).1 < 2 ^ w ∧ DFS.Row image (leaf v).1 (leaf v).2 []) ∧
      rowsAt c r (chainPointers cap c ords (address cap base initial.length)) image
        (fun v => (leaf v).1) := by
  have hr := build_rows (chainLayers c r ords initial) cap base base m
    (chainLayers_capacity c r ords initial hb) fit
  exact ⟨fun v => hr.1 (initial.entries.symm v), chainPointers_rowsAt c r ords initial _ _ _ _ hr.2⟩

/-- Building the descriptor region leaves the rest of memory available to
other pair-simulation phases. -/
theorem build_outside (ls : List Layer) (cap previous base : ℕ) (m : Memory w) (x : ℕ)
    (hx : x < base ∨ base + words cap ls ≤ x) : build cap previous base ls m x = m x := by
  rcases hx with hx | hx
  · exact build_below _ _ _ _ _ hx
  · induction ls generalizing previous base m with
    | nil => rfl
    | cons L ls ih =>
      have he : endPos cap base L + words cap ls ≤ x := by
        simpa [endPos, address, words, Nat.mul_add, Nat.add_assoc] using hx
      have he' : endPos cap base L ≤ x := (Nat.le_add_right _ _).trans he
      have hdiv : L.count ≤ (x - base) / (cap + 2) := by
        apply (Nat.le_div_iff_mul_le (by omega)).mpr
        rw [Nat.mul_comm]
        unfold endPos address at he'
        omega
      exact (ih base (endPos cap base L) _ he).trans (dite_eq_right (fun h => hdiv.not_gt h.2))

omit [CommRing A] in
private theorem count_le_push {t : Term A N} (data : t.output.Site → SiteRecords)
    (counts : N.Site → ℕ) : Fintype.card t.output.Site + ∑ u, counts u ≤
      ∑ v, t.pushHistorySize data counts v := by
  classical
  let e : ((v : t.output.Site) × t.Preimage v) ≃ N.Site :=
    { toFun := fun p => p.2.val
      invFun := fun u => ⟨t.place u, ⟨u, rfl⟩⟩
      left_inv := fun ⟨v, ⟨u, h⟩⟩ => by cases h; rfl
      right_inv := fun _ => rfl }
  have hsum : ∑ v, ∑ u : t.Preimage v, counts u.val = ∑ u, counts u := by
    rw [← Fintype.sum_sigma' (fun v (u : t.Preimage v) => counts u.val)]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [show (∑ v, t.pushHistorySize data counts v) =
    (∑ v, (data v).count) + ∑ v, ∑ u : t.Preimage v, counts u.val by
      simp only [Term.pushHistorySize, Finset.sum_add_distrib], hsum]
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
    show 1 ≤ (data v).count by unfold SiteRecords.count; omega)
  simpa using Nat.add_le_add_right hc (∑ u, counts u)

/-- Every old position is assigned to exactly one successor. Thus the number
of rows, summed over the levels, is at most the total history size across the
final positions. This gives a word bound without inspecting intermediate sites. -/
theorem count_stepLayers_le (c : TermChain A N Y) (r : ChainParsers κ c) (ords : ChainOrders c)
    (initial : Order N.Site) (counts : N.Site → ℕ) :
    ((stepLayers c r ords initial).map Layer.count).sum + ∑ u, counts u ≤
      ∑ v, c.occurrences counts v := by
  classical
  induction c with
  | done => simp [stepLayers, TermChain.occurrences]
  | more t data tail ih =>
    have ho : ords.1.length = Fintype.card t.output.Site := by
      simpa only [Fintype.card_fin] using Fintype.card_congr ords.1.entries
    have h := ih r.2 ords.2 ords.1 (t.pushHistorySize data counts)
    have hp := count_le_push (t := t) data counts
    simp only [stepLayers, stepLayer, List.map_cons, List.sum_cons, TermChain.occurrences, ho]
    omega

section Selected

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates) (f : B.Entry → A)
variable (hf : B.IsSolution f) {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
variable (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)

/-- Exact row counts and old IDs determined by an admissible branch of the
actual compressor. The site numbers of every intermediate state are used. -/
noncomputable def selectedLayers : List Layer :=
  let E := B.execute f hf T hT X
  let data := B.records f hf T hT X
  chainLayers (E.termChain data z) (selectedParsers B f hf T hT X z) (branchOrders E data z)
    (siteOrder X)

/-- The selected descriptor region fits in the product of the fixed stride,
final order and history allowance. This gives a sufficient address-space test
without enumerating the rows. -/
theorem selected_words_le :
    words B.recordLimit (selectedLayers B f hf T hT X z) ≤
      (B.recordLimit + 2) * ((B.execute f hf T hT X).finalState z).positions *
        B.growthConstant ^ T := by
  let E := B.execute f hf T hT X
  let data := B.records f hf T hT X
  let c := E.termChain data z
  let r := selectedParsers B f hf T hT X z
  let ords := branchOrders E data z
  let initial := siteOrder X
  have hi : initial.length = Fintype.card X.network.Site := by
    simpa only [Fintype.card_fin] using Fintype.card_congr initial.entries
  have h₁ := count_stepLayers_le c r ords initial (fun _ => 1)
  have h₂ := Finset.sum_le_sum (s := Finset.univ)
    (fun v _ => (B.branch_bounds f hf T hT X z).2.2.2.1 v)
  change (B.recordLimit + 2) *
    (initial.length + ((stepLayers c r ords initial).map Layer.count).sum) ≤ _
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  rw [hi, Nat.add_comm]
  have hsum : ((stepLayers c r ords initial).map Layer.count).sum + Fintype.card X.network.Site ≤
      ∑ v, c.occurrences (fun _ => 1) v := by simpa using h₁
  have heq : Fintype.card (E.finalState z).network.Site = (E.finalState z).positions := rfl
  rw [← heq]
  exact hsum.trans (by simpa [c, E, data] using h₂)

/-- In the memory constructed for this branch the native DFS reads precisely
the actual placement tree. No hypotheses about the contents of headers or
child lists are required. -/
theorem selected_memory_traversal (base : ℕ) (m : Memory w)
    (fit : base + words B.recordLimit (selectedLayers B f hf T hT X z) < 2 ^ w) :
    let E := B.execute f hf T hT X
    let data := B.records f hf T hT X
    let c := E.termChain data z
    let ptr := chainPointers B.recordLimit c (branchOrders E data z)
      (address B.recordLimit base (siteOrder X).length)
    let leaves := sitePointers B.recordLimit base (siteOrder X)
    let trees := chainTrees c (selectedParsers B f hf T hT X z) ptr (fun v => leafTree (leaves v))
    let image := build B.recordLimit base base (selectedLayers B f hf T hT X z) m
    ∀ v, ∃ es, DFS.Visits image (B.growthConstant ^ T) [((trees v).address : Word w)]
      ((trees v).preorder.map (fun n : ℕ => (n : Word w))) es ∧
      countProbes es < 3 * c.occurrences (fun _ => 1) v ∧
      es.length ≤ 15 * c.occurrences (fun _ => 1) v + 1 := by
  let E := B.execute f hf T hT X
  let data := B.records f hf T hT X
  have hbound := Procedure.repeat_recordBounds (B.recordBounds f hf) _ T lanes
    (Nat.add_sub_of_le hT).symm X
  have hb := E.termChain_bounded data hbound.1 z
  have hr := chain_memory_rows (E.termChain data z) (selectedParsers B f hf T hT X z)
    (branchOrders E data z) (siteOrder X) B.recordLimit base m hb fit
  exact selectedTraversal B f hf T hT X z _ _ _ hr.1 hr.2

end Selected

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
