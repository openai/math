import OAI.Computability.VPVNP.PairTraversalSelectedOrder
import OAI.Computability.VPVNP.CompressorLevelCounts

/-!
# Descriptor storage along the compression schedule

The descriptor arena begins with the cursor input sites, followed by one row
for every output site of every selected elementary pass. The selected pass
origins identify those counts with the actual shrink and refresh outputs.
Neither pass increases the number of sites.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open NetworkKernel LocalHistory Compression CompressorRecords

variable {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}

open Classical in
private noncomputable def placementLayer {N : Network} (t : Term A N) (old : Order N.Site)
    (next : Order t.output.Site) : Layer :=
  ⟨next.length, fun i =>
    let children := old.restrict (fun u => next.entries i = t.place u)
    List.ofFn fun j => (old.entries.symm (children.entries j).val).val⟩

private noncomputable def placementLayers {N Y : Network} (c : TermChain A N Y)
    (orders : ChainOrders c) (initial : Order N.Site) : List Layer :=
  match c with
  | .done _ => []
  | .more t _ tail => placementLayer t initial orders.1 :: placementLayers tail orders.2 orders.1

private theorem stepLayers_ordered {N Y : Network} (c : TermChain A N Y) (r : ChainParsers κ c)
    (orders : ChainOrders c) (initial : Order N.Site) (h : OrderedChildren c r orders initial) :
    stepLayers c r orders initial = placementLayers c orders initial := by
  induction c with
  | done => rfl
  | more t data tail ih =>
    refine congrArg₂ List.cons ?_ (ih r.2 orders.2 orders.1 h.2)
    unfold stepLayer placementLayer
    congr 1
    funext i
    let v := orders.1.entries i
    exact congrArg (fun (s : Order (t.Preimage v)) =>
      List.ofFn fun j => (initial.entries.symm (s.entries j).val).val) (h.1 v)

open private castOrders from OAI.Computability.VPVNP.PairTraversalSelectedOrder
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels

omit [CommRing A] in
private theorem cast_placementLayers {N M Y : Network} (e : N = M) (c : TermChain A M Y)
    (orders : ChainOrders c) (initial : Order M.Site) :
    placementLayers (e.symm ▸ c : TermChain A N Y) (castOrders e c orders) (e.symm ▸ initial) =
      placementLayers c orders initial := by cases e; rfl

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable (f : B.Entry → A) (hf : B.IsSolution f)

/-- Read the actual placement of this scheduled term in increasing old-site
order for each output position. -/
noncomputable def levelLayer (v : SelectedLevel B f hf) : Layer :=
  placementLayer (v.pass.step.term v.term) (siteOrder v.input)
    ((v.pass.output_eq v.term).symm ▸ siteOrder (v.pass.next v.term))

theorem levelLayer_count (v : SelectedLevel B f hf) :
    (levelLayer B f hf v).count = v.outputSites := by
  change ((v.pass.output_eq v.term).symm ▸ siteOrder (v.pass.next v.term) :
    Order (v.pass.step.term v.term).output.Site).length = v.outputSites
  have h {N M : Network} (e : N = M) (s : Order M.Site) :
      (e.symm ▸ s : Order N.Site).length = s.length := by cases e; rfl
  rw [h (v.pass.output_eq v.term)]
  change (siteOrder (v.pass.next v.term)).length = Fintype.card (v.pass.next v.term).network.Site
  simpa only [Fintype.card_fin] using Fintype.card_congr (siteOrder (v.pass.next v.term)).entries

private theorem collect_placementLayers {a g b n : ℕ} {X : State a g} (E : StateExecution A b n X)
    (W : E.MapWitnesses f) (r : ExecutionReaders E W) (o : PassOrigins B f hf E)
    (data : E.Records) (z : E.Choices) :
    placementLayers (E.termChain data z) (branchOrders E data z) (siteOrder X) =
      (collectLevels B f hf E W r o z).map (levelLayer B f hf) := by
  induction E with
  | done => rfl
  | more p tail ih =>
    let c := (tail z.1).termChain (data.2 z.1) z.2
    let orders := branchOrders (tail z.1) (data.2 z.1) z.2
    let next := siteOrder (p.next z.1)
    let e := p.output_eq z.1
    refine congrArg₂ List.cons rfl ?_
    exact (cast_placementLayers e c orders next).trans
      (ih z.1 (W.2 z.1) (r.2 z.1) (o.2 z.1) (data.2 z.1) z.2)

variable {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
variable (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)

/-- Every row and every child identifier, in scan order, is determined by
the corresponding concrete level of the compressor. -/
theorem selectedLayers_eq_levels :
    selectedLayers B f hf T hT X z =
      leafLayer (siteOrder X) :: (executeLevels B f hf T hT X z).map (levelLayer B f hf) := by
  apply congrArg (List.cons (leafLayer (siteOrder X)))
  exact (stepLayers_ordered _ _ _ _ (selectedParsers_ordered B f hf T hT X z)).trans
    (collect_placementLayers B f hf _ _ _ _ _ _)

/-- The count in each actual layer agrees with the selected state's site count. -/
theorem selected_layer_counts :
    (selectedLayers B f hf T hT X z).map Layer.count =
      X.positions :: (executeLevels B f hf T hT X z).map SelectedLevel.outputSites := by
  simp only [selectedLayers_eq_levels, List.map_cons, leafLayer, List.map_map, Function.comp_def,
    levelLayer_count]
  congr 1
  change (siteOrder X).length = Fintype.card X.network.Site
  simpa only [Fintype.card_fin] using Fintype.card_congr (siteOrder X).entries

/-- Every layer, including the initial leaves and the intermediate shrink
and refresh layers, has at most as many sites as the input. -/
theorem selected_layer_count_le (L : Layer) (hL : L ∈ selectedLayers B f hf T hT X z) :
    L.count ≤ X.positions := by
  have hm := List.mem_map_of_mem (f := Layer.count) hL
  rw [selected_layer_counts] at hm
  rcases List.mem_cons.mp hm with h | h
  · exact h.le
  · obtain ⟨v, hv, he⟩ := List.mem_map.mp h
    exact he ▸ v.outputSites_le.trans (executeLevels_limits B f hf T hT X z v hv).1

/-- The leaf stage and at most one stage per elementary compression pass
bound the total number of rows reserved by Appendix E. -/
theorem selected_count_sum_le :
    ((selectedLayers B f hf T hT X z).map Layer.count).sum ≤
      ((S.steps + 1) * T + 1) * X.positions := by
  let sizes := (selectedLayers B f hf T hT X z).map Layer.count
  have hc : ∀ n ∈ sizes, n ≤ X.positions := by
    intro n hn
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hn
    exact selected_layer_count_le B f hf T hT X z L hL
  have hl : sizes.length ≤ (S.steps + 1) * T + 1 := by
    simp only [sizes, selected_layer_counts, List.length_cons, List.length_map]
    exact Nat.succ_le_succ (executeLevels_length B f hf T hT X z)
  exact (List.sum_le_length_nsmul sizes X.positions hc).trans (Nat.mul_le_mul_right _ hl)

/-- The number of words in the selected native descriptor arena, with its
two header words and fixed child-list capacity per row. -/
theorem selected_words_le_stages :
    words B.recordLimit (selectedLayers B f hf T hT X z) ≤
      (B.recordLimit + 2) * ((S.steps + 1) * T + 1) * X.positions := by
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (selected_count_sum_le B f hf T hT X z)

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
