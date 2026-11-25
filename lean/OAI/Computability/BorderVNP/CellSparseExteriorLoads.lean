import OAI.Computability.BorderVNP.DiagonalExternalFragmentCables
import OAI.Computability.BorderVNP.CellTeamLiveDelivery
import OAI.Computability.BorderVNP.CellTeamGeometryCharge
import OAI.Computability.BorderVNP.CellSparseExteriorBatchRun
import OAI.Computability.QuantumFactoring.RawListRange

/-! # Actual per-team width of the native sparse cable and live-delivery stream -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open RoutingISA SparseExterior Packing.Directory Crossing Packing.CellAddresses BorderVNP.Cube Cube.Physical Cube.TeamRowClock
open private incidence from OAI.Computability.BorderVNP.CellTeamExteriorCharge
open scoped Classical

/-- Bit volume physically copied by the RLE encoder for a single list of nonempty intervals. -/
def activeWidth (ss : List Span) := (ss.map (fun s => s.bits.length)).sum

private def pay (cells : Finset ℕ) (q : Quad) := if q.cell∈cells then q.width else 0

private theorem count_selected (cells : Finset ℕ) (qs : List Quad) (data : ℕ → ℕ → Bool) :
    (∑ c ∈ cells, activeWidth (spans qs data c))=(qs.map (pay cells)).sum := by
  induction qs with
  | nil => simp [spans,activeWidth]
  | cons q qs ih =>
    have item (c : ℕ) : activeWidth (spans (q::qs) data c) =
        (if c=q.cell then q.width else 0)+activeWidth (spans qs data c) := by
      by_cases eq : q.cell=c
      · subst c; simp [spans,activeWidth,Quad.span]
      · simp [spans,activeWidth,Quad.span,eq,Ne.symm eq]
    simp only [item,Finset.sum_add_distrib,ih,List.map_cons,List.sum_cons,pay]
    simp

private def optPay (cells : Finset ℕ) : Option Quad → ℕ
  | none => 0
  | some q => pay cells q

private theorem filter_pay {α : Type*} (cells : Finset ℕ) (xs : List α) (f : α → Option Quad) :
    ((xs.filterMap f).map (pay cells)).sum = (xs.map (fun x => optPay cells (f x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases e : f x <;> simp [e,ih,optPay]

private theorem range_pay (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  rw [←ExactQuantumFactoring.ofFn_val_range,List.map_ofFn,List.sum_ofFn]
  rfl

variable {z C m n : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network z P bits) (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (l : HostScatter.Layout) (mem : ℕ → ℕ) (rect : CableRows N cell edgeID portID l mem)

include rect in
private theorem cable_charge (cells : Finset ℕ) (side : Bool) :
    (((List.range l.count).filterMap (cable l mem side)).map (pay cells)).sum =
      ∑ e : N.CrossingEdge cell, if (endpointCell N cell side e).val ∈ cells then N.width e.val else 0 := by
  rw [filter_pay,rect.count,range_pay]
  symm
  apply Fintype.sum_of_injective (Packing.CableTriples.wireOrd N cell edgeID) (Packing.CableTriples.wireOrd N cell edgeID).injective
  · intro i outside
    rw [rect.unused side i outside]
    rfl
  · intro e
    change _ = optPay cells (cable l mem side (edgeID e.val).val)
    rw [rect.crossing]
    by_cases pos : 0<N.width e.val
    · simp only [ite_eq_left pos,optPay,pay,actualQuad]
    · simp [Nat.eq_zero_of_not_pos pos,optPay]

private theorem live_charge (cells : Finset ℕ) (rows : List Row) (supplied base : ℕ → ℕ) :
    ((rows.filterMap (live supplied base)).map (pay cells)).sum ≤
      (rows.map (fun r => if r.cell∈cells then r.width else 0)).sum := by
  rw [filter_pay]
  apply List.sum_le_sum
  intro r _
  unfold live
  split <;> simp [optPay,pay]

include rect in
/-- A single real cell receives only its true crossing cable ends and the occupied
intervals among the rows delivered to that cell. -/
theorem cell_active_le (c : Fin C) (supplied : ℕ → ℕ) (rows : List Row) (data : ℕ → ℕ → Bool) :
    activeWidth (spans (stream l mem supplied rows) data c.val) ≤
      (∑ e : N.CrossingEdge cell, if endpointCell N cell false e=c then N.width e.val else 0)+
      (∑ e : N.CrossingEdge cell, if endpointCell N cell true e=c then N.width e.val else 0)+
      (rows.map (fun r => if r.cell=c.val then r.width else 0)).sum := by
  have sum := count_selected {c.val} (stream l mem supplied rows) data
  simp only [Finset.sum_singleton] at sum
  rw [sum]
  simp only [stream,List.map_append,List.sum_append]
  rw [cable_charge N cell edgeID portID l mem rect {c.val} false,cable_charge N cell edgeID portID l mem rect {c.val} true]
  simp only [Finset.mem_singleton,Fin.val_inj]
  apply Nat.add_le_add_left
  simpa only [Finset.mem_singleton] using live_charge {c.val} rows supplied (fun i => mem (l.cells+2*i+1))

/-- Directly sum the actual three-pass source stream over the assigned host cells.
The private metadata rows need not occupy one interval per original site. -/
theorem active_load {g : GroupWeights.Layout} {teams : TeamNative.Layout} {orig assigned : ℕ → ℕ}
    {dim blocks b K h m' : ℕ} {D : LengthDeclaration dim g.groups} {label : Fin g.cells → Label (dim+1) g.groups}
    {A : Type*} [Fintype A] {recv : A → Fin g.cells} {incoming : A → ℕ}
    {bits : P → ℕ} (N : Network z P bits) (cell : N.Site → Fin g.cells)
    (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n) (ord : N.CrossingEdge cell ≃ Fin m')
    (l : HostScatter.Layout) (mem supplied : ℕ → ℕ) (rows : List Row) (data : ℕ → ℕ → Bool)
    (rect : CableRows N cell edgeID portID l mem)
    (installed : RowLocations rows (Fin.val : Fin g.cells → ℕ) recv incoming)
    (schedule : GroupWeights.ScheduleResult g teams orig assigned)
    (image : GroupWeights.PhysicalImage g orig blocks b K h D label recv incoming) (team : Fin (teams.r+1)) (X : ℕ)
    (pass : TeamNative.unscale (assigned (teams.totals+team.val)) ≤ (X:ℚ)/256)
    (cap : ∀ pair, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
      (crossWidth N cell ∘ ord.symm) pair ≤ blocks*(h*b)) :
    let who := fun c : Fin g.cells => assigned (teams.owners+(label c D.1).val)
    assignedSum who team.val (fun c => activeWidth (spans (stream l mem supplied rows) data c.val)) ≤
      2*(1000000*X/256)+X := by
  intro who
  let selected := Finset.univ.filter (fun c : Fin g.cells => who c=team.val)
  let numeric := selected.image Fin.val
  have select (c : Fin g.cells) : c.val∈numeric ↔ who c=team.val := by
    change c.val ∈ selected.image Fin.val ↔ _
    constructor
    · intro h; obtain ⟨a,ha,e⟩ := Finset.mem_image.mp h
      exact Fin.ext e ▸ (Finset.mem_filter.mp ha).2
    · intro h; exact Finset.mem_image.mpr ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ c,h⟩,rfl⟩
  rw [TypedBatch.assigned_eq_sum]
  change (∑ c ∈ selected, activeWidth (spans (stream l mem supplied rows) data c.val)) ≤ _
  have imageSum : (∑ c ∈ numeric, activeWidth (spans (stream l mem supplied rows) data c)) =
      ∑ c ∈ selected, activeWidth (spans (stream l mem supplied rows) data c.val) :=
    Finset.sum_image (fun _ _ _ _ e => Fin.ext e)
  rw [←imageSum,count_selected]
  simp only [stream,List.map_append,List.sum_append]
  change ((((List.range l.count).filterMap (cable l mem false)).map (pay numeric)).sum +
    (((List.range l.count).filterMap (cable l mem true)).map (pay numeric)).sum) +
    ((rows.filterMap (live supplied fun c => mem (l.cells+2*c+1))).map (pay numeric)).sum ≤ _
  rw [cable_charge N cell edgeID portID l mem rect numeric false,cable_charge N cell edgeID portID l mem rect numeric true]
  simp_rw [select]
  let owner := fun u : Fin g.groups => assigned (teams.owners+u.val)
  have inc := incidence (blocks*(h*b)) D.1 (cablePair ord (crossSrc N cell) (crossDst N cell) label)
    (crossWidth N cell ∘ ord.symm) owner team.val cap
  have re (side : Bool) : (∑ e : N.CrossingEdge cell, if who (endpointCell N cell side e)=team.val then N.width e.val else 0) =
      ∑ i : Fin m', if who (endpointCell N cell side (ord.symm i))=team.val then N.width (ord.symm i).val else 0 :=
    (ord.symm.sum_comp _).symm
  rw [re false,re true]
  have ⟨del,raw⟩ := assigned_input_bounds schedule image team X pass
  apply Nat.add_le_add (inc.trans (Nat.mul_le_mul_left 2 raw))
  apply (live_charge numeric rows supplied _).trans
  have mapped := assignedSum_subitems installed.ordinal (fun i => recv (installed.ordinal i)) recv who team.val
    (fun i => (rows.get i).width) incoming (fun _ => rfl) (fun i => (installed.span i).ge)
  apply le_trans _ (mapped.trans del)
  conv_lhs => rw [←List.ofFn_get rows,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_le_sum
  intro i _
  have cellEq := installed.cell i
  change (recv (installed.ordinal i)).val=(rows.get i).cell at cellEq
  simp only [Function.comp_apply]
  rw [←cellEq]
  simp only [select,le_refl]

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
