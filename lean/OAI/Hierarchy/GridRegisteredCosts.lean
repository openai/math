import OAI.Hierarchy.TraceRegisteredRows
import OAI.Hierarchy.GridPinResourceFiber
import OAI.Hierarchy.TraceReceiverPublishedWork

namespace OAI
/-! # Work, input bits and directional pairs in the registered factor rows -/

namespace Hierarchy.TraceAdmission.Resources

open ThreeFlat Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM
open scoped BigOperators Classical

variable {W : ℕ} (p : Parameters ℕ) (dest : Fin p.lanes → Fin p.roots) (work : Fin p.roots → ℕ)

/-- Column zero is evaluator work, column one counts all original input bits,
and column two plus the direction counts pairs in that direction's original band. -/
def cost (v : Fin p.roots) (column : Fin (p.directions+2)) : ℕ :=
  Fin.cases (motive:=fun _ => ℕ) (work v) (fun j =>
    Fin.cases (motive:=fun _ => ℕ) (inputCount dest v p.cap p.pairSpan)
      (fun i => directionCount dest v p.band p.pairSpan i.val) j) column

@[simp] theorem cost_work (v : Fin p.roots) : cost p dest work v 0 = work v := rfl

@[simp] theorem cost_inputs (v : Fin p.roots) :
    cost p dest work v (0 : Fin (p.directions+1)).succ = inputCount dest v p.cap p.pairSpan := rfl

@[simp] theorem cost_direction (v : Fin p.roots) (i : Fin p.directions) :
    cost p dest work v i.succ.succ = directionCount dest v p.band p.pairSpan i.val := rfl

/-- The native resource table and the pure scheduler read exactly the same integer
at every column of every node, including the two scalar columns. -/
theorem Registered.cost_read {D dst : ℕ} {out : Memory W}
    (registered : Registered D dst p dest work out) (v : Fin p.roots) (j : Fin (p.directions+2)) :
    (out (dst+v.val*(p.directions+2)+j.val)).val = cost p dest work v j := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) j
  · simpa only [Fin.val_zero,Nat.add_zero,cost_work] using registered.charged v
  · simpa only [Fin.val_zero,Fin.val_succ,cost_inputs] using registered.inputs v
  · change (out (dst+v.val*(p.directions+2)+(i.val+1+1))).val = directionCount dest v p.band p.pairSpan i.val
    rw [show i.val+1+1=2+i.val by omega]
    exact registered.directions v i

theorem cost_input_fiber (origin : Fin p.cap→Fin p.roots) (bucket : Fin p.cap→Fin p.lanes)
    (pos : 0<p.pairSpan) (room : p.cap≤p.lanes*(2*p.pairSpan))
    (quotient : ∀ j, (bucket j).val=j.val/(2*p.pairSpan)) (owners : ∀ j, dest (bucket j)=origin j)
    (v : Fin p.roots) :
    cost p dest work v (0 : Fin (p.directions+1)).succ = (FactorPinIntervals.intervalBits origin v).length :=
  GridPinPublisher.inputLength_from_resource dest origin bucket pos room quotient owners v

/-- This form uses the terminal-site fiber appearing in the physical native
input bound, both before and after the true site's ordinal is chosen. -/
theorem ranked_inputs {Site : Type*} (idx : Site ≃ Fin p.roots) (route : Fin p.cap→Site)
    (bucket : Fin p.cap→Fin p.lanes) (pos : 0<p.pairSpan) (room : p.cap≤p.lanes*(2*p.pairSpan))
    (quotient : ∀ j, (bucket j).val=j.val/(2*p.pairSpan))
    (owners : ∀ j, dest (bucket j)=idx (route j)) (v : Fin p.roots) :
    inputCount dest v p.cap p.pairSpan = Nat.card {j : Fin p.cap // route j=idx.symm v} := by
  classical
  rw [GridPinPublisher.inputLength_from_resource dest (fun j=>idx (route j)) bucket pos room quotient owners,
    FactorPinIntervals.length_intervalBits,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp only [idx.eq_symm_apply.symm]

theorem cost_direction_fiber (v : Fin p.roots) (i : Fin p.directions)
    (pos : 0<p.pairSpan) (room : (i.val+1)*p.band≤p.lanes*p.pairSpan)
    (owner : ℕ→Fin p.roots)
    (same : ∀ x∈Finset.Ico (i.val*p.band) ((i.val+1)*p.band), ∀ q : Fin p.lanes,
      x/p.pairSpan=q.val → owner x=dest q) :
    cost p dest work v i.succ.succ =
      ((Finset.Ico (i.val*p.band) ((i.val+1)*p.band)).filter fun x => owner x=v).card :=
  directionCount_eq_card dest v p.band p.pairSpan i.val pos room owner same

/-- For the exterior rail order used by the native simulator, this is precisely
the per-factor accounting identity required by `FactorPinIntervals.scheduledProgram`. -/
theorem exterior_account {rails : ℕ} (total : rails=p.directions*p.band)
    (axis : Fin rails→Fin p.directions) (axisVal : ∀ e, (axis e).val=e.val/p.band)
    (rail : Fin rails ↪ Fin (p.cap/2)) (rank : ∀ e, (rail e).val=e.val)
    (origin : Fin p.cap→Fin p.roots) (bucket : Fin p.cap→Fin p.lanes)
    (quotient : ∀ j, (bucket j).val=j.val/(2*p.pairSpan)) (owners : ∀ j, dest (bucket j)=origin j)
    (spanPos : 0<p.pairSpan) (bandPos : 0<p.band) (room : rails≤p.lanes*p.pairSpan)
    (v : Fin p.roots) (i : Fin p.directions) :
    ((Finset.univ : Finset (Fin rails)).filter (fun e =>
      axis e=i ∧ origin (FactorPinIntervals.pairPorts rail (e,false))=v)).card =
      cost p dest work v i.succ.succ := by
  let port (e : Fin rails) := FactorPinIntervals.pairPorts rail (e,false)
  have portVal (e : Fin rails) : (port e).val=2*e.val := by simp [port,FactorPinIntervals.pairPorts,rank]
  let owner (x : ℕ) := if h : x<rails then origin (port ⟨x,h⟩) else v
  have inside : (i.val+1)*p.band≤rails := by
    rw [total]
    exact Nat.mul_le_mul_right _ i.isLt
  have mem (e : Fin rails) : e.val∈Finset.Ico (i.val*p.band) ((i.val+1)*p.band) ↔ axis e=i := by
    simp only [Finset.mem_Ico,←Nat.le_div_iff_mul_le bandPos,←Nat.div_lt_iff_lt_mul bandPos,←axisVal e]
    exact ⟨fun h => Fin.ext (by omega),fun eq => by rw [eq]; omega⟩
  rw [cost_direction_fiber p dest work v i spanPos (inside.trans room) owner ?_]
  · apply Finset.card_bij (fun e _ => e.val)
    · intro e he
      obtain ⟨d,atNode⟩ := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨(mem e).mpr d,by simpa only [owner,dite_eq_left e.isLt] using atNode⟩
    · intro e _ f _ eq
      exact Fin.ext eq
    · intro x hx
      obtain ⟨inIco,atNode⟩ := Finset.mem_filter.mp hx
      have hx := (Finset.mem_Ico.mp inIco).2.trans_le inside
      let e : Fin rails := ⟨x,hx⟩
      exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem e).mp inIco,
        by simpa only [owner,dite_eq_left hx] using atNode⟩,rfl⟩
  · intro x hx q eq
    have ix := (Finset.mem_Ico.mp hx).2.trans_le inside
    let e : Fin rails := ⟨x,ix⟩
    have b : bucket (port e)=q := by
      apply Fin.ext
      rw [quotient,portVal,Nat.mul_div_mul_left _ _ (by decide : 0<2)]
      exact eq
    simpa only [owner,dite_eq_left ix,←b] using (owners (port e)).symm

/-- Assigning one endpoint to every exterior pair injects each directional
contribution into the input length at the same node. -/
theorem direction_le_inputs (v : Fin p.roots) (i : Fin p.directions)
    (tape : 2*((i.val+1)*p.band)≤p.cap) :
    directionCount dest v p.band p.pairSpan i.val ≤ inputCount dest v p.cap p.pairSpan := by
  unfold directionCount inputCount rootSum
  apply Finset.sum_le_sum
  intro q _
  by_cases hv : dest q=v
  · simp only [ite_eq_left hv]
    unfold bandLength FactorPinIntervals.bucketLength
    calc
      _ ≤ min p.pairSpan ((i.val+1)*p.band-q.val*p.pairSpan) := Nat.sub_le ..
      _ ≤ min (2*p.pairSpan) (p.cap-q.val*(2*p.pairSpan)) := by
        apply min_le_min (by omega)
        rw [show q.val*(2*p.pairSpan)=2*(q.val*p.pairSpan) by ring]
        omega
  · simp only [ite_eq_right hv,le_refl]

theorem cost_bounded (cap : ℕ) (Wfit : ∀ v, work v≤cap)
    (inputs : ∀ v, inputCount dest v p.cap p.pairSpan≤cap)
    (external : 2*(p.directions*p.band)≤p.cap) (v : Fin p.roots) (j : Fin (p.directions+2)) :
    cost p dest work v j ≤ cap := by
  refine Fin.cases (Wfit v) (fun j => Fin.cases (inputs v) (fun i => ?_) j) j
  exact (direction_le_inputs p dest v i (le_trans
    (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right p.band i.isLt)) external)).trans (inputs v)

private theorem sum_finRange {N : ℕ} (f : Fin N→ℕ) :
    ((List.finRange N).map f).sum = ∑ i, f i := by
  simp only [List.finRange,List.map_ofFn,List.sum_ofFn,Function.comp_def]

/-- The exact inventories supplied to the tick and direction pigeonhole bounds
when factors are enumerated in the allocator's actual order. -/
theorem cost_inventory (inputRoom : p.cap≤p.lanes*(2*p.pairSpan))
    (railRoom : p.directions*p.band≤p.lanes*p.pairSpan) :
    (((List.finRange p.roots).map fun v => cost p dest work v 0).sum = ∑ v, work v) ∧
    (((List.finRange p.roots).map fun v => cost p dest work v (0 : Fin (p.directions+1)).succ).sum = p.cap) ∧
    ∀ i : Fin p.directions, ((List.finRange p.roots).map fun v => cost p dest work v i.succ.succ).sum = p.band := by
  refine ⟨sum_finRange work, ?_, ?_⟩
  · exact (sum_finRange _).trans (total_inputCount dest p.cap p.pairSpan inputRoom)
  · intro i
    exact (sum_finRange _).trans (total_directionCount dest p.band p.pairSpan i.val
      ((Nat.mul_le_mul_right _ i.isLt).trans railRoom))

/-- The work total uses the identical numbering and local charge used in
`Resources.registerNodes_selected`. -/
theorem selected_work_total {F : Type} [Field F] {d l : ℕ} {A : State d l}
    (r : Run F A) (h : r.plan.History) (C : r.Charges) (start : A.Site→ℕ) (unit : ℕ)
    (n : Fintype.card (r.plan.finish h).Site=p.roots) :
    let idx := indexEquiv r h n
    let W := fun v => unit*r.chargeAt h C start (idx.symm v)
    ((List.finRange p.roots).map fun v => cost p dest W v 0).sum = unit*r.rootTotal h C start := by
  intro idx W
  rw [sum_finRange]
  exact (idx.symm.sum_comp (fun v => unit*r.chargeAt h C start v)).trans
    (TraceDistribution.Physical.publishedWork_sum r h C start unit)


end Hierarchy.TraceAdmission.Resources

end OAI
