import OAI.Computability.BorderVNP.CubeRouteIncidentCapacity
import OAI.Computability.BorderVNP.CubeScatterTransmissionRealization
import OAI.Computability.BorderVNP.RoutingISATickBudget

/-! # Endpoint widths in the finite field processor's actual routing scan

The native scan consumes even a co-located row. A data row can be charged to
its sender's literal allocation or its receiving group. Each shared row can be
charged to the owning group of an incident symbol.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube Cube.Physical Cube.RouteRecords Transmission TeamContraction Finset Packing.Directory
open private atOrdinal from OAI.Computability.BorderVNP.CubeRouteWrittenRecords

/-- Number of data or shared bits processed by a team in one scheduled row. -/
def endpointWidth (r : TableRow) (team : ℕ) := if r.first=team ∨ r.second=team then r.width else 0

set_option maxHeartbeats 900000 in
theorem endpointWidths_le {n q R : ℕ} (data : List Row) (owner : ℕ → Fin (R+1)) (blocks K h : ℕ)
    (D : LengthDeclaration n q) (group : Fin q → Fin (R+1)) (recv : Fin data.length → Fin q)
    (matchOwner : ∀ i : Fin data.length, owner data[i.val].cell=group (recv i)) (u : Fin (R+1)) :
    (∑ i ∈ range (data.length+q.choose 2), endpointWidth (combinedRow data owner blocks K h D group i) u.val) ≤
      (data.map (fun r => if r.team=u.val then r.width else 0)).sum +
      ∑ x : Fin q, if group x=u then SharedRows.incident blocks K h D x+
        (∑ j : Fin data.length, if recv j=x then data[j.val].width else 0) else 0 := by
  let sent (j : Fin data.length) := if data[j.val].team=u.val then data[j.val].width else 0
  let received (j : Fin data.length) (x : Fin q) := if group x=u ∧ recv j=x then data[j.val].width else 0
  let shared (p : Symbols q) (x : Fin q) := if group x=u ∧ (x=p.val.1 ∨ x=p.val.2) then SharedRows.reserved blocks K h D p else 0
  have d (j : Fin data.length) : endpointWidth (dataRow owner data[j.val]) u.val ≤ sent j + ∑ x, received j x := by
    by_cases outgoing : data[j.val].team=u.val
    · simp [endpointWidth,dataRow,sent,outgoing]
    · by_cases incoming : group (recv j)=u
      · have here := single_le_sum (f:=received j) (fun _ _ => Nat.zero_le _) (mem_univ (recv j))
        simpa only [endpointWidth,dataRow,matchOwner,incoming,or_true,ite_true,sent,ite_eq_right outgoing,
          Nat.zero_add,received,true_and] using here
      · simp [endpointWidth,dataRow,matchOwner,Fin.val_inj,outgoing,incoming]
  have sh (p : Symbols q) : endpointWidth (sharedRow blocks K h D group p) u.val ≤ ∑ x, shared p x := by
    by_cases first : group p.val.1=u
    · have here := single_le_sum (f:=shared p) (fun _ _ => Nat.zero_le _) (mem_univ p.val.1)
      simpa [endpointWidth,sharedRow,first,shared] using here
    · by_cases second : group p.val.2=u
      · have here := single_le_sum (f:=shared p) (fun _ _ => Nat.zero_le _) (mem_univ p.val.2)
        simpa [endpointWidth,sharedRow,second,shared] using here
      · simp [endpointWidth,sharedRow,Fin.val_inj,first,second]
  let f (e : Fin data.length ⊕ Symbols q) := endpointWidth (e.elim (fun j => dataRow owner data[j.val]) (sharedRow blocks K h D group)) u.val
  have sends : (∑ j, sent j)=(data.map (fun r => if r.team=u.val then r.width else 0)).sum := by
    conv_rhs => rw [←List.ofFn_get data,List.map_ofFn,List.sum_ofFn]
    rfl
  rw [←Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ e, f e := ((ordinal data.length q).sum_comp _).symm.trans (sum_congr rfl (fun e _ =>
      congrArg (fun r => endpointWidth r u.val) (atOrdinal ..)))
    _ = _ := Fintype.sum_sum_type f
    _ ≤ (∑ j, (sent j+∑ x, received j x))+(∑ p, ∑ x, shared p x) :=
      Nat.add_le_add (sum_le_sum (fun j _ => d j)) (sum_le_sum (fun p _ => sh p))
    _ = _ := by
      rw [sum_add_distrib,sends,sum_comm (f:=received),sum_comm (f:=shared),Nat.add_assoc,←sum_add_distrib]
      congr 1
      apply sum_congr rfl
      intro x _
      by_cases own : group x=u <;> simp [shared,received,own,SharedRows.incident,Nat.add_comm]

/-- The genuine public routing table fits this team's outgoing literal quota
plus the shared and incoming volume allowed by the physical group budget. -/
theorem scheduled_endpointWidths {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig assigned : ℕ → ℕ}
    {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups} {A : Type*} [Fintype A]
    {label : Fin l.cells → Label (n+1) l.groups} {recv : A → Fin l.cells} {width : A → ℕ}
    (schedule : GroupWeights.ScheduleResult l teams orig assigned)
    (image : GroupWeights.PhysicalImage l orig blocks b K h D label recv width)
    (dir : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (order : Fin (dir.directory pp lp).length ≃ A)
    (sizes : ∀ j : Fin (dir.directory pp lp).length, (dir.directory pp lp)[j.val].width=width (order j))
    (owner : ℕ → Fin (teams.r+1)) (group : Fin l.groups → Fin (teams.r+1))
    (cells : ∀ j : Fin (dir.directory pp lp).length, owner (dir.directory pp lp)[j.val].cell=group (label (recv (order j)) D.1))
    (owners : ∀ x : Fin l.groups, assigned (teams.owners+x.val)=(group x).val)
    (procs : 0<dir.processors) (fields : 0<dir.fields) (block : 0<dir.block) (X : ℕ) (u : Fin (teams.r+1))
    (cap : TeamNative.unscale (assigned (teams.totals+u.val)) ≤ (X:ℚ)/256) :
    let data := dir.directory pp lp
    (∑ i ∈ range (data.length+l.groups.choose 2), endpointWidth (combinedRow data owner blocks K h D group i) u.val) ≤
      (dir.fields+1)*(dir.processors*dir.literal)+X/256 := by
  intro data
  apply (endpointWidths_le data owner blocks K h D group (fun j => label (recv (order j)) D.1) cells u).trans
  apply Nat.add_le_add (dir.populated_outgoing pp lp u.val procs fields block)
  simp_rw [incoming_compact data order label recv width sizes D.1]
  exact charge_le_teamLimit schedule image group owners u X cap

/-- Read back both endpoint numbers and the width of each row from the
concrete scheduler postimage passed to the finite transmission loop. -/
theorem returned_endpointWidths {R r lit k link inner n w : ℕ} {Edge : Type}
    {G : Wiring R r lit k link inner n Edge} {pin : Fin k → Bool} {ext : Exterior R r link → Bool}
    {L : Routing.WireLayout (R+1) r link} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {owner : ℕ → Fin (R+1)} {origin stride : ℕ} {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    (f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins) (u : Fin (R+1)) :
    (∑ i ∈ range f.table.count, ((H u).rows i).incident (H u).team)=
      ∑ i ∈ range f.table.count, endpointWidth (f.row i) u.val := by
  apply sum_congr rfl
  intro i hi
  obtain ⟨_,ha,hb,width,_⟩ := tableRange_fields (f.image u) f.allocated (f.records u) (mem_range.mp hi)
  rw [←f.ranges u] at ha hb width
  simp only [Range.incident,endpointWidth,←Fin.val_inj,(f.bank u).team,ha,hb,width,eq_comm]

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
