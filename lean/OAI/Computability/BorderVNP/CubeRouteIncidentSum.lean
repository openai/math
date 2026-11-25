import OAI.Computability.BorderVNP.CubeRouteWrittenRecords
import OAI.Computability.BorderVNP.TransmissionLegCapacity

/-! # The exterior width charged to one native team by the compact routing table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RouteRecords

open Physical RoutingISA Finset
open Packing.Directory (Row)
open private atOrdinal from OAI.Computability.BorderVNP.CubeRouteWrittenRecords

variable {q a R : ℕ}

set_option maxHeartbeats 900000 in
/-- The actual compact ordinal charges each remote row to this team only if it
sends or receives that row. The outgoing data charge is taken in physical
directory order; shared and incoming charges are collected over its owned groups. -/
theorem incident_le (data : List Row) (owner : ℕ → Fin (R+1)) (blocks K h : ℕ)
    (D : LengthDeclaration a q) (group : Fin q → Fin (R+1)) (recvGroup : Fin data.length → Fin q)
    (matchOwner : ∀ i : Fin data.length, owner data[i.val].cell = group (recvGroup i))
    (team : Fin (R+1)) :
    (∑ i : Fin (data.length+q.choose 2), (combinedRow data owner blocks K h D group i.val).exteriorWidth team.val) ≤
      (data.map (fun r => if r.team = team.val then r.width else 0)).sum +
        ∑ x : Fin q, if group x = team then SharedRows.incident blocks K h D x +
          (∑ i : Fin data.length, if recvGroup i = x then data[i.val].width else 0) else 0 := by
  let sent (i : Fin data.length) := if data[i.val].team = team.val then data[i.val].width else 0
  let recv (x : Fin q) (i : Fin data.length) := if group x = team then
    if recvGroup i = x then data[i.val].width else 0 else 0
  let shared (x : Fin q) (p : Symbols q) := if group x = team then
    if x = p.val.1 ∨ x = p.val.2 then SharedRows.reserved blocks K h D p else 0 else 0
  have sends : (data.map (fun r => if r.team = team.val then r.width else 0)).sum = ∑ i, sent i := by
    conv_lhs => rw [← List.ofFn_get data,List.map_ofFn,List.sum_ofFn]
    rfl
  have chargeData (i : Fin data.length) : (dataRow owner data[i.val]).exteriorWidth team.val ≤ sent i+∑ x, recv x i := by
    have credit : (∑ x : Fin q, recv x i) = if group (recvGroup i) = team then data[i.val].width else 0 := by
      rw [sum_eq_single (recvGroup i)]
      · simp [recv]
      · intro x _ ne
        simp [recv,Ne.symm ne]
      · simp
    rw [credit]
    by_cases sender : data[i.val].team = team.val <;> by_cases receiver : group (recvGroup i) = team
    all_goals simp [dataRow,TableRow.exteriorWidth,sent,matchOwner,sender,receiver,Fin.val_inj]
    all_goals split_ifs <;> omega
  have chargeShared (p : Symbols q) : (sharedRow blocks K h D group p).exteriorWidth team.val ≤ ∑ x, shared x p := by
    unfold TableRow.exteriorWidth
    split
    next test =>
      have hit : group p.val.1 = team ∨ group p.val.2 = team := by simpa [sharedRow,Fin.val_inj] using test.2
      rcases hit with left | right
      · calc
          _ = shared p.val.1 p := by simp [sharedRow,shared,left]
          _ ≤ ∑ x, shared x p := single_le_sum (f := fun x => shared x p) (fun _ _ => Nat.zero_le _) (mem_univ _)
      · calc
          _ = shared p.val.2 p := by simp [sharedRow,shared,right]
          _ ≤ ∑ x, shared x p := single_le_sum (f := fun x => shared x p) (fun _ _ => Nat.zero_le _) (mem_univ _)
    · exact Nat.zero_le _
  let f (e : Fin data.length ⊕ Symbols q) :=
    (e.elim (fun i => dataRow owner data[i.val]) (sharedRow blocks K h D group)).exteriorWidth team.val
  calc
    _ = ∑ e, f e := ((ordinal data.length q).sum_comp _).symm.trans
      (sum_congr rfl fun e _ => congrArg (fun r : TableRow => r.exteriorWidth team.val) (atOrdinal ..))
    _ = (∑ i, (dataRow owner data[i.val]).exteriorWidth team.val) +
        ∑ p, (sharedRow blocks K h D group p).exteriorWidth team.val := Fintype.sum_sum_type f
    _ ≤ (∑ i, (sent i+(∑ x, recv x i))) + ∑ p, ∑ x, shared x p :=
      Nat.add_le_add (sum_le_sum fun i _ => chargeData i) (sum_le_sum fun p _ => chargeShared p)
    _ = (∑ i, sent i) + ∑ x, ((∑ p, shared x p) + ∑ i, recv x i) := by
      rw [sum_add_distrib,sum_comm (f := fun i x => recv x i),sum_comm (f := fun p x => shared x p),sum_add_distrib]
      omega
    _ = _ := by
      rw [sends]
      congr 1
      apply sum_congr rfl
      intro x _
      by_cases hit : group x = team <;> simp [shared,recv,SharedRows.incident,hit]

end Cube.RouteRecords

end BorderVNP
end Computability
end OAI
