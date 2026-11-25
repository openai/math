import OAI.Hierarchy.DescentPhysicalDateHistory

namespace OAI
/-! # Joining the originally billed flag/seed program to the ordered dated executions -/
namespace Hierarchy.DescentSixParty.Chronology.DateCode
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn
open scoped BigOperators
noncomputable section

theorem paid_original_boot {w:ℕ} (flag boot:Procedure w) (date:ℕ→ DateCode w)
    (flags ticks length word T fund c d:ℕ) (narrow:word≤ w)
    (init:((flags+7*DescentStaticWordColumn.names flag)+(ticks+7*DescentStaticWordColumn.names boot))*(w+1)*T≤ c*fund)
    (held:(∑i∈Finset.range length,(date i).tariff)*T≤ d*fund) :
    (flags+afterTicks ticks date length+7*(DescentStaticWordColumn.names flag+DescentStaticWordColumn.names (afterBoot boot date length)))*word*T≤
      (c+d)*fund:=by
  let first:=flags+7*DescentStaticWordColumn.names flag
  let booted:=ticks+7*DescentStaticWordColumn.names boot
  let dated:=afterTicks ticks date length+7*DescentStaticWordColumn.names (afterBoot boot date length)
  let rest:=∑i∈Finset.range length,(date i).tariff
  have split : dated*w=booted*w+rest:=boot_bill boot ticks length date
  have seed : ((first+booted)*w)*T≤ c*fund:=
    (Nat.mul_le_mul_right T (Nat.mul_le_mul_left _ (Nat.le_succ w))).trans init
  have receipt : ((first+dated)*w)*T=((first+booted)*w)*T+rest*T:=by
    calc
      _ = (first*w+dated*w)*T:=by rw [Nat.add_mul]
      _ = (first*w+(booted*w+rest))*T:=by rw [split]
      _ = _:=by ring
  have cost:(flags+afterTicks ticks date length+7*(DescentStaticWordColumn.names flag+DescentStaticWordColumn.names (afterBoot boot date length)))=first+dated:=by
    dsimp [first,dated]
    omega
  rw [cost]
  calc
    _ ≤ (first+dated)*w*T:=Nat.mul_le_mul_right T (Nat.mul_le_mul_left _ narrow)
    _ = _:=receipt
    _ ≤ c*fund+d*fund:=Nat.add_le_add seed held
    _ = _:= (Nat.add_mul ..).symm

end
end Hierarchy.DescentSixParty.Chronology.DateCode

end OAI
