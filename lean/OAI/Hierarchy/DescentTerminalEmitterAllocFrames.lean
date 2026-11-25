import OAI.Hierarchy.DescentTerminalEmitterAllocation

namespace OAI
/-! # Frame and size facts at the actual terminal read/write addresses -/
namespace Hierarchy.DescentTerminalEmitter.Allocation
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM ProtocolRAM
noncomputable section
variable (s:Shape) (i f base:ℕ) (src:Sources) (plane:DescentTerminalDataPlane.Layout)
    (ext:DescentTerminalDenseHeaderRAM.Layout) (blankFmt:ℕ)
local notation "E" => layout s i f base src plane ext blankFmt
local notation "a" => slab s i f
local notation "b" => region s i f base

theorem «protected» {x:ℕ} (low:x<base) (width:x<ext.rem.base) : Later E x := by
  constructor
  · exact width
  all_goals simp only [layout,header,book,route,leaf,region]
  all_goals omega

theorem previous (j:Fin 43) (upto:(src j).base+(src j).size≤base) (k:Fin (src j).size)
    (width:(src j).base+k.val<ext.rem.base) : Later E ((src j).base+k.val) := by
  apply «protected» s i f base src plane ext blankFmt _ width
  omega

theorem indices_live (j:Fin s.rows) : AfterNames E ((E).indices.output.base+j.val) ∧
    (E).indices.output.base+j.val<(E).formats.output.base := by
  have h:=reserve_fit s i f
  unfold reserve at h
  constructor
  · constructor <;> simp only [layout,header,book,route,leaf,region,Bool.false_eq_true,ite_false,
      Nat.zero_mul] <;> omega
  · change base+0*a+j.val<base+2*a;omega

theorem formats_live (j:Fin s.rows) : AfterNames E ((E).formats.output.base+j.val) := by
  have h:=reserve_fit s i f
  unfold reserve at h
  constructor <;> simp only [layout,header,book,route,leaf,region,ite_true] <;> omega

theorem gates_live (j:Fin s.rows) :
    (E).route.gate.base+3*j.val<(E).leaf.cells.base ∧ (E).route.gate.base+3*j.val<(E).scalar := by
  have h:=reserve_fit s i f
  unfold reserve at h
  change base+6*a+3*j.val<base+7*a ∧ base+6*a+3*j.val<base+9*a
  omega

theorem scalar_end : (E).scalar+s.pool≤endAt s i f base := by
  have h:=reserve_fit s i f
  unfold reserve at h
  change base+9*a+s.pool≤base+10*a
  omega

theorem sink_inside (fmt:Bool) : s.rows<(header s i f base src fmt 0 0).output.size := by
  have h:=reserve_fit s i f
  unfold reserve at h
  change s.rows<a
  omega

/-- Blanks go to the reserved row immediately after all purchased rows,
so repeated writes at a blank never change an actual scalar or route row. -/
theorem sink_separate (fmt:Bool) (shift blank:ℕ) (j:Fin s.rows) :
    (header s i f base src fmt shift blank).output.base+j.val≠(header s i f base src fmt shift blank).sink := by
  change (b (if fmt then 2 else 0)).base+j.val ≠ (b (if fmt then 2 else 0)).base+s.rows
  exact fun eqn => (Nat.ne_of_lt j.isLt) (Nat.add_left_cancel eqn)

theorem event_address : (E).leaf.event=src 40 := rfl
theorem aliases : (E).route.names=(E).book.names ∧ (E).leaf.occupancy=(E).leaf.cells := ⟨rfl,rfl⟩

end
end Hierarchy.DescentTerminalEmitter.Allocation

end OAI
