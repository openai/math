import OAI.Hierarchy.DescentTerminalAddressBanks
import OAI.Hierarchy.DescentTerminalEmitterSpace
import OAI.Hierarchy.DescentTerminalEmittedShelfReads
import OAI.Hierarchy.DescentTerminalEmittedAdmission
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Actual terminal RAM allocation after the two genuine flight/width results -/
namespace Hierarchy.DescentTerminalEmitter.Allocation
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalHeaderScatter
noncomputable section

variable (s:Shape) (i f base:ℕ) (src:Sources)
local notation "b" => region s i f base


variable {w:ℕ} (below:∀j,(src j).base+(src j).size≤base) (room:endAt s i f base<2^w)

include below room in
theorem input_fits (j:Fin 43) (t:ℕ) : (src j).Fits w (b t).base := by
  have lo:=below j
  have bound:=room
  unfold endAt at bound
  refine ⟨pow_pos (by decide) _,?_,?_⟩
  · omega
  · change _≤base+t*slab s i f
    omega

include room in
theorem fits (j t:ℕ) (order:j<t) : (b j).Fits w (b t).base := by
  have lim:=room
  unfold endAt at lim
  have pos:0<slab s i f:=pow_pos (by decide) _
  have slots:(j+1)*slab s i f≤t*slab s i f:=Nat.mul_le_mul_right _ order
  rw [Nat.add_mul,one_mul] at slots
  change 0<slab s i f ∧ slab s i f<2^w ∧ base+j*slab s i f+slab s i f≤base+t*slab s i f
  omega

include below room in
private theorem header_room (fmt:Bool) (shift blank:ℕ) : (header s i f base src fmt shift blank).Room w := by
  have big:=reserve_fit s i f
  unfold reserve at big
  have budget:=room
  unfold endAt at budget
  cases fmt
  all_goals
    constructor
    · exact fits s i f base room _ _ (by decide)
    · apply input_fits s i f base src below room
    · simp only [header,legs,DescentTerminalScatterChip.put,DescentTerminalScatterChip.dest,
        DescentTerminalScatterChip.target,DescentTerminalScatterChip.datum,DescentTerminalScatterChip.source,
        DescentTerminalScatterChip.group,DescentTerminalScatterChip.event,DescentTerminalScatterChip.chunk,
        DescentTerminalScatterChip.live,stage,DescentTerminalHeaderScatter.bounded,Expr.Fits,
        Bool.false_eq_true,ite_false,ite_true]
      repeat' first | apply input_fits s i f base src below room | constructor
    · change s.rows≤ slab s i f
      omega
  · change base+1*slab s i f+2*i<2^w
    omega
  · change base+3*slab s i f+2*f<2^w
    omega

include below room in
theorem inner_room (plane:DescentTerminalDataPlane.Layout) (ext:DescentTerminalDenseHeaderRAM.Layout) (blankFmt:ℕ)
    (flights:DescentTerminalDataPlane.Room s.plane plane w) (widths:DescentTerminalDenseHeaderRAM.Fits ext w s.plane.headerRows) :
    Room s (layout s i f base src plane ext blankFmt) w := by
  have big:=reserve_fit s i f
  unfold reserve at big
  have budget:=room
  unfold endAt at budget
  constructor
  · exact flights
  · exact widths
  · exact header_room s i f base src below room false _ _
  · exact header_room s i f base src below room true _ _
  · simp only [layout,book,DescentTerminalLocalPortBook.Gather.load,DescentTerminalLocalPortBook.Gather.raw,Expr.Fits]
    repeat' first | apply input_fits s i f base src below room | constructor
  · change base+4*slab s i f+s.rows<2^w;omega
  · constructor
    · intro x hx
      change x∈[b 4,src 32,src 33,src 34,src 35,src 36] at hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
      · exact fits s i f base room _ _ (by decide)
      all_goals apply input_fits s i f base src below room
    · exact fits s i f base room 5 6 (by decide)
    · change s.rows≤ slab s i f;omega
    · change base+6*slab s i f+3*s.rows<2^w;omega
  · exact fits s i f base room 7 8 (by decide)
  · change s.pool+1≤ slab s i f;omega
  · exact input_fits s i f base src below room 38 7
  · simp only [layout,leaf,DescentTerminalLeafFold.row,DescentTerminalLeafFold.low,DescentTerminalLeafFold.high,
      DescentTerminalLeafFold.address,DescentTerminalHeaderScatter.bounded,stage,Expr.Fits]
    repeat' first | apply input_fits s i f base src below room | constructor
  · simp only [layout,leaf,DescentTerminalLeafFold.lookup,Expr.Fits]
    repeat' first | exact fits s i f base room 7 9 (by decide) | apply input_fits s i f base src below room | constructor
  · change base+8*slab s i f+2*s.leaves<2^w;omega
  · change base+9*slab s i f+s.pool<2^w;omega

end
end Hierarchy.DescentTerminalEmitter.Allocation

end OAI
