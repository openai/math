import OAI.Hierarchy.DescentTerminalAddressBanks
import OAI.Hierarchy.DescentTerminalEmitterAllocFrames

namespace OAI
/-! # One pair of genuine literal words for the address/value scans at all three dates -/
namespace Hierarchy.DescentTerminalEmitter.Allocation
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM ProtocolRAM
open DescentTerminalHeaderScatter
open scoped Fin.CommRing
noncomputable section
variable {w : ℕ}

theorem parity_read {n:ℕ} (start:ℕ) (m:Memory w) (pos:0<w)
    (literal:∀j:Fin 2,m (start+j.val)=(j.val:Word w)) (row:Fin n) (j:Fin 2) :
    (parity start).read m ((field row j).val:Word w)=(j.val:Word w) := by
  have divides:2∣2^w := by obtain ⟨w',rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos);simp [pow_succ]
  change m (start+((2*row.val+j.val)%2^w)%2)=_
  rw [Nat.mod_mod_of_dvd _ divides]
  rw [Nat.mul_add_mod 2 row.val j.val,Nat.mod_eq_of_lt j.isLt]
  exact literal j

variable (s:Shape) (i f base:ℕ) (src:Sources) (plane:DescentTerminalDataPlane.Layout)
    (ext:DescentTerminalDenseHeaderRAM.Layout) (blankFmt:ℕ)
local notation "E" => layout s i f base src plane ext blankFmt

/-- Only two earlier memory words are used when building all three original
`Header.Literal` / leaf-stage constants over the entire physical terminal. -/
theorem installed_parity (m:Memory w) (room:Room s E w) (pos:0<w) (start:ℕ)
    (index:src 1=parity start) (format:src 13=parity start) (leafLanes:src 38=parity start)
    (initial:∀j:Fin 2,m (start+j.val)=(j.val:Word w))
    (survive:∀j:Fin 2,BeforeKey s E (start+j.val) ∧ AfterFlights s E (start+j.val)) :
    Static s E m := by
  have resultAt (j:Fin 2) : result s E m (start+j.val)=(j.val:Word w) :=
    (printed_before s E m room (survive j).1 (survive j).2).trans (initial j)
  have named (j:Fin 2) : AfterNames E (start+j.val) := by
    have before:=(survive j).2.later
    exact ⟨before.names,before.progress,before.gates,before.leaves,before.scalar⟩
  have idx (j:Fin 2) : indexed s E m (start+j.val)=(j.val:Word w) :=
    (after_index s E m room (named j) (survive j).2.later.formats).symm.trans (resultAt j)
  have outs (j:Fin 2) : external s E m (start+j.val)=(j.val:Word w) :=
    (Header.early (E).indices (external s E m) room.idx (survive j).2.later.indices).symm.trans (idx j)
  have routeRows (j:Fin 2) : routed s E m (start+j.val)=(j.val:Word w) :=
    (after_gate s E m room (survive j).2.later.leaves (survive j).2.later.scalar).symm.trans (resultAt j)
  constructor
  · intro row j
    change (src 1).read _ _=_
    rw [index]
    exact parity_read start _ pos outs row j
  · intro row j
    change (src 13).read _ _=_
    rw [format]
    exact parity_read start _ pos idx row j
  · intro row j
    change (src 38).read _ _=_
    rw [leafLanes]
    exact parity_read start _ pos routeRows row j

end
end Hierarchy.DescentTerminalEmitter.Allocation

end OAI
