import OAI.Hierarchy.DescentDatedOrdinaryAny

namespace OAI
/-! Both physical matcher outputs precede the genuine rotation and remain available to the later counter. -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary
open DescentSIMDLookup ProtocolRAM
variable (a:Ordinary) (io:Operands) (floor «until» w:ℕ)
local notation "m" => a.matcher io.roster floor
local notation "rot" => a.rotationEnd io.roster floor

theorem match_banks (early:rot≤«until») (space:«until»<2^w) :
    (m).raw.base+(m).raw.size<2^w ∧ (m).layout.topology.Fits w «until» :=by
  have read:=a.packed_last io.roster floor
  have done:=(a.subphase_order io floor).2.2.2
  have rotate:a.flagEnd io.roster floor≤rot:=by
    unfold rotationEnd
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have top:(m).layout.topology.base+(m).layout.topology.size≤«until»:=
    read.1.trans ((Nat.le_add_right _ a.batch).trans (read.2.le.trans (done.trans (rotate.trans early))))
  have raw:(m).raw.base+(m).raw.size≤(m).layout.topology.base:=by
    change (m).raw.base+(m).raw.size≤(m).raw.base+(m).raw.size+_
    exact Nat.le_add_right ..
  exact ⟨(raw.trans ((Nat.le_add_right ..).trans top)).trans_lt space,
    Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (top.trans_lt space),top⟩

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary

end OAI
