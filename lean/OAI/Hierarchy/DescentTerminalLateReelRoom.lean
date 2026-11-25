import OAI.Hierarchy.DescentTerminalFullAddress
import OAI.Hierarchy.DescentExteriorLateReel
import OAI.Hierarchy.DescentCalendarNumbers

namespace OAI
/-! # The actual final host directory already reserves the late matrix accumulator -/
namespace Hierarchy.DescentCompiler.AtomSchedule
noncomputable section

theorem age_le_hosts (S : AtomSchedule) (first : 0<S.initialSites)
    (growth : 2≤2^S.hostGain*S.radix) (i : ℕ) : i+1≤S.hostSize i := by
  induction i with
  | zero => simpa [hostSize] using (Nat.succ_le_of_lt first)
  | succ i ih =>
    have plus:=Nat.mul_le_mul ih growth
    change i+1+1≤S.initialSites*(2^S.hostGain*S.radix)^(i+1)
    rw [pow_succ,←Nat.mul_assoc]
    exact (by omega : i+1+1≤(i+1)*2).trans plus

end
end Hierarchy.DescentCompiler.AtomSchedule

namespace Hierarchy.DescentSixParty
open DescentCompiler
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem stage_age_le_hosts (t J f g reset M tail i : ℕ) (first : 0<M) :
    i+1≤(stageNumbers G t J f g reset M tail).hostSize i := by
  apply AtomSchedule.age_le_hosts _ first
  let c:=hostRate t reset
  let e:=capRate G t g
  let k:=groupBits t J c e (cutRate t f g)
  have ck : 1≤k:=by dsimp [k,groupBits];omega
  have radix : 2≤2^k:=by simpa using Nat.pow_le_pow_right (by decide : 0<2) ck
  change 2≤2^c*2^k
  have fixed : 1≤2^c:=Nat.two_pow_pos c
  simpa only [one_mul] using Nat.mul_le_mul fixed radix

end
end Hierarchy.DescentSixParty

namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalVertexFields DescentTerminalRowArena
open DescentExteriorMatrixUpdate ProtocolRAM
noncomputable section
variable {blocks : ℕ} (V : Home.Format) (S : Shape) (I : Input) (R : MaskAllocation.Channels blocks)

theorem late_gap (base age : ℕ) (sites : age≤S.sites) :
    base+age+1≤takeOff S I (afterMeter V S R base) := by
  let start:=afterMeter V S R base
  have left : base≤(meter V R base).base:=Nat.le_add_right ..
  have room : base+age+1≤ start:=by dsimp only [start,afterMeter];omega
  let a:=rowArena S I start
  have row : a.start≤a.finish:=Nat.le_add_right ..
  have lower : a.finish≤pageEnd S I start:=by
    change a.finish≤((a.finish+(page a).size)+(events a S.terminal.pool).size)
    omega
  exact room.trans ((show start≤pageEnd S I start from row.trans lower).trans (Nat.le_add_right ..))

theorem late_reel {w d age f origin base : ℕ} (P : Reel) (old : P.Room w d age f origin)
    (previous : origin≤base) (sites : age≤S.sites)
    (fit : takeOff S I (afterMeter V S R base)<2^w) :
    (P.late base).Room w d age base (takeOff S I (afterMeter V S R base)) :=
  P.late_room old previous (late_gap V S I R base age sites) fit

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
