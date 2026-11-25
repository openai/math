import OAI.Hierarchy.DescentTerminalEarnedRates
import OAI.Hierarchy.DescentTerminalPhysicalFieldCount
import OAI.Hierarchy.DescentTerminalFullAddress

namespace OAI
/-! # An absolute marginal address bound for the realized terminal suffix -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalEmitter.Compact DescentTerminalVertexFields
open scoped BigOperators
noncomputable section

theorem EarnedCounts.end_le {h E : ℕ} {S : Shape} {I : Input} (paid : EarnedCounts h S I)
    (base : ℕ) (page : 2^(h/2)≤E) (sites : S.sites≤E) (pool : S.terminal.pool≤E)
    (raw : S.terminal.plane.rawRows≤E) (publicRows : S.terminal.plane.publicRows≤E)
    (widths : S.terminal.plane.headerRows≤E) : endAddress S I base≤base+2048*E :=by
  have pos : 0<E:=(Nat.two_pow_pos _).trans_le page
  have literal : (∑j,need (I.sources j))≤43*(2^(h/2)+4*S.terminal.pool):=calc
    _ ≤ ∑_:Fin 43,(2^(h/2)+4*S.terminal.pool) := Finset.sum_le_sum (fun j _=>paid.literal j)
    _ = _ := by simp
  have bill:=address_bill S I base paid.profile
  rw [paid.indices,paid.formats,paid.paid,paid.leaves,paid.packets] at bill
  omega

theorem EarnedCounts.last_le {h E blocks : ℕ} {S : Shape} {I : Input} (paid : EarnedCounts h S I)
    (V : Home.Format) (R : MaskAllocation.Channels blocks) (start : ℕ)
    (page : 2^h≤E) (fields : fieldSum V blocks≤h) (blockCount : blocks≤E)
    (sites : S.sites≤E) (pool : S.terminal.pool≤E) (raw : S.terminal.plane.rawRows≤E)
    (publicRows : S.terminal.plane.publicRows≤E) (widths : S.terminal.plane.headerRows≤E) :
    last V S I R start≤ start+4096*E :=by
  have pos : 0<E:=(Nat.two_pow_pos _).trans_le page
  have cap : cohortSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
      (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)≤E:=by
    unfold cohortSize
    rw [Finset.prod_pow_eq_pow_sum]
    exact (Nat.pow_le_pow_right (by decide : 0<2) fields).trans page
  have meters:=meter_size V S R start
  unfold channels at meters
  have rest:=paid.end_le (afterMeter V S R start)
    ((Nat.pow_le_pow_right (by decide : 0<2) (Nat.div_le_self h 2)).trans page) sites pool raw publicRows widths
  change endAddress S I (afterMeter V S R start)≤_
  omega

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
