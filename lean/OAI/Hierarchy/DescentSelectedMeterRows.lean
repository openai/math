import OAI.Hierarchy.DescentDatedMeter
import OAI.Hierarchy.DescentPublicMeterAny
import OAI.Hierarchy.DescentOrdinaryAfterMeter

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology
open DescentPacking.PackedMatch.Local.Stage Computability.VPVNP.BurstRAM
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε u : ℝ} {k i z D wire hist w : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he T c n target)

/-- The meter port and packed rows produced by the winning match at this date. -/
def MeterRows (a K : ℕ) (meter : Dated.Meter) (m : Memory w) : Prop :=
  ∃ port : MeterPort prior, MeterPort.Fits ticket port a w K ∧ MeterPort.Pins ticket port m ∧
    Dated.Meter.ofTicket (T:=T) port a=meter

variable {j z₀ D₀ : ℕ} {W₀ : MarkedWorld F d P bits}
    {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}

theorem MeterRows.advance {a K : ℕ} {meter : Dated.Meter} {m current : Memory w}
    (rows : MeterRows ticket a K meter m) (before : Path start prior) (held : before.Held a current)
    (keep : ∀i,i< meter.endAddr→current i=m i) :
    (before.ordinary ticket).Held a (meter.image current) :=by
  obtain ⟨port,fit,pins,rfl⟩:=rows
  have rate := ticket.sourceRate
  subst u
  have sameStage : T = prior.placement.stage := eq_of_heq ticket.placement
  cases sameStage
  have endAt : MeterPort.endAddr ticket port=(Dated.Meter.ofTicket (T:=prior.placement.stage) port a).endAddr := rfl
  have pins' := MeterPort.pins_low ticket port pins
    (fun i hi=>keep i (hi.trans_le (le_of_le_of_eq (MeterPort.pins_before_counter_end ticket port) endAt)))
  have issued:=(MeterPort.advance ticket port a before K current fit pins' held).2.1
  have same : MeterPort.image ticket port a current=(Dated.Meter.ofTicket (T:=prior.placement.stage) port a).image current := rfl
  exact same ▸ issued

end
end Hierarchy.DescentSixParty.Chronology

end OAI
