import OAI.Hierarchy.DescentPrivateCalendarAny

namespace OAI
/-! # Preserving the chosen donor while publishing the next ordinary state -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentSIMDLookup DescentHostDegree DescentPackedPrivateSum DescentRawCablePanel
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist w a K : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {first : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {old : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink old he T c n target) (port : MeterPort old)
local notation "J" => S.groupCount i*2^k*old.placement.cap
local notation "M" => port.groupsPerWord*(2^k*old.placement.cap)

namespace MeterPort
/-- One past the last packed donor row that the ordinary counter reads. -/
def pinEnd := port.base+1+port.hosts*chunks J M

theorem pins_low {m done : Memory w} (pins : Pins ticket port m)
    (keep : ∀x,x<pinEnd port→done x=m x) : Pins ticket port done := by
  intro p
  change done (port.base+1+(row port.hosts J M p).val)=_
  rw [keep _ (by
    unfold pinEnd
    exact Nat.add_lt_add_left (row port.hosts J M p).isLt _)]
  exact pins p

theorem pins_before_counter_end : pinEnd port ≤ endAddr ticket port := by
  let src:=DescentPackedPrivateSpace.source port.base port.hosts J M
  have bound : port.hosts*chunks J M<src.size:=(DescentPackedPrivateSpace.source_size port.base port.hosts J M).1
  change port.base+1+port.hosts*chunks J M≤
    port.base+1+src.size+src.size+_+1+_+_+_+_+2+1
  omega
end MeterPort

namespace MeterCalendar
variable {path : Path first old} (prior : MeterCalendar first a w path)
variable (measured suffix : NativePhase w) (original : Memory w)

/-- Insert the genuine successor publishers between the donor gather and the
private count. The operand and signed tables written there survive
the later meter write wherever they start at its upper boundary. -/
theorem ordinary_after (ready : (prior.ordinary ticket port measured).Ready K original)
    (total : (prior.ordinary ticket port measured).Total K)
    (runs : ∀m,suffix.Runs m)
    (keeps : ∀x,x<MeterPort.endAddr ticket port→
      suffix.image (measured.image (prior.memory original)) x=measured.image (prior.memory original) x) :
    let next:=prior.ordinary ticket port (measured.seq suffix)
    next.Ready K original ∧ next.Total K ∧
      ∀x,MeterPort.endAddr ticket port≤x→
        next.memory original x=suffix.image (measured.image (prior.memory original)) x := by
  intro next
  obtain ⟨past,ran,held,fit,pins⟩:=ready
  obtain ⟨pastTotal,allRuns,geometry⟩:=total
  have issued:=MeterPort.pins_before_counter_end ticket port
  have header : a<MeterPort.pinEnd port := by
    have low:=fit.before
    unfold MeterPort.pinEnd
    omega
  have read:=MeterPort.pins_low ticket port pins (fun x hx=>keeps x (hx.trans_le issued))
  have retained:=keeps a (header.trans_le issued)
  have combined : next.Ready K original := by
    exact ⟨past,measured.seq_runs suffix _ ran (runs _),retained.trans held,fit,read⟩
  refine ⟨combined,⟨pastTotal,fun m=>measured.seq_runs suffix m (allRuns m) (runs _),geometry⟩,?_⟩
  intro x hx
  obtain ⟨_,oldHeader,_⟩:=prior.run K original past
  have newHeader:=oldHeader.keep (retained.trans held)
  have frame:=(MeterPort.advance ticket port a path K _ fit read newHeader).2.2.2
  exact frame x (by omega) (Or.inr hx)
end MeterCalendar
end
end Hierarchy.DescentSixParty.Chronology

end OAI
