import OAI.Hierarchy.DescentPrivateDonorActual
import OAI.Hierarchy.DescentNativePhaseInvoice

namespace OAI
/-! # The true private donor and its closing meter at one attained regular date -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentHostDegree DescentPackedPrivateSum DescentRawCablePanel DescentSIMDLookup
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist}

open DescentCompiler.TerminalScale DescentStaticWordColumn


namespace DonorVisit
open DescentCompiler DescentStaticWordColumn DescentPacking.PackedMatch.Local.Stage DescentCompiler.TerminalScale
variable {header h K p : ℕ} {ticket : OrdinaryLink source he T c n target}
    (r : DonorVisit ticket header h bw K p)

theorem native_bit_bill :
    ((r.install.seq r.venue).seq r.gather).wordInvoice+
      DateBill.bitTariff (MeterPort.program ticket r.port header bw) (MeterPort.ticks ticket r.port header) ≤ 7*r.bill :=by
  let d:=r.gather
  let cost:=MeterPort.price ticket r.port bw K
  let clock:=MeterPort.ticks ticket r.port header
  let code:=MeterPort.program ticket r.port header bw
  have paid : clock*bw ≤ cost:=MeterPort.ticks_price ticket r.port header r.fits
  have eqn : r.bill=(d.ticks*bw+names d.program*bw+cost+names code*bw+
      (r.install.ticks+names r.install.program)*bw)+(r.venue.ticks+names r.venue.program)*bw:=rfl
  rw [NativePhase.wordInvoice_seq,NativePhase.wordInvoice_seq,eqn]
  simp only [NativePhase.wordInvoice,DateBill.bitTariff]
  change (r.install.ticks+7*names r.install.program)*bw+(r.venue.ticks+7*names r.venue.program)*bw+
    (d.ticks+7*names d.program)*bw+(clock+7*names code)*bw≤_
  ring_nf at paid ⊢
  omega

/-- This quote is uniform for a chosen date, including dates with an incomplete ballot. -/
theorem actual_date {t J f g reset M frozen : ℕ}
    (schedule : S=stageNumbers G t J f g reset M frozen)
    (depth : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (blocks : 0 < S.radix) (hosts : 0 < S.hostSize i) (pages : 2^(h/2) ≤ S.hostSize i)
    (grain : ProtocolRAMPortScale.bitWidth (S.grainAt G.b p i) ≤ S.hostSize i) :
    let rates:=donorRates G t f g reset
    ((r.install.seq r.venue).seq r.gather).wordInvoice+
      DateBill.bitTariff (MeterPort.program ticket r.port header bw) (MeterPort.ticks ticket r.port header) ≤ S.hostSize i*h*(7*(2*K)*(1274+6*scale J rates.work))+
      S.hostSize i*(S.groupCount i*S.radix)*(7*(2*K)*(4*scale J rates.amount*(342+2*scale J rates.work))) :=by
  intro rates
  have pair:=selected_input_bounds ticket schedule depth rates.bounds
  have size:=r.dimensions
  have grad : r.grade ≤ scale J rates.work:=size.1.trans pair.1
  have amount : r.amount ≤ scale J rates.amount:=size.2.le.trans pair.2
  have upper:=r.billed blocks hosts pages grain
  apply r.native_bit_bill.trans
  calc
    7*r.bill ≤ 7*(S.hostSize i*h*((2*K)*(1274+6*scale J rates.work))+
      S.hostSize i*(S.groupCount i*S.radix)*((2*K)*(4*scale J rates.amount*(342+2*scale J rates.work)))):=
      Nat.mul_le_mul_left 7 (upper.trans (by gcongr))
    _=_:=by ring

end DonorVisit
end
end Hierarchy.DescentSixParty.Chronology

end OAI
