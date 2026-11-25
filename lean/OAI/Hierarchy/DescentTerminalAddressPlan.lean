import OAI.Hierarchy.DescentTerminalAddressLayout
import OAI.Hierarchy.DescentTerminalEmitterCompact
import OAI.Hierarchy.DescentTerminalDirectoryArena
import OAI.Hierarchy.DescentTerminalAddressInput
import OAI.Hierarchy.DescentDatedEmitterBook
import OAI.Hierarchy.DescentTerminalEmitterFront
import OAI.Hierarchy.DescentTerminalMaskReady
import OAI.Hierarchy.DescentTerminalHomeProgram

namespace OAI
/-! # Literal shared addresses for the complete metered terminal suffix -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalRowArena DescentTerminalVertexFields
noncomputable section

variable (S:Shape) (I:Input) (base:ℕ)

local notation "A" => rowArena S I base
local notation "planeS" => S.terminal.plane
local notation "origin" => takeOff S I base
local notation "flightEnd" => DescentTerminalDataPlane.Arena.finish planeS origin
local notation "src0" => DescentTerminalEmitter.Compact.view (pageEnd S I base) I.sources

def done_ := DescentTerminalEmitter.Allocation.endAt S.terminal I.indexEvents I.formatEvents flightEnd
def chip := DescentTerminalChipRuntime.Dated.placed (done_ S I base) S.terminal.rows
def endAddress := (chip S I base).keys+S.terminal.pool

theorem address_bill {h:ℕ} (short:DescentExteriorShelf.tableBits (planeS).headBits (planeS).restBits (planeS).bitLanes≤h/2) :
    endAddress S I base≤base+92*(S.sites+S.terminal.rows+S.packets+S.terminal.pool+1)+
      2*(∑j,DescentTerminalEmitter.Compact.need (I.sources j))+43+
      64*(S.packets+2^(h/2)+(planeS).rawRows+(planeS).publicRows+(planeS).headerRows+1)+
      60*(S.terminal.rows+S.terminal.pool+S.terminal.leaves+I.indexEvents+I.formatEvents+1)+
      8*S.terminal.rows+6+S.terminal.pool := by
  have pages:=bounds A S.terminal.pool
  have shelf:=Nat.add_le_add_left (DescentTerminalEmitter.Compact.invoice I.sources) (pageEnd S I base)
  have flight:=DescentTerminalDataPlane.Arena.price planeS origin short
  have issue:=DescentTerminalEmitter.Allocation.price S.terminal I.indexEvents I.formatEvents flightEnd
  have end_:=DescentTerminalChipRuntime.Dated.terminal_end (done_ S I base) S.terminal.rows S.terminal.pool
  have chipPrice:=DescentTerminalChipRuntime.Dated.words_le S.terminal.rows S.terminal.pool
  change pageEnd S I base≤base+92*(S.sites+S.terminal.rows+S.packets+S.terminal.pool+1) at pages
  change origin≤_ at shelf
  change flightEnd≤origin+64*(S.packets+2^(h/2)+(planeS).rawRows+(planeS).publicRows+(planeS).headerRows+1) at flight
  change done_ S I base≤_ at issue
  change endAddress S I base=_ at end_
  omega

theorem stages :
    (A).finish≤pageEnd S I base ∧ pageEnd S I base≤origin ∧ origin≤flightEnd ∧
    flightEnd≤done_ S I base ∧ done_ S I base≤endAddress S I base := by
  have end_:=DescentTerminalChipRuntime.Dated.terminal_end (done_ S I base) S.terminal.rows S.terminal.pool
  refine ⟨?_,Nat.le_add_right ..,?_,Nat.le_add_right ..,?_⟩
  · change (A).finish≤(A).finish+_+_;omega
  · change origin≤origin+24*_+_+_+4*_+4*_;omega
  · change endAddress S I base=_ at end_;omega

structure Earlier {blocks : ℕ} (F:MaskedShelf blocks) (bw:ℕ) : Prop where
  old : (A).Lower bw
  gather : ∀j,(I.directory j).base+(I.directory j).size≤(A).finish
  mask : ∀j,(F.channel j).base+(F.channel j).size≤(A).finish ∧ (F.weight j).base+(F.weight j).size≤(A).finish
  maskROM : F.table.base+F.table.size≤(A).finish
  originals : DescentTerminalEmitter.Compact.Earlier (pageEnd S I base) I.sources
  «public» : ∀j,(I.publicTapes j).base+(I.publicTapes j).size≤origin
  cable : ∀j,(I.cable j).base+(I.cable j).size≤origin
  exterior : ∀j,(I.exterior j).base+(I.exterior j).size≤origin
  assignment : I.candidate.base+I.candidate.size≤origin

theorem suffix_room {blocks bw : ℕ} (F:MaskedShelf blocks) (O:DescentPrivateExponentRAM.Banks)
    (old:Earlier S I base F bw) (finish:endAddress S I base<2^bw) :
    Suffix.Fits S (layout S I base O) F bw := by
  obtain ⟨pages,templates,flights,issue,paid⟩:=stages S I base
  have after:=paid.trans_lt finish
  have flightFit:=issue.trans_lt after
  have pageFit:=templates.trans_lt (flights.trans_lt flightFit)
  have arenaFit:=pages.trans_lt pageFit
  have originBefore : origin≤DescentTerminalDataPlane.Arena.post planeS origin:=Nat.le_add_right ..
  have widthBefore : origin≤DescentTerminalDataPlane.Arena.headerBase planeS origin:=by change origin≤origin+24*_+_+_;omega
  have pubBefore : origin≤DescentTerminalDataPlane.Arena.second planeS origin:=by change origin≤origin+24*_+_+_+4*_;omega
  have pf:=DescentTerminalDataPlane.Arena.fits planeS origin I.publicTapes I.cable I.exterior I.candidate
    (fun j=>(old.public j).trans originBefore) (fun j=>(old.cable j).trans widthBefore)
    (fun j=>(old.exterior j).trans pubBefore) (old.assignment.trans originBefore) flightFit
  have inRange (j:Fin 43) : (inputs S I base j).base+(inputs S I base j).size≤flightEnd := by
    unfold inputs
    split
    · have enough:=(A).stride_min
      have hfin:(A).start+2≤(A).finish:=by change _≤(A).start+22*(A).stride;have:=S.sites_pos;change 2*S.sites+_+_+1<(A).stride at enough;omega
      exact hfin.trans (pages.trans (templates.trans flights))
    split
    · change DescentTerminalDataPlane.Arena.headerBase planeS origin+2*DescentTerminalDataPlane.Arena.size (planeS).headerRows+DescentTerminalDataPlane.Arena.size (planeS).headerRows≤
        DescentTerminalDataPlane.Arena.headerBase planeS origin+4*DescentTerminalDataPlane.Arena.size (planeS).headerRows+4*DescentTerminalDataPlane.Arena.size (planeS).headerRows;omega
    split
    · change DescentTerminalDataPlane.Arena.second planeS origin+2*DescentTerminalDataPlane.Arena.size (planeS).headerRows+DescentTerminalDataPlane.Arena.size (planeS).headerRows≤
        DescentTerminalDataPlane.Arena.second planeS origin+4*DescentTerminalDataPlane.Arena.size (planeS).headerRows;omega
    split
    · change DescentTerminalDataPlane.Arena.headerBase planeS origin+3*DescentTerminalDataPlane.Arena.size (planeS).headerRows+DescentTerminalDataPlane.Arena.size (planeS).headerRows≤
        DescentTerminalDataPlane.Arena.headerBase planeS origin+4*DescentTerminalDataPlane.Arena.size (planeS).headerRows+4*DescentTerminalDataPlane.Arena.size (planeS).headerRows;omega
    split
    · change DescentTerminalDataPlane.Arena.second planeS origin+3*DescentTerminalDataPlane.Arena.size (planeS).headerRows+DescentTerminalDataPlane.Arena.size (planeS).headerRows≤
        DescentTerminalDataPlane.Arena.second planeS origin+4*DescentTerminalDataPlane.Arena.size (planeS).headerRows;omega
    split
    · exact templates.trans flights
    exact (DescentTerminalEmitter.Compact.sources_below _ _ old.originals j).trans flights
  have action:=DescentTerminalEmitter.Allocation.inner_room S.terminal I.indexEvents I.formatEvents flightEnd (inputs S I base)
    inRange after (bodyPlane S I base) (publicHeader S I base) I.blank pf.1 pf.2
  have fixedBank (b:Bank) (lo:b.base+b.size≤(A).finish) : b.Fits bw (page A).base :=
    ⟨Nat.two_pow_pos _,by omega,lo⟩
  refine ⟨(A).row_room old.old arenaFit,(A).offset_room old.old arenaFit,(A).sort_room old.old arenaFit,
    (A).slot_room old.old arenaFit,guarded_room F _ _ (fun i=>⟨fixedBank _ (old.mask i).1,fixedBank _ (old.mask i).2⟩)
      (fixedBank _ old.maskROM),?_,?_,?_,action⟩
  · have hp:=DescentTerminalDataPlane.Arena.room (S.sites+1)
    change (A).finish+(S.sites+1)<_
    change (A).finish+DescentTerminalDataPlane.Arena.size (S.sites+1)+DescentTerminalDataPlane.Arena.size S.terminal.pool<_ at pageFit
    omega
  · change (DescentTerminalSiteShelves.gather (directory A I.directory)).Fits bw (inputs S I base 40).base
    rw [show inputs S I base 40=events A S.terminal.pool from by simp [inputs]]
    exact gather_room A _ _ old.gather pageFit
  · change (inputs S I base 40).base+S.terminal.pool<_
    rw [show inputs S I base 40=events A S.terminal.pool from by simp [inputs]]
    have hp:=DescentTerminalDataPlane.Arena.room S.terminal.pool
    change (events A S.terminal.pool).base+DescentTerminalDataPlane.Arena.size S.terminal.pool<_ at pageFit
    omega

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
