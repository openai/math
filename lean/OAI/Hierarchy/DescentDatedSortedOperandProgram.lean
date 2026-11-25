import OAI.Hierarchy.DescentDatedSortedBroadcastRead
import OAI.Hierarchy.DescentOperandSelectorWidth

namespace OAI
/-! # Actual scalar/routing instruction sequence before the final eight operand words -/
namespace Hierarchy.DescentDatedOperandReadPipeline.SortedInput
open DescentDatedSourcePathDirectory DescentSortedRoster DescentHaloWalkRAM DescentSIMDLookup DescentPackedZip
open DescentSharedLeafLookup DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (g : Geometry)
local notation "P" => g.paths
def readBase (base : ℕ) :=finish g (Broadcast.finish g base)
def program (s : Sources g) (base oldHosts pitch : ℕ) (visited sorted : Bank) (w : ℕ) :=
  let middle:=Broadcast.finish g base
  let first:=Broadcast.phase g base oldHosts pitch w
  let mapper:=phase g s (Broadcast.port g base oldHosts visited sorted) middle w
  let reader:=DescentDatedOperandReadPipeline.phase g (sources g s middle) (readBase g base) w
  (first.seq mapper).seq reader

def output (s : Sources g) (base : ℕ) :=expression g (sources g s (Broadcast.finish g base)) (readBase g base)
def stop (base : ℕ) :=endAddress g (readBase g base)
theorem adapter_span (base : ℕ) : readBase g base=
    base+(Public.stop 0 g.hosts g.groups g.lanes g.digitBits+g.stageWords 2 1 P) :=by
  unfold readBase finish Broadcast.finish Public.stop after DescentDatedOperandSelectionRun.endAddress
    DescentDatedOperandSelectionRun.nextAddress DescentDatedOperandMux.endAddress DescentDatedOperandMux.start
    DescentDatedOperandMux.tables DescentDatedOperandMux.span DescentOperandFamilyBook.endAddress
    DescentOperandFamilyBook.words DescentOperandFamilyBook.unit DescentResetStemMux.words DescentResetStemMux.unit
    Geometry.stageWords
  simp only [layout,DescentDatedOperandCoordinates.keyWidth,Nat.zero_add,Nat.add_assoc]

theorem ceilings (base : ℕ) : base≤Broadcast.finish g base ∧ Broadcast.finish g base≤readBase g base ∧
    readBase g base≤ stop g base :=
  ⟨(Nat.le_add_right ..).trans (Nat.le_add_right ..),after_ge g _ 2 1 P,by rw [stop,endAddress_eq_pipelineWords];exact Nat.le_add_right ..⟩

theorem port_fits {w base H : ℕ} (vis srt : Bank)
    (vf : vis.Fits w base) (sf : srt.Fits w base) (space : Broadcast.finish g base<2^w) (s : Fin P) :
    (Broadcast.port g base H vis srt s).Fits w (Broadcast.finish g base) :=
  Broadcast.port_fits g vis srt vf sf space s

theorem program_total {base w : ℕ} (s : Sources g) (H pitch : ℕ) (vis srt : Bank) (m : Memory w)
    (early : SourceRoom g s w base) (vf : vis.Fits w base) (sf : srt.Fits w base) (space : stop g base<2^w) :
    Step base (stop g base) (program g s base H pitch vis srt w) m ∧
      ∀j f,(output g s base j f).Fits w (stop g base) :=by
  obtain ⟨a,b,c⟩:=ceilings g base
  have upper:=c.trans_lt space
  have mid:=b.trans_lt upper
  let lut:=Broadcast.phase g base H pitch w
  have boot:=Broadcast.any (oldHosts:=H) (pitch:=pitch) g m mid
  let map:=phase g s (Broadcast.port g base H vis srt) (Broadcast.finish g base) w
  have normalized:=total g s (Broadcast.port g base H vis srt) (lut.image m)
    (SourceRoom.extend g s early a) (port_fits g vis srt vf sf mid) upper
  have last:=pipeline_total g (sources g s (Broadcast.finish g base)) (map.image (lut.image m)) normalized.2 space
  exact ⟨(boot.thenStep normalized.1).thenStep last.1,last.2⟩

theorem program_observed {base w H : ℕ} (s : Sources g) (v : Data g) (pitch : ℕ) (vis srt : Bank)
    (reach : Fin H→Fin P→Option (Fin H)) (m : Memory w) (data : Recorded g s v base m)
    (vf : vis.Fits w base) (sf : srt.Fits w base) (nv : H*P≤vis.size) (ns : H*P≤ srt.size)
    (high : H<2^w) (paths : P≤2^g.digitBits)
    (raw : ∀h p,m (vis.base+(Ranks.id h p).val)=(number (Gather.select reach h p):Word w))
    (sorted : ∀h t,m (srt.base+(Ranks.id h t).val)=(number (indexed reach h t):Word w))
    (space : stop g base<2^w) :
    let run:=program g s base H pitch vis srt w
    let translated:=values g v (Broadcast.value g pitch reach)
    Step base (stop g base) run m ∧ ∀j f,Held g (stop g base) (run.image m) (output g s base j f)
      (fun h k=>finalLaw g f (fun i=>finalInputs g translated j i h k)) :=by
  intro run translated
  obtain ⟨a,b,c⟩:=ceilings g base
  have upper:=c.trans_lt space
  have mid:=b.trans_lt upper
  let lut:=Broadcast.phase g base H pitch w
  have boot:=Broadcast.any (oldHosts:=H) (pitch:=pitch) g m mid
  have stay (B : Bank) (fit : B.Fits w base) (capacity : H*P≤B.size) (h : Fin H) (p : Fin P) :
      lut.image m (B.base+(Ranks.id h p).val)=m (B.base+(Ranks.id h p).val):=
    boot.frame _ (.inl ((Nat.add_lt_add_left ((Ranks.id h p).isLt.trans_le capacity) _).trans_le fit.2.2))
  let map:=phase g s (Broadcast.port g base H vis srt) (Broadcast.finish g base) w
  have mounted:=Broadcast.issued (oldHosts:=H) (pitch:=pitch) g vis m mid
  have inputs (p : Fin P) :=Broadcast.read_port g vis srt reach p (lut.image m) mid high paths vf sf nv ns
    (fun h t=>(stay vis vf nv h t).trans (raw h t)) (fun h t=>(stay srt sf ns h t).trans (sorted h t)) mounted
  have normalized:=recorded g s v (Broadcast.port g base H vis srt) (Broadcast.value g pitch reach)
    (lut.image m) (Recorded.later g s v data boot) inputs upper
  have last:=observed g (sources g s (Broadcast.finish g base)) translated (map.image (lut.image m)) normalized.2 space
  exact ⟨(boot.thenStep normalized.1).thenStep last.1,last.2⟩

end
end Hierarchy.DescentDatedOperandReadPipeline.SortedInput

end OAI
