import OAI.Hierarchy.TraceResourceNodeRegistration
import OAI.ThreeFlat.Diagonal.TraceNodeHardware
import OAI.ThreeFlat.RAM.PhysicalProcedureSize

namespace OAI
/-! # Hardware size of the actual root registrar at every grid width -/
namespace Hierarchy.TraceAdmission.Resources
open ThreeFlat Diagonal NavigationPass NodePublication
open RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open RAM.HistoryStageBody.Physical (resources resources_seq resources_scan)

theorem mount_size (W H : ℕ) (xs : List ℕ) : resources (mount W H xs)=7*xs.length+2 := by
  induction xs generalizing H with
  | nil => rfl
  | cons x xs ih =>
    rw [mount,resources_seq,ih]
    change 7+(7*xs.length+2)=7*(xs.length+1)+2
    omega

def registerSize := 265+4*((Parents.row 0).work+(scratchExpr (fields 0)).work+(resourceExpr (fields 0)).work)

/-- All concrete operands of the parent reader, list writer and table passes occupy
public words or literal operands with fixed instruction count. -/
theorem register_hardware (W H dp directory stages dst : ℕ) (p : Parameters ℕ) :
    resources (register W H dp directory stages dst p)=registerSize := by
  simp only [register,registration,handoff,Parents.scan,scratchPass,resourcePass,resources_seq,
    resources_scan,HeaderScan.binds_closed,mount_size]
  have a : (Parents.row H).work=(Parents.row 0).work := rfl
  have b : (scratchExpr (fields (H+5))).work=(scratchExpr (fields 0)).work := rfl
  have c : (resourceExpr (fields (H+5))).work=(resourceExpr (fields 0)).work := rfl
  rw [a,b,c]
  change 7*22+2+((18+4*_+37)+((18+4*_+(18+4*_))+18))=_
  unfold registerSize
  omega

theorem registerNodes_hardware (W nodeCtrl H dp directory stages dst : ℕ)
    (a : NodeArchive) (layer : Layer) (p : Parameters ℕ) :
    resources (registerNodes W nodeCtrl H dp directory stages dst a layer p)=
      100+resources (compactPublish W nodeCtrl a (stages+1))+registerSize := by
  simp only [registerNodes,resources_seq,mount_size,register_hardware,nodeWords,List.length_cons,List.length_ofFn]
  omega

/-- For the actual registered trace archive, even the compact node publisher has
fixed text size depending only on the cap of the chosen expander block. -/
theorem capped_registration_hardware (W nodeCtrl H dp directory stages dst cap : ℕ)
    (a : NodeArchive) (layer : Layer) (p : Parameters ℕ)
    (children : a.childCap=cap) (halves : a.halfCap=cap) (motifs : a.motifCap=cap) :
    resources (registerNodes W nodeCtrl H dp directory stages dst a layer p)=
      100+compactHardware cap+registerSize := by
  simp only [registerNodes_hardware,compactPublish_resources,compactHardware,children,halves,motifs]

theorem native_registration_hardware (w lanes perLane pairs trace tariff cap H dp dir n dst : ℕ)
    (layer : Layer) (p : Parameters ℕ) :
    let a:=traceArchive w lanes perLane pairs trace tariff cap cap cap
    let native:=registerNodes (64*w) (compactControl w) H dp dir n dst a layer p
    native.labels+native.registers+native.slots=100+compactHardware cap+registerSize := by
  intro a native
  change resources (registerNodes (64*w) (compactControl w) H dp dir n dst a layer p)=_
  rw [registerNodes_hardware,traceArchive_hardware]

end Hierarchy.TraceAdmission.Resources

end OAI
