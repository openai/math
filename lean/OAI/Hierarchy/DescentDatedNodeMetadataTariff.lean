import OAI.Hierarchy.DescentResetNodeTariff
import OAI.Hierarchy.DescentDatedNodeMetadataOrdinary

namespace OAI
/-! # Clocks and machine-description lengths for the two dated node metadata banks -/
namespace Hierarchy.DescentDatedNodeMetadata.Chart
open DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentStaticWordColumn ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescentPackedColony
noncomputable section
variable {K : ℕ} (v : DescentDatedNodeMetadata.Chart)

def bodyClock (work : ℕ) :=(4+v.jobs*(4+v.rows*(2*work+4)))+
  (4+10*v.dictionary+(4+v.names*(4+v.rows*(2*(1+18*v.nodes)+4))))
def bodyNames (work : ℕ) :=(15+v.jobs*(11+4*work))+
  (15*(v.dictionary+1)+(15+v.names*(11+4*(1+18*v.nodes))))

theorem bodyPrice (floor w U : ℕ) (f : v.Input) (small : ∀a x n,(f a x n).work≤U) :
    v.ticks floor f≤v.bodyClock U ∧ DescentStaticWordColumn.names (v.program floor w f)≤v.bodyNames U :=by
  let es:=List.ofFn (v.gather f)
  have size : es.length=v.jobs:=List.length_ofFn
  have costs : ∀e∈es,e.work≤U:=by
    intro e isMember
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp isMember
    apply small
  obtain ⟨tick,hardware⟩:=DescentResetNodeBooks.charged (v.scalarEnd floor) floor v.names v.nodes v.hosts v.groups v.bits v.lanes w
  have ct:=ProbeStage.Native.columns_clock v.rows floor U es costs
  have cn:=ProbeStage.Native.columns_text w v.rows floor U es costs
  rw [size] at ct cn
  constructor
  · exact Nat.add_le_add ct tick
  · unfold program
    rw [names_seq]
    exact Nat.add_le_add cn hardware

def tallyWork (K q : ℕ) :=(q+13)+(q+11)*K
def setupWords (a b : ℕ) :=DescentResetMetadataInputs.words v.nodes a b v.bits v.lanes

theorem metadataPrice (floor a b w q : ℕ) (paid : v.Counts) (f6 : v.Spans K)
    (cheap : ∀x,(paid x).work≤q) (cost : ∀x n j,(f6 x n j).work≤q) :
    v.metadataTime floor a b paid f6≤4+10*v.setupWords a b+v.bodyClock (tallyWork K q) ∧
    DescentStaticWordColumn.names (v.metadataProgram floor a b w paid f6)≤15*(v.setupWords a b+1)+v.bodyNames (tallyWork K q) :=by
  have body:=v.bodyPrice (v.inputsEnd floor a b) w (tallyWork K q) (v.metaFields floor a b paid f6)
    (DescentResetMetadataInputs.expr_work floor v.nodes a b v.bits v.lanes q paid f6 cheap cost)
  constructor
  · exact Nat.add_le_add le_rfl body.1
  · unfold metadataProgram
    rw [names_seq,DescentResetMetadataInputs.names]
    exact Nat.add_le_add le_rfl body.2

def digitWords (b : ℕ) :=v.nodes*2^((b*v.nodes)*v.lanes)

theorem ordinaryPrice (floor a b w q : ℕ) (paid : v.Counts) (src : v.Vectors K) (cheap : ∀x,(paid x).work≤q) :
    v.ordinaryTime floor a b paid src≤(4+10*v.digitWords b)+(4+10*v.setupWords a b+v.bodyClock (tallyWork K (max q 16))) ∧
    DescentStaticWordColumn.names (v.ordinaryProgram floor a b w paid src)≤
      15*(v.digitWords b+1)+(15*(v.setupWords a b+1)+v.bodyNames (tallyWork K (max q 16))) :=by
  have spans (x n j) : (v.scalarSpan floor b src x n j).work≤ max q 16:=by
    apply le_trans _ (Nat.le_max_right q 16)
    exact (by decide : 12≤16)
  have tail:=v.metadataPrice (v.digitEnd floor b) a b w (max q 16) paid (v.scalarSpan floor b src)
    (fun x=>(cheap x).trans (Nat.le_max_left ..)) spans
  constructor
  · exact Nat.add_le_add le_rfl tail.1
  · unfold ordinaryProgram digitProgram ROM.mount
    rw [names_seq,names_mount]
    exact Nat.add_le_add le_rfl tail.2

end
end Hierarchy.DescentDatedNodeMetadata.Chart

end OAI
