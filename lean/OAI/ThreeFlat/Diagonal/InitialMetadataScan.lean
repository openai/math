import OAI.ThreeFlat.Diagonal.NavigationArchive
import OAI.ThreeFlat.RAM.HeaderScanLayout

namespace OAI
/-! # Native seed metadata: bounded indexed scans and preservation of all other words -/
namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan
open scoped Classical Fin.NatCast
noncomputable section
variable {W : ℕ} (A : Archive)

def metadataScans (W : ℕ) : Scans W :=
  .next (.one ⟨7,8,closed A.initialKernel⟩)
    (.next (.one ⟨9,10,closed A.initialHalfHeader⟩) (.one ⟨11,12,closed A.initialHalf⟩))

def metadataEnd := A.initialRecords+(7+8*A.initialDegree)*A.initialSites

def metadataUnit := 5*(2*A.initialKernel.work+4)+2*(2*A.initialHalfHeader.work+4)+
  8*A.initialDegree*(2*A.initialHalf.work+4)

private theorem three_program (cur : Word W) (kernel halfHeader half : DescriptorExpr.Term W 0 1) :
    (Scans.pipeline cur (.next (.one ⟨7,8,kernel⟩)
      (.next (.one ⟨9,10,halfHeader⟩) (.one ⟨11,12,half⟩)))).program=
    (procedure cur 7 8 kernel).seq ((procedure cur 9 10 halfHeader).seq (procedure cur 11 12 half)) := rfl

theorem metadata_program :
    ((A.metadataScans W).pipeline (A.control:Word W)).program=A.initialMetadata (W:=W) :=
  three_program (A.control:Word W) (closed A.initialKernel) (closed A.initialHalfHeader) (closed A.initialHalf)

theorem metadata_time : (A.metadataScans W).time A.seedWords=33+A.metadataUnit*A.initialSites := by
  change 11+5*A.initialSites*_+((11+2*A.initialSites*_)+(11+8*A.initialDegree*A.initialSites*_))=_
  simp only [binds_closed,metadataUnit];ring

def metadataMemory (m : Memory W) := ((A.metadataScans W).pipeline (A.control:Word W)).run m

structure MetadataSpace (W : ℕ) : Prop where
  controlRoom : A.control<2^W
  control : A.control<A.initialRecords ∨ A.metadataEnd≤A.control
  header : A.seed+64≤A.initialRecords
  endFit : A.metadataEnd<2^W

def metadataKeep (i : ℕ) : Prop := i<A.initialRecords ∨ A.metadataEnd≤ i

theorem MetadataSpace.covers (h : A.MetadataSpace W) :
    (A.metadataScans W).every (Scans.Safe 63 A.seedWords A.metadataKeep) := by
  have top:=h.endFit
  unfold metadataEnd at top
  refine ⟨⟨by change 7≤63; decide,by change 8≤63; decide,?_,?_⟩,
    ⟨by change 9≤63; decide,by change 10≤63; decide,?_,?_⟩,
    ⟨by change 11≤63; decide,by change 12≤63; decide,?_,?_⟩⟩
  all_goals (try intro i hi); simp only [seedWords,metadataKeep,metadataEnd,Nat.add_mul] at *; omega

theorem metadata_spec (m : Memory W) (sp : A.MetadataSpace W) (H : Scans.Header (A.control:Word W) m A.seed 63 A.seedWords) :
    (A.initialMetadata : RAM.PhysicalProcedure.Procedure W).Spec (fun mem=>mem=m)
      (fun _ out=>out=A.metadataMemory m ∧ ∀i,A.metadataKeep i→ out i=m i)
      (33+A.metadataUnit*A.initialSites) := by
  rw [←A.metadata_time (W:=W),←A.metadata_program]
  exact Scans.native_spec _ _ m _ _ _ _ H (by rw [Fin.val_cast_of_lt sp.controlRoom];exact sp.control)
    (fun i hi=>.inl (by have:=sp.header;omega)) (MetadataSpace.covers A sp)

theorem metadata_frame (m : Memory W) (sp : A.MetadataSpace W) (H : Scans.Header (A.control:Word W) m A.seed 63 A.seedWords) :
    ∀i,A.metadataKeep i→A.metadataMemory m i=m i :=
  (Scans.run_spec _ _ m _ _ _ _ H (by rw [Fin.val_cast_of_lt sp.controlRoom];exact sp.control)
    (fun i hi=>.inl (by have:=sp.header;omega)) (MetadataSpace.covers A sp)).2.2


end
end ThreeFlat.Diagonal.NavigationPass.Archive

end OAI
