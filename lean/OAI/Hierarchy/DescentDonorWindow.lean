import OAI.Hierarchy.DescentDonorChipLookup
import OAI.Hierarchy.DescentDonorParts
import OAI.Hierarchy.DescentDonorEncodedBits
import OAI.Hierarchy.DescentDonorLaneNumbers
import OAI.Hierarchy.DescentDonorShape
import OAI.Hierarchy.DescentDonorReceipt
import OAI.Hierarchy.DescentPackedActorHeadRAM
import OAI.Hierarchy.DescentHaloPackedRebase

namespace OAI
/-! # The fixed local donor table reads signed cables, geometry and selected supply widths -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSIMDLookup DescentSixParty DescentPacking.PackedMatch.Local DescentPackedZip
open DescentSharedCableNames DescentHaloWalkRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable (s : Shape)

/-- All public shapes are fixed before evaluating a history. A port
label contains only a bounded neighbor ordinal and the previous signed
grain ticket. The four-step table is shared by all the host's groups. -/
def operands (lay : Bool) (u : Panel s.blocks s.degree (2*s.cap) s.short)
    (sig : Fin s.blocks→Fin (2*s.cap)→Cell (DescentSignedCableCodec.width s.degree s.cap))
    (own : Fin (s.degree+1)→Owners.Register s.blocks s.degree s.short)
    (order flag : Fin (breadth s.degree)→Fin (breadth s.degree+1))
    (fresh : Fin s.blocks→Fin s.cap→Fin 8→Cell s.widths) : Parts s :=
  ⟨Owners.register lay u,
   encode _ _ (fun i=>sig (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2),
   encode _ _ own,DescentHaloPackedRebase.digest order,DescentHaloPackedRebase.digest flag,
   encode _ _ (fun i=>let z:=finProdFinEquiv.symm i;let q:=finProdFinEquiv.symm z.1;fresh q.1 q.2 z.2)⟩

theorem printed (B profile b slots : ℕ) (lay : Bool) (u : Panel s.blocks s.degree (2*s.cap) s.short)
    (sig : Fin s.blocks→Fin (2*s.cap)→Cell (DescentSignedCableCodec.width s.degree s.cap))
    (own : Fin (s.degree+1)→Owners.Register s.blocks s.degree s.short)
    (order flag : Fin (breadth s.degree)→Fin (breadth s.degree+1))
    (fresh : Fin s.blocks→Fin s.cap→Fin 8→Cell s.widths)
    (x : Fin s.blocks) (t : Fin s.cap) :
    (encode (bundleBits 3 s.names s.widths) (s.blocks*s.cap)).symm
      (output s B profile b slots (combine s (operands s lay u sig own order flag fresh))) (finProdFinEquiv (x,t))=
    packDonor (depot s.names s.widths slots b B profile u (sig x)
      (fun w=>⟨(order (ActorPath.index s.degree w)).val,decide ((flag (ActorPath.index s.degree w)).val=1),w.2.2.1,w.2.2.2⟩)
      (Owners.addressed (own 0)) (fun peer=>Owners.addressed (own peer.succ)) (fresh x t) lay x t) := by
  have first {n m : ℕ} (a : Fin n) (b : Fin m) : (finProdFinEquiv (a,b)).divNat = a :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (a,b))
  have second {n m : ℕ} (a : Fin n) (b : Fin m) : (finProdFinEquiv (a,b)).modNat = b :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (a,b))
  cases lay <;> simp [first,second,output,chip,operands,Owners.register,decode_encode_panel,DescentHaloPackedRebase.digest,
    DescentHaloPackedRebase.field]

theorem printed_parts (B profile b slots : ℕ) (lay : Bool) (u : Panel s.blocks s.degree (2*s.cap) s.short)
    (sig : Fin s.blocks→Fin (2*s.cap)→Cell (DescentSignedCableCodec.width s.degree s.cap))
    (own : Fin (s.degree+1)→Owners.Register s.blocks s.degree s.short)
    (order flag : Fin (breadth s.degree)→Fin (breadth s.degree+1))
    (fresh : Fin s.blocks→Fin s.cap→Fin 8→Cell s.widths)
    (x : Fin s.blocks) (t : Fin s.cap) :
    (encode (bundleBits 3 s.names s.widths) (s.blocks*s.cap)).symm
      (chip s B profile b slots (operands s lay u sig own order flag fresh)) (finProdFinEquiv (x,t))=
    packDonor (depot s.names s.widths slots b B profile u (sig x)
      (fun w=>⟨(order (ActorPath.index s.degree w)).val,decide ((flag (ActorPath.index s.degree w)).val=1),w.2.2.1,w.2.2.2⟩)
      (Owners.addressed (own 0)) (fun peer=>Owners.addressed (own peer.succ)) (fresh x t) lay x t) := by
  simpa only [output,separate_combine] using printed s B profile b slots lay u sig own order flag fresh x t

end
end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
