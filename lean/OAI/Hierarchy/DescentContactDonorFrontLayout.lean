import OAI.Hierarchy.DescentContactDonorShape
import OAI.Hierarchy.DescentContactSenderDate
import OAI.Hierarchy.DescentResetSignedHaloLayout

namespace OAI
/-! # Contiguous layout of the earlier donor and original-domain halo data -/
namespace Hierarchy.DescentContactDonorFront

open DescentResetSignedHaloMatrix DescentSIMDLookup ProtocolRAM
noncomputable section
namespace Shape
variable (A : Shape)
def sender (base : ℕ) : DescentContactSenderDate.Layout A.degree A.lows A.cap A.n A.residual A.height A.fieldBits :=
  ⟨base,A.hosts,A.groups,A.batch⟩
def idBase (base : ℕ) := (A.sender base).endAddress
def oldCount (base : ℕ) : Bank := ⟨A.idBase base,0⟩
def owner (base : ℕ) : Bank := ⟨A.idBase base+1,Nat.clog 2 A.hosts⟩
def haloStart (base : ℕ) := A.idBase base+A.idCells
def identityWord (i : ℕ) := if i=0 then A.hosts else i-1
def halo (base : ℕ) (roster : Bank) :=
  arrange (A.haloStart base) A.hosts A.hosts A.degree A.cap A.groups A.batch
    A.fieldBits A.queryBits A.cargoBits (A.oldCount base) (A.owner base) roster
theorem sender_end (base : ℕ) : (A.sender base).endAddress=A.senderEnd base := rfl

theorem halo_end (base : ℕ) (roster : Bank) : (A.halo base roster).high=A.endAddress base := by
  unfold halo
  rw [arrange_extent]
  change A.haloStart base + _ + _ + _ + _ = A.haloStart base + (_ + _ + _ + _)
  simp only [DescentResetOriginalSlots.stride, DescentPackedChildNeighbor.SIMD.ROM.cells,
    DescentPackedChildNeighbor.SIMD.ROM.rowBits, Nat.add_assoc]

end Shape
end
end Hierarchy.DescentContactDonorFront

end OAI
