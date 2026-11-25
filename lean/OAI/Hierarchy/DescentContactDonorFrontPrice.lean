import OAI.Hierarchy.DescentContactDonorFront
import OAI.Hierarchy.DescentContactSenderPrice

namespace OAI
/-! # Instruction and clock accounts for original sender and halo across all old ports -/
namespace Hierarchy.DescentContactDonorFront.Shape
open DescentResetSignedHaloMatrix DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (A : Shape) (base : ℕ)
local notation "H" => A.hosts
local notation "D" => A.degree
local notation "M" => A.batch
local notation "catalog" => DescentPackedChildNeighbor.SIMD.ROM.cells (D+1) A.queryBits A.cargoBits M H A.groups
local notation "decodeLength" => 2*2^(A.fieldBits*M)

def fee (width : ℕ) := ((A.sender base).clockBound width+(4+10*A.idCells))+
  (4+10*cells H D+(4+H*(D+1)*(2*termWork D+4))+(4+10*decodeLength)+(4+10*catalog))

def size (width : ℕ) := ((A.sender base).nameBound width+15*(A.idCells+1))+
  (15*(cells H D+1)+(11+4*termWork D)+15*(decodeLength+1)+15*(catalog+1))

variable (u : DescentContactSenderDate.Prior A.degree A.lows A.cap A.n A.residual) {w : ℕ}

theorem priced (width : ℕ) (board : ∀j,(u.board j).work≤width) (host : u.host.work≤width)
    (ones : u.ones.work≤width) :
    A.ticks base u≤A.fee base width ∧ names (A.program base u w)≤A.size base width := by
  let C:=A.halo base u.routes.roster
  have sender:=(A.sender base).priced (w:=w) u width board host ones
  have cost:=C.tariff
  have namesHalo:=C.hardware w
  constructor
  · exact Nat.add_le_add (Nat.add_le_add_right sender.1 _) cost
  · unfold Shape.program size
    simp only [names_seq,names_mount]
    exact Nat.add_le_add (Nat.add_le_add_right sender.2 _) namesHalo

end
end Hierarchy.DescentContactDonorFront.Shape

end OAI
