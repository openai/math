import OAI.Hierarchy.DescentContactOutputPeriod
import OAI.Hierarchy.DescentContactOutputOperands
import OAI.Hierarchy.DescentResetCompactedCandidates

namespace OAI
/-! # Mask and rank inputs of the physical direct-contact sector -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (A : Shape) (donorStart first : ℕ) {w : ℕ}
local notation "D" => A.donor
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)
local notation "fields" => A.fieldsAt donorStart first u

def issuedProgram (w : ℕ):=A.program donorStart first u fields w
def issuedImage (m : Memory w):=A.image donorStart first u fields m
def issuedTicks:=A.ticks donorStart first u fields

variable (prior : A.donor.endAddress donorStart≤first) (old : A.donor.Space donorStart u w)
variable (room : A.endAddress first<2^w) (batch : 0<A.batch) (blocks : 0<A.blocks)
variable (fits : ∀q f,(A.fieldsAt donorStart first u q f).Fits w (A.projected first))
def issuedPhase : NativePhase w:=A.native donorStart first u fields prior old room batch blocks fits
include prior old room batch blocks fits in
theorem issued_any (m : Memory w) :
    (A.issuedProgram donorStart first u w).Exec m (A.issuedImage donorStart first u m) (A.issuedTicks donorStart first u) ∧
    CheapCode (A.issuedProgram donorStart first u w) ∧
    ∀z,z<first ∨ A.endAddress first≤z→A.issuedImage donorStart first u m z=m z:=
  A.any donorStart first u fields prior old room batch blocks fits m

def fieldExpr (x : Fin A.blocks) (q : Fin A.sockets) (f : Fin 4) : Expr:=
  .lookup (A.output first q f x) .row
def candidate (x : Fin A.blocks) (q : Fin A.sockets) (f : Fin 4) : DescentResetDenseOperand.Operand:=
  .sparse (A.fieldExpr first x q f)

/-- The same physical count bank supplies the nonzero presence digit and the true
width. Ranks occupy columns four through six in the mixed mask stage. -/
def raw (x : Fin A.blocks) (q : Fin A.sockets) (self : DescentResetDenseOperand.Operand) : Fin 9→DescentResetDenseOperand.Operand :=
  let src:=A.candidate first x q
  ![src 0,src 1,src 2,src 3,.compact (.lit 0),.compact (.lit 0),.compact (.lit 0),self,src 0]

/-- The numerical parent index is the catalog row for this block followed by its
direct socket. The private sector follows these slots. -/
def presentRows (privateSlots : ℕ) (job : ℕ) : Option (Fin A.blocks×Fin A.sockets) :=
  let pitch:=A.sockets+privateSlots
  let x:=job/pitch
  let q:=job%pitch
  if h : x<A.blocks ∧ q<A.sockets then some (⟨x,h.1⟩,⟨q,h.2⟩) else none

theorem range (privateSlots : ℕ) (x : Fin A.blocks) (q : Fin A.sockets) :
    A.presentRows privateSlots (x.val*(A.sockets+privateSlots)+q.val)=some (x,q):=by
  let pitch:=A.sockets+privateSlots
  have cut : q.val<pitch:=q.isLt.trans_le (Nat.le_add_right ..)
  have ok : 0<pitch:=Nat.zero_lt_of_lt cut
  have div : (x.val*pitch+q.val)/pitch=x.val:=by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ ok,Nat.div_eq_of_lt cut,Nat.zero_add]
  have remainder : (x.val*pitch+q.val)%pitch=q.val:=by
    rw [Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt cut]
  change (if h : _ then some _ else none)=_
  simp only [pitch] at div remainder
  simp [div,remainder,x.isLt,q.isLt]

include room in
theorem fields_fit (x : Fin A.blocks) (q : Fin A.sockets) (f : Fin 4) :
    (A.fieldExpr first x q f).Fits w (A.endAddress first):=by
  exact ⟨DescentResetStemProject.page_fits _ _ room,trivial⟩

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
