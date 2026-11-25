import OAI.Hierarchy.DescentResetRegisteredOperandRows
import OAI.Hierarchy.DescentDatedOperandOrdinalFields

namespace OAI
/-! # Bind numerical ordinal inputs to the original reset request and candidate RAM -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentPackedZip DescentSIMDLookup DescentOperandCandidateLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

/-- Zero selects no candidate. Each positive emitted word names its preceding zero-based slot. -/
def requestCandidate {n b : ℕ} (q : Cell b) (valid : q.val≤n) : Option (Fin n) :=
  if empty_ : q.val=0 then none else some ⟨q.val-1,by omega⟩

theorem requestCandidate_code {n b : ℕ} (q : Cell b) (valid : q.val≤n) (room : n<2^b) :
    DescentOperandCandidateLookup.code room (requestCandidate q valid)=q :=by
  apply Fin.ext
  by_cases off : q.val=0
  · simp [requestCandidate,DescentOperandCandidateLookup.code,off]
  · simpa only [requestCandidate,dite_eq_right off,DescentOperandCandidateLookup.code] using (show q.val-1+1=q.val by omega)

variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "C" => (v).setup
local notation "A" => (v).receiver
local notation "s" => u.operand
local notation "plan" => (v).linkedRankInputs u.sectors ((v).sheetsStart b)
local notation "rendered" => (v).renderFromRanks plan b
variable (f : Fin 7) (arg : Fin a.successor.setup.retained.args) (x : Fin a.successor.receiver.blocks)
    (n : Fin a.successor.setup.retained.nodes)
local notation "i" => (v).operandOrdinal (s) f arg x n
local notation "marked" ok:arg m:arg => (((C).code ((v).operandFloor b) w u.bank u.laws).image (u.beforeSetupImage ok m))

/-- The bank after the original retained/fresh arbitration contains the query and kept field.
The candidate data is obtained at the same ordinal on the receiver's true signed ports. -/
def OrdinalRead.fromRequest (ok : u.Ready) (actorMem : Memory w) (small : 2*(A).candidates<2^(A).queryBits)
    (q : Fin (A).hosts→Fin (A).groups→Cell (A).queryBits)
    (field : Fin (A).hosts→Fin (A).groups→Cell (C).fieldBits)
    (qfit : (u.rawOperands.query i).Fits w ((v).keepBase b))
    (ffit : (u.rawOperands.kept i).Fits w ((v).keepBase b))
    (queryRead : Source (u.rawOperands.query i) q (A).lanes (marked ok actorMem))
    (fieldRead : Source (u.rawOperands.kept i) field (A).lanes (marked ok actorMem))
    (raw : Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Cell (A).signedBits)
    (candidateRead : ∀j,Source ((v).previous (s) rendered b i j) (raw j) (A).lanes (u.operandEntry ok actorMem))
    (bounded : ∀h g,(q h g).val≤2*(A).candidates)
    (price : ∀h g,((field h g).val:Cell (s).coeff).val+
       (DescentOperandCandidateLookup.selected (fun h g=>requestCandidate (q h g) (bounded h g))
         (fun j h g=>((raw j h g).val:Cell (s).coeff)) h g).val<2^(s).coeff) :
    OrdinalRead u ok small actorMem i :=by
  have address:=u.raw_ordinal_fields f arg x n
  rw [address.1] at queryRead
  rw [address.2] at fieldRead
  obtain ⟨source,kept⟩:=u.operand_ordinal_fields f arg x n ok actorMem q field qfit ffit queryRead fieldRead
  refine ⟨fun h g=>requestCandidate (q h g) (bounded h g),raw,
      fun h g=>(field h g).val,?_,kept,candidateRead,price⟩
  simpa only [requestCandidate_code] using source

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
