import OAI.Hierarchy.DescentOrdinalReadAmount
import OAI.Hierarchy.DescentResetPostedRange
import OAI.Hierarchy.DescentPrimitiveBirthDigits

namespace OAI
/-! # The three range words of a physically issued operand -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedColony DescentPackedZip
open DescentOperandStateBanks DescentOperandCandidateLookup DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "s" => u.operand
local notation "start" => (v).sheetsStart b
local notation "plan" => (v).linkedRankInputs u.sectors start
local notation "rendered" => (v).renderFromRanks plan b
variable (ready : u.Ready) (small : 2*a.successor.receiver.candidates<2^a.successor.receiver.queryBits) (actorMem : Memory w)
local notation "entry" => u.operandEntry ready actorMem


/-- The reset writes literal zero on every candidate wire for a range page. Thus its
posted amount is the concrete retained word, for every query and even outside the roster. -/
theorem OrdinalRead.range_amount (f : Fin 3) (arg : Fin (s).slots) (x : Fin (A).blocks)
    (n : Fin (s).nodes)
    (read : OrdinalRead u ready small actorMem ((v).operandOrdinal s (DescentRetainedRangeDigits.page f) arg x n))
    (word : Fin (A).hosts→Fin (A).groups→Cell (s).coeff)
    (stored : Source ((s).kept ((v).operandOrdinal s (DescentRetainedRangeDigits.page f) arg x n)) word
      (A).lanes entry)
    (live : 0<(A).lanes) (valueRoom : (s).coeff*(A).lanes≤w)
    (signedRoom : (A).signedBits*(A).lanes≤w) (h : Fin (A).hosts) (g : Fin (A).groups) :
    (read.amount h g).val=(word h g).val :=by
  have value:=read.kept_read.determined stored live valueRoom
  have empty (j : Fin (2*(A).candidates)) : read.raw j=(fun _ _=>0):=by
    apply (read.source_read j).determined _ live signedRoom
    rw [(v).previous_range (s) b rendered f arg x n j]
    exact DescentPrimitiveBirth.zero _
  change (read.kept h g).val+(selected read.query (fun j h g=>((read.raw j h g).val:Cell (s).coeff)) h g).val=_
  simp only [value,empty,Fin.val_zero,Nat.cast_zero,selected]
  cases read.query h g <;>simp

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
