import OAI.Hierarchy.DescentResetArchiveValues
import OAI.Hierarchy.DescentPackedSourceUnique

namespace OAI
/-! Any certified native reset operand reports the same value on the same packed input. -/
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
  (i : Fin a.successor.receiver.fields)
local notation "entry" => u.operandEntry ready actorMem

/-- The query code uniquely fixes the selected row, including the no-candidate value. -/
private theorem query_injective {n width : ℕ} (room : n<2^width) :
    Function.Injective (code room) :=by
  rintro (_|j) (_|k) eq
  · rfl
  · have mismatch:=congrArg Fin.val eq
    change 0=k.val+1 at mismatch
    omega
  · have mismatch:=congrArg Fin.val eq
    change j.val+1=0 at mismatch
    omega
  · apply congrArg some
    apply Fin.ext
    have hit:=congrArg Fin.val eq
    change j.val+1=k.val+1 at hit
    omega

theorem OrdinalRead.amount_of_words (observed : OrdinalRead u ready small actorMem i)
    (picked : Fin (A).hosts→Fin (A).groups→Option (Fin (2*(A).candidates)))
    (kept : Fin (A).hosts→Fin (A).groups→Cell (s).coeff)
    (raw : Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Cell (A).signedBits)
    (selection : Source ((s).query i) (fun h g=>code small (picked h g)) (A).lanes entry)
    (stored : Source ((s).kept i) kept (A).lanes entry)
    (inputs : ∀j,Source ((v).previous (s) rendered b i j) (raw j) (A).lanes entry)
    (live : 0<(A).lanes) (queryRoom : (A).queryBits*(A).lanes≤w)
    (wordRoom : (s).coeff*(A).lanes≤w) (signedRoom : (A).signedBits*(A).lanes≤w)
    (h : Fin (A).hosts) (g : Fin (A).groups) :
    (observed.amount h g).val=(kept h g).val+
      (selected picked (fun j h g=>((raw j h g).val:Cell (s).coeff)) h g).val:=by
  have digits:=observed.query_read.determined selection live queryRoom
  have selectedRow : observed.query=picked:=by
    funext host group
    exact query_injective small (congrFun (congrFun digits host) group)
  have keptWord:=observed.kept_read.determined stored live wordRoom
  have signedWords : observed.raw=raw:=by
    funext j
    exact (observed.source_read j).determined (inputs j) live signedRoom
  change (observed.kept h g).val+
    (selected observed.query (fun j h g=>((observed.raw j h g).val:Cell (s).coeff)) h g).val=_
  rw [selectedRow,keptWord,signedWords]

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
