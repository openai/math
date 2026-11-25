import OAI.Hierarchy.DescentResetIssuedRange
import OAI.Hierarchy.DescentDatedRangeRegisters

namespace OAI
/-! # The complete seven-page operand store at the original reset return -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentOperandStateBanks DescentDatedPriorOperand
noncomputable section
open private bankFromLayout from OAI.Hierarchy.DescentResetIssuedRange in
theorem operand_bank (v : ResetOutput) (base : ℕ) (x : Fin v.receiver.blocks)
    (j : Fin v.argumentSlots) (f : Fin 7) :
    previousBank v.rangeLayout (PriorResetArchive.reset v base).arguments x (DescentOperandStateBanks.page f j)=
      v.terminalField base f j x :=
  bankFromLayout v.rangeLayout (v.scalarEnd base) v.nodeBits x (DescentOperandStateBanks.page f j)
end
end Hierarchy.DescentDatedAddressBook.ResetOutput

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
local notation "ports" => reset a floor u
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits

/-- The checked selector, kept contribution and source cells seen by the native reset for one
field. The final cell is computed directly from these inputs. -/
structure OrdinalRead (ok : u.Ready) (small : 2*(A).candidates<2^(A).queryBits)
    (actorMem : Memory w) (i : Fin (A).fields) where
  query : Fin (A).hosts→Fin (A).groups→Option (Fin (2*(A).candidates))
  raw : Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Cell (A).signedBits
  kept : Fin (A).hosts→Fin (A).groups→Cell (s).coeff
  query_read : Source ((s).query i) (fun h g=>code small (query h g)) (A).lanes (u.operandEntry ok actorMem)
  kept_read : Source ((s).kept i) kept (A).lanes (u.operandEntry ok actorMem)
  source_read : ∀j, Source ((v).previous (s) rendered b i j) (raw j) (A).lanes (u.operandEntry ok actorMem)
  room : ∀h g,(kept h g).val+(selected query (fun j h g=>((raw j h g).val:Cell (s).coeff)) h g).val<2^(s).coeff

/-- A single family of native incoming readbacks supplies all seven output sheets on the same
actual return, including padding in the last SIMD word. -/
theorem reset_operand_rows (z : u.FinalInputs) (ok : u.Ready) (space : z.Room) {m mid dst : Memory w}
    (first : u.throughOperandDate.Runs m mid) (run : (PhysicalReset.date z).Runs m dst)
    (bits : (s).coeff=(v).nodeBits) (small : 2*(A).candidates<2^(A).queryBits)
    (layoutEq : (ports).rangeLayout=(v).rangeLayout)
    (reads : ∀actorMem, ((head).seq ((v).actor.actorBody u.actor ((v).middle.stop b) w)).Exec m actorMem
      (ht+(v).actor.actorTicks u.actor ((v).middle.stop b) w) → ∀ f j x n,
      Nonempty (OrdinalRead u ok small actorMem ((v).operandOrdinal (s) f j x n))) :
    ∀(x : Fin (ports).rangeLayout.blocks) (pg : Pages (ports).rangeLayout.operands),
      ∃cells : Fin (ports).rangeLayout.hosts→Fin (ports).rangeLayout.groups→Cell ((ports).operandBits*(ports).rangeLayout.nodes),
        Reads (previousBank (ports).rangeLayout (ports).archive.arguments x pg) cells (ports).rangeLayout.lanes dst :=by
  obtain ⟨actorMem,executed,output⟩:=PhysicalReset.dated_fields z ok space first run bits small
  have one (i : Fin (A).fields) : Nonempty (OrdinalRead u ok small actorMem i) :=by
    obtain ⟨⟨⟨⟨f,j⟩,x⟩,n⟩,rfl⟩:=((v).operandOrder (s)).surjective i
    exact reads actorMem executed f j x n
  let loaded:=fun i=>Classical.choice (one i)
  let value:=fun i h g=>(⟨_,(loaded i).room h g⟩:Cell (s).coeff)
  have post:=output (fun i=>(loaded i).query) (fun i=>(loaded i).raw) (fun i=>(loaded i).kept) value
    (fun i=>(loaded i).query_read) (fun i=>(loaded i).kept_read) (fun i=>(loaded i).source_read) (fun _ _ _=>rfl)
  rw [layoutEq]
  intro x pg
  obtain ⟨⟨f,j⟩,rfl⟩:=((finProdFinEquiv : (Fin 7×Fin (v).argumentSlots)≃Pages (v).argumentSlots).surjective pg)
  have produced:=post f j x
  rw [← (v).operand_bank b x j f] at produced
  exact ⟨_, produced⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
