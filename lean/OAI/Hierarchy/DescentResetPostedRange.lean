import OAI.Hierarchy.DescentOperandZeroCandidate
import OAI.Hierarchy.DescentTerminalResetOperandRead
import OAI.Hierarchy.DescentRetainedRangeDigits

namespace OAI
/-! # The three retained range words pass the signed candidate lookup -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentOperandStateBanks DescentOperandCandidateLookup
noncomputable section
open scoped Fin.CommRing
variable (v : ResetOutput) (ri : v.RankInputs) (s : v.OperandInputs) (base degree : ℕ)
    (bank : v.setup.Sources) (laws : v.setup.Laws)
local notation "A" => v.receiver
local notation "rendered" => v.renderFromRanks ri base
local notation "srcBase" => v.operandDictionaryEnd base

theorem previous_range (r : v.RenderInputs) (f : Fin 3) (arg : Fin s.slots)
    (x : Fin (A).blocks) (n : Fin s.nodes) (j : Fin (2*(A).candidates)) :
    v.previous s r base (v.operandOrdinal s (DescentRetainedRangeDigits.page f) arg x n) j = .lit 0 := by
  fin_cases f <;> simp [previous,v.operandIndex_ordinal,pointerField,DescentRetainedRangeDigits.page]

private theorem cast_row {a b H G M : ℕ} (same : a=b) (x : Fin H→Fin G→Cell a) (j : Row H G M) :
    (data (fun h g=>(x h g).cast (congrArg (2^·) same)) j).val=(data x j).val := by
  subst b
  rfl

theorem span_field_posted {w : ℕ} (m : Memory w) (nodes : s.nodes=v.nodes) (slots : s.slots=v.argumentSlots)
    (bits : s.coeff=v.nodeBits) (early : v.OperandEarly s rendered w base) (room : v.finalEnd base<2^w)
    (f : Fin 3) (arg : Fin v.argumentSlots) (x : Fin (A).blocks)
    (kept : Fin v.nodes→Fin (A).hosts→Fin (A).groups→Cell s.coeff)
    (old : ∀n, Source (s.kept (v.operandOrdinal s (DescentRetainedRangeDigits.page f) (arg.cast slots.symm) x (n.cast nodes.symm)))
      (kept n) (A).lanes (v.terminalQueryMemory ri base degree bank laws m)) :
    Reads (v.terminalField base (DescentRetainedRangeDigits.page f) arg x) (fun h g=>encode v.nodeBits v.nodes
      (fun n=>(kept n h g).cast (congrArg (2^·) bits))) (A).lanes (v.retainedMemory ri s base degree bank laws m) := by
  let part : Fin v.nodeNames := finProdFinEquiv (page (DescentRetainedRangeDigits.page f) arg,x)
  let idx (n : Fin v.nodes) := v.operandOrdinal s (DescentRetainedRangeDigits.page f) (arg.cast slots.symm) x (n.cast nodes.symm)
  have size : (A).fields=v.nodeNames*v.nodes := by simpa only [nodeNames,slots,nodes] using s.channels
  have prior : srcBase+(v.nodeNames*v.nodes)*DescentResetNodeBooks.rows (A).hosts (A).groups (A).lanes≤v.scalarEnd base := by
    change srcBase+_≤ srcBase+(A).fields*_
    rw [size]
    rfl
  apply DescentResetNodeBooks.posted_at (v.scalarEnd base) srcBase v.nodeNames v.nodes (A).hosts (A).groups
    v.nodeBits (A).lanes (v.rankedMemory ri s base degree bank laws m) prior room part
    (fun n h g=>(kept n h g).cast (congrArg (2^·) bits))
  intro n j
  have order : (idx n).val=part.val*v.nodes+n.val := by
    dsimp only [idx]
    rw [v.operandOrdinal_val]
    simp [part,page,finProdFinEquiv_apply_val,nodes,slots,Nat.mul_comm,Nat.add_comm]
  let input:=v.terminalQueryMemory ri base degree bank laws m
  have zero : v.previous s rendered base (idx n)=(fun _=>.lit 0) := by
    funext c
    exact v.previous_range s base rendered f (arg.cast slots.symm) x (n.cast nodes.symm) c
  have rd:=v.operand_source_at s rendered base input early ((v.final_ge base).trans_lt room)
    (idx n) (kept n) (by
      rw [zero]
      exact DescentOperandFieldJoin.stored_blank _ _ input (kept n) (early.1 _) (early.2.1 _) (old n)
        le_rfl ((v.operand_order base).2.trans_lt ((v.final_ge base).trans_lt room))) j
  change _ = ((data (fun h g => (kept n h g).cast (congrArg (2^·) bits)) j).val : Word w)
  rw [cast_row bits (kept n) j]
  simp only [DescentResetNodeBooks.scalar,DescentResetNodeBooks.rows,address,bankBase,order] at rd ⊢
  exact rd

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
