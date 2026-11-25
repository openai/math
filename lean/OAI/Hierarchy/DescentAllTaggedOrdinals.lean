import OAI.Hierarchy.DescentDateTaggedOrdinals
import OAI.Hierarchy.DescentResetArchiveValues

namespace OAI
/-! One family of native reads covers every allocated reset operand ordinal. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty.Chronology.DatePorts DescentOperandCandidateLookup DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing

variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w) {ok : u.Ready}
    {small : 2*a.successor.receiver.candidates < 2^a.successor.receiver.queryBits} {after : Memory w}

theorem seven_at_actor (tags : u.TaggedOrdinals ok small after) :
    ∃read : ∀i, OrdinalRead u ok small after i,
      ∀i, (a.successor.operandIndex u.operand i).2.1=0 → ∀h g,
        ((read i).kept h g).val+
          (DescentOperandCandidateLookup.selected (read i).query (fun j h g=>(((read i).raw j h g).val : Cell u.operand.coeff)) h g).val ≤ 2 := by
  have atOrdinal (i : Fin a.successor.receiver.fields) :
      ∃r : OrdinalRead u ok small after i,
        (a.successor.operandIndex u.operand i).2.1=0 → ∀h g,
          (r.kept h g).val+
            (DescentOperandCandidateLookup.selected r.query (fun j h g=>((r.raw j h g).val : Cell u.operand.coeff)) h g).val ≤ 2 := by
    obtain ⟨⟨⟨⟨f,j⟩,x⟩,n⟩,rfl⟩ := (a.successor.operandOrder u.operand).surjective i
    change ∃r : OrdinalRead u ok small after (a.successor.operandOrdinal u.operand f j x n), _
    by_cases first : f=0
    · subst f
      obtain ⟨r,bounded⟩ := (tags j x n).2
      exact ⟨r,fun _=>bounded⟩
    · obtain ⟨r⟩ := (tags j x n).1 f
      refine ⟨r,fun h=>False.elim (first ?_)⟩
      change (a.successor.operandIndex u.operand (a.successor.operandOrdinal u.operand f j x n)).2.1=0 at h
      simpa only [ResetOutput.operandIndex_ordinal] using h
  exact ⟨fun i=>Classical.choose (atOrdinal i),fun i=>Classical.choose_spec (atOrdinal i)⟩

/-- In the physical tag page, the cell consumed by the reserve archive is at most two. -/
theorem seven_amount_at_actor (tags : u.TaggedOrdinals ok small after) :
    ∃read : ∀i, OrdinalRead u ok small after i,
      ∀j x n h g, ((read (a.successor.operandOrdinal u.operand 0 j x n)).amount h g).val ≤ 2 := by
  obtain ⟨read,bounded⟩ := u.seven_at_actor tags
  refine ⟨read,fun j x n h g=>?_⟩
  exact bounded (a.successor.operandOrdinal u.operand 0 j x n)
    (by rw [ResetOutput.operandIndex_ordinal]) h g

end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
