import OAI.Hierarchy.DescentDatedOperandTagRead
import OAI.Hierarchy.DescentPackedReadUnique
import OAI.Hierarchy.DescentPreviousOperandLayout

namespace OAI
/-! # The observed kind of a packed seven-page operand book -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentOperandStateBanks DescentPriorOperandColumns DescentOrdinaryAtomFieldRAM
open DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {l : Layout}

/-- The kind of every resolver job is the original zero-column digit of that exact
block, argument and node, including the unused part of a padded page. -/
theorem bookTags_of_encoded
    (cells : Fin l.blocks→Pages l.operands→Fin l.hosts→Fin l.groups→Fin l.nodes→Cell (l.size+2))
    (valid : ∀x i h g n,(cells x (pageOf i 0) h g n).val≤2) :
    BookTags (l:=l) (fun x pg h g=>encode (l.size+2) l.nodes (cells x pg h g)) :=by
  intro j h g
  let z:=l.index.symm j
  simpa only [HeaderTag,booksHeader,ScalarOperand.take,Equiv.symm_apply_apply,z]
    using valid z.1 z.2.2 h g z.2.1

/-- Only the kind column must agree with the original tagged register. The other three
header fields may store unused digits of a private or exterior reference. -/
theorem BookTags.of_same_register {original copy : Books l} {base w : ℕ} {m : Memory w}
    (valid : BookTags original) (live : 0<l.lanes)
    (room : ((l.size+2)*l.nodes)*l.lanes≤w)
    (before : ∀x j,Reads (previousBank l base x (pageOf j 0))
      (original x (pageOf j 0)) l.lanes m)
    (after : ∀x j,Reads (previousBank l base x (pageOf j 0))
      (copy x (pageOf j 0)) l.lanes m) : BookTags copy :=by
  intro j h g
  let z:=l.index.symm j
  have cells:=Reads.determined (after z.1 z.2.2) (before z.1 z.2.2) live room
  change (ScalarOperand.take z.2.1 (copy z.1 (pageOf z.2.2 0) h g)).val≤2
  rw [cells]
  exact valid j h g

end
end Hierarchy.DescentDatedPriorOperand

end OAI
