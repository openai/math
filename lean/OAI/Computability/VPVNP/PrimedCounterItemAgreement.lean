import OAI.Computability.VPVNP.PrimedCounterDispatchNative
import OAI.Computability.VPVNP.PrimedCounterFold
import OAI.Computability.VPVNP.PrimedCounterChronology
import OAI.Computability.VPVNP.PrimedCounterItemAgreementBlocks

/-!
# Each native parser call executes its chronological logical transition

The absolute cursor selects the local code and prepares its operands. Row
division and remainder point the node routine at the corresponding assembled
tape. Success, rejection and the memory used by the next call agree with the
logical transition on the same per-call list of branch bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Data

open BurstRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

variable {L : Lengths} {n r H s w : ℕ} {Q : Layout L n r H w}

/-- At a node the pending frames must fit the stack and each counter must
have room for one increment. The administrative phases use these bounds
only when the cursor reaches a node. -/
theorem postItem_agreement (D : Data Q s) (hf : D.Fits) (shared : Internal L r H w → Bool)
    (st : VisitState n n s) (mem : Memory w) (held : D.Holds shared st mem)
    (raw : Chronology.PairTape n r D.labels) (i : Fold.PostItem (2*2^r) n (2*n-1) D.labels)
    (hnode : ∀ u j, i = .inl (u, .inr (.inr j)) →
      leafMass st.pending ≤ n ∧ ∀ a, st.counts a + 1 < 2^w) :
    let pos := Fold.slot (A := D.assembly) i
    ItemAgreement D shared mem (PrimedSchedule.control w D.total (pos.val+1))
      (Fold.call w D.degree D.root (Chronology.rowInput Q D.header shared)
        (labelIndex n n s) D.nomination raw st i)
      (execute D.machine.program D.fuel (D.machine.program.start (pos.val : Word w)) mem (raw pos)) := by
  have hm : D.parserPub (Admin.stackPublic 6) = (n : Word w) := congrFun D.parserPub_stack 6
  let regs : Regs w 52 := fun _ => 0
  let priv : Word w → Word w := fun _ => 0
  rcases i with ⟨u,j | (j | j)⟩ | j
  · let it : Cursor.Item D.assembly (2*2^r) n (2*n-1) D.labels := .inr (.inl (u,.inl j))
    let bs := raw (Cursor.index _ _ _ _ _ it)
    exact ItemAgreement.clear hf held j (Dispatch.prepared_clear_index regs u j)
      (fun out => Dispatch.clear_execute_iff (Opcodes.pubWord Q) D.parserPub hm hf.cursor regs priv mem bs D.fuel out u j)
  · let it : Cursor.Item D.assembly (2*2^r) n (2*n-1) D.labels := .inr (.inl (u,.inr (.inl j)))
    let bs := raw (Cursor.index _ _ _ _ _ it)
    exact ItemAgreement.init hf held (fun out =>
      Dispatch.init_execute_iff (Opcodes.pubWord Q) D.parserPub hm hf.cursor regs priv mem bs D.fuel out u j)
  · let it : Cursor.Item D.assembly (2*2^r) n (2*n-1) D.labels := .inr (.inl (u,.inr (.inr j)))
    let bs := raw (Cursor.index _ _ _ _ _ it)
    let v : Site r := finProdFinEquiv.symm u
    have hu : u.val = v.1.val*2^r + v.2.val := by
      have he : (finProdFinEquiv v).val = u.val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply u)
      change v.2.val + 2^r * v.1.val = _ at he
      rw [← he, Nat.mul_comm, Nat.add_comm]
    have hrow : (Dispatch.prepared regs it ∘ Program.parserRegs) 5 =
        (↑((v.1.val*2^r+v.2.val)*n) : Word w) := by
      change Dispatch.prepared regs it (Program.parserReg 5) = _
      rw [Dispatch.prepared_node_offset, hu]
    obtain ⟨hmass,hcounts⟩ := hnode u j rfl
    exact ItemAgreement.node hf held v.1 v.2 hrow hmass hcounts (fun out =>
      Dispatch.node_execute_iff (Opcodes.pubWord Q) D.parserPub hm hf.cursor regs priv mem bs D.fuel out u j)
  · let it : Cursor.Item D.assembly (2*2^r) n (2*n-1) D.labels := .inr (.inr j)
    let bs := raw (Cursor.index _ _ _ _ _ it)
    exact ItemAgreement.compare hf held j (Dispatch.prepared_compare_index regs j) (fun out =>
      Dispatch.compare_execute_iff (Opcodes.pubWord Q) D.parserPub hm hf.cursor regs priv mem bs D.fuel out j)

end PrimedCounter.Data

end VPVNP
end Computability
end OAI
