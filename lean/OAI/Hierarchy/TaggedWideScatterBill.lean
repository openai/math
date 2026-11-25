import OAI.Hierarchy.TaggedWideScatter
import OAI.Hierarchy.ProtocolRAMTurnText
import OAI.Hierarchy.ProtocolRAMGeneratedWriteCheap
import OAI.ThreeFlat.RAM.ProcedureBank

namespace OAI
/-! # Native instruction and execution counts for a finite bank of scatter procedures -/
noncomputable section
namespace Hierarchy.ProtocolRAM.NativeSiteWork
open Computability.VPVNP.BurstRAM PrivateRAM

/-- The expression traversals are repeated once at each actual native row.
A zero-length input still pays the fixed scan and initialization costs. -/
theorem replay (length n h K B : ℕ) (A V : Expr) (hl : length≤K*2^h) (hn : n≤K*2^h)
    (ha : A.work≤B) (hv : V.work≤B) :
    ProtocolRAMTurnReplay.work length n A V≤(15+K*(24+4*B))*2^h := by
  have ax := Nat.mul_le_mul hn (show 2*A.work+4≤2*B+4 by omega)
  have vx := Nat.mul_le_mul hn (show 2*V.work+4≤2*B+4 by omega)
  have pos : 0<2^h := pow_pos (by decide) _
  unfold ProtocolRAMTurnReplay.work ProtocolRAMGeneratedWrite.work
  nlinarith

end Hierarchy.ProtocolRAM.NativeSiteWork

namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProbeStage Native
open scoped Classical BigOperators

theorem Scatter.native (s : Scatter) (w : ℕ) : CheapCode (s.code w) ∧
    text (s.code w)=57+4*s.address.work+4*s.value.work := by
  constructor
  · exact cheap_seq (scan_cheap w s.base s.length (.lit 0))
      (ProtocolRAMRankCheap.generated w s.scratch (s.scratch+s.rows) s.rows s.address s.value)
  · simp only [Scatter.code,ProtocolRAMTurnReplay.program,text_seq,text_scan,ProtocolRAMTurnText.generated,
      rowText,Expr.work]
    omega

theorem bank_native {w : ℕ} (n : ℕ) (f : Fin (n+1)→Procedure w)
    (cheap : ∀i,CheapCode (f i)) :
    CheapCode (ProcedureBank.program n f) ∧ text (ProcedureBank.program n f)=∑i,text (f i) := by
  induction n with
  | zero=>exact ⟨cheap 0,by simp [ProcedureBank.program]⟩
  | succ n ih=>
    have sub:=ih (fun i=>f i.succ) (fun i=>cheap _)
    refine ⟨cheap_seq (cheap 0) sub.1,?_⟩
    rw [ProcedureBank.program,text_seq,sub.2]
    exact (Fin.sum_univ_succ (fun i : Fin (n+1+1) => text (f i))).symm

theorem scatter_bank_resources {h K B : ℕ} (last W : ℕ) (sheets : Fin (last+1)→Scatter)
    (dims : ∀i,(sheets i).length≤K*2^h ∧ (sheets i).rows≤K*2^h)
    (expr : ∀i,(sheets i).address.work≤B ∧ (sheets i).value.work≤B) :
    (∑i,(sheets i).ticks)≤((last+1)*(15+K*(24+4*B)))*2^h ∧
    text (ProcedureBank.program last (fun i=>(sheets i).code W))≤(last+1)*(57+8*B) ∧
    CheapCode (ProcedureBank.program last (fun i=>(sheets i).code W)) := by
  have native:=bank_native last (fun i=>(sheets i).code W) (fun i=>((sheets i).native W).1)
  have rt (i) : (sheets i).ticks≤(15+K*(24+4*B))*2^h :=
    NativeSiteWork.replay _ _ h K B _ _ (dims i).1 (dims i).2 (expr i).1 (expr i).2
  have program (i) : text ((sheets i).code W)≤57+8*B := by
    rw [((sheets i).native W).2]
    have q:=expr i;omega
  refine ⟨?_,native.2.trans_le ?_,native.1⟩
  · simpa [Nat.mul_assoc] using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>rt i)
  · simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>program i)

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
