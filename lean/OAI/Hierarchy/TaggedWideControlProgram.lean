import OAI.Hierarchy.TaggedWideControlGateEval
import OAI.Hierarchy.ProtocolRAMMachine

namespace OAI
/-! # Mounting an actual native procedure on one binary control gate -/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin.Gate
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ProtocolRAM
open scoped Classical

/-- Mount the literal procedure text with its native terminal-return instruction sequence. -/
def ofProcedure {W S f u : ℕ} (P : Procedure W) (ret start : Word W) (addr : Fin u→Word W)
    (m : ℕ) (word : 3≤W+1) (labels : P.labels+3≤2^(W+1)) (hs : S≤2^W) (clock : f+u≤2^(W+1)) : Gate :=
  ⟨W,P.labels+3,P.registers+1,P.slots,S,f,u,m,ProtocolRAM.machine P ret,word,labels,start,addr,hs,clock⟩

theorem ofProcedure_run {W S f u : ℕ} (P : Procedure W) (ret start : Word W) (addr : Fin u→Word W)
    (m : ℕ) (word : 3≤W+1) (labels : P.labels+3≤2^(W+1)) (hs : S≤2^W) (clock : f+u≤2^(W+1))
    (head : ℕ→Word W) (out : Memory W) (budget : ℕ) (fits : budget+2<f)
    (exec : P.Exec (initialMemory S head) out budget) :
    (ofProcedure P ret start addr m word labels hs clock).Ran head out := by
  obtain ⟨t,ht,done,ran,halt⟩ := machine_run P ret start _ out budget exec
  exact ⟨⟨t,done,some (out ret.val),ht.trans_lt fits,ran,halt⟩⟩

end Hierarchy.Tagged.WideControlJoin.Gate

end
end OAI
