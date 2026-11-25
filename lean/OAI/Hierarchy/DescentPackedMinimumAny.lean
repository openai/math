import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.DescentPackedMinimum
import OAI.Hierarchy.DescentTerminalUniversalWrite

namespace OAI
/-! # Total execution of the score scans on arbitrary preceding words -/
namespace Hierarchy.DescentPackedMinimum
open DescentSIMDLookup DescentPackedScore ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {a M H G w q : ℕ}
attribute [local irreducible] Procedure.Exec

theorem issue_any_framed (L : Layout q) (r : Fits L w a M H G) (m : Memory w) (xs : List (Fin q)) :
    ∃out,(program L w H G M xs).Exec m out (4+xs.length*cost L.work (H*chunks G M)) ∧
      ∀u,u<L.work ∨ L.result≤u → out u=m u :=by
  let n:=H*chunks G M
  have span:=r.workspace;have ledger:=r.ledger.2.2;have room:=r.room
  induction xs with
  | nil=>
      have go:=scan_exec L.work 0 (.lit 0) m trivial (by omega)
      refine ⟨ProtocolRAM.image L.work 0 (.lit 0) m,?_,?_⟩
      · simpa only [program,List.length_nil,Nat.zero_mul,Nat.add_zero] using go
      · intro u _
        apply ProtocolRAMGeneratedWrite.frame_image
        omega
  | cons i xs ih=>
      obtain ⟨mid,step,prior⟩:=ih
      let term:=SumScores.step w L.work n 0 (DescentPackedScore.read (L.source i) (L.dictionary i))
      have execute:=DescentTerminalUniversalWrite.run term L.work (n+1) mid (by dsimp [n];omega)
      have fee:2*term.binds+4=66:=by rw [show term.binds=19+(DescentPackedScore.read (L.source i) (L.dictionary i)).work from SumScores.step_binds ..];rfl
      rw [fee] at execute
      have fitted : (fetch L.work n).Fits w (L.ledger.base+i.val):=by
        unfold fetch;split
        · trivial
        · refine ⟨⟨by simp [Bank.size],by simpa [Bank.size] using r.word,?_⟩,trivial⟩
          change L.work+(n-1)+1≤L.ledger.base+i.val;dsimp [n];omega
      have ix:=i.isLt.trans_le r.capacity
      let scored:=DescentTerminalUniversalWrite.image term L.work (n+1) mid
      have copied:=scan_exec (L.ledger.base+i.val) 1 (fetch L.work n) scored fitted (by omega)
      refine ⟨ProtocolRAM.image (L.ledger.base+i.val) 1 (fetch L.work n) scored,?_,?_⟩
      · have amt : (4+xs.length*cost L.work n+(4+(n+1)*66))+(4+1*(2*(fetch L.work n).work+4))=4+(i::xs).length*cost L.work n:=by simp only [List.length_cons,Nat.succ_mul,cost];ring
        rw [←amt]
        exact (step.then execute).then copied
      · intro u away
        have saved : ¬(L.work≤u ∧ u<L.work+(n+1)):=by dsimp [n];omega
        have off : u<L.ledger.base+i.val ∨ L.ledger.base+i.val+1≤u:=by
          have count:=i.isLt
          have cap:=r.capacity
          omega
        have persistent : scored u=mid u:=by
          simp only [scored,DescentTerminalUniversalWrite.image,fillSegment,ite_eq_right saved]
        exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ off).trans (persistent.trans (prior u away))

theorem any (L : Layout q) (r : Fits L w a M H G) (m : Memory w) :
    ∃o,(search L w H G M).Exec m o ((4+q*cost L.work (H*chunks G M))+DescentFirstMinimumRAM.ticks L.result L.ledger (List.range q)) :=by
  obtain ⟨mid,ran,_⟩:=issue_any_framed L r m (List.finRange q)
  have pick:=DescentFirstMinimumRAM.exec L.ledger mid (List.range q) r.ledger (by simpa using r.room) r.word
  exact ⟨_,by simpa only [search,List.length_finRange] using ran.then pick⟩

end
end Hierarchy.DescentPackedMinimum

end OAI
