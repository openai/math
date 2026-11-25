import OAI.Hierarchy.CheapISACommit

namespace OAI
/-! # One source instruction has a bounded physical execution on the same RAM -/

namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing

variable {w p r k : ℕ} (M : Machine w p r k) (hp : p≤2^(w+1)) (hr : r≤2^(w+1))

include hp hr in
theorem step (cheap : ∀i,TaggedShorterCheapCPU.Cheap (M.code i))
    (c m d n) (rep : Rel M c m d n) (c' m') (ran : advance M.program 1 c m=some (c',m')) :
    ∃v e o,0≤v ∧ v≤64 ∧ advance (machine w p r M.entry).program v d n=some (e,o) ∧ Rel M c' m' e o := by
  obtain ⟨t,out,time,decoded,row⟩:=decode M hp hr rep
  obtain ⟨s,e,o,cost,go,h⟩:=commit M hp hr cheap row ran
  exact ⟨t+s,e,o,Nat.zero_le _,by omega,advance_trans decoded go,h⟩

include hp hr in
private theorem arrived_finish (i : Instr w p r k) (c m d n) (h : Entered M i c m d n)
    (ans : Option (Word w)) (endAt : i.run M.publicData c=.finish ans) :
    (machine w p r M.entry).program.step d=.finish (ans.map wide) := by
  cases i <;> try contradiction
  case returnState x =>
    cases endAt
    have pc : d.pc=63:=h.pc
    have val : d.reg 8=wide (c.reg x) := by
      have load:=h.x
      change d.reg 8=n (regAddr p x : Word (width w)).val at load
      rw [Fin.val_cast_of_lt (reg_fits hp hr x),h.banks.register] at load
      exact load
    simp [machine,Machine.program,pc,code,Instr.run,val]
  case accept =>
    cases endAt
    have pc : d.pc=64:=h.pc
    simp [machine,Machine.program,pc,code,Instr.run]

include hp hr in
theorem halt (c m d n) (rep : Rel M c m d n) (ans : Option (Word w))
    (endAt : M.program.step c=.finish ans) :
    ∃v e,v≤64 ∧ advance (machine w p r M.entry).program v d n=some (e,n) ∧
      (machine w p r M.entry).program.step e=.finish (ans.map wide) := by
  obtain ⟨t,e,paid,go,h⟩:=decode M hp hr rep
  exact ⟨t,e,by omega,go,arrived_finish M hp hr _ c m e n h ans endAt⟩

private theorem arrived_reject (i : Instr w p r k) (c m d n) (h : Entered M i c m d n)
    (fail : i.run M.publicData c=.reject) : (machine w p r M.entry).program.step d=.reject := by
  cases i <;> try contradiction
  case reject =>
    have pc : d.pc=48:=h.pc
    simp [machine,Machine.program,pc,code,Instr.run]

include hp hr in
theorem rejects (c m d n) (rep : Rel M c m d n) (fail : M.program.step c=.reject) :
    ∃v e,v≤47 ∧ advance (machine w p r M.entry).program v d n=some (e,n) ∧
      (machine w p r M.entry).program.step e=.reject := by
  obtain ⟨t,e,paid,go,h⟩:=decode M hp hr rep
  exact ⟨t,e,paid,go,arrived_reject M _ c m e n h fail⟩

end Hierarchy.CheapISA

end OAI
