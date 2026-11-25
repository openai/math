import OAI.Optimization.LinearProgramming.BitRAM.DispatchCompiler

/-! External application data in the even part of the address bank survives every
dispatched bit instruction. Linked binary heap nodes occupy odd addresses. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace Dispatch
open RAM RAM.Tape OracleSpec
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem action_complete {p : BitProgram} {c : p.Config} (op : Op p)
    {m : Memory K} {P : K → Prop} (r : Rep p c m) (safe : Good P m) :
    ∃ t k, k ≤ 10 ∧ Block.Eval (Good P) (actionBlock p op) m k t ∧
      Issued p c op t ∧ t.data=m.data ∧ StableHeaders m t ∧ StableEven m t := by
  cases ht : ordinaryTarget c op with
  | some t =>
    obtain ⟨out,k,exec,bound,rep,data,headers,even⟩ := action_complete_frame op ht r safe
    exact ⟨out,k,bound,exec,.ordinary ht rep,data,headers,even⟩
  | none =>
    obtain ⟨q,rfl⟩ : ∃ q, op = .ask q := by cases op <;> simp_all [ordinaryTarget]
    obtain ⟨out,exec,waiting,data,headers,even⟩ := ask_complete_frame q r safe
    exact ⟨out,2,by decide,exec,.ask waiting,data,headers,even⟩

theorem issuedTable_complete_frame {p : BitProgram} {c : p.Config} {q : Fin p.states}
    (hpc : c.pc = some q) {m : Memory K} {P : K → Prop} (r : Rep p c m) (safe : Good P m) :
    ∃ t k, k ≤ 2*p.states+27 ∧ Block.Eval (Good P) (issuedTable p) m k t ∧
      Issued p c (p.instruction q (c.store (p.scan q)).head?) t ∧ t.data=m.data ∧
      StableHeaders m t ∧ StableEven m t := by
  apply issuedTable_of_actions (fun a t => StableHeaders a t ∧ StableEven a t) _ _ hpc r safe
  · intro m a t eqv fr
    exact ⟨fun i lo hi => (fr.1 i lo hi).trans (eqv i (by omega) (by unfold thresholdReg;omega)),
      fun i lo ev => (fr.2 i lo ev).trans (eqv i (by omega) (by unfold thresholdReg;omega))⟩
  · exact fun op _ h g => action_complete op h g

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI
