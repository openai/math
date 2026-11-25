import OAI.Optimization.LinearProgramming.BitRAM.Dispatch
import OAI.Optimization.LinearProgramming.BitRAM.Ops

/-! The finite RAM decision table, with the real linked-heap subprogram installed in
every row. It implements all ordinary bit instructions and stages each oracle request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

variable {K : Type*}
open RAM RAM.Tape OracleSpec
namespace Dispatch

def issuedTable (p : BitProgram) : Block :=
  table p (fun s => peek (headReg (some s))) (actionBlock p)

inductive Issued (p : BitProgram) (c : p.Config) : Op p → Memory K → Prop where
  | ordinary {op c' m} (next : ordinaryTarget c op = some c') (result : Rep p c' m) :
      Issued p c op m
  | ask {q m} (prepared : Awaiting p c q m) : Issued p c (.ask q) m

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem action_issues {p : BitProgram} {c : p.Config} (op : Op p)
    {m : Memory K} {P : K → Prop} (r : Rep p c m) (safe : Good P m) :
    ∃ t k, k ≤ 10 ∧ Block.Eval (Good P) (actionBlock p op) m k t ∧
      Issued p c op t ∧ t.data = m.data ∧ StableHeaders m t := by
  cases ht : ordinaryTarget c op with
  | some t =>
    obtain ⟨out,k,hk,bound,rep,data,headers⟩ := action_framed op ht r safe
    exact ⟨out,k,bound,hk,.ordinary ht rep,data,headers⟩
  | none =>
    obtain ⟨q,rfl⟩ : ∃ q, op = .ask q := by
      cases op <;> simp_all [ordinaryTarget]
    obtain ⟨out,hk,waiting,data,headers⟩ := ask_framed q r safe
    exact ⟨out,2,by decide,hk,.ask waiting,data,headers⟩

private theorem tag_correct (b : Option Bool) : topTag b = (tagIndex b).val := by
  cases b with
  | none => rfl
  | some b => cases b <;> rfl

/-- The instruction is selected by the stored program counter and the actual top of the
specified stack. No inspection of the host configuration is performed by the RAM code. -/
theorem issuedTable_of_actions {p : BitProgram} {c : p.Config} {q : Fin p.states} {P : K → Prop}
    (frame : Memory K → Memory K → Prop)
    (extend : ∀ m a t, (∀ i, i≠0 → i≠thresholdReg → a.index i=m.index i) → frame a t → frame m t)
    (actions : ∀ (op : Op p) (m : Memory K), Rep p c m → Good P m →
      ∃ t k, k ≤ 10 ∧ Block.Eval (Good P) (actionBlock p op) m k t ∧
        Issued p c op t ∧ t.data=m.data ∧ frame m t)
    (hpc : c.pc=some q) {m : Memory K} (r : Rep p c m) (safe : Good P m) :
    ∃ t k, k ≤ 2*p.states+27 ∧ Block.Eval (Good P) (issuedTable p) m k t ∧
      Issued p c (p.instruction q (c.store (p.scan q)).head?) t ∧ t.data=m.data ∧ frame m t := by
  let b := (c.store (p.scan q)).head?
  let s := m.putIndex thresholdReg (q.val+1)
  have repr : Rep p c s := r.putScratch (i := thresholdReg) (by decide) _
  obtain ⟨mid,j,pe,hj,hd,hidx,htag⟩ := peek_correct repr.heap (show Good P s from safe) (some (p.scan q))
  have rmid : Rep p c mid := repr.of_odd_eq (fun i hi _ => hidx i (by omega))
  let a := mid.putIndex thresholdReg ((tagIndex b).val+1)
  have ra : Rep p c a := rmid.putScratch (i := thresholdReg) (by decide) _
  obtain ⟨out,k,hk,run,result,data,headers⟩ :=
    actions (p.instruction q b) a ra (show Good P a from pe.safe_end)
  have tc : mid.index 0=(tagIndex b).val := htag.trans (tag_correct b)
  have qc : m.index 39=q.val := by simpa only [show 39 = stateReg from rfl,hpc,pcCode,Option.elim] using r.stateCode
  have whole := table_eval p (fun s => peek (headReg (some s))) (actionBlock p) q b safe
    (fun _ => safe) qc pe (fun _ => pe.safe_end) tc run
  refine ⟨out,_,?_,whole,result,data.trans hd,?_⟩
  · have hi := (tagIndex b).isLt
    have hq := q.isLt
    omega
  · apply extend m a out _ headers
    intro i nz neq
    exact (Memory.putIndex_ne _ neq _).trans ((hidx i nz).trans (Memory.putIndex_ne _ neq _))

theorem issuedTable_correct {p : BitProgram} {c : p.Config} {q : Fin p.states}
    (hpc : c.pc = some q) {m : Memory K} {P : K → Prop} (r : Rep p c m) (safe : Good P m) :
    ∃ t k, k ≤ 2*p.states+27 ∧ Block.Eval (Good P) (issuedTable p) m k t ∧
      Issued p c (p.instruction q (c.store (p.scan q)).head?) t ∧ t.data=m.data ∧ StableHeaders m t :=
  issuedTable_of_actions StableHeaders
    (fun _ _ _ eqv fr i lo hi => (fr i lo hi).trans (eqv i (by omega) (by unfold thresholdReg; omega)))
    (fun op _ h g => action_issues op h g) hpc r safe

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI
