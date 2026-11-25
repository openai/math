import OAI.Hierarchy.DescentOperandCandidateLookup
import OAI.Hierarchy.DescentOperandStateBanks

namespace OAI
/-! # One shared native dictionary serves the dated reset's candidate-indexed pointer pages -/
namespace Hierarchy.DescentOperandCandidateLookup.Batch
open DescentSIMDLookup DescentPackedZip DescentOperandStateBanks DescentOrdinaryAtomFieldRAM.ROM
open DescentColonies.SplitRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {n count a b H G M w base out : ℕ}

def term (query : Fin count→Expr) (previous : Fin count→Fin n→Expr) (base a b M : ℕ) (j : ℕ) :=
  if h : j<count then expr (query ⟨j,h⟩) (previous ⟨j,h⟩) base a b M else .lit 0

def passes (query : Fin count→Expr) (previous : Fin count→Fin n→Expr) (base out a b H G M : ℕ) :=
  DescentPackedFlowBatch.passes out (H*chunks G M) (H*chunks G M) (term query previous base a b M) 0 count

def program (query : Fin count→Expr) (previous : Fin count→Fin n→Expr) (base out a b H G M w : ℕ) :=
  (mount (pages n a b M) (bits a b M) w base).seq (ProtocolRAM.program w (passes query previous base out a b H G M))

def imageAt (query : Fin count→Expr) (previous : Fin count→Fin n→Expr) (base out a b H G M : ℕ) (m : Memory w) :=
  result (passes query previous base out a b H G M) (after (pages n a b M) (bits a b M) base m)

def work (query : Fin count→Expr) (previous : Fin count→Fin n→Expr) (base out a b H G M : ℕ) :=
  4+10*((n*2)*2^(bits a b M))+clock (passes query previous base out a b H G M)

def outputEnd (count H G M out : ℕ) := out+count*(H*chunks G M)

theorem work_le (q : Fin count→Expr) (v : Fin count→Fin n→Expr) (cost : ℕ)
    (cap : ∀j i,(q j).work+(v j i).work+11≤cost) :
    work q v base out a b H G M ≤
      4+10*((n*2)*2^(bits a b M))+(4+count*(4+(H*chunks G M)*(2*(1+n*(cost+1))+4))) := by
  apply Nat.add_le_add_left
  apply DescentPackedFlowBatch.tariff
  intro j h
  simp only [term,dite_eq_left h,expr]
  let at_:=fun i=>(table base a b M i).read (q ⟨j,h⟩) (v ⟨j,h⟩ i)
  have every (i : Fin n) : (at_ i).work≤cost := by
    simpa only [at_,DescentPackedZip.work] using cap ⟨j,h⟩ i
  simpa only [List.length_finRange] using work_total at_ cost every (List.finRange n)

theorem run (query : Fin count→Expr) (old : Fin count→Fin n→Expr) (source : Memory w)
    (tickets : Fin count→Fin H→Fin G→Option (Fin n)) (item : Fin count→Fin n→Fin H→Fin G→Cell b)
    (fits : ∀j,(query j).Fits w base) (prev : ∀j i,(old j i).Fits w base) (small : n<2^a)
    (queries : ∀j,Source (query j) (fun h g=>code small (tickets j h g)) M source)
    (values : ∀j i,Source (old j i) (item j i) M source)
    (apart : dictionaryEnd n a b M base ≤ out) (room : outputEnd count H G M out<2^w) :
    let done:=imageAt query old base out a b H G M source
    (program query old base out a b H G M w).Exec source done (work query old base out a b H G M) ∧
      (∀j r,done (address out (H*chunks G M) j (row H G M r))=((data (selected (tickets j) (item j)) r).val:Word w)) ∧
      (∀z,z<base ∨ (dictionaryEnd n a b M base ≤ z ∧ z<out) ∨ outputEnd count H G M out≤z → done z=source z) ∧
      CheapCode (program query old base out a b H G M w) := by
  intro done
  let span:=bits a b M
  let book:=pages n a b M
  let dict:=after book span base source
  let rows:=H*chunks G M
  let expression:=term query old base a b M
  have limit : out+count*rows<2^w:=room
  have stop : out<2^w := (Nat.le_add_right ..).trans_lt limit
  have sep : base+(n*2)*2^span≤out:=apart
  have fromROM:=DescentOrdinaryAtomFieldRAM.ROM.run book span base source (sep.trans_lt stop)
  have romFrame:=DescentOrdinaryAtomFieldRAM.ROM.frame book span base source
  have prepared_ (j : Fin count) := prepared (query j) (old j) source (tickets j) (item j) (fits j)
    (prev j) small (queries j) (values j) apart stop
  have early (j : ℕ) (h : j<count) : (expression j).Fits w out := by
    simpa only [expression,term,dite_eq_left h] using (prepared_ ⟨j,h⟩).1
  obtain ⟨scanned,output,below⟩:=DescentPackedFlowBatch.execute out rows rows count expression dict early limit le_rfl
  refine ⟨Procedure.Exec.then fromROM.1 scanned,?_,?_,cheap_seq (cheap book span w base) (program_cheap w _)⟩
  · intro j r
    have stored:=output j (row H G M r)
    change result (DescentPackedFlowBatch.passes out rows rows expression 0 count) dict
      (out+j.val*rows+(row H G M r).val) = _
    exact stored.trans (by simpa only [expression,term,dite_eq_left j.isLt] using (prepared_ j).2 r)
  · intro z where_
    rcases where_ with lo|gap|hi
    · exact (below z (lo.trans_le ((Nat.le_add_right ..).trans sep))).trans (romFrame z (.inl lo))
    · exact (below z gap.2).trans (romFrame z (.inr gap.1))
    · have frame:=DescentPackedFlowBatch.above out rows rows expression dict 0 count z le_rfl (by simpa [outputEnd,rows] using hi)
      exact frame.trans (romFrame z (.inr (sep.trans ((Nat.le_add_right ..).trans hi))))

end
end Hierarchy.DescentOperandCandidateLookup.Batch

end OAI
