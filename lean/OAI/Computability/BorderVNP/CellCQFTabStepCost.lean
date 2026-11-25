import OAI.Computability.BorderVNP.CellCQFMeterPair
import OAI.Computability.QuantumFactoring.BitStackTabulate

/-! # Cost of the concrete native tabulation body at one actual list prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → ℕ → β}

private theorem meter_listCons (e : β → List Bool) (b : β) (bs : List β) :
    (listCons e).meter (b,bs) ≤ 3*((prodCode e (listCode e) (b,bs)).length+1) := by
  have ht := (listCons e).cost_le_bound (b,bs)
  change _ ≤ (Polynomial.C (2:ℕ)).eval _ at ht
  rw [Polynomial.eval_C] at ht
  simp only [meter,prodCode,pairBits_length,listCode_length_cons]
  omega

private theorem meter_unarySuccessor (i : ℕ) : unarySuccessor.meter i ≤ 3*(i+1) := by
  have ht := unarySuccessor.cost_le_bound i
  change _ ≤ (1 : Polynomial ℕ).eval _ at ht
  rw [Polynomial.eval_one] at ht
  simp only [meter,unaryCode,List.length_replicate]; omega

/-- Only the actual user-supplied body is invoked. Its input is the original
environment and current unary index; prefix construction and projection cost
linearly in the sizes of that prefix, environment, and new row. -/
theorem meter_tabStepP (p : Procedure (prodCode unaryCode ea) eb (fun x => f x.2 x.1)) (i : ℕ) (a : α) (ys : List β) :
    (tabStepP p).meter (i,a,ys) ≤ 10^46*(p.meter (i,a) + (listCode eb ys).length + 1) := by
  let lc := listCode eb
  let ctx := prodCode ea lc
  let idx := first unaryCode ctx
  let rest := second unaryCode ctx
  let env := (first ea lc).comp rest
  let prev := (second ea lc).comp rest
  let inp := idx.pair env
  let child := p.comp inp
  let pairList := child.pair prev
  let cons := (listCons eb).comp pairList
  let inner := env.pair cons
  let succ := unarySuccessor.comp idx
  let z := (i,a,ys)
  have hidx := meter_first unaryCode ctx z
  have hrest := meter_second unaryCode ctx z
  have hen := meter_comp (first ea lc) rest z
  have hen' := meter_first ea lc (a,ys)
  have hprev := meter_comp (second ea lc) rest z
  have hprev' := meter_second ea lc (a,ys)
  have hi := meter_pair idx env z
  have hp := meter_comp p inp z
  have hpl := meter_pair child prev z
  have hl := meter_comp (listCons eb) pairList z
  have hl' := meter_listCons eb (f a i) ys
  have hinner := meter_pair env cons z
  have hsucc := meter_comp unarySuccessor idx z
  have hsucc' := meter_unarySuccessor i
  have htop := meter_pair succ inner z
  have hw := p.words_le_meter (i,a)
  change (succ.pair inner).meter z ≤ _
  change idx.meter z ≤ _ at hidx
  change rest.meter z ≤ _ at hrest
  change env.meter z ≤ 6*(rest.meter z+(first ea lc).meter (a,ys)) at hen
  change prev.meter z ≤ 6*(rest.meter z+(second ea lc).meter (a,ys)) at hprev
  change inp.meter z ≤ _ at hi
  change child.meter z ≤ 6*(inp.meter z+p.meter (i,a)) at hp
  change pairList.meter z ≤ _ at hpl
  change cons.meter z ≤ 6*(pairList.meter z+(listCons eb).meter (f a i,ys)) at hl
  change inner.meter z ≤ _ at hinner
  change succ.meter z ≤ 6*(idx.meter z+unarySuccessor.meter i) at hsucc
  simp only [z,ctx,lc,prodCode,pairBits_length,unaryCode,List.length_replicate] at *
  omega

end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  meter_tabStepP)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
