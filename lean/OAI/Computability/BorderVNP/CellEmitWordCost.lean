import OAI.Computability.BorderVNP.CellEmitWord
import OAI.Computability.BorderVNP.CellCQFMeterPair

/-! # Input-specific physical clock for the private word emitters -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram
open RationalHitting.StackLanguage (codeWord)

variable {α : Type} {ea : α → List Bool} {a b : α → List Bool}

/-- The framing table uses seven source steps per payload bit and fixed overhead. -/
theorem meter_codeWordP (xs : List Bool) : codeWordP.meter xs ≤ 10*xs.length+7 := by
  have h := codeWordP.cost_le_bound xs
  change _ ≤ (Polynomial.C 7*Polynomial.X+Polynomial.C 5).eval xs.length at h
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] at h
  simp only [Procedure.meter,id_eq,RationalHitting.StackLanguage.codeWord_length]
  omega

/-- The physical concatenation program has linear overhead in both of its child
executions and the words copied through its registers. -/
theorem meter_wordAppend (p : Word ea a) (q : Word ea b) (x : α) :
    (wordAppend p q).meter x ≤ 10^12*(p.meter x+q.meter x) := by
  have h := Procedure.meter_comp Procedure.append (p.pair q) x
  have hp := Procedure.meter_pair p q x
  have ha := Procedure.meter_append (a x,b x)
  have hw := p.words_le_meter x
  have hz := q.words_le_meter x
  simp only [id_eq] at hw hz
  simp only [prodCode,pairBits_length,id_eq] at ha
  unfold wordAppend
  omega

/-- Prepending a fixed prefix charges its actual length in addition to the
child's clean execution. -/
theorem meter_wordPrepend (tag : List Bool) (p : Word ea a) (x : α) :
    (wordPrepend tag p).meter x ≤ 32*(p.meter x+tag.length+1) := by
  let q := Procedure.prepend id tag
  have h := Procedure.meter_comp q p x
  have hp := q.cost_le_bound (a x)
  change q.cost (a x) ≤ (Polynomial.C (tag.length+1)).eval _ at hp
  rw [Polynomial.eval_C] at hp
  have hw := p.words_le_meter x
  simp only [id_eq] at hw
  have hq : q.meter (a x) ≤ 2*((a x).length+tag.length+1) := by
    simp only [Procedure.meter,id_eq,List.length_append]
    omega
  simpa only [wordPrepend,Procedure.meter_result] using (h.trans (by omega))

/-- A constant emitter clears its actual input and prints the fixed result. -/
theorem meter_constWord (ea : α → List Bool) (w : List Bool) (x : α) :
    (constWord (ea:=ea) w).meter x ≤ 3*((ea x).length+w.length+1) :=
  Procedure.meter_constant ea id w x

/-- Framing a computed payload is linear in its own measured execution. -/
theorem meter_framed (p : Word ea a) (x : α) : (framed p).meter x ≤ 120*p.meter x := by
  have h := Procedure.meter_comp codeWordP p x
  have hq := meter_codeWordP (a x)
  have hw := p.words_le_meter x
  simp only [id_eq] at hw
  exact h.trans (by omega)

/-- One complete native instruction record uses a marker and one framed payload. -/
theorem meter_singleRecord (p : Word ea a) (x : α) : (singleRecord p).meter x ≤ 4000*p.meter x := by
  have h := meter_wordPrepend [true] (framed p) x
  have hf := meter_framed p x
  have hw := p.words_le_meter x
  simp only [List.length_singleton] at h
  simpa only [singleRecord,Procedure.meter_congrFun] using h.trans (by omega)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
