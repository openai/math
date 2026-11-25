import OAI.Computability.BorderVNP.CellEmitAddressCost
import OAI.Computability.BorderVNP.CellEmitStatement

/-! # Sharp native printing clocks for compact control statements -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram
open CellMacro.Generator (serialized)

variable {α : Type} {ea : α → List Bool} {a b : α → NatExpr} {s t : α → Stmt}

/-- Printing a constant statement charges its actual sparse serialization. -/
theorem meter_constStmt (ea : α → List Bool) (s : Stmt) (x : α) :
    (constStmt ea s).meter x ≤ 3*((ea x).length+(serialized 8 s).length+1) :=
  meter_constWord ea _ x

/-- Sequential composition concatenates the actual two outputs. -/
theorem meter_seqStmt (p : Statement ea s) (q : Statement ea t) (x : α) :
    (seqStmt p q).meter x ≤ 10^12*(p.meter x+q.meter x) := by
  have he (z : α) : serialized 8 (s z) ++ serialized 8 (t z) = serialized 8 (.seq (s z) (t z)) := by
    simp [serialized,CellMacro.Generator.wire,records_append]
  change ((wordAppend p q).congrFun he).meter x ≤ _
  rw [Procedure.meter_congrFun (wordAppend p q) he x]
  exact meter_wordAppend p q x

/-- Read records have only constant framing overhead in addition to their address. -/
theorem meter_readStmt (p : Address ea a) (x : α) :
    (readStmt p).meter x ≤ 10^7*(addrMeter p x+1) := by
  have h := meter_singleRecord (wordPrepend [false,false,true] (p 8)) x
  have h₁ := meter_wordPrepend [false,false,true] (p 8) x
  have h₂ := meter_le_addrMeter p x (d:=8) (by decide)
  simp only [List.length_cons,List.length_nil] at h₁
  exact h.trans (by omega)

/-- Binary extraction prints its two address operands with linear overhead. -/
theorem meter_bitStmt (p : Address ea a) (q : Address ea b) (x : α) :
    (bitStmt p q).meter x ≤ 10^20*(addrMeter p x+addrMeter q x+1) := by
  let payload := wordAppend (framed (p 8)) (q 8)
  have h := meter_singleRecord (wordPrepend [false,true] payload) x
  have h₁ := meter_wordPrepend [false,true] payload x
  have h₂ := meter_wordAppend (framed (p 8)) (q 8) x
  have h₃ := meter_framed (p 8) x
  have h₄ := meter_le_addrMeter p x (d:=8) (by decide)
  have h₅ := meter_le_addrMeter q x (d:=8) (by decide)
  change payload.meter x ≤ _ at h₂
  simp only [List.length_cons,List.length_nil] at h₁
  exact h.trans (by omega)

/-- A dynamic loop prints its compact body just once. -/
theorem meter_loopStmt (p : Address ea a) (q : Statement ea s) (x : α) :
    (loopStmt p q).meter x ≤ 10^20*(addrMeter p x+q.meter x+1) := by
  let payload := wordAppend (framed (p 8)) q
  have h := meter_singleRecord (wordPrepend [true,false] payload) x
  have h₁ := meter_wordPrepend [true,false] payload x
  have h₂ := meter_wordAppend (framed (p 8)) q x
  have h₃ := meter_framed (p 8) x
  have h₄ := meter_le_addrMeter p x (d:=8) (by decide)
  change payload.meter x ≤ _ at h₂
  simp only [List.length_cons,List.length_nil] at h₁
  exact h.trans (by omega)

/-- Printing both alternatives, the difference address and their framing adds
only a fixed linear factor to the input-specific charges. -/
theorem meter_ifEqStmt (p : Address ea a) (q : Address ea b) (yes : Statement ea s)
    (no : Statement ea t) (x : α) :
    (ifEqStmt p q yes no).meter x ≤
      10^90*(addrMeter p x+addrMeter q x+yes.meter x+no.meter x+1) := by
  let delta := addAddr (subAddr p q) (subAddr q p)
  let arms := wordAppend (framed yes) no
  let payload := wordAppend (framed (delta 8)) arms
  have hd₀ := meter_addAddr (subAddr p q) (subAddr q p) x
  have hd₁ := meter_subAddr p q x
  have hd₂ := meter_subAddr q p x
  have h₀ := meter_le_addrMeter delta x (d:=8) (by decide)
  have h₁ := meter_framed (delta 8) x
  have h₂ := meter_framed yes x
  have h₃ := meter_wordAppend (framed yes) no x
  have h₄ := meter_wordAppend (framed (delta 8)) arms x
  have h₅ := meter_wordPrepend [true,true] payload x
  have h := meter_singleRecord (wordPrepend [true,true] payload) x
  change addrMeter delta x ≤ _ at hd₀
  simp only [List.length_cons,List.length_nil] at h₅
  change arms.meter x ≤ _ at h₃
  change payload.meter x ≤ _ at h₄
  exact h.trans (by omega)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
