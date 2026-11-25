import OAI.Computability.BorderVNP.CellEmitBoolean
import OAI.Computability.BorderVNP.CellProfileAuxRow
import OAI.Computability.QuantumFactoring.BitStackAdder

/-! # Native descriptor emission for one-hot prefix checks

Every output is the compact serialization of the original bounded-loop command.
The symbolic row index and selector are supplied at their actual lexical depth.
The candidate loop stores one transition body for all possible prefix counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram CellMacro.Generator

variable {α : Type} {ea : α → List Bool}

/-- Increment a native binary scalar while assembling the compact address tree. -/
noncomputable def prefixSucc {c : α → ℕ} (hc : Procedure ea Nat.bits c) :
    Procedure ea Nat.bits (fun x => c x+1) :=
  Procedure.binaryAdd.comp (hc.pair (Procedure.constant _ _ 1))

/-- Produce the physical row-major address expression of a single prefix flag. -/
noncomputable def prefixFlag {base cap : α → ℕ} {i k : α → NatExpr}
    (hb : Procedure ea Nat.bits base) (hc : Procedure ea Nat.bits cap) (hi : Address ea i) (hk : Address ea k) :
    Boolean ea (fun x => Prefix.flagTerm (base x) (cap x) (i x) (k x)) :=
  wireBool (addAddr (addAddr (litAddr hb) (mulAddr hi (litAddr (prefixSucc hc)))) hk)

/-- Serialize the bounded initialization loop for one flag rectangle. -/
noncomputable def prefixInit {base cap : α → ℕ} (hb : Procedure ea Nat.bits base) (hc : Procedure ea Nat.bits cap) :
    Statement ea (fun x => Prefix.initGen (base x) (cap x)) := by
  let k := constAddr ea (.index 0)
  let z := constAddr ea (.lit 0)
  let flag := prefixFlag hb hc z k
  exact loopStmt (litAddr (prefixSucc hc)) (ifEqStmt k z (guardBool flag) (guardBool (notBool flag)))

/-- Emit the exact NAND implementation of a transition, with the previous flag
supplied by the zero or positive candidate branch. -/
noncomputable def prefixTest {base cap : α → ℕ} {i k : α → NatExpr} {m prior : α → Term}
    (hb : Procedure ea Nat.bits base) (hc : Procedure ea Nat.bits cap)
    (hi : Address ea i) (hk : Address ea k) (hm : Boolean ea m) (hp : Boolean ea prior) :
    Boolean ea (fun x => Prefix.rowTest (base x) (cap x) (i x) (k x) (m x) (prior x)) :=
  equalBool (prefixFlag hb hc (addAddr hi (constAddr ea (.lit 1))) hk)
    (orBool (andBool (notBool hm) (prefixFlag hb hc hi hk)) (andBool hm hp))

/-- Emit the two candidate branches and their common loop. Caller-supplied
addresses and match terms are embedded under this candidate counter. -/
noncomputable def prefixStep {base cap : α → ℕ} {i : α → NatExpr} {m : α → Term}
    (hb : Procedure ea Nat.bits base) (hc : Procedure ea Nat.bits cap)
    (hi : Address ea (fun x => (i x).weaken)) (hm : Boolean ea (fun x => (m x).weaken)) :
    Statement ea (fun x => Prefix.stepGen (base x) (cap x) (i x) (m x)) := by
  let k := constAddr ea (.index 0)
  let z := constAddr ea (.lit 0)
  let pred := prefixFlag hb hc hi (subAddr k (constAddr ea (.lit 1)))
  let zero := guardBool (prefixTest hb hc hi k hm (constBool ea (.lit false)))
  let positive := guardBool (prefixTest hb hc hi k hm pred)
  exact loopStmt (litAddr (prefixSucc hc)) (ifEqStmt k z zero positive)

/-- Serialize the full copy loop and candidate loop without expanding either trip count. -/
noncomputable def prefixGenerator {base copies cap : α → ℕ} {m : α → NatExpr → Term}
    (hb : Procedure ea Nat.bits base) (hj : Procedure ea Nat.bits copies) (hc : Procedure ea Nat.bits cap)
    (hm : Boolean ea (fun x => (m x (.index 0)).weaken)) :
    Statement ea (fun x => Prefix.generator (base x) (copies x) (cap x) (m x)) :=
  seqStmt (prefixInit hb hc) (loopStmt (litAddr hj)
    (prefixStep (i := fun _ => .index 0) hb hc (constAddr ea (.index 1)) hm))

/-- Locally allocated flags use two bounded-loop descriptors irrespective of their number. -/
noncomputable def scopedFlags {n : α → ℕ} {s : α → Stmt} (hn : Procedure ea Nat.bits n) (hs : Statement ea s) :
    Statement ea (fun x => localFlags (n x) (s x)) :=
  seqStmt (loopStmt (litAddr hn) (constStmt ea (.fixed .guess))) (seqStmt hs (loopStmt (litAddr hn)
    (constStmt ea (.seq (.fixed (.literal false)) (.seq (.fixed .nand) (.fixed .guard))))))

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
