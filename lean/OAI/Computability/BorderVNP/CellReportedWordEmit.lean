import OAI.Computability.BorderVNP.CellTableTermEmit
import OAI.Computability.BorderVNP.CellPrefixEmit
import OAI.Computability.BorderVNP.CellReportedWord

/-! # Physical emission of a reported binary subtotal check

The bit at an ordinal is compared to that ordinal of the candidate count.
A unary field width already encodes the all-ones binary mask for that width,
including the empty encoding at width zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring ExactQuantumFactoring.BitStackProgram

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

/-- Obtain the current ordinal and its original list element together with the source input. -/
noncomputable def withIndexedEntry (b : β) {items : α → List β} (hl : Procedure ea (listCode eb) items) :
    Procedure (prodCode ea Nat.bits) (prodCode ea (prodCode Nat.bits eb))
      (fun x => (x.1,x.2,((items x.1).drop x.2).headD b)) := by
  let arg := Procedure.first ea Nat.bits
  let i := Procedure.second ea Nat.bits
  let value := (Procedure.listGet eb b).comp (i.pair (hl.comp arg))
  exact arg.pair (i.pair value)

/-- Compile a conjunction whose operands read both the original list entry and
its binary position. -/
noncomputable def allIdxList (b : β) {items : α → List β} {t : α → ℕ → β → Term}
    (hl : Procedure ea (listCode eb) items)
    (ht : Boolean (prodCode ea (prodCode Nat.bits eb)) (fun z => t z.1 z.2.1 z.2.2)) :
    Boolean ea (fun x => Term.all ((items x).zipIdx.map fun z => t x z.2 z.1)) := by
  let step := preBool ht (withIndexedEntry b hl)
  let q := allRange (t := fun x i => t x i (((items x).drop i).headD b))
    ((NativeAIG.Emission.listUnaryLength eb b).comp hl) step
  refine q.congrFun fun x => congrArg (fun ts => CellMacro.Generator.serialized 8 ((Term.all ts).emit x.2)) ?_
  refine (map_range_getD_index (items x.1) b (t x.1)).trans ?_
  rw [List.mapIdx_eq_zipIdx_map]

/-- Emit the equality between the addressed input bit and the indicated bit of the candidate. -/
noncomputable def subtotalLane {off : α → ℕ} {k : α → NatExpr}
    (ho : Procedure ea Nat.bits off) (hk : Address ea k) :
    Boolean (prodCode ea (prodCode Nat.bits Nat.bits)) (fun z =>
      (Term.wire (.lit (off z.1+z.2.2))).equal (.paramBit (k z.1) (.lit z.2.1))) := by
  let env := Procedure.first ea (prodCode Nat.bits Nat.bits)
  let data := Procedure.second ea (prodCode Nat.bits Nat.bits)
  let i := (Procedure.first Nat.bits Nat.bits).comp data
  let bit := (Procedure.second Nat.bits Nat.bits).comp data
  let lhs := wireBool (litAddr (Procedure.binaryAdd.comp ((ho.comp env).pair bit)))
  let rhs := paramBool (preAddr hk env) (litAddr i)
  exact equalBool lhs rhs

/-- Print the exact generator that tests every supplied bit of a subtotal. -/
noncomputable def digitChecksBool {off : α → ℕ} {bits : α → List ℕ} {k : α → NatExpr}
    (ho : Procedure ea Nat.bits off) (hs : Procedure ea (listCode Nat.bits) bits) (hk : Address ea k) :
    Boolean ea (fun x => digitChecks (off x) (bits x) (k x)) := by
  exact allIdxList (t := fun x i p => (Term.wire (.lit (off x+p))).equal (.paramBit (k x) (.lit i)))
    0 hs (subtotalLane ho hk)

private theorem mask_bits (n : ℕ) : (2^n-1).bits = unaryCode n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : 2^(n+1)-1 = Nat.bit true (2^n-1) := by
      have hp : 0 < 2^n := pow_pos (by decide) _
      rw [pow_succ, Nat.bit_true]
      dsimp only
      omega
    rw [h, Nat.bits_append_bit _ true (by simp), ih]
    rfl

private noncomputable def fieldLimit {cap : α → ℕ} {bits : α → List ℕ}
    (hc : Procedure ea Nat.bits cap) (hs : Procedure ea (listCode Nat.bits) bits) :
    Procedure ea Nat.bits (fun x => min (cap x) (2^(bits x).length-1)) := by
  let width := (NativeAIG.Emission.listUnaryLength Nat.bits 0).comp hs
  let mask : Procedure ea Nat.bits (fun x => 2^(bits x).length-1) := width.result (fun x => (mask_bits _).symm)
  exact (Procedure.conditional (Procedure.binaryLe.comp (hc.pair mask)) hc mask).congrFun
    (fun x => by dsimp only [Function.comp_apply]; simp only [decide_eq_true_eq, min_def])

/-- Serialize the candidate loop, bounded binary subtotal guard, and the branch
rejecting an active flag for an out-of-range candidate. -/
noncomputable def finishCountStmt {base off cap : α → ℕ} {bits : α → List ℕ}
    (hBase : Procedure ea Nat.bits base) (hOff : Procedure ea Nat.bits off)
    (hCap : Procedure ea Nat.bits cap) (hBits : Procedure ea (listCode Nat.bits) bits) :
    Statement ea (fun x => finishCount (base x) (off x) (cap x) (bits x)) := by
  let k := constAddr ea (.index 0)
  let flag := prefixFlag hBase hCap (litAddr hCap) k
  let digits := digitChecksBool hOff hBits k
  let test := subAddr k (litAddr (fieldLimit hCap hBits))
  exact loopStmt (litAddr (prefixSucc hCap)) (ifEqStmt test (constAddr ea (.lit 0))
    (guardBool (impliesBool flag digits)) (guardBool (notBool flag)))

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
