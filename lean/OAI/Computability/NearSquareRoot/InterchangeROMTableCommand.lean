import OAI.Computability.NearSquareRoot.InterchangeROMTableDecode
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPRDecode
import OAI.Computability.NearSquareRoot.ScheduleRegisterTableEffective

/-! # Effective two-register code for each matrix slot of a searched repair ROM -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMTable

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open InterchangeROMRepair GeneratorSyntax

def slotCommand (p pitch slot : ℕ) (tape : Raw.Tape) (outIdx inIdx : List ℕ) : Cmd :=
  RegisterTable.command (slotTable p pitch slot tape outIdx inIdx)

theorem slotCommand_within (p pitch slot : ℕ) (tape : Raw.Tape) (outIdx inIdx : List ℕ) :
    CommonRegisters.Within 2 (slotCommand p pitch slot tape outIdx inIdx) :=
  RegisterTable.within (le_refl 2) _

theorem effective_slotCommand {X : Type} [Primcodable X] {p pitch slot : X → ℕ}
    {tape : X → Raw.Tape} {outIdx inIdx : X → List ℕ}
    (hp : Computable p) (hc : Computable pitch) (hs : Computable slot)
    (ht : Computable tape) (ho : Computable outIdx) (hi : Computable inIdx) :
    Effective ltr (fun x => slotCommand (p x) (pitch x) (slot x) (tape x) (outIdx x) (inIdx x)) :=
  RegisterTable.effective (computable_spelled_slotTable hp hc hs ht ho hi)

theorem slotCommand_run {rows cols : ℕ} (p slot : ℕ) (tape : Raw.Tape)
    (input : Series (Fin cols)) (output : Series (Fin rows)) (x : Fin cols → ZMod (p+1))
    (env : Env) (r : Deck) :
    let outIdx := output.tab Fin.val
    let inIdx := input.tab Fin.val
    let t := slotTable p cols slot tape outIdx inIdx
    let M := Raw.interpret p rows cols (Raw.atSlot tape slot cols)
    let u := stripe input (fun j => numeral (x j).val)
    let v := stripe output (fun i => numeral (M.mulVec x i).val)
    Fits env (slotCommand p cols slot tape outIdx inIdx) (pile 0 u r) (pile 0 v r)
      (RegisterTable.cost t) := by
  have h := slotTable_correct p slot tape input output x
  exact RegisterTable.run_lookup _ _ _ h.2 h.1 env r

/-- All the matrix-shaped operands in a decoded repair template, in the exact
slot numbering of the searched certificate. -/
inductive MatrixRole (m : ℕ)
  | base
  | term (j : Fin m)
  | extract
  | restore
  | correct (η : Fin m → Bool) (out inp : Bool)

namespace MatrixRole

variable {m : ℕ}

def slot : MatrixRole m → ℕ
  | .base => 0
  | .term j => 1+j.val
  | .extract => 1+m
  | .restore => 2+m
  | .correct η o i => 3+m+4*(Raw.mask η).val+2*o.toNat+i.toNat

def rows (w s : ℕ) : MatrixRole m → ℕ
  | .extract | .correct .. => s
  | _ => w

def cols (w s : ℕ) : MatrixRole m → ℕ
  | .restore | .correct .. => s
  | _ => w

def matrix {p w s : ℕ} (T : Spec (ZMod (p+1)) (Fin w) (Fin s) m) (k : MatrixRole m) :
    Matrix (Fin (k.rows w s)) (Fin (k.cols w s)) (ZMod (p+1)) :=
  match k with
  | .base => T.base
  | .term j => T.term j
  | .extract => T.extract
  | .restore => T.restore
  | .correct η o i => T.correct η o i

theorem matrix_decode (p w s : ℕ) (t : Raw.Tape) (k : MatrixRole m) :
    k.matrix (Raw.decode p w s m t) = Raw.interpret p (k.rows w s) (k.cols w s)
      (Raw.atSlot t k.slot (k.cols w s)) := by cases k <;> rfl

/-- The register compiler and the semantic algebra address the identical slot. -/
theorem run (p w s : ℕ) (tape : Raw.Tape) (k : MatrixRole m)
    (input : Series (Fin (k.cols w s))) (output : Series (Fin (k.rows w s)))
    (x : Fin (k.cols w s) → ZMod (p+1)) (env : Env) (r : Deck) :
    let outIdx := output.tab Fin.val
    let inIdx := input.tab Fin.val
    let t := slotTable p (k.cols w s) k.slot tape outIdx inIdx
    let M := k.matrix (Raw.decode p w s m tape)
    let u := stripe input (fun j => numeral (x j).val)
    let v := stripe output (fun i => numeral (M.mulVec x i).val)
    Fits env (slotCommand p (k.cols w s) k.slot tape outIdx inIdx)
      (pile 0 u r) (pile 0 v r) (RegisterTable.cost t) := by
  simpa only [matrix_decode] using slotCommand_run p k.slot tape input output x env r

end MatrixRole
end InterchangeROMTable

end NearSquareRoot
end Computability
end OAI
