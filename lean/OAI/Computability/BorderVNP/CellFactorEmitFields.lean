import OAI.Computability.BorderVNP.CellProfileEmitAddress
import OAI.Computability.BorderVNP.CellSparseFactorCode
import OAI.Computability.QuantumFactoring.BitStackOptions

/-! # Typed factor fields for the one-copy private table printer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.FactorData

open ExactQuantumFactoring.BitStackProgram

private abbrev B := prodCode Typed.naturals Typed.booleans
private abbrev N := prodCode Typed.naturals Typed.naturals
private abbrev U := prodCode Nat.bits Typed.port

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → Factor}

/-- Four real binary-tag branches retrieve a payload field or return its caller-supplied
default. The computational branch is selected by the typed factor's actual constructor. -/
noncomputable def fold {ba bb : List ℕ × List Bool → β} {bc : List ℕ × List ℕ → β} {bd : ℕ × Port → β}
    (p : Procedure ea Typed.factor f)
    (a : Procedure B eb ba) (b : Procedure B eb bb) (c : Procedure N eb bc) (d : Procedure U eb bd) :
    Procedure ea eb (fun x => Sum.elim ba (Sum.elim bb (Sum.elim bc bd)) (Typed.factorFields (f x))) := by
  let z := (Procedure.casesSum a (Procedure.casesSum b (Procedure.casesSum c d))).precompose Typed.factorFields
  exact z.comp p

/-- Evaluate a truth table on the four constructor tags. -/
def tag (a b c d : Bool) : Factor → Bool
  | .truth .. => a
  | .sign .. => b
  | .gadget .. => c
  | .unary .. => d

/-- Compile a constructor-tag predicate. -/
noncomputable def tagP (a b c d : Bool) (p : Procedure ea Typed.factor f) :
    Procedure ea Procedure.boolCode (fun x => tag a b c d (f x)) :=
  (fold p (Procedure.constant B Procedure.boolCode a) (Procedure.constant B Procedure.boolCode b) (Procedure.constant N Procedure.boolCode c)
    (Procedure.constant U Procedure.boolCode d)).congrFun (fun x => by cases f x <;> rfl)

/-- Wire numbers in a one-copy truth, sign, or gadget table. -/
def wires : Factor → List ℕ
  | .truth ws _ | .sign ws _ | .gadget ws _ => ws
  | .unary .. => []

/-- Retrieve the literal list of wire offsets from the selected constructor. -/
noncomputable def wiresP (p : Procedure ea Typed.factor f) :
    Procedure ea Typed.naturals (fun x => wires (f x)) :=
  (fold p (Procedure.first ..) (Procedure.first ..) (Procedure.first ..) (Procedure.constant U Typed.naturals []))
    |>.congrFun (fun x => by cases f x <;> rfl)

/-- The Boolean rows of a truth or sign table. -/
def boolRows : Factor → List Bool
  | .truth _ bs | .sign _ bs => bs
  | _ => []

/-- Retrieve the Boolean table without converting any row to a field element. -/
noncomputable def boolRowsP (p : Procedure ea Typed.factor f) :
    Procedure ea Typed.booleans (fun x => boolRows (f x)) :=
  (fold p (Procedure.second ..) (Procedure.second ..) (Procedure.constant N Typed.booleans [])
    (Procedure.constant U Typed.booleans [])).congrFun (fun x => by cases f x <;> rfl)

/-- Natural-number identifiers of a gadget table. -/
def ids : Factor → List ℕ
  | .gadget _ is => is
  | _ => []

/-- Retrieve all gadget position identifiers in table order. -/
noncomputable def idsP (p : Procedure ea Typed.factor f) : Procedure ea Typed.naturals (fun x => ids (f x)) :=
  (fold p (Procedure.constant B Typed.naturals []) (Procedure.constant B Typed.naturals [])
    (Procedure.second ..) (Procedure.constant U Typed.naturals [])).congrFun (fun x => by cases f x <;> rfl)

/-- The unary wire offset and reported use-bit port. -/
def unaryFields : Factor → ℕ × Port
  | .unary n p => (n,p)
  | _ => (0,⟨0,0,0⟩)

/-- Retrieve the two fields of the unary-use constructor. -/
noncomputable def unaryP (p : Procedure ea Typed.factor f) : Procedure ea U (fun x => unaryFields (f x)) :=
  (fold p (Procedure.constant B U (0,⟨0,0,0⟩)) (Procedure.constant B U (0,⟨0,0,0⟩))
    (Procedure.constant N U (0,⟨0,0,0⟩)) (Procedure.identity U)).congrFun (fun x => by cases f x <;> rfl)

/-- Physically recompute a shifted literal port base and preserve its two encoded strides. -/
noncomputable def shiftPort {aux : α → ℕ} {p : α → Port}
    (ha : Procedure ea Nat.bits aux) (hp : Procedure ea Typed.port p) :
    Procedure ea Typed.port (fun x => (p x).shift (aux x)) := by
  let v := ProfileData.portFields.comp hp
  let first := (Procedure.first ..).comp v
  let rest := (Procedure.second ..).comp v
  exact ((Procedure.binaryAdd.comp (ha.pair first)).pair rest).result (fun _ => rfl)

end CellSparse.Packet.Emit.FactorData

end BorderVNP
end Computability
end OAI
