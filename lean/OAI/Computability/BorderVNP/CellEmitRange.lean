import OAI.Computability.QuantumFactoring.BitStackListMapIdx
import OAI.Computability.QuantumFactoring.BitStackListMapWith
import OAI.Computability.QuantumFactoring.BitStackListWords

/-! # Native iteration for concatenating compact descriptor fragments

The counter for tabulation is unary, so no loop here requests a number of visits
exponential in a binary input length. Each visit sees the original environment
and its actual binary index. The output concatenates the separately generated
binary fragments in the given order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

/-- Tabulate a word-valued function at all smaller indices and concatenate the results. -/
noncomputable def flatRange {n : α → ℕ} {f : α → ℕ → List Bool}
    (hn : Procedure ea unaryCode n) (hf : Procedure (prodCode ea Nat.bits) id (fun x => f x.1 x.2)) :
    Procedure ea id (fun x => (List.range (n x)).flatMap (f x)) := by
  let i := Procedure.first unaryCode ea
  let env := Procedure.second unaryCode ea
  let step := hf.comp (env.pair (Procedure.unaryToBits.comp i))
  let items := (Procedure.tabulate (f := f) [] step).comp (hn.pair (Procedure.identity ea))
  exact (Procedure.listJoinWords.comp items).congrFun (fun _ => List.flatMap_def.symm)

/-- Generate a word for each entry of a named data list, then concatenate. -/
noncomputable def flatMapList (b : β) {items : α → List β} {f : α → β → List Bool}
    (hl : Procedure ea (listCode eb) items)
    (hf : Procedure (prodCode ea eb) id (fun x => f x.1 x.2)) :
    Procedure ea id (fun x => (items x).flatMap (f x)) := by
  let q := (Procedure.listMapWith b [] hf).comp ((Procedure.identity ea).pair hl)
  exact (Procedure.listJoinWords.comp q).congrFun (fun _ => List.flatMap_def.symm)

/-- Use each entry's zero-based binary index together with the original list data. -/
noncomputable def flatMapIdxList (b : β) {items : α → List β} {f : α → ℕ → β → List Bool}
    (hl : Procedure ea (listCode eb) items)
    (hf : Procedure (prodCode ea (prodCode Nat.bits eb)) id (fun x => f x.1 x.2.1 x.2.2)) :
    Procedure ea id (fun x => ((items x).mapIdx (f x)).flatten) :=
  Procedure.listJoinWords.comp ((Procedure.listMapIdxWith b [] hf).comp ((Procedure.identity ea).pair hl))

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
