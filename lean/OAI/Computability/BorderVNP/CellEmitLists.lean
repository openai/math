import OAI.Computability.BorderVNP.CellEmitRange
import OAI.Computability.BorderVNP.CellEmitWord
import OAI.Computability.BorderVNP.CellSerializedLength

/-! # Concatenating static record bodies into a compact command sequence -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram CellMacro.Generator

/-- Serialized sequences concatenate their component streams, including the empty sequence. -/
theorem serialized_sequence_list (d : ℕ) (l : List Stmt) :
    serialized d (sequence l) = l.flatMap (serialized d) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.flatMap_cons,sequence,List.foldr_cons,serialized,wire,records_append] using
      congrArg (serialized d x ++ ·) ih

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

/-- Visit each metadata record and emit the corresponding stored command tree. -/
noncomputable def sequenceMap (b : β) {l : α → List β} {f : α → β → Stmt}
    (hl : Procedure ea (listCode eb) l) (hf : Statement (prodCode ea eb) (fun z => f z.1 z.2)) :
    Statement ea (fun x => sequence ((l x).map (f x))) :=
  (flatMapList (f := fun a i => serialized 8 (f a i)) b hl hf).congrFun (fun x => by rw [serialized_sequence_list,List.flatMap_def,List.flatMap_def,List.map_map]; rfl)

/-- Emit a command body for each explicitly stored row together with its zero-based index. -/
noncomputable def sequenceMapIdx (b : β) {l : α → List β} {f : α → ℕ → β → Stmt}
    (hl : Procedure ea (listCode eb) l)
    (hf : Statement (prodCode ea (prodCode Nat.bits eb)) (fun z => f z.1 z.2.1 z.2.2)) :
    Statement ea (fun x => sequence ((l x).zipIdx.map fun z => f x z.2 z.1)) :=
  (flatMapIdxList (f := fun a i b => serialized 8 (f a i b)) b hl hf).congrFun (fun x => by
    rw [serialized_sequence_list,List.mapIdx_eq_zipIdx_map,List.flatMap_def,List.map_map]
    rfl)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
