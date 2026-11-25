import OAI.Computability.BorderVNP.CellGadgetEmit
import OAI.Computability.BorderVNP.CellDirectoryInputSize

/-! # Inputs and compact output lengths of individual reported subtotal rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram CellMacro.Generator

/-- The actual native child invoked by the subtotal pass at one indexed report. -/
noncomputable def reportRow :
    Statement (prodCode Typed.directory (prodCode Nat.bits Typed.naturals))
      (fun x => Gadget.row x.1 x.2.1 x.2.2) := by
  let env := Procedure.first Typed.directory (prodCode Nat.bits Typed.naturals)
  let entry := Procedure.second Typed.directory (prodCode Nat.bits Typed.naturals)
  exact gadgetRowStmt ((Procedure.identity Typed.directory).comp env)
    ((Procedure.first Nat.bits Typed.naturals).comp entry) ((Procedure.second Nat.bits Typed.naturals).comp entry)

private theorem piece_length {T : Type} (f : T → List Bool) (xs : List T) (x : T) (hx : x ∈ xs) :
    (f x).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp at hx
  | cons t ts ih =>
    rw [List.flatMap_cons,List.length_append]
    rcases List.mem_cons.mp hx with rfl | hm
    · exact Nat.le_add_right ..
    · exact (ih hm).trans (Nat.le_add_left ..)

/-- The serialization of each report row is a contiguous component of the full
private directory serialization. Consequently a size bound on the whole directory
also bounds every true output retained during indexed report compilation. -/
theorem reportRow_output_length (D : Directory) (p : ℕ) (i : Fin D.reportedCounts.length) :
    (serialized 8 (Gadget.row D i D.reportedCounts[i])).length ≤ (serialized 8 (D.program p)).length := by
  have hr : Gadget.row D i D.reportedCounts[i] ∈ D.reportedCounts.zipIdx.map (fun z => Gadget.row D z.2 z.1) :=
    List.mem_map.mpr ⟨(D.reportedCounts[i],i.val),List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem i.isLt),rfl⟩
  have hs : (serialized 8 (Gadget.row D i D.reportedCounts[i])).length ≤ (serialized 8 D.subtotalGuards).length := by
    rw [Directory.subtotalGuards,serialized_sequence_list]
    exact piece_length _ _ _ hr
  apply hs.trans
  simp only [Directory.program,Directory.checkAssignment,Directory.countGuards,serialized,wire,records_append,List.length_append]
  omega

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
