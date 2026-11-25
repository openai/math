import OAI.Computability.NearSquareRoot.CRTPositionProgram
import OAI.Computability.NearSquareRoot.CRTControlledSizes
import OAI.Computability.IntegerMultiplication.Carry.Figure

/-! # Preparing the physical dispatch header from a position table

The image table determines its width by its list length. The program computes
the logarithmic guard, assembles the opcodes, and supplies the original width
alongside each opcode.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Staff IntegerMultiplication.Carry Reflections

private def tableRegime : Regime Table := ⟨size,send,Dom.base _⟩

private theorem realize_table_width : Realizes tableRegime (fun t : Table => t.length) := by
  change Poly (fun t : Table => tally t.length)
  have h := (Easy.identity (X := Table)).ruler.poly
  simpa only [ruler, tally, List.map_const', id_eq] using h

/-- Compute the guard width in unary using just the input image table. -/
theorem tableGuard_poly : Poly (fun t : Table => tally (guardWidth t.length)) := by
  have h := (Figure.of_spoken (realize_table_width.plus (Realizes.fix 1))).short_log
  exact (Realizes.fix 7).plus ((Realizes.fix 2).times h)

/-- Produce the complete chronological list of dispatch keys. -/
def tableHeader (t : Table) : List (Tally × Op) :=
  polyPush id (ruler t,assemble (tally (guardWidth t.length),t))

theorem tableHeader_poly : Poly tableHeader := by
  have ops := (tableGuard_poly.pair Poly.identity).compose assemble_poly
  exact ((Easy.ruler Easy.identity).poly.pair ops).compose
    (Poly.push ([] : Tally) (swapChunks (0,1)) Poly.identity)

private theorem encode_header {n : ℕ} (p : Equiv.Perm (Fin n)) :
    send (tableHeader (table p)) = Task.forest (fun q => send (tally n,q))
      (assemble (tally (guardWidth n),table p)) := by
  have len : (table p).length = n := List.length_ofFn
  have ruler_eq : ruler (table p) = tally n := by rw [← recover_tally (ruler (table p)),ruler_length,len]
  simp only [tableHeader,polyPush,id_eq,ruler_eq,len,← Task.forest_send,Task.forest_map]

variable {X : Type*} (k : X → ℕ) (p : (x : X) → Equiv.Perm (Fin (k x)))

private theorem table_input_dom : Dom k (fun x => size (table (p x))) :=
  ⟨2,2, fun x => table_size (p x)⟩

/-- Uniform table-only setup of the width-annotated physical opcode forest. -/
theorem tableHeader_setup :
    Task.BT k (fun x => send (table (p x))) (fun x =>
      Task.forest (fun q => send (tally (k x),q)) (assemble (tally (guardWidth (k x)),table (p x)))) := by
  simp_rw [← encode_header]
  exact tableHeader_poly.on (table_input_dom k p)

/-- The size bound includes the copy of the width on every entry. -/
theorem tableHeader_dom :
    Dom k (fun x => (Task.forest (fun q => send (tally (k x),q))
      (assemble (tally (guardWidth (k x)),table (p x)))).count) :=
  (tableHeader_setup k p).length (table_input_dom k p)

private theorem entry_count {α : Type*} (f : α → Tree) (s : List α) {q : α} (h : q ∈ s) :
    (f q).count ≤ (Task.forest f s).count := by
  induction s with
  | nil => contradiction
  | cons a s ih =>
    rw [Task.forest_cons,Tree.count]
    rcases List.mem_cons.mp h with rfl | e
    · omega
    · have u := ih e
      omega

/-- A shared polynomial bounds every dispatch key in the chronological list. -/
theorem tableHeader_keys :
    ∃ d C : ℕ, ∀ x, ∀ q ∈ assemble (tally (guardWidth (k x)),table (p x)),
      size (tally (k x),q) ≤ C * (k x+1)^d := by
  obtain ⟨d,C,bound⟩ := tableHeader_dom k p
  exact ⟨d,C,fun x _ h => (entry_count _ _ h).trans (bound x)⟩

theorem tableHeader_key_dom (q : X → Op)
    (hq : ∀ x, q x ∈ assemble (tally (guardWidth (k x)),table (p x))) :
    Dom k (fun x => size (tally (k x),q x)) := by
  obtain ⟨d,C,bound⟩ := tableHeader_keys k p
  exact ⟨d,C,fun x => bound x _ (hq x)⟩

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
