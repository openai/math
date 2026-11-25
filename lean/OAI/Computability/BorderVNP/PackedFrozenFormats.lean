import OAI.Computability.BorderVNP.PackedFrozenNodeProgram
import OAI.Computability.BorderVNP.PackedFrozenBottomRows
import OAI.Computability.BorderVNP.PackedFrozenSubdivisionImage
import OAI.Computability.BorderVNP.PackedFrozenRowCapacity

/-! # Finite public row and field types of a cumulative frozen program

Each format includes the row and payload types of the physical gate frame.
The combined format is the very schema consumed by the node and subdivision
writers, with the same output coordinates and order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing Shortening Shortening.PublicCapacity

/-- Static finite row and scalar-bit types together with their physical ordering and tags. -/
structure Format where
  /-- One named slot for each candidate public record. -/
  Rows : Type
  /-- The public scalar bits retained by the frame. -/
  Payload : Type
  /-- Enumeration of all reserved row slots. -/
  [rowsFinite : Fintype Rows]
  /-- Enumeration of all physical scalar pins. -/
  [payloadFinite : Fintype Payload]
  /-- Fixed record order, relocation tags, widths and payload coordinates. -/
  schema : Schema Rows Payload

attribute [instance] Format.rowsFinite Format.payloadFinite

namespace Format

/-- Package an already checked physical schema without changing its row or field types. -/
def ofSchema {R B : Type} [Fintype R] [Fintype B] (s : Schema R B) : Format := ⟨R,B,s⟩

/-- The public bottom tape, with actual birth records and any reserved empty slots. -/
noncomputable def bottom {V : Type} [Fintype V] (rows : V → List CellSparse.Record) (holes w : ℕ) : Format :=
  ofSchema (Bottom.schema rows holes w)

/-- A disjoint copy of every prior slot in each physical child rectangle. -/
def parallel (S : Format) (k : ℕ) : Format := ofSchema (S.schema.parallel k)

/-- Concatenate two chronological blocks using the real source-word tags. -/
def append (S T : Format) : Format := ofSchema (S.schema.append T.schema)

/-- The original endpoint and inserted relay rectangle at an outer boundary. -/
def subdivision (old np extra w : ℕ) : Format := ofSchema (Subdivision.Gates.tapeSchema old np extra w)

/-- The actual joined child tapes followed by retained intervals, new birth rows and terminal hooks.
The old edge capacity and port capacity are those of the joined network. -/
noncomputable def round {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m) (A : Type)
    [Fintype A] (k old np w : ℕ) (prior : Format) : Format :=
  ofSchema (Node.schema e (0,false) (A := A) (prior.schema.parallel k) old np w)

/-- State pins after saving the named geometry, both work-width words and the cumulative tape. -/
abbrev Output (S : Format) (geometry : Type) (sites w d : ℕ) :=
  (geometry ⊕ (Fin sites × Bool × Fin w)) ⊕ Pins S.Rows S.Payload d

/-- The output cost includes only actual raw geometry, both site width words,
one owner and enable field per reserved record, and the retained scalar bits. -/
theorem output_card (S : Format) (geometry : Type) [Fintype geometry] (sites w d : ℕ) :
    Fintype.card (S.Output geometry sites w d) =
      Fintype.card geometry + sites*(2*w) + (Fintype.card S.Rows*(1+d)+Fintype.card S.Payload) := by
  simp only [Output,Pins,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_unit]

end Format

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
