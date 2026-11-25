import OAI.Computability.BorderVNP.FiniteEvaluatorCellsCubeNative

/-! # Report-dependent field descriptions for a single fixed physical decoder

The private report choices change the bytes described at the source. Every
sparse description nevertheless drives the same physical table and field
return. This permits one fixed machine before any report choices are made.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA

/-- Use the attained logical sparse fields in the proof of a fixed decoder. -/
def Cells.Codec.withFields (codec : Cells.Codec) (fields : ℕ → SparseExterior.Field) : Cells.Codec :=
  match codec with
  | .dense => .dense
  | .sparse _ => .sparse fields

/-- For every trace budget the proof's fields yield exactly the same native
field weighted sum on the actual instruction table. -/
theorem Cells.Codec.bounded_withFields {F : Type*} [Field F] [Fintype F] {w : ℕ}
    (codec : Cells.Codec) (fields : ℕ → SparseExterior.Field) (pub : Arg → Word w)
    (fuel : ℕ) (c : Code) (s : Bank w) (m : Memory w) (ticks burst clock : ℕ) :
    boundedWeight pub (Cells.library F (codec.withFields fields)) (Cells.terminals F (codec.withFields fields))
      fuel c s m ticks burst clock =
    boundedWeight pub (Cells.library F codec) (Cells.terminals F codec) fuel c s m ticks burst clock := by
  cases codec <;> rfl

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
